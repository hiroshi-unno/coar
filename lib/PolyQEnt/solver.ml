open Core
open Common
open Common.Ext
open Ast
open Ast.Logic

module type SolverType = sig
  val solve :
    ?print_sol:bool -> PCSP.Problem.t -> PCSP.Problem.solution Or_error.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let solve ?(print_sol = false) pqes =
    if false then (
      Debug.print @@ lazy (PCSP.Problem.str_of pqes);
      Debug.print @@ lazy "");
    let filename = "temp_polyqent.smt2" in
    (* output generated PQEs *)
    let ppf =
      Format.formatter_of_out_channel
      @@ if true then Stdlib.open_out filename else Out_channel.stdout
    in
    let s =
      if true then
        let pqes =
          PCSP.Problem.elim_ite_prob @@ PCSP.Problem.remove_unused_params pqes
        in
        let esenv = PCSP.Problem.senv_of pqes in
        String.concat
          ((Map.data
           @@ Map.Poly.mapi esenv ~f:(fun ~key ~data ->
                  assert (ExtTerm.is_real_sort data);
                  "(declare-const " ^ Ident.name_of_tvar key ^ " Real)\n"))
          @ Set.to_list
              (Set.Poly.map (PCSP.Problem.formulas_of pqes)
                 ~f:(fun (usenv, c) ->
                   sprintf "(assert %s)\n"
                     (let s =
                        let phi = Logic.ExtTerm.to_old_fml esenv usenv c in
                        let phis = LogicOld.Formula.disjuncts_list_of phi in
                        let phis1, phis2 =
                          List.partition_map phis ~f:(function
                            | LogicOld.Formula.UnaryOp (Not, phi, _) ->
                                First phi
                            | phi -> Second phi (*ToDo: [phi] may contain =>*))
                        in
                        SMT.Smtlib2.str_of_formula
                        @@
                        if List.is_empty phis1 then
                          let conc =
                            LogicOld.Formula.or_of
                              phis2 (*ToDo: phis2 may contain =>?*)
                          in
                          if
                            Map.is_empty usenv || LogicOld.Formula.is_imply conc
                          then conc
                          else
                            (*ToDo: PolyQEnt requires this dummy condition*)
                            LogicOld.(
                              Formula.mk_imply
                                (Formula.eq (T_real.rzero ()) (T_real.rzero ()))
                                conc)
                        else
                          LogicOld.Formula.mk_imply
                            (LogicOld.Formula.and_of phis1)
                            (LogicOld.Formula.or_of phis2)
                      in
                      if Map.is_empty usenv then s
                      else
                        sprintf "(forall (%s) %s)"
                          (String.concat_map_list ~sep:" "
                             (Map.Poly.to_alist usenv) ~f:(fun (x, sort) ->
                               sprintf "(%s %s)" (Ident.name_of_tvar x)
                                 (SMT.Smtlib2.str_of_sort
                                    (ExtTerm.to_old_sort sort))))
                          s)))
          @ [ "(check-sat)\n"; "(get-model)\n" ])
      else
        Printer.Smtlib2.of_pcsp ~id:None (*ToDo*) ~add_missing_forall:false pqes
    in
    Format.fprintf ppf "%s@." s;
    let res =
      (* PolyQEnt d9a87b83d406c21e904467c3a0549ed5e1e89b0d *)
      let cmd = config.path ^ " " ^ filename ^ " " ^ config.config_path in
      let cin = Core_unix.open_process_in cmd in
      let s0 =
        ignore (In_channel.input_line cin);
        In_channel.input_line cin
      in
      let s1 =
        ignore (In_channel.input_line cin);
        let rec loop acc =
          match In_channel.input_line cin with
          | None -> acc
          | Some s -> loop (s :: acc)
        in
        List.rev @@ loop []
      in
      In_channel.close cin;
      match (Core_unix.close_process_in cin, s0) with
      | Error err, _ ->
          Debug.print
          @@ lazy (Core_unix.Exit_or_signal.to_string_hum (Error err));
          Debug.print @@ lazy "Error";
          None
      | Ok _, Some "The system is sat" -> Some (Some s1)
      | Ok _, Some "The system is unsat" -> Some None
      | Ok _, Some s -> failwith s
      | Ok _, None -> None
    in
    let open Or_error in
    (match res with
    | None -> Or_error.error_string "PQE solving failed"
    | Some (Some ss) ->
        Debug.print @@ lazy "satisfiable";
        let model =
          List.map ss ~f:(fun s ->
              match String.split s ~on:':' with
              | [ v; r ] -> (
                  let r =
                    Typeinf.typeinf_term
                      ~print:(fun _ -> ())
                      ~sort_opt:(Some LogicOld.T_real.SReal)
                      ~instantiate_num_to_int:false
                    @@ SMT.Smtlib2.of_term ~print:Debug.print ~inline:true
                         SMT.Problem.
                           {
                             uni_senv = Map.Poly.empty;
                             exi_senv = Map.Poly.empty;
                             kind_map = Map.Poly.empty;
                             fenv = Map.Poly.empty;
                             dtenv = Map.Poly.empty;
                           }
                    @@ SMT.Parser.sexp SMT.Lexer.token
                    @@ Lexing.from_string r
                  in
                  (*print_endline @@ LogicOld.Term.str_of r;*)
                  ( Ident.Tvar v,
                    match Evaluator.eval_term r with
                    | Value.Real r -> ExtTerm.mk_real r
                    | _ -> failwith "unexpected" ))
              | _ -> failwith "unexpected")
        in
        Ok (PCSP.Problem.Sat (Map.Poly.of_alist_exn model))
    | Some None ->
        (* We cannot conclude that PQEs is unsatisfiable, even though PolyQEnt reports unsat. *)
        Debug.print @@ lazy "unknown";
        Ok PCSP.Problem.Unknown)
    >>= fun sol ->
    if print_sol then print_endline (PCSP.Problem.str_of_sol_with_witness sol);
    Ok sol
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
