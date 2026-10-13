(* Backend that hands a system of polynomial quantified entailments to the
   external PolyQEnt tool.  Its unknowns must be real-valued constants
   (template coefficients); a problem with any other unknown, such as a
   predicate, is refused with an [Error] before anything is written.  The
   entailments are printed as SMT-LIB assertions to a per-process file and
   PolyQEnt is run on it as a separate process (under [timeout] when a budget
   is given); a [sat] answer's model is parsed back into real values.
   PolyQEnt's [unsat] and [unknown] both become the [Unknown] verdict, since
   neither shows that no real assignment exists; a non-zero exit or empty
   output becomes an [Error]. *)
open Core
open Common
open Common.Ext
open Ast
open Ast.Logic

module type SolverType = sig
  val solve :
    ?timeout:int option ->
    ?print_sol:bool ->
    PCSP.Problem.t ->
    PCSP.Problem.solution Or_error.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (* PolyQEnt decides polynomial quantified entailments: its unknowns are
     real-valued template coefficients, declared as constants, and it has no
     notion of an unknown predicate (the translation below declares every
     unknown that some constraint mentions as a [Real] constant).  A problem with one -- any CHC or pCSP
     input given to this backend directly -- used to fail inside the
     translation below with a message about SMT printing or the clausal form,
     reported as a crash; it is a pairing this backend declines. *)
  let non_real_unknowns pqes =
    Map.Poly.fold
      (PCSP.Problem.senv_of @@ PCSP.Problem.remove_unused_params pqes)
      ~init:[]
      ~f:(fun ~key ~data acc ->
        if ExtTerm.is_real_sort data then acc else key :: acc)

  let solve ?(timeout = None) ?(print_sol = false) pqes =
    match non_real_unknowns pqes with
    | _ :: _ as unknowns ->
        Or_error.error_string
        @@ sprintf
             "PolyQEnt solves polynomial quantified entailments whose \
              unknowns are real-valued template coefficients, but this \
              problem has %d unknown(s) of another sort, such as a predicate: \
              %s.  Use PCSat."
             (List.length unknowns)
             (String.concat ~sep:", " (List.rev_map unknowns ~f:Ident.name_of_tvar))
    | [] ->
    if false then (
      Debug.print @@ lazy (PCSP.Problem.str_of pqes);
      Debug.print @@ lazy "");
    let filename =
      (* the process id keeps two concurrent runs in one directory from writing,
         reading and overwriting the same file, which fed PolyQEnt another
         run's half-written text *)
      sprintf "temp_polyqent_p%d.smt2" (Pid.to_int @@ Core_unix.getpid ())
    in
    (* output generated PQEs *)
    let s =
      if true then (
        let pqes =
          PCSP.Problem.elim_ite_quant @@ PCSP.Problem.remove_unused_params pqes
        in
        Debug.print ~id:None
        @@ lazy
             (sprintf "******* if-eliminated PQEs:\n%s"
             @@ PCSP.Problem.str_of pqes);
        let esenv = PCSP.Problem.senv_of pqes in
        String.concat
          ((Map.data
           @@ Map.Poly.mapi esenv ~f:(fun ~key ~data ->
               assert (ExtTerm.is_real_sort data);
               "(declare-const " ^ Ident.name_of_tvar key ^ " Real)\n"))
          @ Set.to_list
              (Set.Poly.filter_map (PCSP.Problem.formulas_of pqes)
                 ~f:(fun (usenv, c) ->
                   let phi = Logic.ExtTerm.to_old_fml esenv usenv c in
                   if LogicOld.Formula.is_true @@ Evaluator.simplify phi then
                     None
                   else
                     Option.return
                     @@ sprintf "(assert %s)\n"
                          (let s =
                             let phis =
                               LogicOld.Formula.disjuncts_list_of phi
                             in
                             let phis1, phis2 =
                               List.partition_map phis ~f:(function
                                 | LogicOld.Formula.UnaryOp (Not, phi, _) ->
                                     First phi
                                 | phi ->
                                     Second phi (*ToDo: [phi] may contain =>*))
                             in
                             SMT.Smtlib2.str_of_formula
                             @@
                             if List.is_empty phis1 then
                               let conc =
                                 LogicOld.Formula.or_of
                                   phis2 (*ToDo: phis2 may contain =>?*)
                               in
                               if
                                 Map.is_empty usenv
                                 || LogicOld.Formula.is_imply conc
                               then conc
                               else
                                 (*ToDo: PolyQEnt requires this dummy condition*)
                                 LogicOld.(
                                   Formula.mk_imply
                                     (Atom.elim_true (Formula.mk_true ()))
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
          @ [ "(check-sat)\n"; "(get-model)\n" ]))
      else
        Printer.Smtlib2.of_pcsp ~id:None (*ToDo*) ~add_missing_forall:false pqes
    in
    Out_channel.with_file filename ~f:(fun channel ->
        Format.fprintf (Format.formatter_of_out_channel channel) "%s@." s);
    (* why PolyQEnt gave no answer, for the error message: a non-zero exit
       (its own parse error on a non-polynomial term is the usual case) or no
       output at all *)
    let failure_reason = ref "" in
    let res =
      (* PolyQEnt d9a87b83d406c21e904467c3a0549ed5e1e89b0d *)
      let cmd =
        (match
           match timeout with Some _ -> timeout | None -> config.timeout
         with
          | None -> ""
          | Some timeout -> sprintf "timeout %f " (float_of_int timeout /. 1000.))
        ^ Filename.quote config.path ^ " " ^ Filename.quote filename
        ^ if String.is_empty config.config_path then ""
          else " " ^ Filename.quote config.config_path
      in
      let (s0, ss1), status =
        Common.Util.Command.read_process cmd ~f:(fun cin ->
          let s0 =
            ignore (In_channel.input_line cin);
            In_channel.input_line cin
          in
          let ss1 =
            ignore (In_channel.input_line cin);
            let rec loop acc =
              match In_channel.input_line cin with
              | None -> acc
              | Some s -> loop (s :: acc)
            in
            List.rev @@ loop []
          in
          (s0, ss1))
      in
      match (status, s0) with
      | Error err, _ ->
          Debug.print
          @@ lazy (Core_unix.Exit_or_signal.to_string_hum (Error err));
          Debug.print @@ lazy "Error";
          failure_reason :=
            sprintf "PolyQEnt %s on %s, which this run keeps for inspection"
              (Core_unix.Exit_or_signal.to_string_hum (Error err))
              filename;
          None
      | Ok _, Some "The system is sat" ->
          let ss =
            let rec loop acc = function
              | [] -> if String.(acc = "") then [] else [ acc ]
              | s :: ss ->
                  if String.contains s ':' then
                    if String.(acc = "") then loop s ss else acc :: loop s ss
                  else loop (acc ^ s) ss
            in
            loop "" ss1
          in
          Some (Some ss)
      | Ok _, Some "The system is unsat" -> Some None
      (* PolyQEnt could not decide the system.  Reported as the [unknown]
         verdict, the same as its [unsat] just above (which is also not a
         conclusion about the entailment): turning it into an exception made
         the tool print a backtrace where it had an answer to give. *)
      | Ok _, Some "The system is unknown" -> Some None
      | Ok _, Some s -> failwith s
      | Ok _, None ->
          failure_reason := "PolyQEnt printed no answer";
          None
    in
    let open Or_error in
    (match res with
      | None ->
          Or_error.error_string
          @@ sprintf "PQE solving failed: %s" !failure_reason
      | Some (Some ss) ->
          Debug.print @@ lazy "satisfiable";
          let model =
            List.map ss ~f:(fun s ->
                match String.split s ~on:':' with
                | [ v; r ] -> (
                    let r =
                      try
                        Typeinf.typeinf_term
                          ~print:(fun _ -> ())
                          ~sort_opt:(Some LogicOld.T_real.SReal)
                          ~default:(Some LogicOld.T_real.SReal (*ToDo*))
                        @@ SMT.Smtlib2.of_term ~print:Debug.print ~inline:true
                             SMT.Problem.
                               {
                                 decl_reading = SMT.Problem.Synthesize;
                                 candidates = Map.Poly.empty;
                                 uni_sort = Set.Poly.empty;
                                 uni_senv = Map.Poly.empty;
                                 exi_senv = Map.Poly.empty;
                                 dep_map = Map.Poly.empty;
                                 kind_map = Map.Poly.empty;
                                 fenv = Map.Poly.empty;
                                 dtenv = Map.Poly.empty;
                               }
                        @@ SMT.Parser.sexp SMT.Lexer.token
                        @@ Lexing.from_string r
                      with exn ->
                        Debug.print @@ lazy ("Failed to parse: " ^ r);
                        if true then raise exn else LogicOld.T_real.rzero ()
                    in
                    (*print_endline @@ LogicOld.Term.str_of r;*)
                    ( Ident.Tvar v,
                      match Evaluator.eval_term r with
                      | Value.Real r -> ExtTerm.mk_real r
                      | _ -> failwith ("unexpected @ 1" ^ s) ))
                | _ -> failwith ("unexpected @ 2: " ^ s))
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
