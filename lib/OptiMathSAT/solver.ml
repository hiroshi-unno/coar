open Core
open Common.Ext
open Ast
open Ast.LogicOld

let minimize constrs obj =
  let filename =
    (* the process id keeps two concurrent runs in one directory from writing,
       reading and overwriting the same file *)
    sprintf "temp_optimathsat_p%d.smt2" (Pid.to_int @@ Core_unix.getpid ())
  in
  let senv =
    Set.union (Formula.term_sort_env_of (Formula.and_of constrs))
      (Term.term_sort_env_of obj)
  in
  (* output generated OMT *)
  let s =
    String.concat
      ("(set-logic OMT_QF_NRA)"
       :: Set.to_list
            (Set.Poly.map senv ~f:(fun (x, s) ->
                 assert (Term.is_real_sort s);
                 "(declare-const " ^ Ident.name_of_tvar x ^ " Real)\n"))
      @ List.filter_map constrs ~f:(fun phi ->
          let phi = Evaluator.simplify phi in
          if LogicOld.Formula.is_true phi then None
          else
            Option.return
            @@ sprintf "(assert %s)\n" (SMT.Smtlib2.str_of_formula phi))
      @ [ sprintf "(minimize %s)\n" (SMT.Smtlib2.str_of_term obj) ]
      @ [ "(check-sat)\n"; "(get-objectives)\n"; "(get-model)\n" ])
  in
  Out_channel.with_file filename ~f:(fun channel ->
      Format.fprintf (Format.formatter_of_out_channel channel) "%s@." s);
  let res =
    let cmd =
      if true then (*ToDo*)
        "./optimathsat.exe -optimization=true -model_generation=true \
         -opt.strategy=ada -opt.abort_interval=2 " ^ filename
      else "./cvc5 --produce-models " ^ filename
    in
    let (s0, lines), status =
      Common.Util.Command.read_process cmd ~f:(fun cin ->
          let s0 = In_channel.input_line cin in
          let lines = In_channel.input_lines cin in
          (s0, lines))
    in
    match (status, s0) with
    | Error _err, _ -> None
    | Ok _, Some "sat" ->
        if List.is_empty lines then None
        else
          let responses =
            try SMT.Parser.program SMT.Lexer.token
                  (Lexing.from_string (String.concat ~sep:"\n" lines))
            with exn_ when not (Common.Timer.is_async exn_) -> failwith "invalid OMT response"
          in
          let open Ppx_sexp_conv_lib.Sexp in
          (match responses with
          | [ List objectives; List entries ]
            when (match objectives with
                  | Atom "objectives" :: _ | List _ :: _ -> true
                  | _ -> false) ->
              let entries = match entries with Atom "model" :: rest -> rest | _ -> entries in
              Some (Some entries)
          | _ -> failwith "invalid OMT response")
    | Ok _, Some "unsat" -> Some None
    | Ok _, Some s -> failwith s
    | Ok _, None -> None
  in
  match res with
  | None -> (*Or_error.error_string*) failwith "OMT solving failed"
  | Some (Some ss) ->
      let seen = Hash_set.create (module String) in
      let model =
        List.map ss ~f:(fun entry ->
            let open Ppx_sexp_conv_lib.Sexp in
            match entry with
            | List [ Atom "define-fun"; Atom name; List []; Atom "Real"; body ] ->
              if Hash_set.mem seen name then failwith "duplicate OMT model entry";
              Hash_set.add seen name;
              let t =
                try
                  Option.return
                  @@ Typeinf.typeinf_term
                       ~print:(fun _ -> ())
                       ~sort_opt:(Some LogicOld.T_real.SReal)
                       ~default:(Some LogicOld.T_real.SReal (*ToDo*))
                  @@ SMT.Smtlib2.of_term
                       ~print:(fun _ -> ())
                       ~inline:true
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
                  @@ body
                with exn_ when not (Common.Timer.is_async exn_) -> failwith "invalid OMT model value"
              in
              ((Ident.Tvar name, T_real.SReal), t)
            | _ -> failwith "invalid OMT model entry")
      in
      (* Callers substitute this model before evaluating the objective and bounds.
         A structurally valid partial model leaves those expressions open. *)
      Set.iter senv ~f:(fun (x, _) ->
          if not (Hash_set.mem seen (Ident.name_of_tvar x)) then
            failwith "incomplete OMT model");
      Some (None, None, model)
  | Some None -> None
