open Core
open Common.Ext
open Ast
open Ast.LogicOld

let minimize constrs obj =
  let filename = "temp_optimathsat.smt2" in
  (* output generated OMT *)
  let ppf =
    Format.formatter_of_out_channel
    @@ if true then Stdlib.open_out filename else Out_channel.stdout
  in
  let s =
    let senv = Formula.term_sort_env_of @@ Formula.and_of constrs in
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
  Format.fprintf ppf "%s@." s;
  let res =
    let cmd =
      if true then (*ToDo*)
        "./optimathsat.exe -optimization=true -model_generation=true \
         -opt.strategy=ada -opt.abort_interval=2 " ^ filename
      else "./cvc5 --produce-models " ^ filename
    in
    let cin = Core_unix.open_process_in cmd in
    let s0 = In_channel.input_line cin in
    let ss1 =
      ignore (In_channel.input_line cin);
      ignore (In_channel.input_line cin);
      ignore (In_channel.input_line cin);
      ignore (In_channel.input_line cin);
      ignore (In_channel.input_line cin);
      let rec loop acc =
        match In_channel.input_line cin with
        | None -> acc
        | Some s -> loop (s :: acc)
      in
      List.rev @@ List.tl_exn @@ loop []
    in
    In_channel.close cin;
    match (Core_unix.close_process_in cin, s0) with
    | Error _err, _ -> None
    | Ok _, Some "sat" -> Some (Some ss1)
    | Ok _, Some "unsat" -> Some None
    | Ok _, Some s -> failwith s
    | Ok _, None -> None
  in
  match res with
  | None -> (*Or_error.error_string*) failwith "OMT solving failed"
  | Some (Some ss) ->
      if false then print_endline (String.concat ~sep:"\n" ss);
      let model =
        let re =
          Str.regexp
            "^[ \t]*(define-fun[ \t]+\\([^ \t]+\\)[ \t]+()[ \t]+Real[ \
             \t]+\\((.*)\\))[ \t]*$"
        in
        List.filter_map ss ~f:(fun line ->
            if Str.string_match re line 0 then
              let name = Str.matched_group 1 line in
              let body = Str.matched_group 2 line in
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
                           uni_senv = Map.Poly.empty;
                           exi_senv = Map.Poly.empty;
                           kind_map = Map.Poly.empty;
                           fenv = Map.Poly.empty;
                           dtenv = Map.Poly.empty;
                         }
                  @@ SMT.Parser.sexp SMT.Lexer.token
                  @@ Lexing.from_string body
                with e ->
                  if false then print_endline (Exn.to_string e);
                  None
              in
              Some ((Ident.Tvar name, T_real.SReal), t)
            else (
              if false then print_endline line;
              None))
      in
      Some (None, None, model)
  | Some None -> None
