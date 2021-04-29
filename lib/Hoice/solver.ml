open Core
open Common
open Ast
open Ast.LogicOld

module Make (Cfg: Config.ConfigType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val (Debug.Config.(if config.verbose then enable else disable)))

  let ctx =
    let options =
      match config.timeout with
      | None -> []
      | Some timeout -> ["timeout", string_of_int @@ timeout * 1000]
    in
    Z3.mk_context options
  let solver = Z3.Fixedpoint.mk_fixedpoint ctx

  let rec get_status_from_hoice_output result =
    match result with
    | [] -> failwith "no result"
    | "sat" :: _ -> PCSP.Problem.Sat Map.Poly.empty(** ToDo: return a solution *)
    | "unsat" :: _ -> PCSP.Problem.Unsat
    | "timeout" :: _ -> raise PCSP.Problem.Timeout (*ToDo*)
    | msg :: tail ->
      if Str.string_match (Str.regexp "^(error \\\"$") msg 0 then
        let rec read_error errors = function
          | [] -> failwith @@ Printf.sprintf "can't read error from %s" @@ String.concat ~sep:"\n" result
          | "\")" :: tail -> errors, tail
          | error :: tail -> read_error (error :: errors) tail
        in
        let errors, tail = read_error [] tail in
        try let _ = get_status_from_hoice_output tail in
          raise @@ Z3.Error (String.concat ~sep:"\n" errors)
        with Z3.Error error ->
          raise @@ Z3.Error ((String.concat ~sep:"\n" errors) ^ "\n\n" ^ error)
      else if Str.string_match (Str.regexp "^; |===| Warning:") msg 0 then
        let rec read_warning = function
          | [] -> failwith @@ Printf.sprintf "can't read warning from %s" @@ String.concat ~sep:"\n" result
          | "; |===|" :: tail -> tail
          | _ :: tail -> read_warning tail
        in
        let tail = read_warning tail in
        get_status_from_hoice_output tail
      else
        failwith @@ Printf.sprintf "unknown result: %s" msg

  let solve ?(print_sol=false) pcsp =
    assert (Set.Poly.is_empty @@ PCSP.Problem.wfpvs_of pcsp &&
            Set.Poly.is_empty @@ PCSP.Problem.fnpvs_of pcsp
            (* ToDo: check if pcsp is of CHC *));
    let pcsp = pcsp |> PCSP.Problem.to_nnf |> PCSP.Problem.to_cnf in
    let cls = pcsp |> PCSP.Problem.clauses_of in
    let dtenv = Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx @@ PCSP.Problem.dtenv_of pcsp in
    let query_name, exi_senv =
      try
        let query_name = "__query__" in
        query_name, Logic.SortMap.add_exn (PCSP.Problem.senv_of pcsp) ~key:(Ident.Tvar query_name) ~data:Logic.BoolTerm.SBool
      with _ ->
        let query_name = "__query__hmm__" (*ToDo*) in
        query_name, Logic.SortMap.add_exn (PCSP.Problem.senv_of pcsp) ~key:(Ident.Tvar query_name) ~data:Logic.BoolTerm.SBool
    in
    let fenv = PCSP.Problem.fenv_of pcsp in
    let penv =
      List.map (Logic.SortMap.to_alist exi_senv) ~f:(fun (tvar, sort) ->
          let Ident.Tvar name = tvar in
          let arg_sorts =
            Logic.Sort.args_of sort
            |> List.map ~f:(fun s -> Z3Smt.Z3interface.of_sort ctx dtenv @@ Logic.ExtTerm.to_old_sort s) in
          let symbol = Z3.Symbol.mk_string ctx name in
          let func_decl = Z3.FuncDecl.mk_func_decl ctx symbol arg_sorts (Z3.Boolean.mk_sort ctx) in
          (Ident.Pvar name, func_decl))
    in
    let exists_query = ref false in
    List.iter ~f:(fun (_, funcdecl) -> Z3.Fixedpoint.register_relation solver funcdecl) penv;
    Set.Poly.iter cls ~f:(fun (uni_senv, ps, ns, phi) ->
        let senv = (Logic.SortMap.merge exi_senv uni_senv) in
        let ps =
          match Set.Poly.length ps with
          | 0 ->
            exists_query := true;
            Set.Poly.singleton (Atom.mk_app (Predicate.mk_var (Ident.Pvar query_name) []) [])
          | 1 -> Set.Poly.map ps ~f:(fun t -> Logic.ExtTerm.to_old_atom senv t [])
          | _ -> assert false
        in
        let ns = Set.Poly.map ns ~f:(fun t -> Logic.ExtTerm.to_old_atom senv t []) in
        let body =
          Formula.mk_neg (Logic.ExtTerm.to_old_formula senv phi []) ::
          (ns |> Set.Poly.map ~f:Formula.mk_atom |> Set.Poly.to_list)
          |> Formula.and_of
        in
        let head = 
          ps |> Set.Poly.map ~f:(fun a -> Formula.mk_atom a) |> Set.Poly.to_list |> Formula.and_of
        in
        let phi' = Formula.mk_imply body head in
        Debug.print @@ lazy (Formula.str_of phi');
        let tenv = Logic.SortMap.to_alist uni_senv |> List.map ~f:(fun (x, s) -> x, Logic.ExtTerm.to_old_sort s) in
        let c = Z3Smt.Z3interface.of_formula ctx tenv penv fenv dtenv phi' in
        Z3.Fixedpoint.add_rule solver c None);
    (* set params *)
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "print_fixedpoint_extensions") false;
    Z3.Fixedpoint.set_parameters solver params;
    (* make smt string *)
    let prefix = ref "" in
    let inputs =
      let reg_assert = Str.regexp "^(assert \\(.*\\)$" in
      let reg_forall = Str.regexp "^(forall " in
      Z3.Fixedpoint.to_string solver
      |> String.split_on_chars ~on:['\n']
      |> List.map
        ~f:(fun line ->
            if Str.string_match reg_assert line 0 then
              let matched_str = Str.matched_group 1 line in
              let line' = !prefix in
              line'
              ^
              if not @@ Str.string_match reg_forall matched_str 0 then begin
                prefix := ")\n";
                "(assert (forall () " ^ matched_str
              end else begin
                prefix := "";
                line
              end else line)
    in
    let inputs = inputs @ [ !prefix ] in
    let inputs = inputs @ if !exists_query then [ Printf.sprintf "(assert (forall () (not (%s))))" query_name ] else [] in
    let inputs = inputs @ [ "(check-sat)" ] in
    let inputs = if config.produce_proofs then
        "(set-option :produce-proofs true)" :: inputs @ ["(get-proof)"]
      else inputs in
    let inputs = inputs @ ["(exit)"] in
    Debug.print @@ lazy ("input to Hoice: " ^ String.concat ~sep:"\n" inputs);
    let args = match config.timeout with None -> [] | Some timeout -> ["--timeout"; string_of_int timeout] in
    try
      Util.Command.sync_command "hoice" args inputs
      |> get_status_from_hoice_output
      |> (fun res ->
          if print_sol then print_endline (PCSP.Problem.str_of_solution res);
          Or_error.return res)
    with
    | Util.Command.Shell_error error ->
      Debug.print @@ lazy (Printf.sprintf "Shell Error in hoice: %s\n" error);
      Or_error.error_string error
end