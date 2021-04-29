(* simple parser of fixpoint logic for debug *)

open Core
open Ast
open Ast.Logic
open Parsexp
open Problem

module Sexp = Ppx_sexp_conv_lib.Sexp

module type TermType = sig
  val of_term: Sexp.t list -> (Logic.term list, Error.t) result
  val sort_of_text: string -> Logic.Sort.t
  val term_of_op: string -> Sexp.t list -> Logic.term option
end

let count = ref 0
let get_var () = incr count; Ident.Tvar (Printf.sprintf "INV_%d" (!count))

module IntTerm : TermType = struct
  open Logic.IntTerm
  let of_term _sexps = failwith "not implemented yet"

  let sort_of_text = function
    | "Int" -> SInt
    | s -> failwith @@ Printf.sprintf "unknown sort : %s" s

  let term_of_op op args = match op with
    | "+" -> mk_add () |> Option.some
    | "-" -> begin
        match List.length args with
        | 1 -> mk_neg () |> Option.some
        | 2 -> mk_sub () |> Option.some
        | _ -> None
      end
    | "*" -> mk_mult () |> Option.some
    | "div" -> mk_div () |> Option.some
    | "mod" -> mk_mod () |> Option.some
    | "abs" -> mk_abs () |> Option.some
    | text ->
      try mk_int (Z.of_string text) |> Option.some (* assume that the text can be converted into bigint *)
      with Invalid_argument err -> failwith (op ^ " not supported by term_of_op\n" ^ err)
end

module BoolTerm : TermType = struct
  open Logic.BoolTerm
  let of_term _sexps = failwith "not implemented yet"

  let sort_of_text = function
    | "Bool" -> SBool
    | s -> failwith @@ Printf.sprintf "unknown sort : %s" s

  let term_of_op op _args = match op with
    | "true" -> mk_bool true |> Option.some
    | "false" -> mk_bool false |> Option.some
    | "not" -> mk_not () |> Option.some
    | "and" -> mk_and () |> Option.some
    | "or" -> mk_or () |> Option.some
    | "=>" -> mk_imply () |> Option.some
    | "xor" -> mk_xor () |> Option.some
    | "=" -> mk_bool_eq () |> Option.some
    | "ite" -> mk_bool_ite () |> Option.some
    | _ -> None
end

module ExtTerm : TermType = struct
  open Logic.ExtTerm

  let of_term _sexps = failwith "not implemented yet"

  let sort_of_text = function
    | "Int" -> Logic.ExtTerm.SInt
    | "Bool" -> Logic.ExtTerm.SBool
    | s -> failwith @@ Printf.sprintf "unknown sort : %s" s

  let term_of_op op args = match op with
    | "=" -> mk_int_eq () |> Option.some (* '=' is used only for comparing int value in LIA *)
    | "<=" -> mk_leq () |> Option.some
    | ">=" -> mk_geq () |> Option.some
    | "<" -> mk_lt () |> Option.some
    | ">" -> mk_gt () |> Option.some
    | op -> begin
        match BoolTerm.term_of_op op args with
        | None -> IntTerm.term_of_op op args
        | x -> x
      end
end

module Make (Term : TermType) (ProblemTerm : Problem.TermType) : sig
  val parse_term: Problem.Make(ProblemTerm).t -> (Ident.tvar, Logic.term) Map.Poly.t -> Logic.SortMap.t -> Sexp.t -> Logic.term
  val of_problem: Sexp.t list -> (Problem.Make(ProblemTerm).t, Error.t) result
end = struct
  module CFG = Problem.CFG(ProblemTerm)
  module Problem = Problem.Make(ProblemTerm)
  open Logic.Term

  let rec parse_bfTerm = function
    | Sexp.Atom idORlit -> begin
        match Term.term_of_op idORlit [] with
        | Some term -> CFG.mk_bfTerm_literal term
        | None -> failwith "unknown style of bfTerm"
      end
    | Sexp.List [Sexp.Atom "_"; _; _] -> failwith "this style of identifier is not supported yet"
    | Sexp.List (Sexp.Atom id :: bfTerms) -> begin
        match Term.term_of_op id bfTerms with
        | Some term -> List.map ~f:(parse_bfTerm) bfTerms |> CFG.mk_bfTerm_fun (CFG.mk_identifier term)
        | None -> failwith "unknown style of bfTerm"
      end
    | _ -> failwith "unknown style of bfTerm"

  let parse_gTerm = function
    | Sexp.List [Sexp.Atom "Constant"; Sexp.Atom sort] -> Term.sort_of_text sort |> CFG.mk_gTerm_constant
    | Sexp.List [Sexp.Atom "Variable"; Sexp.Atom sort] -> Term.sort_of_text sort |> CFG.mk_gTerm_variable
    | bfterm -> parse_bfTerm bfterm |> CFG.mk_gTerm_bfTerm

  let parse_cfg (symbol_def : Sexp.t list) grammer_def =
    let starting_symbol =
      match symbol_def with
      | (Sexp.List [Sexp.Atom sym; Sexp.Atom _sort]) :: _ -> CFG.mk_symbol sym
      | _ -> failwith "unknown style of symbol_def"
    in
    let grammer =
      List.map ~f:(function
          | Sexp.List [(Sexp.Atom sym); (Sexp.Atom sort); Sexp.List rule] ->
            sym, (Term.sort_of_text sort, List.map ~f:(fun r -> parse_gTerm r) rule)
          | _ -> failwith "invalid syntax in grammer"
        ) grammer_def
      |> List.fold ~f:(fun acc (sym, rule) -> Map.Poly.add_exn acc ~key:sym ~data:rule) ~init:Map.Poly.empty

    in
    CFG.mk_cfg starting_symbol grammer

  let parse_synth_fun problem name (args : Sexp.t list) (sort : Logic.Sort.t) (grammer : Sexp.t list) : Problem.t =
    let cfg =
      match grammer with
      | [Sexp.List symbol_def; Sexp.List grammer_def] -> parse_cfg symbol_def grammer_def |> Option.some
      | [] -> None
      | _ -> failwith "unknown style of a grammer of synth_fun"
    in
    let parse_arg = function
      | (Sexp.List [Sexp.Atom _name; Sexp.Atom sort]) -> Term.sort_of_text sort
      | _ -> failwith "unknown style of args"
    in
    let sort = List.fold_right ~f:(fun arg acc -> Logic.Sort.mk_arrow (parse_arg arg) acc) ~init:sort args in
    Problem.add_synth_fun problem name sort cfg

  let rec parse_term problem fenv venv = function
    | Sexp.List (Sexp.Atom op :: args) -> begin
        let open Logic.Term in
        match Problem.find_synth_fun_of problem (Ident.Tvar op) with (* uninterpreted variable *)
        | Some (_sort, _cfg) ->
          List.fold ~init:(mk_var (Ident.Tvar op)) args
            ~f:(fun acc arg -> parse_term problem fenv venv arg |> mk_app acc)
        | None -> begin
            match Map.Poly.find fenv (Ident.Tvar op) with
            | Some term -> (* if the term is an interpreted variable, sub
                              stitute it  *)
              Logic.Term.beta_reduction term (List.map ~f:(fun arg -> parse_term problem fenv venv arg) args)
            | None -> begin
                match op with
                | "+" -> Logic.IntTerm.sum (List.map ~f:(parse_term problem fenv venv) args)
                | "*" -> Logic.IntTerm.prod (List.map ~f:(parse_term problem fenv venv) args)
                | "and" -> Logic.BoolTerm.and_of (List.map ~f:(parse_term problem fenv venv) args)
                | "or" -> Logic.BoolTerm.or_of (List.map ~f:(parse_term problem fenv venv) args)
                | "let" -> begin
                    match args with
                    | [Sexp.List binds; body] ->
                      let fenv = List.fold binds ~init:fenv ~f:(fun acc -> function
                          | Sexp.List [Sexp.Atom var; _sort; def] ->
                            Map.Poly.set acc ~key:(Ident.Tvar var) ~data:(parse_term problem fenv venv def)
                          | _ -> failwith "let") in
                      parse_term problem fenv venv body
                    | _ -> failwith "let"
                  end
                | _ ->
                  match Term.term_of_op op args with
                  | Some x ->
                    List.fold ~f:(fun acc sexp -> mk_app acc (parse_term problem fenv venv sexp)) ~init:x args (* if the operator is defined in the theory *)
                  | None -> failwith @@ Printf.sprintf "unknown operator : %s" op
              end
          end
      end
    | Sexp.Atom var -> begin
        match Logic.SortMap.find venv (Ident.Tvar var) with
        | Some _sort -> mk_var (Ident.Tvar var)
        | None -> begin
            match Map.Poly.find fenv (Ident.Tvar var) with
            | Some term -> (* if the term is an interpreted variable, sub
                              stitute it  *)
              Logic.Term.beta_reduction term []
            | None -> begin
                match Term.term_of_op var [] with
                | Some term -> term (* nullary term *)
                | None -> failwith @@ Printf.sprintf "unknown operator : %s" var
              end end end
    | _ -> failwith "unknown style of constraint"

  let parse_inv_constraint problem fenv inv_f pre_f trans_f post_f =
    let open Logic.BoolTerm in
    let sort_of_inv_f =
      match Problem.find_synth_fun_of problem inv_f with
      | Some (sort, _) -> sort
      | None -> begin
          match Problem.find_synth_fun_of problem pre_f with
          | Some(sort, _) -> sort
          | None -> begin
              match Problem.find_synth_fun_of problem post_f with
              | Some(sort, _) -> sort
              | None -> failwith "sort need to be known by trans_f"
            end end
    in
    (* p1 = pre_f x1 x2 .. xn *)
    (* p2 = inv_f x1 x2 .. xn *)
    (* p3 = trans_f x1 x2 .. xn x1' x2' .. xn' *)
    (* p4 = inv_f x1' x2' .. xn' *)
    (* p5 = post_f x1 x2 .. xn *)

    (* p1 => p2 *)
    (* p2 and p3 => p4 *)
    (* p2 => p5 *)
    let var_list, var_list' =
      let rec sub acc = function
        | Sort.SArrow (s1, s2) -> sub ((get_var (), s1)::acc) s2
        | _ -> List.rev acc
      in
      sub [] sort_of_inv_f, sub [] sort_of_inv_f
    in
    let mk_atom pvar var_list =
      match Map.Poly.find fenv pvar with
      | Some term -> begin
          let term, map =
            let rec sub term var_list map =
              match var_list with
              | [] -> term, map
              | (v, _)::vs -> assert (is_lam term);
                let _, var, _sort, term, _ = let_bin term in
                let map' = Map.Poly.add_exn map ~key:var ~data:(mk_var v) in
                sub term vs map'
            in
            sub term var_list Map.Poly.empty
          in subst map term
        end
      | None ->
        List.fold ~f:(fun acc (var, _sort) -> mk_app acc (mk_var var))
          ~init:(mk_var pvar) var_list
    in
    let p1 = mk_atom pre_f var_list in
    let p2 = mk_atom inv_f var_list in
    let p3 = mk_atom trans_f @@ var_list @ var_list' in
    let p4 = mk_atom inv_f var_list' in
    let p5 = mk_atom post_f var_list in
    List.fold ~f:(fun acc (var, sort) -> Problem.add_declared_var acc var sort) ~init:problem (var_list @ var_list'),
    mk_apps (mk_imply ()) [p1; p2] ::
    mk_apps (mk_imply ()) [mk_apps (mk_and ()) [p2; p3]; p4] ::
    mk_apps (mk_imply ()) [p2; p5] :: []

  let var_and_sort_of_arg = function
    | Sexp.List [Sexp.Atom var; Sexp.Atom sort] -> Ident.Tvar var, Term.sort_of_text sort
    | _ -> failwith "args are invalid"

  let add_args_to_venv venv args =
    List.fold ~f:(fun acc (var, sort) -> Logic.SortMap.update acc var ~f:(function | _ -> sort)) ~init:venv args

  let parse_smt_cmd problem fenv venv = function
    | Sexp.List [Sexp.Atom "declare-datatype"; _; _]
    | Sexp.List [Sexp.Atom "declare-datatypes"; _; _]
      -> failwith "declare-datatype(s) is not supported yet"
    | Sexp.List [Sexp.Atom "declare-sort"; _; _]
      -> failwith "declare-sort is not supported yet"
    | Sexp.List [Sexp.Atom "define-fun"; Sexp.Atom name; Sexp.List args; Sexp.Atom _sort; def] ->
      let args = List.map ~f:var_and_sort_of_arg args in
      (* The defined fun contains neighter any free variable nor any synth-fun*)
      let venv' = add_args_to_venv venv args in
      let body = parse_term (Problem.mk_problem Map.Poly.empty Logic.SortMap.empty []) fenv venv' def in
      let term = mk_lambda args body in
      problem, Map.Poly.add_exn fenv ~key:(Ident.Tvar name) ~data:term
    | Sexp.List [Sexp.Atom "define-sort"]
      -> failwith "define-sort is not supported yet"
    | Sexp.List [Sexp.Atom "set-info"] -> failwith "not implemented yet"
    | Sexp.List [Sexp.Atom "set-option"] -> failwith "not implemented yet"
    | Sexp.List (Sexp.Atom cmd :: _) -> failwith @@ Printf.sprintf "unknown smt cmd : %s" cmd
    | _ -> failwith "unknown smt cmd"

  let rec parse_cmds problem fenv (venv : Logic.SortMap.t) = function
    | [] -> Result.fail @@ Error.of_string "lack of check-synth command"
    | (Sexp.List [Sexp.Atom "check-synth"]) :: [] -> Ok (problem)
    | (Sexp.List (Sexp.Atom "constraint" :: constraint_ :: [])) :: es ->
      let problem' = Problem.add_constraint problem @@ parse_term problem fenv venv constraint_ in
      parse_cmds problem' fenv venv es
    | (Sexp.List [Sexp.Atom "declare-var"; Sexp.Atom var; Sexp.Atom sort]) :: es
    | (Sexp.List [Sexp.Atom "declare-primed-var"; Sexp.Atom var; Sexp.Atom sort]) :: es ->
      let var = Ident.Tvar var in
      let sort = Term.sort_of_text sort in
      let problem' = Problem.add_declared_var problem var sort in
      parse_cmds problem' fenv (Logic.SortMap.add_exn venv ~key:var ~data:sort) es
    | (Sexp.List ((Sexp.Atom "inv-constraint") :: (Sexp.Atom inv_f):: (Sexp.Atom pre_f) :: (Sexp.Atom trans_f) :: (Sexp.Atom post_f) :: [])) :: es ->
      let inv_f, pre_f, trans_f, post_f =
        Ident.Tvar inv_f, Ident.Tvar pre_f, Ident.Tvar trans_f, Ident.Tvar post_f in
      let problem, constraints = parse_inv_constraint problem fenv inv_f pre_f trans_f post_f in
      let problem' = List.fold ~f:(fun acc c -> Problem.add_constraint acc c) ~init:problem constraints in
      parse_cmds problem' fenv venv es
    | (Sexp.List [Sexp.Atom "set-feature"]) :: _es -> failwith "not implemented yet"
    | (Sexp.List ((Sexp.Atom "synth-fun") :: (Sexp.Atom name) :: (Sexp.List args) :: (Sexp.Atom sort) :: grammer_def)) :: es ->
      let problem' = parse_synth_fun problem (Ident.Tvar name) args (Term.sort_of_text sort) grammer_def in
      parse_cmds problem' fenv venv es
    | (Sexp.List ((Sexp.Atom "synth-inv") :: (Sexp.Atom name) :: (Sexp.List args) :: grammer_def)) :: es ->
      let problem' = parse_synth_fun problem (Ident.Tvar name) args Logic.BoolTerm.SBool grammer_def in
      parse_cmds problem' fenv venv es
    | cmd :: es ->
      let problem', fenv' = parse_smt_cmd problem fenv venv cmd in
      parse_cmds problem' fenv' venv es

  let of_problem es =
    let problem = parse_cmds (Problem.mk_problem Map.Poly.empty Logic.SortMap.empty []) Map.Poly.empty Logic.SortMap.empty es in
    problem

end

let parse = function
  | (Sexp.List [Sexp.Atom "set-logic"; Sexp.Atom logic]) :: es -> 
    let logic = logic_type_of_str logic in begin
      match logic with
      | Lia ->
        let module Parser =  Make (ExtTerm) (Problem.ExtTerm) in Parser.of_problem es
      | _ -> failwith "parser of the logic is not implemented yet"
    end
  | _ -> Result.fail @@ Error.of_thunk
      (fun () -> Printf.sprintf "sygus problem file should start from 'set-logic'")

let from_file filename =
  let src = In_channel.read_all filename in
  match Many.parse_string src with
  | Ok (sexps) -> parse sexps
  | Error err ->
    Result.fail @@
    Error.of_thunk (fun () ->
        let pos = Parse_error.position err in
        let msg = Parse_error.message err in
        Printf.sprintf "at line %d, col %d: %s" pos.line pos.col msg
      )
