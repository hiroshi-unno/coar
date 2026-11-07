(* The translation B from the OCaml representation back to an HES, the inverse
   of [HflToOCaml.print] on its image.

   Reads the untyped OCaml syntax tree (types come from the parameter
   annotations, which [HflToOCaml] always writes, and are completed by
   [HflTyping.infer]).  Refuses a structure without
   [[@@@mode "hfl_prop_as_bool"]], since only that mode gives [let rec] the
   meaning of a fixed point.  Accepts: the prelude's [forall_int]/[exists_int]
   definitions (skipped; their applications become quantifiers), exactly one
   recursive group whose bindings are named [pv_X] (the equations, in order,
   with the kind of their [[@@fix]], greatest when absent), [[@@@hfl_free]],
   and any [[@@@assert]] (the question is determined by the equations).
   Expressions: [&&], [||], [not] (pushed to the atoms), comparisons,
   [+ - * / mod] and unary minus on integers, integer and Boolean constants,
   [fun], application, [pv_X ()] for a nullary equation, and
   [if c then a else b], read as [(not c || a) && (c || b)] -- so [T (B o)] is
   [o] only for programs without [if]. *)

open Core
open HflSyntax
module P = Parsetree

exception Refused of string

let refuse fmt = ksprintf (fun s -> raise (Refused s)) fmt

let var_of_ocaml x =
  if String.is_suffix x ~suffix:"_" && String.length x > 1 then
    String.drop_suffix x 1
  else x

let eqn_of_ocaml x =
  if String.is_prefix x ~prefix:"pv_" then Some (String.drop_prefix x 3)
  else None

let rec sty_of_core (ty : P.core_type) =
  match ty.ptyp_desc with
  | Ptyp_constr ({ txt = Lident "int"; _ }, []) -> TInt
  | Ptyp_constr ({ txt = Lident ("bool" | "prop"); _ }, []) -> TProp
  | Ptyp_arrow (Nolabel, a, b) -> TArrow (sty_of_core a, sty_of_core b)
  | _ -> refuse "unsupported type annotation"

let name_of_ident (lid : Longident.t) =
  match lid with Lident x -> x | _ -> refuse "a qualified name"

let rec param_of_pat (p : P.pattern) =
  match p.ppat_desc with
  | Ppat_var { txt; _ } -> `Var (txt, None)
  | Ppat_constraint (p', ty) -> (
      match param_of_pat p' with
      | `Var (x, _) -> `Var (x, Some (sty_of_core ty))
      | `Unit -> `Unit)
  | Ppat_construct ({ txt = Lident "()"; _ }, None) -> `Unit
  | _ -> refuse "unsupported parameter pattern"

let params_of (params : P.function_param list) =
  List.filter_map params ~f:(fun (fp : P.function_param) ->
      match fp.pparam_desc with
      | Pparam_val (Nolabel, None, p) -> (
          match param_of_pat p with
          | `Var (x, ty) -> Some (var_of_ocaml x, ty)
          | `Unit -> None)
      | Pparam_val _ -> refuse "a labelled or optional parameter"
      | Pparam_newtype _ -> refuse "a type parameter")

let rec term_of (e : P.expression) =
  match e.pexp_desc with
  | Pexp_constraint (e', _) -> term_of e'
  | Pexp_constant { pconst_desc = Pconst_integer (s, None); _ } ->
      let n = Int.of_string s in
      if n < 0 then Neg (Int (-n)) else Int n
  | Pexp_construct ({ txt = Lident "true"; _ }, None) -> Bool true
  | Pexp_construct ({ txt = Lident "false"; _ }, None) -> Bool false
  | Pexp_ident { txt; _ } -> (
      let x = name_of_ident txt in
      match eqn_of_ocaml x with Some n -> Var n | None -> Var (var_of_ocaml x))
  | Pexp_function (params, _, Pfunction_body body) ->
      let xs = params_of params in
      List.fold_right xs ~init:(term_of body) ~f:(fun (x, ty) b ->
          Abs (x, ty, b))
  | Pexp_function (_, _, Pfunction_cases _) -> refuse "a function by cases"
  | Pexp_ifthenelse (c, a, Some b) ->
      let c = term_of c in
      And (Or (HflNeg.neg c, term_of a), Or (c, term_of b))
  | Pexp_apply ({ pexp_desc = Pexp_ident { txt; _ }; _ }, args) -> (
      let f = name_of_ident txt in
      let args = List.map args ~f:(fun (lbl, a) ->
          match lbl with
          | Asttypes.Nolabel -> a
          | _ -> refuse "a labelled argument")
      in
      match (f, args) with
      | "&&", [ a; b ] -> And (term_of a, term_of b)
      | "||", [ a; b ] -> Or (term_of a, term_of b)
      | "not", [ a ] -> HflNeg.neg (term_of a)
      | ("~-" | "-"), [ a ] -> Neg (term_of a)
      | "+", [ a; b ] -> Op (Add, term_of a, term_of b)
      | "-", [ a; b ] -> Op (Sub, term_of a, term_of b)
      | "*", [ a; b ] -> Op (Mul, term_of a, term_of b)
      | "/", [ a; b ] -> Op (Div, term_of a, term_of b)
      | "mod", [ a; b ] -> Op (Mod, term_of a, term_of b)
      | "=", [ a; b ] -> Pred (Eq, term_of a, term_of b)
      | "<>", [ a; b ] -> Pred (Neq, term_of a, term_of b)
      | "<=", [ a; b ] -> Pred (Le, term_of a, term_of b)
      | ">=", [ a; b ] -> Pred (Ge, term_of a, term_of b)
      | "<", [ a; b ] -> Pred (Lt, term_of a, term_of b)
      | ">", [ a; b ] -> Pred (Gt, term_of a, term_of b)
      | ("forall_int" | "exists_int"), [ a ] -> (
          match term_of a with
          | Abs (x, _, body) ->
              if String.equal f "forall_int" then Forall (x, body)
              else Exists (x, body)
          | _ -> refuse "%s applied to something other than a lambda" f)
      | _, [ { pexp_desc = Pexp_construct ({ txt = Lident "()"; _ }, None); _ } ]
        when Option.is_some (eqn_of_ocaml f) ->
          Var (Option.value_exn (eqn_of_ocaml f))
      | _ ->
          apps (term_of { e with pexp_desc = Pexp_ident { txt; loc = e.pexp_loc } })
            (List.map args ~f:term_of))
  | Pexp_apply (h, args) ->
      apps (term_of h)
        (List.map args ~f:(fun (lbl, a) ->
             match lbl with
             | Asttypes.Nolabel -> term_of a
             | _ -> refuse "a labelled argument"))
  | _ -> refuse "an unsupported OCaml expression"

let string_payload (attr : P.attribute) =
  match attr.attr_payload with
  | PStr
      [
        {
          pstr_desc =
            Pstr_eval
              ({ pexp_desc = Pexp_constant { pconst_desc = Pconst_string (s, _, _); _ }; _ }, _);
          _;
        };
      ] ->
      s
  | _ -> refuse "attribute %s without a string" attr.attr_name.txt

let fix_of_attrs (attrs : P.attributes) =
  match
    List.find attrs ~f:(fun a -> String.equal a.P.attr_name.txt "fix")
  with
  | None -> Nu
  | Some a -> (
      match string_payload a with
      | "nu" -> Nu
      | "mu" -> Mu
      | s -> refuse "[@fix %S]: expected \"nu\" or \"mu\"" s)

let eqn_of_vb (vb : P.value_binding) =
  let name =
    match vb.pvb_pat.ppat_desc with
    | Ppat_var { txt; _ } -> (
        match eqn_of_ocaml txt with
        | Some n -> n
        | None -> refuse "a binding %s not named pv_X" txt)
    | _ -> refuse "a binding that is not a variable"
  in
  let params, body =
    match vb.pvb_expr.pexp_desc with
    | Pexp_function (params, _, Pfunction_body body) ->
        (params_of params, term_of body)
    | _ -> ([], term_of vb.pvb_expr)
  in
  { name; params; fix = fix_of_attrs vb.pvb_attributes; body }

let of_structure (str : P.structure) =
  let mode = ref None and closure = ref [] and groups = ref [] in
  List.iter str ~f:(fun item ->
      match item.pstr_desc with
      | Pstr_attribute a when String.equal a.attr_name.txt "mode" ->
          mode := Some (string_payload a)
      | Pstr_attribute a when String.equal a.attr_name.txt "hfl_free" ->
          closure :=
            List.map ~f:var_of_ocaml
              (String.split ~on:' ' (string_payload a)
              |> List.filter ~f:(Fn.non String.is_empty))
      | Pstr_attribute _ -> ()
      | Pstr_value (_, vbs) ->
          let is_prelude (vb : P.value_binding) =
            match vb.pvb_pat.ppat_desc with
            | Ppat_var { txt; _ } ->
                List.mem HflToOCaml.prelude_names txt ~equal:String.equal
            | _ -> false
          in
          if List.for_all vbs ~f:is_prelude then ()
          else groups := !groups @ [ vbs ]
      | _ -> refuse "an unsupported structure item");
  (match !mode with
  | Some "hfl_prop_as_bool" -> ()
  | Some m -> refuse "mode %S is not the Boolean HFL mode" m
  | None -> refuse "no [@@@mode \"hfl_prop_as_bool\"]: not an HFL program");
  match !groups with
  | [ vbs ] -> { eqns = List.map vbs ~f:eqn_of_vb; closure = !closure; env_ignored = false }
  | [] -> refuse "no equations"
  | _ -> refuse "more than one recursive group"

let parse ?(filename = "") text =
  let lexbuf = Lexing.from_string text in
  Lexing.set_filename lexbuf filename;
  let str =
    try Parse.implementation lexbuf
    with exn -> refuse "%s: OCaml syntax error (%s)" filename (Exn.to_string exn)
  in
  let hes = of_structure str in
  try HflTyping.infer hes
  with HflTyping.Error msg -> refuse "%s: %s" filename msg

let from_file filename = parse ~filename (In_channel.read_all filename)
