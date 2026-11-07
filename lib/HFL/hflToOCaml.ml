(* The translation T from an HES to its OCaml representation, the input of
   RCaml's Boolean HFL mode.

   The output is one OCaml structure:
   - [[@@@mode "hfl_prop_as_bool"]] first, always: RCaml's ordinary mode must
     never read the output, since its rule for [let rec] is partial
     correctness, under which a diverging conjunction proves anything, while
     a greatest fixed point of the same equation is false;
   - the quantifiers over [int] that the HES uses, as lambda-HFL basic
     operators [forall_int]/[exists_int] defined by a recursion over the
     integers: [forall_int p] is the greatest fixed point of
     [F n = p n && p (-n) && F (n + 1)] at [0], which is [forall x. p x], and
     [exists_int] is dually a least fixed point;
   - one recursive group [let rec pv_X1 ... and ... pv_Xn ...] in HES order,
     each binding carrying [[@@fix "nu"]] or [[@@fix "mu"]], every parameter
     annotated with its simple type ([prop] is [bool], a nullary equation
     takes [()]);
   - [[@@@hfl_free "x y"]] when the main formula had free variables;
   - the question, when every parameter of the main equation is an integer:
     [[@@@assert "typeof(pv_X1) <: int -> ... -> { v : prop | v }"]] (valid)
     for an HES of greatest fixed points, and [{ v : prop | v = false }] (not
     valid) for one of least fixed points, the only direction RCaml's
     admissible refinements can prove for each kind.  An alternating HES is
     printed without an assertion: its group with per-binding kinds is a
     carrier whose meaning is the tools' nesting, not OCaml's.

   Names: an equation [X] becomes [pv_X]; any other name is kept unless it is
   an OCaml keyword, a name of the prelude, starts with [pv_] or ends with
   [_], in which case [_] is appended ([HflOfOCaml] inverts this).
   Integer [/] and [%] become OCaml's [/] and [mod], which truncate, as the
   HES's do. *)

open Core
open HflSyntax

let ocaml_keywords =
  [
    "and"; "as"; "assert"; "asr"; "begin"; "class"; "constraint"; "do"; "done";
    "downto"; "effect"; "else"; "end"; "exception"; "external"; "false"; "for";
    "fun"; "function"; "functor"; "if"; "in"; "include"; "inherit";
    "initializer"; "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match";
    "method"; "mod"; "module"; "mutable"; "new"; "nonrec"; "not"; "object"; "of";
    "open"; "or"; "private"; "rec"; "sig"; "struct"; "then"; "to"; "true"; "try";
    "type"; "val"; "virtual"; "when"; "while"; "with"; "unif"; "raise";
  ]

let prelude_names =
  [ "forall_int"; "exists_int"; "forall_int_from"; "exists_int_from" ]

let needs_escape x =
  List.mem ocaml_keywords x ~equal:String.equal
  || List.mem prelude_names x ~equal:String.equal
  || String.is_prefix x ~prefix:"pv_"
  || String.is_suffix x ~suffix:"_"
  || String.equal x "_"

let ocaml_of_var x = if needs_escape x then x ^ "_" else x
let ocaml_of_eqn x = "pv_" ^ x

let rec ocaml_of_sty = function
  | TProp -> "bool"
  | TInt -> "int"
  | TArrow (a, b) ->
      let a' = ocaml_of_sty a in
      let a' = match a with TArrow _ -> "(" ^ a' ^ ")" | _ -> a' in
      a' ^ " -> " ^ ocaml_of_sty b

let rec rtype_of_sty = function
  | TProp -> "prop"
  | TInt -> "int"
  | TArrow (a, b) ->
      let a' = rtype_of_sty a in
      let a' = match a with TArrow _ -> "(" ^ a' ^ ")" | _ -> a' in
      a' ^ " -> " ^ rtype_of_sty b

(* OCaml precedence levels, lowest first *)
let lv_fun = 0
let lv_or = 1
let lv_and = 2
let lv_cmp = 3
let lv_add = 4
let lv_mul = 5
let lv_app = 6
let lv_atom = 7

let str_of_term ~eqns t =
  let is_eqn x = Map.find eqns x in
  let rec pr lv t =
    let paren l s = if lv > l then "(" ^ s ^ ")" else s in
    match t with
    | Var x -> (
        match is_eqn x with
        | Some 0 -> paren lv_app (ocaml_of_eqn x ^ " ()")
        | Some _ -> ocaml_of_eqn x
        | None -> ocaml_of_var x)
    | Int n -> if n < 0 then sprintf "(%d)" n else Int.to_string n
    | Bool b -> if b then "true" else "false"
    | Neg a -> "(- " ^ pr lv_app a ^ ")"
    | Op (o, a, b) ->
        let l, s =
          match o with
          | Add -> (lv_add, "+")
          | Sub -> (lv_add, "-")
          | Mul -> (lv_mul, "*")
          | Div -> (lv_mul, "/")
          | Mod -> (lv_mul, "mod")
        in
        paren l (sprintf "%s %s %s" (pr l a) s (pr (l + 1) b))
    | Pred (p, a, b) ->
        let s =
          match p with
          | Eq -> "="
          | Neq -> "<>"
          | Le -> "<="
          | Ge -> ">="
          | Lt -> "<"
          | Gt -> ">"
        in
        paren lv_cmp (sprintf "%s %s %s" (pr lv_add a) s (pr lv_add b))
    | And (a, b) ->
        paren lv_and (sprintf "%s && %s" (pr (lv_and + 1) a) (pr lv_and b))
    | Or (a, b) ->
        paren lv_or (sprintf "%s || %s" (pr (lv_or + 1) a) (pr lv_or b))
    | Forall (x, a) ->
        paren lv_app
          (sprintf "forall_int (fun (%s : int) -> %s)" (ocaml_of_var x)
             (pr lv_fun a))
    | Exists (x, a) ->
        paren lv_app
          (sprintf "exists_int (fun (%s : int) -> %s)" (ocaml_of_var x)
             (pr lv_fun a))
    | Abs _ ->
        let rec binders acc = function
          | Abs (x, ty, b) -> binders (acc @ [ (x, ty) ]) b
          | b -> (acc, b)
        in
        let xs, body = binders [] t in
        paren lv_fun
          (sprintf "fun %s -> %s"
             (String.concat ~sep:" "
                (List.map xs ~f:(fun (x, ty) ->
                     match ty with
                     | Some ty ->
                         sprintf "(%s : %s)" (ocaml_of_var x) (ocaml_of_sty ty)
                     | None -> ocaml_of_var x)))
             (pr lv_fun body))
    | App _ ->
        let h, args = unapps t in
        paren lv_app
          (String.concat ~sep:" " (pr lv_atom h :: List.map args ~f:(pr lv_atom)))
  in
  pr lv_fun t

let uses p hes =
  let rec go = function
    | Forall (_, a) -> p `Forall || go a
    | Exists (_, a) -> p `Exists || go a
    | Var _ | Int _ | Bool _ -> false
    | Neg a | Abs (_, _, a) -> go a
    | Op (_, a, b) | Pred (_, a, b) | And (a, b) | Or (a, b) | App (a, b) ->
        go a || go b
  in
  List.exists hes.eqns ~f:(fun e -> go e.body)

let prelude_forall =
  {|let rec forall_int_from (p : int -> bool) (n : int) : bool =
  p n && p (- n) && forall_int_from p (n + 1)
[@@fix "nu"]

let forall_int (p : int -> bool) : bool = forall_int_from p 0
|}

let prelude_exists =
  {|let rec exists_int_from (p : int -> bool) (n : int) : bool =
  p n || p (- n) || exists_int_from p (n + 1)
[@@fix "mu"]

let exists_int (p : int -> bool) : bool = exists_int_from p 0
|}

let mode_attribute = {|[@@@mode "hfl_prop_as_bool"]|}

let print (hes : hes) =
  let eqns =
    String.Map.of_alist_reduce ~f:(fun a _ -> a)
      (List.map hes.eqns ~f:(fun e -> (e.name, List.length e.params)))
  in
  let buf = Buffer.create 1024 in
  let add = Buffer.add_string buf in
  add mode_attribute;
  add "\n\n";
  if uses (function `Forall -> true | `Exists -> false) hes then (
    add prelude_forall;
    add "\n");
  if uses (function `Exists -> true | `Forall -> false) hes then (
    add prelude_exists;
    add "\n");
  List.iteri hes.eqns ~f:(fun i e ->
      let params =
        match e.params with
        | [] -> " ()"
        | ps ->
            String.concat
              (List.map ps ~f:(fun (x, ty) ->
                   sprintf " (%s : %s)" (ocaml_of_var x)
                     (ocaml_of_sty (Option.value ty ~default:TInt))))
      in
      add
        (sprintf "%s %s%s : bool =\n  %s\n[@@fix \"%s\"]\n"
           (if i = 0 then "let rec" else "and")
           (ocaml_of_eqn e.name) params
           (str_of_term ~eqns e.body)
           (string_of_fix e.fix)));
  if not (List.is_empty hes.closure) then
    add
      (sprintf "\n[@@@hfl_free \"%s\"]\n"
         (String.concat ~sep:" " (List.map hes.closure ~f:ocaml_of_var)));
  (match hes.eqns with
  | main :: _
    when (not (is_alternating hes))
         && List.for_all main.params ~f:(fun (_, ty) ->
             match ty with Some TInt -> true | _ -> false) ->
      let args =
        match main.params with
        | [] -> "unit -> "
        | ps -> String.concat (List.map ps ~f:(fun _ -> "int -> "))
      in
      let goal = match main.fix with Nu -> "v = true" | Mu -> "v = false" in
      add
        (sprintf "\n[@@@assert \"typeof(%s) <: %s{ v : prop | %s }\"]\n"
           (ocaml_of_eqn main.name) args goal)
  | _ -> ());
  Buffer.contents buf

let rtype_of_main hes =
  match hes.eqns with
  | main :: _ ->
      String.concat
        (List.map main.params ~f:(fun (_, ty) ->
             rtype_of_sty (Option.value ty ~default:TInt) ^ " -> "))
  | [] -> ""
