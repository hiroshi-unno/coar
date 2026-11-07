(* Printing an HES in one of the tools' dialects.

   Contract: for a typed HES [e] that dialect [d] can express,
   [HflReader.parse ~dialect:d (print ~dialect:d e)] is [e] up to the
   canonical forms the reader produces (right-associated [&&]/[||], equation
   bodies of type [Prop]), the types it infers, and alpha-renaming.  What [d]
   cannot express is refused with [Unprintable] naming it: [forall] and [%]
   for hflmc2, [exists] for ReTHFL and hflmc2, [%] for MuHFL (whose lexer
   cannot read it), a ['] in a name for ReTHFL and hflmc2.  The closure
   parameters of the main equation are printed as free variables, as the tools
   write them; a least fixed point is [=μ], which every dialect reads. *)

open Core
open HflSyntax

exception Unprintable of string

(* precedence levels, lowest first, following the grammar *)
let lv_lam = 0
let lv_quant = 1
let lv_or = 2
let lv_and = 3
let lv_pred = 4
let lv_add = 5
let lv_mul = 6
let lv_neg = 7
let lv_app = 8
let lv_atom = 9

let str_of_pred = function
  | Eq -> "="
  | Neq -> "<>"
  | Le -> "<="
  | Ge -> ">="
  | Lt -> "<"
  | Gt -> ">"

let str_of_aop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"

let check_name ~dialect x =
  match dialect with
  | (Rethfl | Hflmc2) when String.contains x '\'' ->
      raise
        (Unprintable
           (sprintf "the %s dialect has no ' in names (%s)"
              (string_of_dialect dialect) x))
  | _ -> x

let rec pr ~dialect lv t =
  let paren l s = if lv > l then "(" ^ s ^ ")" else s in
  let pr = pr ~dialect in
  match t with
  | Var x -> check_name ~dialect x
  | Int n -> if n < 0 then paren lv_neg (sprintf "-%d" (-n)) else Int.to_string n
  | Bool b -> if b then "true" else "false"
  | Neg a -> (
      match a with
      | Neg _ -> paren lv_neg ("-(" ^ pr lv_lam a ^ ")")
      | _ -> paren lv_neg ("-" ^ pr lv_neg a))
  | Op (o, a, b) ->
      (match (dialect, o) with
      | (Hflmc2 | Muhfl), Mod ->
          raise
            (Unprintable
               (sprintf "the %s dialect has no %%" (string_of_dialect dialect)))
      | _ -> ());
      let l = match o with Add | Sub -> lv_add | Mul | Div | Mod -> lv_mul in
      paren l (sprintf "%s %s %s" (pr l a) (str_of_aop o) (pr (l + 1) b))
  | Pred (p, a, b) ->
      paren lv_pred
        (sprintf "%s %s %s" (pr lv_add a) (str_of_pred p) (pr lv_add b))
  | And (a, b) -> paren lv_and (sprintf "%s && %s" (pr (lv_and + 1) a) (pr lv_and b))
  | Or (a, b) -> paren lv_or (sprintf "%s || %s" (pr (lv_or + 1) a) (pr lv_or b))
  | Forall (x, a) ->
      if equal_dialect dialect Hflmc2 then
        raise (Unprintable "the hflmc2 dialect has no forall");
      paren lv_quant (sprintf "∀%s. %s" (check_name ~dialect x) (pr lv_quant a))
  | Exists (x, a) ->
      (match dialect with
      | Rethfl | Hflmc2 ->
          raise
            (Unprintable
               (sprintf "the %s dialect has no exists"
                  (string_of_dialect dialect)))
      | _ -> ());
      paren lv_quant (sprintf "∃%s. %s" (check_name ~dialect x) (pr lv_quant a))
  | Abs _ ->
      let rec binders acc = function
        | Abs (x, _, b) -> binders (acc @ [ check_name ~dialect x ]) b
        | b -> (acc, b)
      in
      let xs, body = binders [] t in
      let lams =
        match dialect with
        | Hflmc2 -> String.concat ~sep:" " (List.map xs ~f:(sprintf "\\%s."))
        | _ -> "\\" ^ String.concat ~sep:" " xs ^ "."
      in
      paren lv_lam (sprintf "%s %s" lams (pr lv_quant body))
  | App _ ->
      let h, args = unapps t in
      paren lv_app
        (String.concat ~sep:" "
           (pr lv_atom h :: List.map args ~f:(pr lv_atom)))

let str_of_formula ?(dialect = Coar) t = pr ~dialect lv_lam t

let str_of_eqn ~dialect ?(drop = 0) e =
  let params = List.drop e.params drop in
  sprintf "%s%s %s %s."
    (check_name ~dialect e.name)
    (String.concat (List.map params ~f:(fun (x, _) -> " " ^ check_name ~dialect x)))
    (match e.fix with Nu -> "=v" | Mu -> "=μ")
    (pr ~dialect lv_lam e.body)

let print ~dialect hes =
  let lines =
    List.mapi hes.eqns ~f:(fun i e ->
        let drop =
          if i = 0 then
            let n = List.length hes.closure in
            if
              List.equal String.equal
                (List.map (List.take e.params n) ~f:fst)
                hes.closure
            then n
            else 0
          else 0
        in
        str_of_eqn ~dialect ~drop e)
  in
  String.concat ~sep:"\n" ("%HES" :: lines) ^ "\n"
