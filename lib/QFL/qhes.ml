(* The printer of a QFL problem in the concrete syntax of the [.qhes] reader
   ([lexer.mll], [parser.mly]): [str_of p] is a text that [Util.from_string]
   reads back as [p], up to the renaming of identifiers the reader cannot take
   and the spelling of constants (a negative literal is printed as a negation,
   which the reader keeps as one).

   Contract.  Every compound term and formula is printed in parentheses, so the
   result never depends on the grammar's precedences; an atom is printed bare,
   because the reader takes a parenthesis that opens a formula and one that
   opens a term apart only by what follows.  An [int] constant is printed as
   an integer literal and a [real] one with a decimal point, because the
   reader types a literal by its spelling and has no implicit conversion: a
   real [1] printed as [1] reads back as an [int] and the body is refused as
   ill-sorted.  A rational that is not a finite decimal is printed as a
   quotient of two real literals, which the reader types as real division.
   Integer division and remainder are printed only in their truncated mode,
   the only one the format has.

   What the format cannot say is refused by name ([Common.Refusal]) rather
   than approximated: a conversion from [real] to [int] ([int] to [real] is
   [real(t)]), a Boolean
   variable or predicate, a [let], a tuple, any other theory's symbol, an
   equation whose fixpoint is undecided ([MuOrNu]).  The argument constraints
   of an equation (the domain on which it is defined, which the bound checker
   reads as an antecedent of each obligation on that equation) are printed
   after [requires], the annotations after [|]. *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

let refuse = Common.Refusal.refuse

(* the reader's keywords: an identifier spelled like one is renamed *)
let keywords =
  Set.Poly.of_list
    [ "ASAT"; "dist"; "ensures"; "if"; "then"; "else"; "true"; "false";
      "int"; "bool"; "real"; "not"; "and"; "or"; "div"; "tdiv"; "rem"; "mod";
      "max"; "min"; "unif"; "forall"; "exists"; "where"; "requires" ]

(* an identifier of the lexer: [[a-zA-Z#_][a-zA-Z0-9'_#]*] or [@n] *)
let is_ident s =
  let first c = Char.is_alpha c || Char.equal c '#' || Char.equal c '_' in
  let rest c = first c || Char.is_digit c || Char.equal c '\'' in
  (not (String.is_empty s))
  && (not (Set.mem keywords s))
  && ((first s.[0] && String.for_all (String.drop_prefix s 1) ~f:rest)
     || (Char.equal s.[0] '@'
        && String.length s > 1
        && Char.( <> ) s.[1] '0'
        && String.for_all (String.drop_prefix s 1) ~f:Char.is_digit))

(* Identifier naming.  An identifier the lexer takes is printed as it is; any
   other is given [qhes_<n>], the same one at every occurrence, avoiding every
   name the problem prints as it is.  Names are global to the problem, so a
   renamed variable is renamed alike in every equation that binds it, which
   preserves every binding. *)
type names = {
  taken : (string, unit) Hashtbl.t;  (** the names printed as they are *)
  renamed : (string, string) Hashtbl.t;
  mutable next : int;
}

let ident names (Ident.Tvar s) =
  if is_ident s then (
    Hashtbl.set names.taken ~key:s ~data:();
    s)
  else
    match Hashtbl.find names.renamed s with
    | Some s' -> s'
    | None ->
        let rec fresh () =
          let s' = sprintf "qhes_%d" names.next in
          names.next <- names.next + 1;
          if Hashtbl.mem names.taken s' then fresh () else s'
        in
        let s' = fresh () in
        Hashtbl.set names.renamed ~key:s ~data:s';
        s'

let str_of_int n =
  if Z.(lt n zero) then sprintf "(- %s)" (Z.to_string (Z.neg n))
  else Z.to_string n

(* a non-negative rational with a decimal point: exact as a decimal when the
   denominator divides a power of ten, a quotient of two literals otherwise *)
let str_of_nonneg_real q =
  let num = Q.num q and den = Q.den q in
  let rec strip k d =
    if Z.(equal (d mod of_int 2) zero) then strip k Z.(d / of_int 2)
    else if Z.(equal (d mod of_int 5) zero) then strip k Z.(d / of_int 5)
    else (k, d)
  in
  if Z.equal den Z.one then Z.to_string num ^ ".0"
  else
    match strip 0 den with
    | _, d when Z.equal d Z.one ->
        (* the least [k] with [den | 10^k] *)
        let rec digits k p = if Z.(equal (p mod den) zero) then k else digits (k + 1) Z.(p * of_int 10) in
        let k = digits 1 (Z.of_int 10) in
        let scaled = Z.(num * pow (of_int 10) k / den) |> Z.to_string in
        let scaled = String.make (max 0 (k + 1 - String.length scaled)) '0' ^ scaled in
        let i = String.length scaled - k in
        String.prefix scaled i ^ "." ^ String.drop_prefix scaled i
    | _ -> sprintf "(%s.0 / %s.0)" (Z.to_string num) (Z.to_string den)

let str_of_real q =
  if Q.(lt q zero) then sprintf "(- %s)" (str_of_nonneg_real (Q.neg q))
  else str_of_nonneg_real q

let str_of_sort = function
  | T_int.SInt -> "int"
  | T_real.SReal -> "real"
  | T_bool.SBool -> "bool"
  | s -> refuse "the sort %s has no syntax in .qhes" (Term.str_of_sort s)

let str_of_bounds names params =
  String.concat_map_list ~sep:" " params ~f:(fun (x, s) ->
      sprintf "(%s : %s)" (ident names x) (str_of_sort s))

let rec str_of_term names t =
  let term = str_of_term names in
  let bin op a b = sprintf "(%s %s %s)" (term a) op (term b) in
  match t with
  | Term.Var (x, _, _) -> ident names x
  | FunApp (T_int.Int n, [], _) -> str_of_int n
  | FunApp (T_real.Real q, [], _) -> str_of_real q
  | FunApp ((T_int.Add | T_real.RAdd | T_num.NAdd _), [ a; b ], _) -> bin "+" a b
  | FunApp ((T_int.Sub | T_real.RSub | T_num.NSub _), [ a; b ], _) -> bin "-" a b
  | FunApp ((T_int.Mul | T_real.RMul | T_num.NMul _), [ a; b ], _) -> bin "*" a b
  | FunApp ((T_real.RDiv | T_int.Div Value.Truncated), [ a; b ], _) -> bin "/" a b
  | FunApp (T_num.NDiv (_, Value.Truncated), [ a; b ], _) -> bin "/" a b
  | FunApp ((T_int.Rem Value.Truncated | T_num.NRem (_, Value.Truncated)), [ a; b ], _) ->
      bin "%" a b
  | FunApp ((T_int.Neg | T_real.RNeg | T_num.NNeg _), [ a ], _) ->
      sprintf "(- %s)" (term a)
  | FunApp (T_bool.IfThenElse, [ c; a; b ], _) ->
      sprintf "(if %s then %s else %s)"
        (str_of_formula names (Formula.of_bool_term c))
        (term a) (term b)
  | FunApp (FVar (Ident.Tvar ("max" | "min" as op), _, _), args, _) when not (List.is_empty args) ->
      sprintf "(%s %s)" op (String.concat_map_list ~sep:" " args ~f:term)
  | FunApp (FVar (Ident.Tvar "unif", _, _), _, _) -> (
      match Unif.let_unif t with
      | Some (r, body) -> sprintf "(unif %s. %s)" (ident names r) (term body)
      | None -> refuse "the integral %s has no syntax in .qhes" (Term.str_of t))
  | FunApp (FVar (f, _, _), [], _) -> ident names f
  | FunApp (FVar (f, _, _), args, _) ->
      sprintf "(%s %s)" (ident names f) (String.concat_map_list ~sep:" " args ~f:term)
  | FunApp (T_irb.IntToReal, [ a ], _) -> sprintf "real(%s)" (term a)
  | FunApp (T_irb.RealToInt, _, _) ->
      refuse "the conversion %s has no syntax in .qhes, which converts int to real only"
        (Term.str_of t)
  | _ -> refuse "the term %s has no syntax in .qhes" (Term.str_of t)

and str_of_formula names phi =
  let formula = str_of_formula names in
  match phi with
  | Formula.Atom (Atom.True _, _) -> "true"
  | Atom (False _, _) -> "false"
  | Atom (App (Predicate.Psym sym, [ a; b ], _), _) ->
      let op =
        match sym with
        | T_int.Leq | T_real.RLeq | T_num.NLeq _ -> "<="
        | T_int.Geq | T_real.RGeq | T_num.NGeq _ -> ">="
        | T_int.Lt | T_real.RLt | T_num.NLt _ -> "<"
        | T_int.Gt | T_real.RGt | T_num.NGt _ -> ">"
        | T_bool.Eq -> "="
        | T_bool.Neq -> "!="
        | _ -> refuse "the atom %s has no syntax in .qhes" (Formula.str_of phi)
      in
      sprintf "%s %s %s" (str_of_term names a) op (str_of_term names b)
  | UnaryOp (Not, phi, _) -> sprintf "!(%s)" (formula phi)
  | BinaryOp (And, a, b, _) -> sprintf "(%s /\\ %s)" (formula a) (formula b)
  | BinaryOp (Or, a, b, _) -> sprintf "(%s \\/ %s)" (formula a) (formula b)
  | BinaryOp (Imply, a, b, _) -> sprintf "(%s => %s)" (formula a) (formula b)
  | BinaryOp (Iff, a, b, _) -> sprintf "(%s <=> %s)" (formula a) (formula b)
  | Bind (((Forall | Exists) as binder), params, body, _) ->
      sprintf "(%s %s. %s)"
        (match binder with Forall -> "forall" | _ -> "exists")
        (str_of_bounds names params) (formula body)
  | _ -> refuse "the formula %s has no syntax in .qhes" (Formula.str_of phi)

let str_of_formulas names = String.concat_map_list ~sep:", " ~f:(str_of_formula names)

let str_of_pred names (pred : Pred.t) =
  let fix =
    match pred.kind with
    | Predicate.Mu -> "=mu"
    | Nu -> "=nu"
    | MuOrNu ->
        refuse "the equation of %s is neither a least nor a greatest fixpoint"
          (Ident.name_of_tvar pred.name)
  in
  sprintf "%s %s : real%s%s %s\n  %s;"
    (ident names pred.name)
    (str_of_bounds names pred.args)
    (if List.is_empty pred.annots then ""
     else " | " ^ str_of_formulas names pred.annots)
    (if List.is_empty pred.arg_constrs then ""
     else " requires " ^ str_of_formulas names pred.arg_constrs)
    fix
    (str_of_term names pred.body)

let str_of_app names name args =
  if List.is_empty args then ident names name
  else
    sprintf "%s %s" (ident names name)
      (String.concat_map_list ~sep:" " args ~f:(str_of_term names))

let str_of_query names = function
  | Problem.Check check ->
      let op =
        match (check.kind, check.strict) with
        | UB, false -> "<="
        | UB, true -> "<"
        | LB, false -> ">="
        | LB, true -> ">"
      in
      let atom =
        sprintf "%s %s %s"
          (str_of_app names check.name check.args)
          op
          (str_of_term names check.bound)
      in
      (* the reader takes a quantified query only as [forall xs. left => atom],
         so a query with an antecedent or parameters has both, [true] standing
         for an absent antecedent *)
      if List.is_empty check.params && Option.is_none check.left then atom
      else
        sprintf "forall %s. %s => %s"
          (str_of_bounds names check.params)
          (match check.left with
          | None -> "true"
          | Some left -> str_of_formula names left)
          atom
  | ASAT (init, params, constr) ->
      sprintf "ASAT%s %s | %s"
        (match init with
        | None -> ""
        | Some (name, args) -> sprintf " (%s)" (str_of_app names name args))
        (str_of_bounds names params)
        (str_of_formula names constr)
  | DistCheck dist ->
      sprintf "dist (%s) ensures %s -> (%s)"
        (str_of_app names dist.name dist.args)
        (str_of_bounds names dist.params)
        (str_of_formula names dist.bound)

let render names (qfl : Problem.t) =
  if List.is_empty qfl.preds then
    refuse "a problem without equations has no syntax in .qhes";
  sprintf "%s\ns.t.\n%s\n"
    (str_of_query names qfl.query)
    (String.concat_map_list ~sep:"\n" qfl.preds ~f:(str_of_pred names))

(* Printed twice: the first pass records every name printed as it is, so that
   the second gives a renamed identifier a name no other one has. *)
let str_of (qfl : Problem.t) =
  let names () =
    { taken = Hashtbl.create (module String); renamed = Hashtbl.create (module String); next = 0 }
  in
  let first = names () in
  ignore (render first qfl : string);
  render { (names ()) with taken = first.taken } qfl
