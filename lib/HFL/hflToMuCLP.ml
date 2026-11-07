(* An order-1 HES as a muCLP: the route that hands a first-order system to
   MuVal.  Built with the muCLP constructors ([MuCLP.Pred.make],
   [MuCLP.Problem.make]) over [Ast.LogicOld] terms, never through a muCLP
   reader, so it does not depend on that format's concrete syntax.

   Defined only when [HflSyntax.is_order1] holds after beta-reduction (every
   equation takes only integer arguments and no body has a lambda);
   otherwise [Not_order1] is raised.  The equations map one to one, in HES
   order, to the predicates of the muCLP, with their fixpoint kinds; the query
   is the main equation applied to its parameters, universally closed.  For
   an HES with one fixpoint kind the order of the predicates does not matter
   (Bekic); an alternating HES keeps the tools' order (the last equation
   innermost).  Integer [/] and [%] become truncating division and remainder
   ([Value.Truncated]), as the HES's are.  Variable and predicate names are
   kept. *)

open Core
open Ast
open Ast.LogicOld
open HflSyntax

exception Not_order1 of string

let tvar x = Ident.Tvar x
let ivar x = Term.mk_var (tvar x) T_int.SInt

(** [formula_of ~preds ~arity t] is the first-order formula of a
    beta-normal [t] whose applications all have an equation of [preds] as
    their head; [arity] gives each equation's number of (integer)
    parameters *)
let formula_of ~arity t =
  let rec term = function
    | Var x -> ivar x
    | Int n -> T_int.mk_int (Z.of_int n)
    | Neg a -> T_int.mk_neg (term a)
    | Op (o, a, b) -> (
        let a = term a and b = term b in
        match o with
        | Add -> T_int.mk_add a b
        | Sub -> T_int.mk_sub a b
        | Mul -> T_int.mk_mul a b
        | Div -> T_int.mk_div Value.Truncated a b
        | Mod -> T_int.mk_rem Value.Truncated a b)
    | _ -> raise (Not_order1 "a formula in an integer position")
  in
  let rec fml t =
    match t with
    | Bool true -> Formula.mk_true ()
    | Bool false -> Formula.mk_false ()
    | Pred (p, a, b) ->
        let a = term a and b = term b in
        Formula.mk_atom
          (match p with
          | Eq -> T_bool.mk_eq a b
          | Neq -> T_bool.mk_neq a b
          | Le -> T_int.mk_leq a b
          | Ge -> T_int.mk_geq a b
          | Lt -> T_int.mk_lt a b
          | Gt -> T_int.mk_gt a b)
    | And (a, b) -> Formula.mk_and (fml a) (fml b)
    | Or (a, b) -> Formula.mk_or (fml a) (fml b)
    | Forall (x, a) -> Formula.mk_forall [ (tvar x, T_int.SInt) ] (fml a)
    | Exists (x, a) -> Formula.mk_exists [ (tvar x, T_int.SInt) ] (fml a)
    | Var _ | App _ -> (
        match unapps t with
        | Var p, args -> (
            match arity p with
            | Some n when n = List.length args ->
                Formula.mk_atom
                  (Atom.mk_pvar_app (Ident.Pvar p)
                     (List.map args ~f:(fun _ -> T_int.SInt))
                     (List.map args ~f:term))
            | _ ->
                raise
                  (Not_order1
                     (sprintf "%s is not an equation applied to all its arguments"
                        p)))
        | _ -> raise (Not_order1 "an application whose head is not a variable"))
    | Abs _ -> raise (Not_order1 "a lambda")
    | Int _ | Op _ | Neg _ -> raise (Not_order1 "an integer in a formula position")
  in
  fml t

let to_problem (hes : hes) =
  let hes =
    { hes with eqns = List.map hes.eqns ~f:(fun e -> { e with body = beta e.body }) }
  in
  if not (is_order1 hes) then
    raise (Not_order1 "an equation with a non-integer parameter");
  let arities =
    String.Map.of_alist_reduce ~f:(fun a _ -> a)
      (List.map hes.eqns ~f:(fun e -> (e.name, List.length e.params)))
  in
  let arity = Map.find arities in
  let bounds e = List.map e.params ~f:(fun (x, _) -> (tvar x, T_int.SInt)) in
  let preds =
    List.map hes.eqns ~f:(fun e ->
        MuCLP.Pred.make
          (match e.fix with Nu -> Predicate.Nu | Mu -> Predicate.Mu)
          (Ident.Pvar e.name) (bounds e) (formula_of ~arity e.body))
  in
  let main = List.hd_exn hes.eqns in
  let app =
    Formula.mk_atom
      (Atom.mk_pvar_app (Ident.Pvar main.name)
         (List.map main.params ~f:(fun _ -> T_int.SInt))
         (List.map main.params ~f:(fun (x, _) -> ivar x)))
  in
  let query =
    match main.params with [] -> app | _ -> Formula.mk_forall (bounds main) app
  in
  MuCLP.Problem.make preds query

let to_text hes = MuCLP.Problem.str_of (to_problem hes)
