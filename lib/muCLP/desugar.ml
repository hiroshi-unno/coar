open Core
open Ast
open Ast.LogicOld

let rec of_formula phi = let open Formula in
  match phi with
  | Atom (atom, info) -> Atom (of_atom atom, info)
  | UnaryOp (op, phi, info) -> UnaryOp (op, of_formula phi, info)
  | BinaryOp (Imply, phi1, phi2, info) ->
    let phi1 = of_formula phi1 in
    let phi2 = of_formula phi2 in
    mk_or (mk_neg phi1) phi2 ~info
  | BinaryOp (Iff, phi1, phi2, info) ->
    let phi1 = of_formula phi1 in
    let phi2 = of_formula phi2 in
    mk_and (mk_or (mk_neg phi1) phi2) (mk_or (mk_neg phi2) phi1) ~info
  | BinaryOp (op, phi1, phi2, info) ->
    let phi1 = of_formula phi1 in
    let phi2 = of_formula phi2 in
    BinaryOp (op, phi1, phi2, info)
  | Bind (binder, params, phi, info) ->
    let phi = of_formula phi in
    let fp, conne = match binder with
      | Forall -> Predicate.Nu, and_of
      | Exists -> Predicate.Mu, or_of
      | Random _ -> assert false
    in
    List.fold (SortEnv.list_of params) ~init:phi ~f:(fun phi (ident, sort) ->
        if Stdlib.(=) sort T_bool.SBool then
          conne [
            subst (Core.Map.Poly.singleton ident (T_bool.of_atom (Atom.mk_true ()))) phi;
            subst (Core.Map.Poly.singleton ident (T_bool.of_atom (Atom.mk_false ()))) phi;
          ]
        else
          (* (\nu pvar(x:int). phi /\ X(x+1) /\ X(x-1))(0) *)
          let pident = Ident.mk_fresh_pvar () in
          let tvar = Term.mk_var ident sort in
          let next = T_int.mk_add tvar (T_int.one ()) in
          let prev = T_int.mk_sub tvar (T_int.one ()) in
          let pvar = Predicate.Var (pident, [sort]) in
          let next_app = Atom.mk_app pvar [next] in
          let prev_app = Atom.mk_app pvar [prev] in
          let pred = Predicate.Fixpoint (fp, pident, SortEnv.singleton ident sort, conne [
              phi;
              mk_atom next_app;
              mk_atom prev_app;
            ]) in
          let atom = Atom.mk_app pred [T_int.zero ()] in
          mk_atom atom ~info)
  | LetRec (bounded, phi, info) ->
    let bounded = List.map bounded ~f:(fun (fp, pvar, params, body) ->
        (fp, pvar, params, of_formula body) ) in
    let phi = of_formula phi in
    LetRec (bounded, phi, info)
and of_atom atom = let open Atom in
  match atom with
  | App (pred, args, info) ->
    App (of_pred pred, List.map args ~f:(fun x -> of_term x), info)
  | _ -> atom
and of_pred pred = let open Predicate in
  match pred with
  | Fixpoint (fp, ident, params, phi) ->
    Fixpoint (fp, ident, params, of_formula phi)
  | _ -> pred
and of_term term = let open Term in
  match term with
  | FunApp (sym, args, info) ->
    FunApp (sym, List.map args ~f:(fun x -> of_term x), info)
  | _ -> term

let of_muclp (Problem.MuCLP (funcs, entry)) =
  let entry' = of_formula entry in
  let funcs' = List.map ~f:(fun (fp, pvar, params, phi) -> (fp, pvar, params, of_formula phi)) funcs in
  Problem.MuCLP (funcs', entry')

(* NOTE : stub implementation *)
       (*
let nnf_to_cnf phi =
  let open Formula in
  let rec tseitin phi =
    match phi with
    | BinaryOp (Or, a, b, info) ->
       let (a', env1) = in_disjunction a in
       let (b', env2) = in_disjunction b in
       BinaryOp (Or, a', b', info), (env1@env2)
    | BinaryOp (And, a, b, info) ->
       let (a', env1) = tseitin a in
       let (b', env2) = tseitin b in
       BinaryOp (And, a', b', info), (env1@env2)
    | _ -> phi, []
    and
      in_disjunction =function
      | BinaryOp (Or, a, b, info) ->
         let (a', env1) = in_disjunction a in
         let (b', env2) = in_disjunction b in
         BinaryOp (Or, a', b', info), (env1@env2)
      | (BinaryOp (And, a, b, info)) as phi ->
         factor_out phi
      | _ as phi -> phi, []
    and
      factor_out = function
      | BinaryOp (And, a, b, info) when (is_atom a && is_atom b) ->
         let newatom = gen_pred a b in
         let x_impl_a_and_b =
           mk_and
             (mk_or (mk_neg newatom) a)
             (mk_or (mk_neg newatom) b) in
         newatom, [x_impl_a_and_b]
      | BinaryOp (Or, a, b, info) when (is_atom a && is_atom b) ->
         let newatom = gen_pred a b in
         let y_impl_a_or_b =
           mk_or (mk_neg newatom)
                 (mk_or a b)
         in newatom, [y_impl_a_or_b]
      | BinaryOp (op, a, b, info) ->
         let (a', env1) = factor_out a in
         let (b', env2) = factor_out b in
         let (c', env3) = factor_out (BinaryOp (op, a', b', info)) in
         c', (env1@env2@env3)
      | phi -> phi, []
    and gen_pred a b =
      match a, b with
      | Atom(App (_, paramsa, _), _), Atom(App, (_, paramsb, _),_) ->
         let params = paramsa  in
      let pvar = assert false in
      mk_atom (Atom.mk_app pvar params)
  in tseitin phi
          and let is_atom = function
  | Atom _ | UnaryOp (Neg, (Atom _), _)) -> true
                                       | _ -> false
        *)
