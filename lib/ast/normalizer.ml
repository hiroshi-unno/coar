open Core
open Common
open Util
open LogicOld
open ArithTerm

let rec int_monomials_of (coeff : Value.t) (term : Term.t) : ((Term.t, int) Map.Poly.t, Value.t) Map.Poly.t =
  match term with
  | Var _ -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff
  | FunApp (T_int.Int n, [], _) -> Map.Poly.singleton Map.Poly.empty (Value.mult coeff (Value.Int n))
  | FunApp (T_int.Neg, [t], _) ->
    int_monomials_of (Value.neg coeff) t
  | FunApp (T_int.Add, [t1; t2], _) ->
    NonLinear.add_monomials (int_monomials_of coeff t1) (int_monomials_of coeff t2)
  | FunApp (T_int.Sub, [t1; t2], _) ->
    NonLinear.add_monomials (int_monomials_of coeff t1) (int_monomials_of (Value.neg coeff) t2)
  | FunApp (T_int.Mult, [t1; t2], _) ->
    let ms1 = int_monomials_of (Value.Int Z.one) t1 |> NonLinear.int_simplify in
    let ms2 = int_monomials_of (Value.Int Z.one) t2 |> NonLinear.int_simplify in
    Map.cartesian_map ms1 ms2 ~f:(fun acc m1 c1 m2 c2 ->
        NonLinear.add_update acc (NonLinear.mult_monomials m1 m2) (Value.mult coeff (Value.mult c1 c2)))
  | FunApp (T_int.Div, [t1; t2], _) ->
    Map.Poly.singleton (Map.Poly.singleton (T_int.mk_div (normalize_term t1) (normalize_term t2)) 1) coeff
  | FunApp (T_int.Mod, [t1; t2], _) ->
    Map.Poly.singleton (Map.Poly.singleton (T_int.mk_mod (normalize_term t1) (normalize_term t2)) 1) coeff
  | FunApp (T_int.Rem, [t1; t2], _) ->
    Map.Poly.singleton (Map.Poly.singleton (T_int.mk_rem (normalize_term t1) (normalize_term t2)) 1) coeff
  | FunApp (T_bool.IfThenElse, [t1; t2; t3], _) ->
    Map.Poly.singleton
      (Map.Poly.singleton (T_bool.mk_if_then_else (normalize_term t1) (normalize_term t2) (normalize_term t3)) 1) coeff
  | FunApp (T_array.ASelect, [arr; ti], _) -> 
    begin match T_array.eval_select arr ti with
      | Some te -> int_monomials_of coeff te
      | None -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff
    end
  | FunApp (T_dt.DTSel _, _, _) ->
    let term' = Evaluator.simplify_term term in
    if Stdlib.(=) term term' then Map.Poly.singleton (Map.Poly.singleton term 1) coeff 
    else int_monomials_of coeff term
  | FunApp (FVar (x, sorts), terms, _) ->
    Map.Poly.singleton (Map.Poly.singleton (Term.mk_fvar_app x sorts (List.map ~f:normalize_term terms)) 1) coeff
  | FunApp (T_recfvar.RecFVar (x, env, ret_sort, body), terms, _) ->
    Map.Poly.singleton (Map.Poly.singleton (T_recfvar.mk_recfvar_app x env ret_sort body (List.map ~f:normalize_term terms)) 1) coeff
  | FunApp (fun_sym, terms, _) ->
    (* real_monomials_of (Value.Real Q.one) term *)
    failwith @@ Printf.sprintf "I:the other patterns must not happen: (%s [%s])"
      (Term.str_of_funsym fun_sym)
      (String.concat ~sep:";" @@ List.map ~f:Term.str_of terms)
and real_monomials_of (coeff : Value.t) (term : Term.t)  = 
  match term with
  | Var _ -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff
  | FunApp (T_real.Real n, [], _) -> Map.Poly.singleton Map.Poly.empty (Value.mult coeff (Value.Real n))
  | FunApp (T_real.RNeg, [t], _) -> real_monomials_of (Value.neg coeff) t
  | FunApp (T_real.RAdd, [t1; t2], _) -> NonLinear.add_monomials (real_monomials_of coeff t1) (real_monomials_of coeff t2)
  | FunApp (T_real.RSub, [t1; t2], _) -> NonLinear.add_monomials (real_monomials_of coeff t1) (real_monomials_of (Value.neg coeff) t2)
  | FunApp (T_real.RMult, [t1; t2], _) ->
    let ms1 = real_monomials_of (Value.Real Q.one) t1 |> NonLinear.real_simplify in
    let ms2 = real_monomials_of (Value.Real Q.one) t2 |> NonLinear.real_simplify in
    Map.cartesian_map ms1 ms2 ~f:(fun acc m1 c1 m2 c2 ->
        NonLinear.add_update acc (NonLinear.mult_monomials m1 m2) (Value.mult coeff (Value.mult c1 c2)))
  | FunApp (T_real.RDiv, [t1; t2], _) ->
    Map.Poly.singleton (Map.Poly.singleton (T_real.mk_rdiv (normalize_term t1) (normalize_term t2)) 1) coeff
  | FunApp (T_bool.IfThenElse, [t1; t2; t3], _) ->
    Map.Poly.singleton
      (Map.Poly.singleton (T_bool.mk_if_then_else (normalize_term t1) (normalize_term t2) (normalize_term t3)) 1) coeff
  | FunApp (FVar (x, sorts), terms, _) ->
    Map.Poly.singleton (Map.Poly.singleton (Term.mk_fvar_app x sorts (List.map ~f:normalize_term terms)) 1) coeff
  | FunApp (fun_sym, terms, _) ->
    failwith @@ Printf.sprintf "R:the other patterns must not happen: (%s [%s])"
      (Term.str_of_funsym fun_sym)
      (String.concat ~sep:";" @@ List.map ~f:Term.str_of terms)  
and normalize_datatype_eq psym cons_name dt ts t2  = (* psym must be eq/neq *)
  match Datatype.look_up_cons dt cons_name with
  | Some cons ->
    let is_cons = T_dt.mk_is_cons dt cons t2 in
    let sels = Datatype.sels_of_cons cons in
    let sel_eqs = List.map2_exn sels ts ~f:(
        fun sel t ->
          (Evaluator.simplify_atom @@ Atom.mk_psym_app psym [(T_dt.mk_sel dt (Datatype.name_of_sel sel) t2); t])
      ) in
    begin match psym with 
      | T_bool.Eq ->
        Evaluator.simplify @@ Formula.and_of @@ (Formula.mk_atom is_cons)::sel_eqs
      | T_bool.Neq ->
        Evaluator.simplify @@ Formula.or_of @@ List.map ~f:Formula.mk_neg @@ (Formula.mk_atom is_cons)::sel_eqs
      | _ -> assert false end
  | _ -> assert false
and normalize_term term =
  match Term.sort_of term with
  | T_int.SInt ->
    int_monomials_of (Value.Int Z.one) term
    |> NonLinear.int_simplify |> Map.Poly.to_alist
    |> List.map ~f:(fun (m, c) ->
        if Map.Poly.is_empty m then Term.of_value c
        else if Stdlib.(=) c (Value.Int Z.one) then NonLinear.int_prod m
        else T_int.mk_mult (Term.of_value c) (NonLinear.int_prod m))
    |> (function [] -> T_int.zero () | [t] -> t | t::ts -> T_int.mk_sum t ts)
  | T_real.SReal ->
    real_monomials_of (Value.Real Q.one) term
    |> NonLinear.real_simplify |> Map.Poly.to_alist
    |> List.map ~f:(fun (m, c) ->
        if Map.Poly.is_empty m then Term.of_value c
        else if Stdlib.(=) c (Value.Real Q.one) then NonLinear.real_prod m
        else T_real.mk_rmult (Term.of_value c) (NonLinear.real_prod m))
    |> (function [] -> T_real.rzero () | [t] -> t | t::ts -> T_real.mk_rsum t ts)
  | _ -> (* normalize non-numeric terms *) Evaluator.simplify_term term
let rec normalize_psym psym terms =
  match psym, terms with (* use only Geq, Eq and Neq *)
  | T_bool.Neq, [t1; t2] when Stdlib.(=) (Term.sort_of t1) T_bool.SBool && not @@ Term.is_var t2 ->
    normalize_psym T_bool.Eq [normalize_term t1; normalize_term (T_bool.neg t2)]
  | T_bool.Neq, [t1; t2] when Stdlib.(=) (Term.sort_of t1) T_bool.SBool && not @@ Term.is_var t1 ->
    normalize_psym T_bool.Eq [normalize_term (T_bool.neg t1); normalize_term t2]
  | (T_bool.Eq | T_bool.Neq), [t1; t2] ->
    psym,
    (match Term.sort_of t1, Term.sort_of t2 with
     | T_int.SInt, T_int.SInt -> [normalize_term @@ T_int.mk_sub t1 t2; T_int.zero ()]
     | T_real.SReal, T_real.SReal -> [normalize_term @@ T_real.mk_rsub t1 t2; T_real.rzero ()]
     | _ ->
       let t1 = normalize_term t1 in 
       let t2 = normalize_term t2 in
       match t1, t2 with
       | Term.Var _, Term.FunApp _ -> [t1; t2]
       | Term.FunApp _, Term.Var _ -> [t2; t1]
       | t1, t2 -> if String.compare (Term.str_of t1) (Term.str_of t2) <= 0 then [t1; t2] else [t2; t1])
  | T_int.Geq, [t1; t2] -> T_int.Geq, [normalize_term @@ T_int.mk_sub t1 t2; T_int.zero ()]
  | T_int.Gt, [t1; t2] -> normalize_psym T_int.Geq [t1; T_int.mk_add t2 (T_int.mk_int Z.one)]
  | T_int.Leq, [t1; t2] -> normalize_psym T_int.Geq [t2; t1]
  | T_int.Lt, [t1; t2] -> normalize_psym T_int.Gt [t2; t1]
  | T_real.RGeq, [t1; t2] -> T_real.RGeq, [normalize_term @@ T_real.mk_rsub t1 t2; T_real.rzero ()]
  | T_real.RGt, [t1; t2] -> T_real.RGt, [normalize_term @@ T_real.mk_rsub t1 t2; T_real.rzero ()]
  | T_real.RLeq, [t1; t2] -> normalize_psym T_real.RGeq [t2; t1]
  | T_real.RLt, [t1; t2] -> normalize_psym T_real.RGt [t2; t1]
  | _ -> psym, List.map terms ~f:normalize_term
let normalize_atom (atom : Atom.t) : Atom.t =
  match atom with
  | Atom.True _ | Atom.False _ -> atom
  | Atom.App (Predicate.Var (pvar, sorts), terms, _) ->
    Atom.mk_pvar_app pvar sorts (List.map terms ~f:normalize_term)
  | Atom.App (Predicate.Psym psym, terms, _) ->
    let psym, terms = normalize_psym psym (List.map terms ~f:normalize_term) in
    Atom.mk_psym_app psym terms
  | Atom.App (_, _, _) -> atom (* never happens for qualifiers *)
let rec normalize (phi : Formula.t) : Formula.t =
  match phi with
  | Atom(Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as psym) , [t1; Term.FunApp(T_dt.DTCons (name, _, dt), ts, _)], _), _) 
  | Atom(Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as psym) , [Term.FunApp(T_dt.DTCons (name, _, dt), ts, _); t1], _), _) ->
    normalize_datatype_eq psym name dt ts t1 
  | Atom (atom, info) -> Atom(normalize_atom atom, info)
  | UnaryOp(Not, phi, info) -> UnaryOp (Not, normalize phi, info)
  | BinaryOp (op, phi1, phi2, info) ->
    BinaryOp (op, normalize phi1, normalize phi2, info)
  | Bind (binder, bounds, phi, info) ->
    Bind (binder, bounds, normalize phi, info)
  | LetRec(_funcs, _phi, _info) -> assert false

let homogenize_term term =
  match Term.sort_of term with
  | T_int.SInt ->
    int_monomials_of (Value.Int Z.one) term
    |> NonLinear.int_simplify |> Map.Poly.to_alist
    |> List.map ~f:(fun (m, c) ->
        if Map.Poly.is_empty m then (*Term.of_value c*) T_int.zero ()
        else if Stdlib.(=) c (Value.Int Z.one) then NonLinear.int_prod m
        else T_int.mk_mult (Term.of_value c) (NonLinear.int_prod m))
    |> (function [] -> T_int.zero () | [t] -> t | t::ts -> T_int.mk_sum t ts)
  | T_real.SReal ->
    real_monomials_of (Value.Real Q.one) term
    |> NonLinear.real_simplify |> Map.Poly.to_alist
    |> List.map ~f:(fun (m, c) ->
        if Map.Poly.is_empty m then (*Term.of_value c*) T_real.rzero ()
        else if Stdlib.(=) c (Value.Real Q.one) then NonLinear.real_prod m
        else T_real.mk_rmult (Term.of_value c) (NonLinear.real_prod m))
    |> (function [] -> T_real.rzero () | [t] -> t | t::ts -> T_real.mk_rsum t ts)
  | _ -> (* normalize only numeric terms *) term
let homogenize_atom (atom : Atom.t) : Atom.t =
  match atom with
  | Atom.True _ | Atom.False _ -> atom
  | Atom.App (Predicate.Var (pvar, sorts), terms, _) ->
    Atom.mk_pvar_app pvar sorts (List.map terms ~f:normalize_term)
  | Atom.App (Predicate.Psym psym, terms, _) ->
    let psym, terms = normalize_psym psym terms in
    Atom.mk_psym_app psym (List.map terms ~f:homogenize_term)
  | Atom.App (_, _, _) -> atom (* never happens for qualifiers *)
let rec homogenize (phi : Formula.t) : Formula.t =
  match phi with
  | Atom (atom, info) -> Atom (homogenize_atom atom, info)
  | UnaryOp(Not, phi, info) -> UnaryOp (Not, homogenize phi, info)
  | BinaryOp (op, phi1, phi2, info) ->
    BinaryOp (op, homogenize phi1, homogenize phi2, info)
  | Bind (binder, bounds, phi, info) ->
    Bind (binder, bounds, homogenize phi, info)
  | LetRec(_funcs, _phi, _info) -> assert false

let linear_int_monomials_of coeff term =
  let monomials = NonLinear.int_simplify @@int_monomials_of coeff term in
  Linear.to_linear monomials
let linear_real_monomials_of coeff term =
  let monomials = NonLinear.real_simplify @@real_monomials_of coeff term in
  Linear.to_linear monomials