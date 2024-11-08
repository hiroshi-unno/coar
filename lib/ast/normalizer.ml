open Core
open Common.Ext
open Common.Combinator
open LogicOld
open ArithTerm

let rec int_monomials_of (coeff : Value.t) = function
  | Term.Var _ as term -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff
  | FunApp (T_int.Int n, [], _) ->
      Map.Poly.singleton Map.Poly.empty (Value.mult coeff (Value.Int n))
  | FunApp (T_int.Neg, [ t ], _) -> int_monomials_of (Value.neg coeff) t
  | FunApp (T_int.Abs, [ t ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton (T_int.mk_abs (normalize_term t)) 1)
        coeff
  | FunApp (T_int.Add, [ t1; t2 ], _) ->
      NonLinear.add_monomials
        (int_monomials_of coeff t1)
        (int_monomials_of coeff t2)
  | FunApp (T_int.Sub, [ t1; t2 ], _) ->
      NonLinear.add_monomials
        (int_monomials_of coeff t1)
        (int_monomials_of (Value.neg coeff) t2)
  | FunApp (T_int.Mult, [ t1; t2 ], _) ->
      let ms1 =
        int_monomials_of (Value.Int Z.one) t1 |> NonLinear.int_simplify
      in
      let ms2 =
        int_monomials_of (Value.Int Z.one) t2 |> NonLinear.int_simplify
      in
      Map.cartesian_map ms1 ms2 ~f:(fun acc m1 c1 m2 c2 ->
          NonLinear.add_update acc
            (NonLinear.mult_monomials m1 m2)
            (Value.mult coeff (Value.mult c1 c2)))
  | FunApp (T_int.Div, [ t1; t2 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (T_int.mk_div (normalize_term t1) (normalize_term t2))
           1)
        coeff
  | FunApp (T_int.Mod, [ t1; t2 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (T_int.mk_mod (normalize_term t1) (normalize_term t2))
           1)
        coeff
  | FunApp (T_int.Rem, [ t1; t2 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (T_int.mk_rem (normalize_term t1) (normalize_term t2))
           1)
        coeff
  | FunApp (T_irb.RealToInt, [ t1 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton (T_irb.mk_real_to_int (normalize_term t1)) 1)
        coeff
  | FunApp (T_irb.BVToInt size, [ t1 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton (T_irb.mk_bv_to_int ~size (normalize_term t1)) 1)
        coeff
  | FunApp (FVar (x, sorts), ts, _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (Term.mk_fvar_app x sorts (List.map ~f:normalize_term ts))
           1)
        coeff
  | FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], _) ->
      let mono =
        T_bool.mk_if_then_else (normalize_term t1) (normalize_term t2)
          (normalize_term t3)
      in
      Map.Poly.singleton (Map.Poly.singleton mono 1) coeff
  | FunApp (T_ref.Deref _, [ t ], _) as term -> (
      match T_ref.eval_select t with
      | Some te -> int_monomials_of coeff te
      | None -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff (*ToDo*))
  | FunApp (T_array.ASelect _, [ arr; ti ], _) as term -> (
      match T_array.eval_select arr ti with
      | Some te -> int_monomials_of coeff te
      | None -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  | FunApp (T_tuple.TupleSel (_, i), [ t ], _) as term -> (
      match T_tuple.eval_select t i with
      | Some te -> int_monomials_of coeff te
      | None -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  | FunApp (T_dt.DTSel (sel_name, dt, _), [ t ], _) as term -> (
      match T_dt.eval_select sel_name dt t with
      | Some te -> int_monomials_of coeff te
      | None -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  | FunApp (fun_sym, terms, _) as term ->
      (* real_monomials_of (Value.Real Q.one) term *)
      failwith
      @@ sprintf "[int_monomials_of] not supported: %s : (%s [%s])"
           (Term.str_of term)
           (Term.str_of_funsym fun_sym)
           (String.concat_map_list ~sep:";" ~f:Term.str_of terms)
  | LetTerm (_, _, _, _, _) as term -> failwith @@ Term.str_of term

and real_monomials_of (coeff : Value.t) = function
  | Term.Var _ as term -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff
  | FunApp (T_real.Real n, [], _) ->
      Map.Poly.singleton Map.Poly.empty (Value.mult coeff (Value.Real n))
  | FunApp (T_real.Alge n, [ t ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton (T_real.mk_alge (normalize_term t) n) 1)
        coeff
  | FunApp (T_real.RNeg, [ t ], _) -> real_monomials_of (Value.neg coeff) t
  | FunApp (T_real.RAdd, [ t1; t2 ], _) ->
      NonLinear.add_monomials
        (real_monomials_of coeff t1)
        (real_monomials_of coeff t2)
  | FunApp (T_real.RSub, [ t1; t2 ], _) ->
      NonLinear.add_monomials
        (real_monomials_of coeff t1)
        (real_monomials_of (Value.neg coeff) t2)
  | FunApp (T_real.RMult, [ t1; t2 ], _) ->
      let ms1 =
        real_monomials_of (Value.Real Q.one) t1 |> NonLinear.real_simplify
      in
      let ms2 =
        real_monomials_of (Value.Real Q.one) t2 |> NonLinear.real_simplify
      in
      Map.cartesian_map ms1 ms2 ~f:(fun acc m1 c1 m2 c2 ->
          NonLinear.add_update acc
            (NonLinear.mult_monomials m1 m2)
            (Value.mult coeff (Value.mult c1 c2)))
  | FunApp (T_real.RDiv, [ t1; t2 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (T_real.mk_rdiv (normalize_term t1) (normalize_term t2))
           1)
        coeff
  | FunApp (T_real.RPower, [ t1; t2 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (T_real.mk_rpower (normalize_term t1) (normalize_term t2))
           1)
        coeff
  | FunApp (T_real.RAbs, [ t1 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton (T_real.mk_rabs (normalize_term t1)) 1)
        coeff
  | FunApp (T_irb.IntToReal, [ t1 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton (T_irb.mk_int_to_real (normalize_term t1)) 1)
        coeff
  | FunApp (FVar (x, sorts), ts, _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (Term.mk_fvar_app x sorts (List.map ~f:normalize_term ts))
           1)
        coeff
  | FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], _) ->
      let mono =
        T_bool.mk_if_then_else (normalize_term t1) (normalize_term t2)
          (normalize_term t3)
      in
      Map.Poly.singleton (Map.Poly.singleton mono 1) coeff
  | FunApp (T_ref.Deref _, [ t ], _) as term -> (
      match T_ref.eval_select t with
      | Some te -> real_monomials_of coeff te
      | None -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff (*ToDo*))
  | FunApp (T_array.ASelect _, [ arr; ti ], _) as term -> (
      match T_array.eval_select arr ti with
      | Some te -> real_monomials_of coeff te
      | None -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  | FunApp (T_tuple.TupleSel (_, i), [ t ], _) as term -> (
      match T_tuple.eval_select t i with
      | Some te -> real_monomials_of coeff te
      | None -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  | FunApp (T_dt.DTSel (sel_name, dt, _), [ t ], _) as term -> (
      match T_dt.eval_select sel_name dt t with
      | Some te -> real_monomials_of coeff te
      | None -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  | FunApp (fun_sym, terms, _) ->
      failwith
      @@ sprintf "[real_monomials_of] not supported: (%s [%s])"
           (Term.str_of_funsym fun_sym)
           (String.concat_map_list ~sep:";" ~f:Term.str_of terms)
  | LetTerm (_, _, _, _, _) as term -> failwith @@ Term.str_of term

and normalize_datatype_eq psym cons_name dt ts t2 =
  (* psym must be eq/neq *)
  match Datatype.look_up_cons dt cons_name with
  | None -> assert false
  | Some cons -> (
      let sels = Datatype.sels_of_cons cons in
      match psym with
      | T_bool.Eq ->
          let is_cons = Formula.mk_atom @@ T_dt.mk_is_cons dt cons_name t2 in
          Evaluator.simplify @@ Formula.and_of
          @@ is_cons
             :: List.map2_exn sels ts ~f:(fun sel t ->
                    Evaluator.simplify
                    @@ Formula.eq
                         (T_dt.mk_sel dt (Datatype.name_of_sel sel) t2)
                         t)
      | T_bool.Neq ->
          let is_not_cons =
            Formula.mk_atom @@ T_dt.mk_is_not_cons dt cons_name t2
          in
          Evaluator.simplify @@ Formula.or_of
          @@ is_not_cons
             :: List.map2_exn sels ts ~f:(fun sel t ->
                    Evaluator.simplify
                    @@ Formula.neq
                         (T_dt.mk_sel dt (Datatype.name_of_sel sel) t2)
                         t)
      | _ -> assert false)

and normalize_term ?(drop_coeff = false) = function
  | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, normalize_term def, normalize_term body, info)
  | Term.FunApp (T_bool.Formula phi, [], info) ->
      Term.FunApp (T_bool.Formula (normalize phi), [], info)
  | term -> (
      match Term.sort_of term with
      | T_int.SInt -> (
          int_monomials_of (Value.Int Z.one) term
          |> NonLinear.int_simplify
          |> (if drop_coeff then NonLinear.div_by_gcd else Fn.id)
          |> Map.Poly.to_alist
          |> List.map ~f:(fun (m, c) ->
                 if Map.Poly.is_empty m then Term.of_value c
                 else if Stdlib.(c = Value.Int Z.one) then NonLinear.int_prod m
                 else T_int.mk_mult (Term.of_value c) (NonLinear.int_prod m))
          |> function
          | [] -> T_int.zero ()
          | [ t ] -> t
          | t :: ts -> T_int.mk_sum t ts)
      | T_real.SReal -> (
          real_monomials_of (Value.Real Q.one) term
          |> NonLinear.real_simplify
          |> (if false (*drop_coeff*) then NonLinear.div_by_gcd else Fn.id)
          |> Map.Poly.to_alist
          |> List.map ~f:(fun (m, c) ->
                 if Map.Poly.is_empty m then Term.of_value c
                 else if Stdlib.(c = Value.Real Q.one) then
                   NonLinear.real_prod m
                 else T_real.mk_rmult (Term.of_value c) (NonLinear.real_prod m))
          |> function
          | [] -> T_real.rzero ()
          | [ t ] -> t
          | t :: ts -> T_real.mk_rsum t ts)
      | _ -> (* normalize non-numeric terms *) Evaluator.simplify_term term)

and normalize_psym psym terms =
  match (psym, terms) with
  | T_bool.Neq, [ t1; t2 ]
    when (Term.is_bool_sort @@ Term.sort_of t1)
         && Fn.non Term.is_var t2
         && not
              (T_dt.is_sel t2 || T_tuple.is_tuple_sel t2 || Term.is_fvar_app t2)
    ->
      normalize_psym T_bool.Eq
        [ normalize_term t1; normalize_term (T_bool.neg t2) ]
  | T_bool.Neq, [ t1; t2 ]
    when (Term.is_bool_sort @@ Term.sort_of t1)
         && Fn.non Term.is_var t1
         && not
              (T_dt.is_sel t1 || T_tuple.is_tuple_sel t1 || Term.is_fvar_app t1)
    ->
      normalize_psym T_bool.Eq
        [ normalize_term (T_bool.neg t1); normalize_term t2 ]
  | (T_bool.Eq | T_bool.Neq), [ t1; t2 ] ->
      (* assume that [t1] and [t2] are let-normalized *)
      ( psym,
        match (Term.sort_of t1, Term.sort_of t2) with
        | T_int.SInt, T_int.SInt ->
            [
              normalize_term ~drop_coeff:true @@ T_int.mk_sub t1 t2;
              T_int.zero ();
            ]
        | T_real.SReal, T_real.SReal ->
            [
              normalize_term ~drop_coeff:true @@ T_real.mk_rsub t1 t2;
              T_real.rzero ();
            ]
        | _ -> (
            let t1 = normalize_term t1 in
            let t2 = normalize_term t2 in
            match (t1, t2) with
            | Term.Var _, Term.FunApp _ -> [ t1; t2 ]
            | Term.FunApp _, Term.Var _ -> [ t2; t1 ]
            | t1, t2 ->
                if String.compare (Term.str_of t1) (Term.str_of t2) <= 0 then
                  [ t1; t2 ]
                else [ t2; t1 ]) )
  (* the return value does not use Gt, Leq, and Lt *)
  | T_int.Geq, [ t1; t2 ] ->
      ( T_int.Geq,
        [ normalize_term ~drop_coeff:true @@ T_int.mk_sub t1 t2; T_int.zero () ]
      )
  | T_int.Gt, [ t1; t2 ] ->
      normalize_psym T_int.Geq [ t1; T_int.mk_add t2 (T_int.mk_int Z.one) ]
  | T_int.Leq, [ t1; t2 ] -> normalize_psym T_int.Geq [ t2; t1 ]
  | T_int.Lt, [ t1; t2 ] -> normalize_psym T_int.Gt [ t2; t1 ]
  (*| T_int.PDiv [t1; t2] | T_int.NotPDiv [t1; t2] -> failwith ""*)
  (* the return value does not use RLeq and RLt *)
  | T_real.RGeq, [ t1; t2 ] ->
      ( T_real.RGeq,
        [
          normalize_term ~drop_coeff:true @@ T_real.mk_rsub t1 t2;
          T_real.rzero ();
        ] )
  | T_real.RGt, [ t1; t2 ] ->
      ( T_real.RGt,
        [
          normalize_term ~drop_coeff:true @@ T_real.mk_rsub t1 t2;
          T_real.rzero ();
        ] )
  | T_real.RLeq, [ t1; t2 ] -> normalize_psym T_real.RGeq [ t2; t1 ]
  | T_real.RLt, [ t1; t2 ] -> normalize_psym T_real.RGt [ t2; t1 ]
  | _ -> (psym, List.map terms ~f:normalize_term)

and normalize_atom = function
  | (Atom.True _ | Atom.False _) as atom -> atom
  | Atom.App (Predicate.Var (pvar, sorts), terms, _)
    when Map.Poly.mem (get_fenv ()) (Ident.pvar_to_tvar pvar) ->
      T_bool.mk_eq
        (Term.mk_fvar_app (Ident.pvar_to_tvar pvar) (sorts @ [ T_bool.SBool ])
           (List.map ~f:normalize_term terms))
        (T_bool.mk_true ())
  | Atom.App (Predicate.Var (pvar, sorts), terms, _) ->
      Atom.mk_pvar_app pvar sorts @@ List.map terms ~f:normalize_term
  | Atom.App (Predicate.Psym psym, terms, _) ->
      uncurry Atom.mk_psym_app @@ normalize_psym psym
      @@ List.map terms ~f:normalize_term
  | Atom.App (Predicate.Fixpoint _, _, _) as atom -> atom

and normalize = function
  (* | Atom (Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq as op), [Term.Var (Ident.Tvar v, T_bool.SBool, _); t], _), _)
     when T_bool.is_true t || T_bool.is_false t ->
      let atom = Atom.mk_pvar_app (Ident.Pvar v) [] [] in
      if (Stdlib.(op = T_bool.Eq) && T_bool.is_true t) || (Stdlib.(op = T_bool.Neq) && T_bool.is_false t) then
        Formula.mk_atom atom
      else
        Formula.mk_atom atom |> Formula.mk_neg
     | Atom (Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq as op), [t; Term.Var (Ident.Tvar v, T_bool.SBool, _)], _), _)
     when T_bool.is_true t || T_bool.is_false t ->
      let atom = Atom.mk_pvar_app (Ident.Pvar v) [] [] in
      if (Stdlib.(op = T_bool.Eq) && T_bool.is_true t) || (Stdlib.(op = T_bool.Neq) && T_bool.is_false t) then
        Formula.mk_atom atom
      else
        Formula.mk_atom atom |> Formula.mk_neg *)
  (* | Atom (Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq as op), [t1; t2], _), _) when T_bool.is_sbool t1 ->
     let phi1, phi2 = Formula.of_bool_term t1, Formula.of_bool_term t2 in
     let nphi1, nphi2 = Formula.mk_neg phi1, Formula.mk_neg phi2 in
     normalize @@ if Stdlib.(op = T_bool.Eq) then
      Formula.or_of [Formula.and_of[phi1; phi2]; Formula.and_of [nphi1; nphi2]]
     else
      Formula.or_of [Formula.and_of[phi1; nphi2]; Formula.and_of [nphi1; phi2]] *)
  (*| Atom (Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as psym),
                    [t1; Term.FunApp (T_dt.DTCons (name, _, dt), ts, _)], _), _)
    | Atom (Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as psym),
                    [Term.FunApp (T_dt.DTCons (name, _, dt), ts, _); t1], _), _) ->
    normalize_datatype_eq psym name dt ts t1*)
  | Atom (atom, info) -> Atom (normalize_atom atom, info)
  | UnaryOp (Not, phi, info) -> UnaryOp (Not, normalize phi, info)
  | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, normalize phi1, normalize phi2, info)
  | Bind (binder, bounds, phi, info) ->
      Bind (binder, bounds, normalize phi, info)
  | LetRec (_funcs, _phi, _info) -> assert false
  | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, sort, normalize_term def, normalize body, info)

(* assume [term] is alpha-renamed by LogicOld.Term.alpha_rename_let *)
let rec normalize_let_term = function
  | Term.Var _ as term -> term
  | Term.LetTerm (var, sort, def, body, info) ->
      let def' = normalize_let_term def in
      let body' = normalize_let_term body in
      Term.replace_let_body def'
      @@ Term.LetTerm (var, sort, Term.body_of_let def', body', info)
  | Term.FunApp (T_bool.Formula phi, [], info) ->
      FunApp (T_bool.Formula (normalize_let_formula phi), [], info)
  | Term.FunApp (op, ts, info) ->
      let ts' = List.map ts ~f:normalize_let_term in
      let term = Term.mk_fsym_app op (List.map ts' ~f:Term.body_of_let) ~info in
      List.fold ts' ~init:term ~f:(Fn.flip Term.replace_let_body)

and normalize_let_atom ?(info = LogicOld.Dummy) = function
  | (Atom.True _ | Atom.False _) as atom -> Formula.mk_atom atom ~info
  | Atom.App (pred, ts, info) ->
      let ts' = List.map ts ~f:normalize_let_term in
      let body =
        Formula.mk_atom
        @@ Atom.mk_app pred (List.map ts' ~f:Term.body_of_let) ~info
      in
      List.fold ts' ~init:body ~f:(Fn.flip Formula.replace_let_term_body)

and normalize_let_formula = function
  | Formula.Atom (atom, info) -> normalize_let_atom atom ~info
  | Formula.LetFormula (var, sort, def, body, info) ->
      let def' = normalize_let_term def in
      let body' = normalize_let_formula body in
      Formula.replace_let_term_body def'
      @@ Formula.LetFormula (var, sort, Term.body_of_let def', body', info)
  | Formula.UnaryOp (op, phi1, info) ->
      let phi1' = normalize_let_formula phi1 in
      Formula.replace_let_body phi1'
      @@ UnaryOp (op, Formula.body_of_let phi1', info)
  | Formula.BinaryOp (op, phi1, phi2, info) ->
      let phi1' = normalize_let_formula phi1 in
      let phi2' = normalize_let_formula phi2 in
      Formula.replace_let_body phi2'
      @@ Formula.replace_let_body phi1'
      @@ Formula.BinaryOp
           (op, Formula.body_of_let phi1', Formula.body_of_let phi2', info)
  | Formula.Bind (binder, bounds, phi1, info) ->
      Formula.Bind (binder, bounds, normalize_let_formula phi1, info)
  (* let phi1' = normalize_let_formula phi1 in
     Formula.replace_let_body phi1' @@
     Bind (binder, bounds, Formula.body_of_let phi1', info) *)
  | Formula.LetRec _ as phi -> phi

let normalize_let ?(rename = false) phi =
  normalize_let_formula @@ if rename then Formula.alpha_rename_let phi else phi

let homogenize_term term =
  match Term.sort_of term with
  | T_int.SInt -> (
      int_monomials_of (Value.Int Z.one) term
      |> NonLinear.int_simplify |> Map.Poly.to_alist
      |> List.map ~f:(fun (m, c) ->
             if Map.Poly.is_empty m then (*Term.of_value c*) T_int.zero ()
             else if Stdlib.(c = Value.Int Z.one) then NonLinear.int_prod m
             else T_int.mk_mult (Term.of_value c) (NonLinear.int_prod m))
      |> function
      | [] -> T_int.zero ()
      | [ t ] -> t
      | t :: ts -> T_int.mk_sum t ts)
  | T_real.SReal -> (
      real_monomials_of (Value.Real Q.one) term
      |> NonLinear.real_simplify |> Map.Poly.to_alist
      |> List.map ~f:(fun (m, c) ->
             if Map.Poly.is_empty m then (*Term.of_value c*) T_real.rzero ()
             else if Stdlib.(c = Value.Real Q.one) then NonLinear.real_prod m
             else T_real.mk_rmult (Term.of_value c) (NonLinear.real_prod m))
      |> function
      | [] -> T_real.rzero ()
      | [ t ] -> t
      | t :: ts -> T_real.mk_rsum t ts)
  | _ -> (* normalize only numeric terms *) term

let homogenize_atom = function
  | (Atom.True _ | Atom.False _) as atom -> atom
  | Atom.App (Predicate.Var (pvar, sorts), terms, _) ->
      Atom.mk_pvar_app pvar sorts @@ List.map terms ~f:normalize_term
  | Atom.App (Predicate.Psym psym, terms, _) ->
      let psym, terms = normalize_psym psym terms in
      Atom.mk_psym_app psym @@ List.map terms ~f:homogenize_term
  | Atom.App (_, _, _) as atom -> atom (* never happens for qualifiers *)

let rec homogenize = function
  | Formula.Atom (atom, info) -> Formula.Atom (homogenize_atom atom, info)
  | Formula.UnaryOp (Not, phi, info) ->
      Formula.UnaryOp (Not, homogenize phi, info)
  | Formula.BinaryOp (op, phi1, phi2, info) ->
      Formula.BinaryOp (op, homogenize phi1, homogenize phi2, info)
  | Formula.Bind (binder, bounds, phi, info) ->
      Formula.Bind (binder, bounds, homogenize phi, info)
  | Formula.LetRec (_funcs, _phi, _info) -> failwith "LetRec not implemented"
  | Formula.LetFormula (var, sort, def, body, info) ->
      Formula.LetFormula (var, sort, homogenize_term def, homogenize body, info)

let linear_int_monomials_of coeff term =
  try Linear.to_linear @@ NonLinear.int_simplify @@ int_monomials_of coeff term
  with _ ->
    failwith
    @@ sprintf "[linear_int_monomials_of] %s not supported" (Term.str_of term)

let linear_real_monomials_of coeff term =
  try
    Linear.to_linear @@ NonLinear.real_simplify @@ real_monomials_of coeff term
  with _ ->
    failwith
    @@ sprintf "[linear_real_monomials_of] %s not supported" (Term.str_of term)
