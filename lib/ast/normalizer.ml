open Core
open Common.Ext
open LogicOld


(* A memo for [normalize] and [normalize_atom] that lives for one scope of
   [with_shared_normalize], keyed by node address.

   Contract of [with_shared_normalize f]: when [share_normalize] is set,
   [f ()] runs with this domain's [normalize] remembering the result for
   every formula node, and [normalize_atom] for every atom, whose computation
   drew no fresh name ([Ident.fresh_stamp] unchanged); a node met again in
   the scope, physically the same value, gets the remembered result; the
   tables are dropped when [f] returns or raises, and an inner scope uses the
   outer one.  Unset, it only runs [f].  Exact for the reason the
   simplifier's memo is: a node's normal form is a function of the node and
   of the function environment, which no normalisation changes, and a
   remembered computation drew no name, so the results are the ones without
   the scope, value for value and draw for draw, only more shared. *)
let share_normalize = Atomic.make false

module PhysFml = Stdlib.Hashtbl.Make (struct
  type t = Formula.t

  let equal = phys_equal
  let hash = Common.Ext.Hashtbl.phys_hash
end)

module PhysAtm = Stdlib.Hashtbl.Make (struct
  type t = Atom.t

  let equal = phys_equal
  let hash = Common.Ext.Hashtbl.phys_hash
end)

type normalize_tables = { fmls : Formula.t PhysFml.t; atoms : Atom.t PhysAtm.t }

let normalize_scope : normalize_tables option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_shared_normalize f =
  if not (Atomic.get share_normalize) then f ()
  else
    match Stdlib.Domain.DLS.get normalize_scope with
    | Some _ -> f ()
    | None ->
        Stdlib.Domain.DLS.set normalize_scope
          (Some { fmls = PhysFml.create 1024; atoms = PhysAtm.create 1024 });
        Exn.protect ~f ~finally:(fun () ->
            Stdlib.Domain.DLS.set normalize_scope None)

let rec int_monomials_of (coeff : Value.t) = function
  | Term.Var _ as term -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff
  | FunApp (T_int.Int n, [], _) ->
      Map.Poly.singleton Map.Poly.empty (Value.mul coeff (Value.Int n))
  | FunApp (T_int.Neg, [ t ], _) -> int_monomials_of (Value.neg coeff) t
  | FunApp (T_int.Nop, [ t ], _) -> int_monomials_of coeff t
  | FunApp (T_int.Abs, [ t ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton (T_int.mk_abs (normalize_term t)) 1)
        coeff
  | FunApp (T_int.Add, [ t1; t2 ], _) ->
      PolyTerm.int_add_monomials
        (int_monomials_of coeff t1)
        (int_monomials_of coeff t2)
  | FunApp (T_int.Sub, [ t1; t2 ], _) ->
      PolyTerm.int_add_monomials
        (int_monomials_of coeff t1)
        (int_monomials_of (Value.neg coeff) t2)
  | FunApp (T_int.Mul, [ t1; t2 ], _) ->
      let ms1 =
        int_monomials_of (Value.Int Z.one) t1 |> PolyTerm.int_simplify
      in
      let ms2 =
        int_monomials_of (Value.Int Z.one) t2 |> PolyTerm.int_simplify
      in
      Map.cartesian_map ms1 ms2 ~f:(fun acc m1 c1 m2 c2 ->
          PolyTerm.int_add_update acc
            (PolyTerm.mul_monomials m1 m2)
            (Value.mul coeff (Value.mul c1 c2)))
  | FunApp (T_int.Div m, [ t1; t2 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (T_int.mk_div m (normalize_term t1) (normalize_term t2))
           1)
        coeff
  | FunApp (T_int.Rem m, [ t1; t2 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (T_int.mk_rem m (normalize_term t1) (normalize_term t2))
           1)
        coeff
  | FunApp (T_int.Power, [ t1; t2 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (T_int.mk_power (normalize_term t1) (normalize_term t2))
           1)
        coeff
  | FunApp (T_irb.RealToInt, [ t1 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton (T_irb.mk_real_to_int (normalize_term t1)) 1)
        coeff
  | FunApp (T_irb.BVToInt (size, signed), [ t1 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (T_irb.mk_bv_to_int ~size ~signed (normalize_term t1))
           1)
        coeff
  | FunApp (FVar (x, sargs, sret), ts, _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (Term.mk_fvar_app x sargs sret (List.map ~f:normalize_term ts))
           1)
        coeff
  | FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], _) ->
      let mono =
        T_bool.mk_if_then_else (normalize_term t1) (normalize_term t2)
          (normalize_term t3)
      in
      Map.Poly.singleton (Map.Poly.singleton mono 1) coeff
  | FunApp (T_int.Case n, t1 :: branches, _) ->
      let mono =
        T_int.mk_case n (normalize_term t1)
          (List.map branches ~f:normalize_term)
      in
      Map.Poly.singleton (Map.Poly.singleton mono 1) coeff
  | FunApp (T_array.ASelect _, [ arr; ti ], _) as term -> (
      match T_array.eval_select arr ti with
      | Some te when Stdlib.(Term.sort_of te = T_int.SInt) ->
          int_monomials_of coeff te
      (* Until typing resolves a numeric literal, retain the select's rank
         constraint instead of sending its beta reduct to arithmetic, which
         crashes on a literal whose sort is still a variable. *)
      | _ -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  (* Constructor projections have the same rank obligation as array reads:
     an unresolved reduct must retain the operator constraint. *)
  | FunApp (T_tuple.TupleSel (_, i), [ t ], _) as term -> (
      match T_tuple.eval_select t i with
      | Some te when Stdlib.(Term.sort_of te = T_int.SInt) ->
          int_monomials_of coeff te
      | _ -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  | FunApp (T_dt.DTSel (sel_name, dt, _), [ t ], _) as term -> (
      match T_dt.eval_select sel_name dt t with
      | Some te when Stdlib.(Term.sort_of te = T_int.SInt) ->
          int_monomials_of coeff te
      | _ -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  | FunApp (T_ref.Deref _, [ t ], _) as term -> (
      match T_ref.eval_select t with
      | Some te when Stdlib.(Term.sort_of te = T_int.SInt) ->
          int_monomials_of coeff te
      | _ -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff (*ToDo*))
  | FunApp ((T_seq.SqLen _ | T_seq.SqNth _), _, _) as term ->
      (* an integer the sequence theory decides and this normal form cannot
         see inside: the length of a sequence, or one of its elements *)
      Map.Poly.singleton (Map.Poly.singleton term 1) coeff
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
      Map.Poly.singleton Map.Poly.empty (Value.rmul coeff (Value.Real n))
  | FunApp (T_real.Alge n, [ t ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton (T_real.mk_alge (normalize_term t) n) 1)
        coeff
  | FunApp (T_real.RNeg, [ t ], _) -> real_monomials_of (Value.neg coeff) t
  | FunApp (T_real.RAbs, [ t1 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton (T_real.mk_rabs (normalize_term t1)) 1)
        coeff
  | FunApp (T_real.RAdd, [ t1; t2 ], _) ->
      PolyTerm.real_add_monomials
        (real_monomials_of coeff t1)
        (real_monomials_of coeff t2)
  | FunApp (T_real.RSub, [ t1; t2 ], _) ->
      PolyTerm.real_add_monomials
        (real_monomials_of coeff t1)
        (real_monomials_of (Value.neg coeff) t2)
  | FunApp (T_real.RMul, [ t1; t2 ], _) ->
      let ms1 =
        real_monomials_of (Value.Real Q.one) t1 |> PolyTerm.real_simplify
      in
      let ms2 =
        real_monomials_of (Value.Real Q.one) t2 |> PolyTerm.real_simplify
      in
      Map.cartesian_map ms1 ms2 ~f:(fun acc m1 c1 m2 c2 ->
          PolyTerm.real_add_update acc
            (PolyTerm.mul_monomials m1 m2)
            (Value.rmul coeff (Value.rmul c1 c2)))
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
  | FunApp (T_irb.IntToReal, [ t1 ], _) ->
      Map.Poly.singleton
        (Map.Poly.singleton (T_irb.mk_int_to_real (normalize_term t1)) 1)
        coeff
  | FunApp (FVar (x, sargs, sret), ts, _) ->
      Map.Poly.singleton
        (Map.Poly.singleton
           (Term.mk_fvar_app x sargs sret (List.map ~f:normalize_term ts))
           1)
        coeff
  | FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], _) ->
      let mono =
        T_bool.mk_if_then_else (normalize_term t1) (normalize_term t2)
          (normalize_term t3)
      in
      Map.Poly.singleton (Map.Poly.singleton mono 1) coeff
  | FunApp (T_int.Case n, t1 :: branches, _) ->
      let mono =
        T_int.mk_case n (normalize_term t1)
          (List.map branches ~f:normalize_term)
      in
      Map.Poly.singleton (Map.Poly.singleton mono 1) coeff
  | FunApp (T_ref.Deref _, [ t ], _) as term -> (
      match T_ref.eval_select t with
      | Some te when Stdlib.(Term.sort_of te = T_real.SReal) ->
          real_monomials_of coeff te
      | _ -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff (*ToDo*))
  | FunApp (T_array.ASelect _, [ arr; ti ], _) as term -> (
      match T_array.eval_select arr ti with
      | Some te when Stdlib.(Term.sort_of te = T_real.SReal) ->
          real_monomials_of coeff te
      | _ -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  | FunApp (T_tuple.TupleSel (_, i), [ t ], _) as term -> (
      match T_tuple.eval_select t i with
      | Some te when Stdlib.(Term.sort_of te = T_real.SReal) ->
          real_monomials_of coeff te
      | _ -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  | FunApp (T_dt.DTSel (sel_name, dt, _), [ t ], _) as term -> (
      match T_dt.eval_select sel_name dt t with
      | Some te when Stdlib.(Term.sort_of te = T_real.SReal) ->
          real_monomials_of coeff te
      | _ -> Map.Poly.singleton (Map.Poly.singleton term 1) coeff)
  | FunApp (T_seq.SqNth _, _, _) as term ->
      (* an element of a sequence of reals: a real the sequence theory decides
         and this normal form cannot see inside, an atom exactly as it is for a
         sequence of integers *)
      Map.Poly.singleton (Map.Poly.singleton term 1) coeff
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
          Evaluator.simplify @@ Formula.and_of
          @@ (Formula.mk_atom @@ T_dt.mk_is_cons dt cons_name t2)
             :: List.map2_exn sels ts ~f:(fun sel t ->
                 Evaluator.simplify
                 @@ Formula.eq (T_dt.mk_sel dt (Datatype.name_of_sel sel) t2) t)
      | T_bool.Neq ->
          Evaluator.simplify @@ Formula.or_of
          @@ (Formula.mk_atom @@ T_dt.mk_is_not_cons dt cons_name t2)
             :: List.map2_exn sels ts ~f:(fun sel t ->
                 Evaluator.simplify
                 @@ Formula.neq (T_dt.mk_sel dt (Datatype.name_of_sel sel) t2) t)
      | _ -> assert false)

and normalize_term ?(drop_coeff = false) ?(canon_sign = false) = function
  | LetTerm (var, sort, def, body, info) ->
      Term.mk_let_term ~info var sort (normalize_term def) (normalize_term body)
  | FunApp (T_bool.Formula phi, [], info) ->
      Term.mk_fsym_app ~info (T_bool.Formula (normalize phi)) []
  | term -> (
      match Term.sort_of term with
      | T_int.SInt -> (
          int_monomials_of (Value.Int Z.one) term
          |> PolyTerm.int_simplify
          |> (if drop_coeff then PolyTerm.div_by_gcd else Fn.id)
          |> (if canon_sign then PolyTerm.canon_sign else Fn.id)
          |> Map.Poly.to_alist
          |> List.map ~f:(fun (m, c) ->
              if Map.Poly.is_empty m then Term.of_value (get_dtenv ()) c
              else if Stdlib.(c = Value.Int Z.one) then PolyTerm.int_prod m
              else
                T_int.mk_mul
                  (Term.of_value (get_dtenv ()) c)
                  (PolyTerm.int_prod m))
          |> function
          | [] -> T_int.zero ()
          | [ t ] -> t
          | t :: ts -> T_int.mk_sum t ts)
      | T_real.SReal -> (
          real_monomials_of (Value.Real Q.one) term
          |> PolyTerm.real_simplify
          |> (if false (*drop_coeff*) then PolyTerm.div_by_gcd else Fn.id)
          |> (if canon_sign then PolyTerm.canon_sign else Fn.id)
          |> Map.Poly.to_alist
          |> List.map ~f:(fun (m, c) ->
              if Map.Poly.is_empty m then Term.of_value (get_dtenv ()) c
              else if Stdlib.(c = Value.Real Q.one) then PolyTerm.real_prod m
              else
                T_real.mk_rmul
                  (Term.of_value (get_dtenv ()) c)
                  (PolyTerm.real_prod m))
          |> function
          | [] -> T_real.rzero ()
          | [ t ] -> t
          | t :: ts -> T_real.mk_rsum t ts)
      | _ -> (* normalize non-numeric terms *) Evaluator.simplify_term term)

and normalize_psym psym terms =
  match (psym, terms) with
  | T_bool.Neq, [ t1; t2 ]
    when Term.(is_bool_sort @@ sort_of t1)
         && Fn.non Term.is_var t2
         && not
              (T_dt.is_sel t2 || T_tuple.is_tuple_sel t2 || Term.is_fvar_app t2)
    ->
      normalize_psym T_bool.Eq
        [ normalize_term t1; normalize_term (T_bool.negate t2) ]
  | T_bool.Neq, [ t1; t2 ]
    when Term.(is_bool_sort @@ sort_of t1)
         && Fn.non Term.is_var t1
         && not
              (T_dt.is_sel t1 || T_tuple.is_tuple_sel t1 || Term.is_fvar_app t1)
    ->
      normalize_psym T_bool.Eq
        [ normalize_term (T_bool.negate t1); normalize_term t2 ]
  | T_bool.(Eq | Neq), [ t1; t2 ] ->
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
                (* Any total order orients the equation; comparing the terms directly
                   rather than their printed forms avoids building two strings on every
                   equality.  A bit-vector circuit prints to megabytes, and doing it here
                   exhausted memory inside normalization. *)
                if Stdlib.compare t1 t2 <= 0 then [ t1; t2 ] else [ t2; t1 ]) )
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

and normalize_atom atom =
  match Stdlib.Domain.DLS.get normalize_scope with
  | None -> normalize_atom_node atom
  | Some tbls -> (
      match PhysAtm.find_opt tbls.atoms atom with
      | Some a -> a
      | None ->
          let stamp = Ident.fresh_stamp () in
          let a = normalize_atom_node atom in
          if Ident.fresh_stamp () = stamp then PhysAtm.replace tbls.atoms atom a;
          a)

and normalize_atom_node = function
  | Atom.(True _ | False _) as atom -> atom
  | Atom.App (Predicate.Var (pvar, sargs), terms, _)
    when Map.Poly.mem (get_fenv ()) (Ident.pvar_to_tvar pvar) ->
      T_bool.mk_eq
        (Term.mk_fvar_app (Ident.pvar_to_tvar pvar) sargs T_bool.SBool
        @@ List.map ~f:normalize_term terms)
        (T_bool.mk_true ())
  | Atom.App (Predicate.Var (pvar, sorts), terms, _) ->
      Atom.mk_pvar_app pvar sorts @@ List.map terms ~f:normalize_term
  | Atom.App (Predicate.Psym psym, terms, _) ->
      Tuple2.uncurry Atom.mk_psym_app
      @@ normalize_psym psym
      @@ List.map terms ~f:normalize_term
  | Atom.App (Predicate.Fixpoint _, _, _) as atom -> atom

and normalize phi =
  match Stdlib.Domain.DLS.get normalize_scope with
  | None -> normalize_node phi
  | Some tbls -> (
      match PhysFml.find_opt tbls.fmls phi with
      | Some r -> r
      | None ->
          let stamp = Ident.fresh_stamp () in
          let r = normalize_node phi in
          if Ident.fresh_stamp () = stamp then PhysFml.replace tbls.fmls phi r;
          r)

and normalize_node = function
  (* | Atom
         ( Atom.App
             ( Predicate.Psym (T_bool.(Eq | Neq) as op),
               [ Term.Var (Ident.Tvar v, T_bool.SBool, _); t ],
               _ ),
           _ )
       when T_bool.is_true t || T_bool.is_false t ->
         let atom = Atom.mk_pvar_app (Ident.Pvar v) [] [] in
         if
           (Stdlib.(op = T_bool.Eq) && T_bool.is_true t)
           || (Stdlib.(op = T_bool.Neq) && T_bool.is_false t)
         then Formula.mk_atom atom
         else Formula.mk_atom atom |> Formula.mk_neg
     | Atom
         ( Atom.App
             ( Predicate.Psym (T_bool.(Eq | Neq) as op),
               [ t; Term.Var (Ident.Tvar v, T_bool.SBool, _) ],
               _ ),
           _ )
       when T_bool.is_true t || T_bool.is_false t ->
         let atom = Atom.mk_pvar_app (Ident.Pvar v) [] [] in
         if
           (Stdlib.(op = T_bool.Eq) && T_bool.is_true t)
           || (Stdlib.(op = T_bool.Neq) && T_bool.is_false t)
         then Formula.mk_atom atom
         else Formula.mk_atom atom |> Formula.mk_neg
     | Atom (Atom.App (Predicate.Psym (T_bool.(Eq | Neq) as op), [ t1; t2 ], _), _)
       when T_bool.is_sbool t1 ->
         let phi1, phi2 = (Formula.of_bool_term t1, Formula.of_bool_term t2) in
         let nphi1, nphi2 = (Formula.mk_neg phi1, Formula.mk_neg phi2) in
         normalize @@ Formula.or_of
         @@
         if Stdlib.(op = T_bool.Eq) then
           [ Formula.and_of [ phi1; phi2 ]; Formula.and_of [ nphi1; nphi2 ] ]
         else [ Formula.and_of [ phi1; nphi2 ]; Formula.and_of [ nphi1; phi2 ] ]
     | Atom
         ( Atom.App
             ( Predicate.Psym (T_bool.(Eq | Neq) as psym),
               ( [ t1; Term.FunApp (T_dt.DTCons (name, _, dt), ts, _) ]
               | [ Term.FunApp (T_dt.DTCons (name, _, dt), ts, _); t1 ] ),
               _ ),
           _ ) ->
         normalize_datatype_eq psym name dt ts t1 *)
  | Atom (atom, info) -> Formula.mk_atom ~info (normalize_atom atom)
  | UnaryOp (Not, phi, info) -> Formula.mk_unop ~info Not (normalize phi)
  | BinaryOp (op, phi1, phi2, info) ->
      Formula.mk_binop ~info op (normalize phi1) (normalize phi2)
  | Bind (binder, bounds, phi, info) ->
      Formula.mk_bind ~info binder bounds (normalize phi)
  | LetRec (_funcs, _phi, _info) -> assert false
  | LetFormula (var, sort, def, body, info) ->
      Formula.mk_let_formula ~info var sort (normalize_term def)
        (normalize body)

(* assume [term] is alpha-renamed by LogicOld.Term.alpha_rename_let.

   Inside a scope of [LogicOld.with_shared_let_passes] the three functions
   below remember each node's result by physical identity (they draw no
   fresh name and read no state, so a remembered result is the one computed
   again), and a node shared by several formulas or paths is rebuilt once;
   outside one they rebuild every node of every path, as a tree. *)
let rec normalize_let_term t =
  match Stdlib.Domain.DLS.get LogicOld.let_pass_scope with
  | None -> normalize_let_term_node t
  | Some tb ->
      PhysMemo.memo tb.LogicOld.nl_terms t () () (fun () ->
          normalize_let_term_node t)

and normalize_let_term_node = function
  | Term.Var _ as term -> term
  | Term.LetTerm (var, sort, def, body, info) ->
      let def' = normalize_let_term def in
      let body' = normalize_let_term body in
      Term.replace_let_body def'
      @@ Term.mk_let_term ~info var sort (Term.body_of_let def') body'
  | Term.FunApp (T_bool.Formula phi, [], info) ->
      Term.mk_fsym_app ~info (T_bool.Formula (normalize_let_formula phi)) []
  | Term.FunApp ((T_array.ALambda _ as op), [ body ], info) ->
      (* A lifted definition can read the lambda binder. Keep its substitution
         inside that scope rather than hoisting a free copy outside, where
         the definition would read an unbound variable. *)
      Term.mk_fsym_app ~info op [ Term.elim_let (normalize_let_term body) ]
  | Term.FunApp (op, ts, info) ->
      let ts' = List.map ts ~f:normalize_let_term in
      let term = Term.mk_fsym_app op (List.map ts' ~f:Term.body_of_let) ~info in
      List.fold ts' ~init:term ~f:(Fn.flip Term.replace_let_body)

and normalize_let_atom ?(info = LogicOld.Dummy) atom =
  match Stdlib.Domain.DLS.get LogicOld.let_pass_scope with
  | Some tb when phys_equal info LogicOld.Dummy ->
      PhysMemo.memo tb.LogicOld.nl_atoms atom () () (fun () ->
          normalize_let_atom_node ~info atom)
  | _ -> normalize_let_atom_node ~info atom

and normalize_let_atom_node ~info = function
  | Atom.(True _ | False _) as atom -> Formula.mk_atom atom ~info
  | Atom.App (pred, ts, info) ->
      let ts' = List.map ts ~f:normalize_let_term in
      let body =
        Formula.mk_atom
        @@ Atom.mk_app pred (List.map ts' ~f:Term.body_of_let) ~info
      in
      List.fold ts' ~init:body ~f:(Fn.flip Formula.replace_let_term_body)

and normalize_let_formula phi =
  match Stdlib.Domain.DLS.get LogicOld.let_pass_scope with
  | None -> normalize_let_formula_fold phi
  | Some tb -> normalize_let_formula_shared tb.LogicOld.nl_fmls phi

(* [normalize_let_formula_fold]'s fold, one node at a time, each node's
   result remembered: the same cases with the same constructions *)
and normalize_let_formula_shared tbl phi =
  PhysMemo.memo tbl phi () () @@ fun () ->
  let r = normalize_let_formula_shared tbl in
  let bin mk phi1 phi2 =
    let phi2 = r phi2 in
    let phi1 = r phi1 in
    Formula.(
      replace_let_body phi2 @@ replace_let_body phi1
      @@ mk (body_of_let phi1) (body_of_let phi2))
  in
  match phi with
  | Formula.Atom (atom, _) -> normalize_let_atom atom
  | UnaryOp (Not, phi1, _) ->
      let phi1 = r phi1 in
      Formula.(replace_let_body phi1 @@ mk_neg @@ body_of_let phi1)
  | BinaryOp (And, phi1, phi2, _) -> bin Formula.mk_and phi1 phi2
  | BinaryOp (Or, phi1, phi2, _) -> bin Formula.mk_or phi1 phi2
  | BinaryOp (Imply, phi1, phi2, _) -> bin Formula.mk_imply phi1 phi2
  | BinaryOp (Iff, phi1, phi2, _) -> bin Formula.mk_iff phi1 phi2
  | BinaryOp (Xor, phi1, phi2, _) -> bin Formula.mk_xor phi1 phi2
  | Bind (binder, bounds, phi1, _) -> Formula.mk_bind binder bounds (r phi1)
  | LetRec _ -> normalize_let_formula_fold phi
  | LetFormula (x, s, def, body, _) ->
      let body = r body in
      let def = normalize_let_term def in
      Formula.(
        replace_let_term_body def
        @@ mk_let_formula x s (Term.body_of_let def) body)

and normalize_let_formula_fold phi =
  Formula.fold phi
    ~f:
      (object
         method fatom atom = normalize_let_atom atom

         method fnot phi1 =
           Formula.(replace_let_body phi1 @@ mk_neg @@ body_of_let phi1)

         method fand phi1 phi2 =
           Formula.(
             replace_let_body phi2 @@ replace_let_body phi1
             @@ mk_and (body_of_let phi1) (body_of_let phi2))

         method for_ phi1 phi2 =
           Formula.(
             replace_let_body phi2 @@ replace_let_body phi1
             @@ mk_or (body_of_let phi1) (body_of_let phi2))

         method fimply phi1 phi2 =
           Formula.(
             replace_let_body phi2 @@ replace_let_body phi1
             @@ mk_imply (body_of_let phi1) (body_of_let phi2))

         method fiff phi1 phi2 =
           Formula.(
             replace_let_body phi2 @@ replace_let_body phi1
             @@ mk_iff (body_of_let phi1) (body_of_let phi2))

         method fxor phi1 phi2 =
           Formula.(
             replace_let_body phi2 @@ replace_let_body phi1
             @@ mk_xor (body_of_let phi1) (body_of_let phi2))

         method fbind binder bounds phi1 =
           if true then Formula.mk_bind binder bounds phi1
           else
             Formula.(
               replace_let_body phi1 @@ mk_bind binder bounds (body_of_let phi1))

         method fletrec funcs phi1 = Formula.mk_letrec funcs phi1 (*ToDo*)

         method flet x s def body =
           let def = normalize_let_term def in
           Formula.(
             replace_let_term_body def
             @@ mk_let_formula x s (Term.body_of_let def) body)
      end)

(* Fix the sign of every equation in a formula that [normalize] has already put into the
   form (e, 0) over the integers or the reals.  [e = 0] and [-e = 0] are the same constraint,
   as are [e <> 0] and [-e <> 0], so two spellings of one equation become one value.

   WHY THIS IS A SEPARATE FUNCTION AND NOT PART OF [normalize].  Doing it inside the
   normalizer is the obvious place and it is wrong: [normalize] runs on every problem on
   every path, so changing the sign of the equations in a CLAUSE changes what the qualifier
   extractor reads out of that clause, and therefore what the homogenization and the
   parameter-permutation steps downstream of it are handed.  That was measured, and it turned
   a Rust-derived sequence benchmark from an answer in 6-8 s into no answer at 120 s, while a
   120-file constrained-Horn differential showed no verdict disagreement and no answer lost --
   the corpus that broke was not in the corpus that was measured.

   The benefit is entirely in the hypothesis space, so it is taken there: applied to a
   FINISHED qualifier, after extraction, homogenization and permutation have run, the only
   effect available is to merge two qualifiers that denote the same constraint. *)
let canon_eq_signs =
  Formula.map_atom ~f:(fun atom ->
      Formula.mk_atom
      @@
      match atom with
      | Atom.App (Predicate.Psym (T_bool.(Eq | Neq) as psym), [ t1; t2 ], _)
        -> (
          match Term.sort_of t1 with
          | T_int.SInt ->
              Atom.mk_psym_app psym
                [
                  normalize_term ~drop_coeff:true ~canon_sign:true
                  @@ T_int.mk_sub t1 t2;
                  T_int.zero ();
                ]
          | T_real.SReal ->
              Atom.mk_psym_app psym
                [
                  normalize_term ~drop_coeff:true ~canon_sign:true
                  @@ T_real.mk_rsub t1 t2;
                  T_real.rzero ();
                ]
          | _ -> atom)
      | _ -> atom)

let normalize_let ?(rename = false) phi =
  normalize_let_formula @@ if rename then Formula.alpha_rename_let phi else phi

let homogenize_term term =
  match Term.sort_of term with
  | T_int.SInt -> (
      int_monomials_of (Value.Int Z.one) term
      |> PolyTerm.int_simplify |> Map.Poly.to_alist
      |> List.map ~f:(fun (m, c) ->
          if Map.Poly.is_empty m then (*Term.of_value (get_dtenv ())c*)
            T_int.zero ()
          else if Stdlib.(c = Value.Int Z.one) then PolyTerm.int_prod m
          else
            T_int.mk_mul (Term.of_value (get_dtenv ()) c) (PolyTerm.int_prod m))
      |> function
      | [] -> T_int.zero ()
      | [ t ] -> t
      | t :: ts -> T_int.mk_sum t ts)
  | T_real.SReal -> (
      real_monomials_of (Value.Real Q.one) term
      |> PolyTerm.real_simplify |> Map.Poly.to_alist
      |> List.map ~f:(fun (m, c) ->
          if Map.Poly.is_empty m then (*Term.of_value (get_dtenv ())c*)
            T_real.rzero ()
          else if Stdlib.(c = Value.Real Q.one) then PolyTerm.real_prod m
          else
            T_real.mk_rmul
              (Term.of_value (get_dtenv ()) c)
              (PolyTerm.real_prod m))
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

let homogenize =
  Formula.fold
    ~f:
      (object
         method fatom atom = Formula.mk_atom @@ homogenize_atom atom
         method fnot phi1 = Formula.mk_neg phi1
         method fand phi1 phi2 = Formula.mk_and phi1 phi2
         method for_ phi1 phi2 = Formula.mk_or phi1 phi2
         method fimply phi1 phi2 = Formula.mk_imply phi1 phi2
         method fiff phi1 phi2 = Formula.mk_iff phi1 phi2
         method fxor phi1 phi2 = Formula.mk_xor phi1 phi2
         method fbind binder bounds phi1 = Formula.mk_bind binder bounds phi1
         method fletrec funcs phi1 = Formula.mk_letrec funcs phi1

         method flet x s def body =
           Formula.mk_let_formula x s (homogenize_term def) body
      end)

let linear_int_monomials_of coeff term =
  try
    AffineTerm.to_affine @@ PolyTerm.int_simplify @@ int_monomials_of coeff term
  with exn_ when not (Common.Timer.is_async exn_) ->
    failwith
    @@ sprintf "[linear_int_monomials_of] %s not supported" (Term.str_of term)

let linear_real_monomials_of coeff term =
  try
    AffineTerm.to_affine @@ PolyTerm.real_simplify
    @@ real_monomials_of coeff term
  with exn_ when not (Common.Timer.is_async exn_) ->
    failwith
    @@ sprintf "[linear_real_monomials_of] %s not supported" (Term.str_of term)
