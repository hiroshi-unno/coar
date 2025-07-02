open Core
open Common.Ext
open Common.Util
open Common.Combinator
open LogicOld

(*val eval_term: Term.t -> Value.t*)
let rec eval_term ?(env = Map.Poly.empty) =
  let open Term in
  function
  | Var (tvar, _, _) -> (
      match Map.Poly.find env tvar with
      | Some v -> v
      | None -> failwith @@ Ident.name_of_tvar tvar ^ " is not bound")
  | FunApp (FVar (fvar, _, _), ts, _) as term ->
      if false then print_endline @@ "eval rec fun: " ^ Term.str_of term;
      let params, _, def, _, _ = Map.Poly.find_exn (get_fenv ()) fvar in
      let env =
        Map.update_with env @@ Map.Poly.of_alist_exn
        @@ List.zip_exn (List.map ~f:fst params)
        @@ List.map ts ~f:(eval_term ~env)
      in
      eval_term ~env def
  | FunApp (T_bool.Formula phi, [], _) -> Value.Bool (eval ~env phi)
  | FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], _) -> (
      let t2', t3' = (eval_term ~env t2, eval_term ~env t3) in
      if Stdlib.(t2' = t3') then t2'
      else
        match eval_term ~env t1 with
        | Value.Bool true -> t2'
        | Value.Bool false -> t3'
        | _ ->
            failwith
              "a conditional expression must be evaluated to a boolean value")
  | FunApp (T_int.Int i, [], _) -> Value.Int i
  | FunApp (T_real.Real r, [], _) -> Value.Real r
  | FunApp (T_bv.BVNum (size, i), [], _) -> Value.BV (size, i)
  | FunApp (T_array.AConst (si, _), [ t ], _) ->
      Value.Arr
        (eval_term ~env @@ Term.mk_dummy si, eval_term ~env t, Map.Poly.empty)
  | FunApp (T_array.AStore _, [ t1; t2; t3 ], _) -> (
      match eval_term ~env t1 with
      | Value.Arr (dummy, v, m) ->
          let v2 = eval_term ~env t2 in
          let v3 = eval_term ~env t3 in
          if Value.equal v v3 then Value.Arr (dummy, v, m)
          else Value.Arr (dummy, v, Map.Poly.set m ~key:v2 ~data:v3)
      | _ ->
          failwith @@ "Array store: first term must be an array, but got "
          ^ Term.str_of t1)
  | FunApp (T_tuple.TupleCons sorts, ts, _) ->
      let ts' = List.map ~f:(eval_term ~env) ts in
      if List.length ts' <> List.length sorts then
        failwith "Tuple constructor: number of terms does not match sorts";
      Value.TupleCons ts'
  | FunApp (T_dt.DTCons (name, sorts, dt), ts, _) ->
      let vs = List.map ~f:(eval_term ~env) ts in
      if List.length vs <> List.length sorts then
        failwith "Datatype constructor: number of terms does not match sorts";
      Value.DTCons
        ( name,
          List.map (Datatype.params_of dt) ~f:(Term.mk_dummy >> eval_term ~env),
          vs )
  | FunApp (T_irb.RealToInt, [ FunApp (T_real.Real r, [], _) ], _) ->
      Value.Int (Q.to_bigint r (* ToDo: conforms to the semantics of smtlib? *))
  | FunApp (T_irb.IntToReal, [ FunApp (T_int.Int i, [], _) ], _) ->
      Value.Real (Q.of_bigint i)
  | FunApp ((T_int.Neg | T_real.RNeg), [ t1 ], _) ->
      Value.neg (eval_term ~env t1)
  | FunApp ((T_int.Add | T_real.RAdd), [ t1; t2 ], _) ->
      Value.add (eval_term ~env t1) (eval_term ~env t2)
  | FunApp ((T_int.Sub | T_real.RSub), [ t1; t2 ], _) ->
      Value.sub (eval_term ~env t1) (eval_term ~env t2)
  | FunApp ((T_int.Mul | T_real.RMul), [ t1; t2 ], _) ->
      Value.mul (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_int.Div m, [ t1; t2 ], _) ->
      Value.div m (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_real.RDiv, [ t1; t2 ], _) ->
      Value.rdiv (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_int.Rem m, [ t1; t2 ], _) ->
      Value.rem m (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_int.Nop, [ t1 ], _) -> eval_term ~env t1
  | FunApp ((T_int.Abs | T_real.RAbs), [ t1 ], _) ->
      Value.abs (eval_term ~env t1)
  | FunApp (T_int.Power, [ t1; t2 ], _) ->
      Value.pow (eval_term ~env t1) (eval_term ~env t2)
  | FunApp
      (T_bv.BVNot _ (*ToDo*), [ FunApp (T_bv.BVNum (Some size, i), [], _) ], _)
    ->
      Value.BV (Some size, bvnot size i)
  | FunApp
      ( T_bv.BVAnd _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvand (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVOr _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvor (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVXor _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvxor (T_bv.bits_of size) i1 i2)
  | FunApp (T_bv.BVNeg _ (*ToDo*), [ FunApp (T_bv.BVNum (size1, i1), [], _) ], _)
    ->
      Value.BV (size1, bvneg (T_bv.bits_of size1) i1)
  | FunApp
      ( T_bv.BVAdd _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvadd (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVSub _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvsub (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVMul _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvmul (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVDiv (_ (*ToDo*), Some signed),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV
        (size, (if signed then bvsdiv else bvudiv) (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVSHL _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2
         &&
         try
           let _ = Z.to_int i2 in
           true
         with _ -> false ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvshl (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVLSHR _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2
         &&
         try
           let _ = Z.to_int i2 in
           true
         with _ -> false ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvlshr i1 i2)
  | FunApp
      ( T_bv.BVASHR _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2
         &&
         try
           let _ = Z.to_int i2 in
           true
         with _ -> false ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvashr (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVEXTRACT (_ (*ToDo*), h, l),
        [ FunApp (T_bv.BVNum (size, i), [], _) ],
        _ ) ->
      let bvextract size h l i =
        let size' = h - l + 1 in
        if size' <= 0 then
          failwith
            "getbit_range: the range is not valid (h must be greater than or \
             equal to l)"
        else if size' > size then
          failwith "getbit_range: the range is larger than the bitvector size"
        else
          let mask = Z.(shift_left (of_int 1) size' - one) in
          let i' = Z.(shift_right i l land mask) in
          Value.BV (Some size', i')
      in
      bvextract (T_bv.bits_of size) h l i
  | FunApp
      ( T_bv.BVCONCAT (_ (*ToDo*), _ (*ToDo*)),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ ) ->
      let i = Z.(shift_left i1 (T_bv.bits_of size2) + i2) in
      Value.BV (T_bv.add_size size1 size2, i)
  | LetTerm (var, _, def, body, _) ->
      let subst =
        Map.Poly.singleton var
        @@ Term.of_value (get_dtenv ())
        @@ eval_term ~env def
      in
      eval_term ~env @@ Term.subst subst body
  | _ -> failwith "[eval_term] not supported"

(*val eval_pred: pred_sym -> Term.t list -> bool*)
and eval_pred ?(env = Map.Poly.empty) psym terms =
  match (psym, terms) with
  | T_tuple.IsTuple _, [ Term.FunApp (T_tuple.TupleCons _, _, _) ] -> true
  | T_tuple.NotIsTuple _, [ Term.FunApp (T_tuple.TupleCons _, _, _) ] -> false
  | T_dt.IsCons (n1, _), [ Term.FunApp (T_dt.DTCons (n2, _, _), _, _) ] ->
      String.(n1 = n2)
  | T_dt.NotIsCons (n1, _), [ Term.FunApp (T_dt.DTCons (n2, _, _), _, _) ] ->
      String.(n1 <> n2)
  | _ -> (
      match (psym, List.map ~f:(eval_term ~env) terms) with
      | T_bool.Eq, [ BV (size1, i1); BV (size2, i2) ]
        when T_bv.eq_size size1 size2 ->
          Z.Compare.(i1 = i2)
      | T_bool.Eq, [ t1; t2 ] -> Value.equal t1 t2
      | T_bool.Neq, [ BV (size1, i1); BV (size2, i2) ]
        when T_bv.eq_size size1 size2 ->
          Z.Compare.(i1 <> i2)
      | T_bool.Neq, [ t1; t2 ] ->
          Value.compare Z.Compare.( <> ) Q.( <> ) ~opb:Stdlib.( <> ) t1 t2
      | (T_int.Leq | T_real.RLeq | T_bv.BVLeq (_, Some false)), [ t1; t2 ] ->
          Value.compare Z.Compare.( <= ) Q.( <= ) t1 t2
      | ( T_bv.BVLeq (_ (*Some s*), Some true),
          [ Value.BV (s1, i1); Value.BV (s2, i2) ] )
        when (*s = s1 &&*) T_bv.eq_size s1 s2 -> (
          match
            ( Z.testbit i1 (T_bv.bits_of s1 - 1),
              Z.testbit i2 (T_bv.bits_of s2 - 1) )
          with
          | false, true -> false
          | true, false -> true
          | _ -> Z.Compare.(i1 <= i2))
      | (T_int.Geq | T_real.RGeq | T_bv.BVGeq (_, Some false)), [ t1; t2 ] ->
          Value.compare Z.Compare.( >= ) Q.( >= ) t1 t2
      | ( T_bv.BVGeq (_ (*Some s*), Some true),
          [ Value.BV (s1, i1); Value.BV (s2, i2) ] )
        when (*s = s1 &&*) T_bv.eq_size s1 s2 -> (
          match
            ( Z.testbit i1 (T_bv.bits_of s1 - 1),
              Z.testbit i2 (T_bv.bits_of s2 - 1) )
          with
          | false, true -> true
          | true, false -> false
          | _ -> Z.Compare.(i1 >= i2))
      | (T_int.Lt | T_real.RLt | T_bv.BVLt (_, Some false)), [ t1; t2 ] ->
          Value.compare Z.Compare.( < ) Q.( < ) t1 t2
      | ( T_bv.BVLt (_ (*Some s*), Some true),
          [ Value.BV (s1, i1); Value.BV (s2, i2) ] )
        when (*s = s1 &&*) T_bv.eq_size s1 s2 -> (
          match
            ( Z.testbit i1 (T_bv.bits_of s1 - 1),
              Z.testbit i2 (T_bv.bits_of s2 - 1) )
          with
          | false, true -> false
          | true, false -> true
          | _ -> Z.Compare.(i1 < i2))
      | (T_int.Gt | T_real.RGt | T_bv.BVGt (_, Some false)), [ t1; t2 ] ->
          Value.compare Z.Compare.( > ) Q.( > ) t1 t2
      | ( T_bv.BVGt (_ (*Some s*), Some true),
          [ Value.BV (s1, i1); Value.BV (s2, i2) ] )
        when (*s = s1 &&*) T_bv.eq_size s1 s2 -> (
          match
            ( Z.testbit i1 (T_bv.bits_of s1 - 1),
              Z.testbit i2 (T_bv.bits_of s2 - 1) )
          with
          | false, true -> true
          | true, false -> false
          | _ -> Z.Compare.(i1 > i2))
      | T_int.PDiv, [ t1; t2 ] ->
          Value.compare Z.Compare.( = ) Q.( = )
            (Value.rem Euclidean t2 t1)
            (Value.Int Z.zero)
      | T_int.NotPDiv, [ t1; t2 ] ->
          Value.compare Z.Compare.( <> ) Q.( <> )
            (Value.rem Euclidean t2 t1)
            (Value.Int Z.zero)
      | _ -> failwith "[eval_pred] not supported")

(*val eval_atom: Atom.t -> bool*)
and eval_atom ?(env = Map.Poly.empty) = function
  | Atom.True _ -> true
  | False _ -> false
  | App (Predicate.Psym psym, terms, _) -> eval_pred ~env psym terms
  | App (Predicate.(Var (_, _) | Fixpoint _), _, _) ->
      failwith "Predicate variables and fixpoints applications not supported"

(*val eval: Formula.t -> bool*)
and eval ?(env = Map.Poly.empty) =
  let open Formula in
  function
  | Atom (atom, _) -> eval_atom ~env atom
  | UnaryOp (Not, phi, _) -> Fn.non (eval ~env) phi
  | BinaryOp (And, phi1, phi2, _) -> eval ~env phi1 && eval ~env phi2
  | BinaryOp (Or, phi1, phi2, _) -> eval ~env phi1 || eval ~env phi2
  | BinaryOp (Imply, phi1, phi2, _) -> Fn.non (eval ~env) phi1 || eval ~env phi2
  | BinaryOp (Iff, phi1, phi2, _) -> Stdlib.(eval ~env phi1 = eval ~env phi2)
  | BinaryOp (Xor, phi1, phi2, _) -> Stdlib.(eval ~env phi1 <> eval ~env phi2)
  | LetRec (_, _, _) -> failwith "[eval] LetRec not supported"
  | Bind (_, _, _, _) -> failwith "[eval] Bind not supported"
  | LetFormula (tvar, _, def, body, _) ->
      let env = Map.Poly.set env ~key:tvar ~data:(eval_term ~env def) in
      eval ~env body

and size_threshold = 3
and count_threshold = 1
and prod_threshold = 16

(*val simplify_term: Term.t -> Term.t*)
and simplify_term = function
  | Term.Var (_, sort, _) when Datatype.is_unit_sort sort -> Datatype.mk_unit ()
  | Var (tvar, sort, info) -> Var (tvar, sort, info)
  | FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], info) ->
      let t1' = simplify_term t1 in
      let t2' = simplify_term t2 in
      let t3' = simplify_term t3 in
      if T_bool.is_true t1' then t2'
      else if T_bool.is_false t1' then t3'
      else if Stdlib.(t2' = t3') then t2'
      else if T_bool.is_true t2' && T_bool.is_false t3' then t1'
      else if T_bool.is_false t2' && T_bool.is_true t3' then T_bool.negate t1'
      else FunApp (T_bool.IfThenElse, [ t1'; t2'; t3' ], info)
  | LetTerm (tvar, sort, def, body, info) ->
      let def' = simplify_term def in
      let body' = simplify_term body in
      let size =
        Term.ast_size def'
        (*ToDo*)
      in
      let count = Term.occur_times tvar body' in
      if
        size <= size_threshold || count <= count_threshold
        || size * count <= prod_threshold
      then simplify_term @@ Term.subst (Map.Poly.singleton tvar def') body'
      else LetTerm (tvar, sort, def', body', info)
  | FunApp (fsym, ts, info) -> (
      let ts' = List.map ~f:simplify_term ts in
      try Term.of_value (get_dtenv ()) @@ eval_term @@ FunApp (fsym, ts', info)
      with _ -> (
        match (fsym, ts') with
        | T_bool.Formula phi, [] -> T_bool.of_formula (simplify phi) ~info
        | T_int.Neg, [ t ] -> (
            match t with
            | FunApp (T_int.Int n, [], _) -> FunApp (T_int.Int Z.(-n), [], info)
            | FunApp (T_int.Neg, [ t1 ], _) -> t1
            | FunApp (T_int.Mul, [ Term.FunApp (T_int.Int n, [], _); t1 ], _)
            | FunApp (T_int.Mul, [ t1; Term.FunApp (T_int.Int n, [], _) ], _) ->
                (* n is not 0, 1, -1 *)
                T_int.mk_mul (T_int.mk_int Z.(-n)) t1
            | _ -> FunApp (fsym, [ t ], info))
        | ( T_int.Add,
            [ FunApp (T_int.Neg, [ t1 ], _); FunApp (T_int.Neg, [ t2 ], _) ] )
          ->
            T_int.mk_neg @@ simplify_term (T_int.mk_add t1 t2)
        | T_int.Add, [ FunApp (T_int.Neg, [ t1 ], _); t2 ] ->
            simplify_term (T_int.mk_sub t2 t1)
        | T_int.Add, [ t1; FunApp (T_int.Neg, [ t2 ], _) ] ->
            simplify_term (T_int.mk_sub t1 t2)
        | T_int.Add, [ t1; t2 ] -> (
            if T_int.is_zero t2 then t1
            else if T_int.is_zero t1 then t2
            else
              match (t1, t2) with
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) ->
                  FunApp (T_int.Int Z.(n1 + n2), [], info)
              | _, _ -> FunApp (fsym, [ t1; t2 ], info))
        | ( T_int.Sub,
            [ FunApp (T_int.Neg, [ t1 ], _); FunApp (T_int.Neg, [ t2 ], _) ] )
          ->
            simplify_term (T_int.mk_sub t2 t1)
        | T_int.Sub, [ FunApp (T_int.Neg, [ t1 ], _); t2 ] ->
            T_int.mk_neg @@ simplify_term (T_int.mk_add t1 t2)
        | T_int.Sub, [ t1; FunApp (T_int.Neg, [ t2 ], _) ] ->
            simplify_term (T_int.mk_add t1 t2)
        | T_int.Sub, [ t1; t2 ] -> (
            if T_int.is_zero t2 then t1
            else if T_int.is_zero t1 then T_int.mk_neg t2
            else if Stdlib.(t1 = t2) then T_int.zero ()
            else
              match (t1, t2) with
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) ->
                  FunApp (T_int.Int Z.(n1 - n2), [], info)
              | _, _ -> FunApp (fsym, [ t1; t2 ], info))
        | ( T_int.Mul,
            [ FunApp (T_int.Neg, [ t1 ], _); FunApp (T_int.Neg, [ t2 ], _) ] )
          ->
            simplify_term (T_int.mk_mul t1 t2)
        | T_int.Mul, [ FunApp (T_int.Neg, [ t1 ], _); t2 ]
        | T_int.Mul, [ t1; FunApp (T_int.Neg, [ t2 ], _) ] ->
            T_int.mk_neg @@ simplify_term (T_int.mk_mul t1 t2)
        | T_int.Mul, [ t1; t2 ] -> (
            if T_int.is_zero t1 || T_int.is_zero t2 then T_int.zero ()
            else if T_int.is_unit t1 then t2
            else if T_int.is_unit t2 then t1
            else if T_int.is_minus_one t1 then T_int.mk_neg t2
            else if T_int.is_minus_one t2 then T_int.mk_neg t1
            else
              match (t1, t2) with
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) ->
                  FunApp (T_int.Int Z.(n1 * n2), [], info)
              | _, _ -> FunApp (fsym, [ t1; t2 ], info))
        | T_int.Div m, [ t1; t2 ] -> (
            if T_int.is_zero t1 then T_int.zero ()
            else if T_int.is_unit t2 then t1
            else if T_int.is_minus_one t2 then T_int.mk_neg t1
            else
              match (t1, t2) with
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _)
                when Z.Compare.(n2 <> Z.zero) ->
                  FunApp (T_int.Int (Value.div_of m n1 n2), [], info)
              | _, _ -> FunApp (fsym, [ t1; t2 ], info))
        | T_int.Rem m, [ t1; t2 ] -> (
            if T_int.is_zero t1 then T_int.zero ()
            else if T_int.is_unit t2 then T_int.zero ()
            else if T_int.is_minus_one t2 then T_int.mk_neg t1
            else
              match (t1, t2) with
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _)
                when Z.Compare.(n2 <> Z.zero) ->
                  FunApp (T_int.Int (Value.rem_of m n1 n2), [], info)
              | _, _ -> FunApp (fsym, [ t1; t2 ], info))
        | T_int.Nop, [ t ] -> t
        | T_real.RNeg, [ t ] -> (
            match t with
            | FunApp (T_real.Real r, [], _) ->
                FunApp (T_real.Real Q.(-r), [], info)
            | FunApp (T_real.RNeg, [ t1 ], _) -> t1
            | FunApp (T_real.RMul, [ Term.FunApp (T_real.Real r, [], _); t1 ], _)
            | FunApp (T_real.RMul, [ t1; Term.FunApp (T_real.Real r, [], _) ], _)
              ->
                (* r is not 0, 1, -1 *)
                T_real.mk_rmul (T_real.mk_real Q.(-r)) t1
            | _ -> FunApp (fsym, [ t ], info))
        | ( T_real.RAdd,
            [ FunApp (T_real.RNeg, [ t1 ], _); FunApp (T_real.RNeg, [ t2 ], _) ]
          ) ->
            T_real.mk_rneg @@ simplify_term (T_real.mk_radd t1 t2)
        | T_real.RAdd, [ FunApp (T_real.RNeg, [ t1 ], _); t2 ] ->
            simplify_term (T_real.mk_rsub t2 t1)
        | T_real.RAdd, [ t1; FunApp (T_real.RNeg, [ t2 ], _) ] ->
            simplify_term (T_real.mk_rsub t1 t2)
        | T_real.RAdd, [ t1; t2 ] -> (
            if T_real.is_rzero t2 then t1
            else if T_real.is_rzero t1 then t2
            else
              match (t1, t2) with
              | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                ->
                  FunApp (T_real.Real Q.(r1 + r2), [], info)
              | _, _ -> FunApp (fsym, [ t1; t2 ], info))
        | ( T_real.RSub,
            [ FunApp (T_real.RNeg, [ t1 ], _); FunApp (T_real.RNeg, [ t2 ], _) ]
          ) ->
            simplify_term (T_real.mk_rsub t2 t1)
        | T_real.RSub, [ FunApp (T_real.RNeg, [ t1 ], _); t2 ] ->
            T_real.mk_rneg @@ simplify_term (T_real.mk_radd t1 t2)
        | T_real.RSub, [ t1; FunApp (T_real.RNeg, [ t2 ], _) ] ->
            simplify_term (T_real.mk_radd t1 t2)
        | T_real.RSub, [ t1; t2 ] -> (
            if T_real.is_rzero t2 then t1
            else if T_real.is_rzero t1 then T_real.mk_rneg t2
            else if Stdlib.(t1 = t2) then T_real.rzero ()
            else
              match (t1, t2) with
              | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                ->
                  FunApp (T_real.Real Q.(r1 - r2), [], info)
              | _, _ -> FunApp (fsym, [ t1; t2 ], info))
        | ( T_real.RMul,
            [ FunApp (T_real.RNeg, [ t1 ], _); FunApp (T_real.RNeg, [ t2 ], _) ]
          ) ->
            simplify_term (T_real.mk_rmul t1 t2)
        | T_real.RMul, [ FunApp (T_real.RNeg, [ t1 ], _); t2 ]
        | T_real.RMul, [ t1; FunApp (T_real.RNeg, [ t2 ], _) ] ->
            T_real.mk_rneg @@ simplify_term (T_real.mk_rmul t1 t2)
        | T_real.RMul, [ t1; t2 ] -> (
            if T_real.is_rzero t1 || T_real.is_rzero t2 then T_real.rzero ()
            else if T_real.is_runit t1 then t2
            else if T_real.is_runit t2 then t1
            else if T_real.is_rminus_one t1 then T_real.mk_rneg t2
            else if T_real.is_rminus_one t2 then T_real.mk_rneg t1
            else
              match (t1, t2) with
              | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                ->
                  FunApp (T_real.Real Q.(r1 * r2), [], info)
              | _, _ -> FunApp (fsym, [ t1; t2 ], info))
        | T_real.RDiv, [ t1; t2 ] -> (
            if T_real.is_rzero t1 then T_real.rzero ()
            else if T_real.is_runit t2 then t1
            else if T_int.is_minus_one t2 then T_real.mk_rneg t1
            else
              match (t1, t2) with
              | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                when Q.(r2 <> zero) ->
                  FunApp (T_real.Real Q.(r1 / r2), [], info)
              | _, _ -> FunApp (fsym, [ t1; t2 ], info))
        | T_bv.BVAdd _size, [ t1; t2 ] ->
            if T_bv.is_bvzero t2 then t1
            else if T_bv.is_bvzero t1 then t2
            else FunApp (fsym, [ t1; t2 ], info)
        | T_bv.BVSub size, [ t1; t2 ] ->
            if T_bv.is_bvzero t2 then t1
            else if T_bv.is_bvzero t1 then T_bv.mk_bvneg ~size t2
            else if Stdlib.(t1 = t2) then T_bv.bvzero ~size ()
            else FunApp (fsym, [ t1; t2 ], info)
        | T_bv.BVMul size, [ t1; t2 ] ->
            if T_bv.is_bvzero t1 || T_bv.is_bvzero t2 then T_bv.bvzero ~size ()
            else if T_bv.is_bvunit t1 then t2
            else if T_bv.is_bvunit t2 then t1
            else FunApp (fsym, [ t1; t2 ], info)
        | T_bv.BVDiv (size, _signed), [ t1; t2 ] ->
            if T_bv.is_bvzero t1 then T_bv.bvzero ~size ()
            else if T_bv.is_bvunit t2 then t1
            else FunApp (fsym, [ t1; t2 ], info)
        | T_irb.RealToInt, [ FunApp (T_real.Real r, [], _) ] ->
            T_int.mk_int
              (Q.to_bigint r (* ToDo: conforms to the semantics of smtlib? *))
        | T_irb.IntToReal, [ FunApp (T_int.Int i, [], _) ] ->
            T_real.mk_real (Q.of_bigint i)
        | T_irb.IntToBV size, [ FunApp (T_int.Int i, [], _) ] ->
            T_bv.mk_bvnum ~size i
        | ( T_irb.BVToInt (_size, Some signed),
            [ FunApp (T_bv.BVNum (Some s, i), [], _) ] ) ->
            if s = 0 then T_int.mk_int Z.zero
            else
              T_int.mk_int
                (if signed && Z.testbit i (s - 1) then
                   Z.sub i (Z.shift_left Z.one s)
                 else i)
        | T_sequence.SeqConcat _, [ FunApp (T_sequence.SeqEpsilon, [], _); t ]
        | T_sequence.SeqConcat _, [ t; FunApp (T_sequence.SeqEpsilon, [], _) ]
          ->
            t
        | T_regex.RegComplement, [ FunApp (T_regex.RegEmpty, [], _); _ ] ->
            T_regex.mk_full ()
        | T_regex.RegComplement, [ FunApp (T_regex.RegFull, [], _); _ ] ->
            T_regex.mk_empty ()
        | ( T_regex.RegComplement,
            [ FunApp (T_regex.RegComplement, [ t1 ], _); _ ] ) ->
            t1
        | T_regex.RegComplement, [ FunApp (T_regex.RegUnion, [ t1; t2 ], _); _ ]
          ->
            T_regex.mk_inter
              (simplify_term @@ T_regex.mk_complement t1)
              (simplify_term @@ T_regex.mk_complement t2)
        | T_regex.RegComplement, [ FunApp (T_regex.RegInter, [ t1; t2 ], _); _ ]
          ->
            T_regex.mk_union
              (simplify_term @@ T_regex.mk_complement t1)
              (simplify_term @@ T_regex.mk_complement t2)
        | T_regex.RegUnion, [ t1; FunApp (T_regex.RegComplement, [ t2 ], _) ]
          when Stdlib.(t1 = t2) ->
            T_regex.mk_full ()
        | T_regex.RegUnion, [ FunApp (T_regex.RegComplement, [ t1 ], _); t2 ]
          when Stdlib.(t1 = t2) ->
            T_regex.mk_full ()
        | T_regex.RegUnion, [ FunApp (T_regex.RegEmpty, [], _); t1 ]
        | T_regex.RegUnion, [ t1; FunApp (T_regex.RegEmpty, [], _) ] ->
            t1
        | T_regex.RegUnion, [ FunApp (T_regex.RegFull, [], _); _ ]
        | T_regex.RegUnion, [ _; FunApp (T_regex.RegFull, [], _) ] ->
            T_regex.mk_full ()
        | T_regex.RegInter, [ t1; FunApp (T_regex.RegComplement, [ t2 ], _) ]
          when Stdlib.(t1 = t2) ->
            T_regex.mk_empty ()
        | T_regex.RegInter, [ FunApp (T_regex.RegComplement, [ t1 ], _); t2 ]
          when Stdlib.(t1 = t2) ->
            T_regex.mk_empty ()
        | T_regex.RegInter, [ FunApp (T_regex.RegEmpty, [], _); _ ]
        | T_regex.RegInter, [ _; FunApp (T_regex.RegEmpty, [], _) ] ->
            T_regex.mk_empty ()
        | T_regex.RegInter, [ FunApp (T_regex.RegFull, [], _); t1 ]
        | T_regex.RegInter, [ t1; FunApp (T_regex.RegFull, [], _) ] ->
            t1
        | T_regex.RegConcat, [ FunApp (T_regex.RegEmpty, [], _); _ ]
        | T_regex.RegConcat, [ _; FunApp (T_regex.RegEmpty, [], _) ] ->
            T_regex.mk_empty ()
        | T_regex.RegConcat, [ FunApp (T_regex.RegEpsilon, [], _); t1 ]
        | T_regex.RegConcat, [ t1; FunApp (T_regex.RegEpsilon, [], _) ] ->
            t1
        | ( T_array.AStore _,
            [ (FunApp (T_array.AConst _, [ t1 ], _) as t); _; t2 ] )
          when Stdlib.(t1 = t2) ->
            t
        | ( T_array.AStore _,
            [ FunApp (T_array.AStore (s1, s2), [ t1; t2; _ ], _); t3; t4 ] )
          when Stdlib.(t2 = t3) ->
            T_array.mk_store s1 s2 t1 t3 t4
        | ( T_array.AStore (s1, s2),
            [
              FunApp (T_array.AStore (s3, s4), [ tarr; ti1; te1 ], _); ti2; te2;
            ] )
          when Stdlib.(ti1 > ti2) ->
            T_array.mk_store s3 s4 (T_array.mk_store s1 s2 tarr ti2 te2) ti1 te1
        | T_array.ASelect _, [ arr; ti ] -> (
            match T_array.eval_select arr ti with
            | Some te -> simplify_term te
            | None -> FunApp (fsym, ts', info))
        | T_tuple.TupleSel (_, i), [ t ] -> (
            match T_tuple.eval_select t i with
            | Some te -> simplify_term te
            | None -> FunApp (fsym, ts', info))
        | T_dt.DTSel (sel_name, dt, _), [ t ] -> (
            match T_dt.eval_select sel_name dt t with
            | Some te -> simplify_term te
            | None -> FunApp (fsym, ts', info))
        | T_ref.Deref _, [ t ] -> (
            match T_ref.eval_select t with
            | Some te -> simplify_term te
            | None -> FunApp (fsym, ts', info))
        | fsym, ts -> FunApp (fsym, ts, info)))
(* including T_int.int, T_real.Real *)

(*val simplify_pred: Predicate.t -> Predicate.t*)
and simplify_pred = function
  | Predicate.Var (var, sort) -> Predicate.Var (var, sort)
  | Psym psym -> Psym psym
  | Fixpoint def -> Fixpoint { def with body = simplify def.body }

(*val simplify_pred_neg: Predicate.t -> Predicate.t option*)
and simplify_pred_neg = function
  | Predicate.Var _ -> None
  | Fixpoint def ->
      Option.return
      @@ Predicate.Fixpoint
           {
             def with
             kind = Predicate.flip_fop def.kind;
             body = simplify_neg def.body;
           }
  | Psym psym -> (
      try Option.return @@ Predicate.Psym (Predicate.negate_psym psym)
      with _ -> None)

(*val simplify_atom: Atom.t -> Formula.t*)
and can_simplify = function
  | Term.Var (_, _, _) -> false
  | Term.FunApp (FVar _, _, _) -> false
  | Term.FunApp (T_dt.DTSel _, _, _) -> false
  | Term.FunApp (T_tuple.TupleSel _, _, _) -> false
  | Term.FunApp (T_array.ASelect _, _, _) -> false
  | _ -> true

and simplify_atom = function
  | Atom.True _ -> Formula.mk_true ()
  | False _ -> Formula.mk_false ()
  | App (pred, terms, info) -> (
      match (simplify_pred pred, List.map ~f:simplify_term terms) with
      | Predicate.Psym T_bool.Eq, [ t1; t2 ] when Stdlib.(t1 = t2) ->
          Formula.mk_true ()
      | Predicate.Psym T_bool.Neq, [ t1; t2 ] when Stdlib.(t1 = t2) ->
          Formula.mk_false ()
      | ( Predicate.Psym psym,
          [ t1; FunApp (T_bool.IfThenElse, [ t21; t22; t23 ], _) ] ) ->
          Formula.of_bool_term
          @@ T_bool.mk_if_then_else t21
               (T_bool.of_atom @@ Atom.mk_psym_app psym [ t1; t22 ])
               (T_bool.of_atom @@ Atom.mk_psym_app psym [ t1; t23 ])
      | ( Predicate.Psym psym,
          [ FunApp (T_bool.IfThenElse, [ t21; t22; t23 ], _); t1 ] ) ->
          Formula.of_bool_term
          @@ T_bool.mk_if_then_else t21
               (T_bool.of_atom @@ Atom.mk_psym_app psym [ t22; t1 ])
               (T_bool.of_atom @@ Atom.mk_psym_app psym [ t23; t1 ])
      (*| (Predicate.Psym T_bool.Eq, [t1; t2] | Predicate.Psym T_bool.Neq, [t1; t2])
        when Stdlib.(Term.sort_of t1 <> Term.sort_of t2) ->
        failwith @@ sprintf "inconsistent sorts of %s and %s"
          (Term.str_of_sort @@ Term.sort_of t1) (Term.str_of_sort @@ Term.sort_of t2)*)
      | Predicate.Psym psym, [ t1; t2 ]
        when ((Stdlib.(psym = T_bool.Eq) && T_bool.is_true t1)
             || (Stdlib.(psym = T_bool.Neq) && T_bool.is_false t1))
             && can_simplify t2 ->
          simplify @@ Formula.of_bool_term t2
      | Predicate.Psym psym, [ t1; t2 ]
        when ((Stdlib.(psym = T_bool.Eq) && T_bool.is_false t1)
             || (Stdlib.(psym = T_bool.Neq) && T_bool.is_true t1))
             && can_simplify t2 ->
          simplify_neg @@ Formula.of_bool_term t2
      | Predicate.Psym psym, [ t1; t2 ]
        when ((Stdlib.(psym = T_bool.Eq) && T_bool.is_true t2)
             || (Stdlib.(psym = T_bool.Neq) && T_bool.is_false t2))
             && can_simplify t1 ->
          simplify @@ Formula.of_bool_term t1
      | Predicate.Psym psym, [ t1; t2 ]
        when ((Stdlib.(psym = T_bool.Eq) && T_bool.is_false t2)
             || (Stdlib.(psym = T_bool.Neq) && T_bool.is_true t2))
             && can_simplify t1 ->
          simplify_neg @@ Formula.of_bool_term t1
      | Predicate.Psym T_bool.Eq, [ t1; t2 ]
        when Term.is_bool_sort @@ Term.sort_of t1 ->
          (*ToDo*)
          if Stdlib.(t1 = T_bool.negate t2) then Formula.mk_false ()
          else if
            can_simplify t1 && can_simplify t2
            && not (T_bool.is_atom t1 && T_bool.is_atom t2)
          then
            let p1 = Formula.of_bool_term t1 in
            let p2 = Formula.of_bool_term t2 in
            simplify
            @@ Formula.mk_or ~info (Formula.mk_and p1 p2)
                 (Formula.mk_and (Formula.mk_neg p1) (Formula.mk_neg p2))
          else if
            can_simplify t1 && can_simplify t2
            && not (T_bool.is_atom t1 && T_bool.is_atom t2)
          then
            let p1 = Formula.of_bool_term t1 in
            let p2 = Formula.of_bool_term t2 in
            simplify
            @@ Formula.mk_or ~info (Formula.mk_and p1 p2)
                 (Formula.mk_and (Formula.mk_neg p1) (Formula.mk_neg p2))
          else
            Formula.mk_atom (App (Predicate.Psym T_bool.Eq, [ t1; t2 ], info))
            (*ToDo*)
      | Predicate.Psym T_bool.Neq, [ t1; t2 ]
        when Term.is_bool_sort @@ Term.sort_of t1 ->
          (*ToDo*)
          if Stdlib.(t1 = T_bool.negate t2) then Formula.mk_true ()
          else if
            can_simplify t1 && can_simplify t2
            && not (T_bool.is_atom t1 && T_bool.is_atom t2)
          then
            let p1 = Formula.of_bool_term t1 in
            let p2 = Formula.of_bool_term t2 in
            simplify
            @@ Formula.mk_or ~info
                 (Formula.mk_and (Formula.mk_neg p1) p2)
                 (Formula.mk_and p1 (Formula.mk_neg p2))
          else
            Formula.mk_atom (App (Predicate.Psym T_bool.Neq, [ t1; t2 ], info))
            (*ToDo*)
      | ( Predicate.Psym (T_bool.(Eq | Neq) as psym),
          [
            Term.FunApp (T_int.Neg, [ t1 ], _);
            t2 (*| [ t2; Term.FunApp (T_int.Neg, [ t1 ], _) ]*);
          ] ) ->
          simplify_atom (Atom.mk_psym_app psym [ t1; T_int.mk_neg t2 ])
      | ( Predicate.Psym (T_int.(Lt | Leq) as op),
          [ Term.FunApp (T_int.Abs, [ t1 ], _); t2 ] ) ->
          Formula.mk_and
            (simplify_atom @@ Atom.mk_psym_app op [ T_int.mk_neg t2; t1 ])
            (Formula.mk_atom @@ Atom.mk_psym_app op [ t1; t2 ])
      | ( Predicate.Psym (T_int.(Gt | Geq) as op),
          [ t1; Term.FunApp (T_int.Abs, [ t2 ], _) ] ) ->
          Formula.mk_and
            (Formula.mk_atom @@ Atom.mk_psym_app op [ t1; t2 ])
            (simplify_atom @@ Atom.mk_psym_app op [ t2; T_int.mk_neg t1 ])
      | ( Predicate.Psym (T_bool.(Eq | Neq) as psym),
          [
            Term.FunApp (T_real.RNeg, [ t1 ], _);
            t2 (* | [ t2; Term.FunApp (T_real.RNeg, [ t1 ], _) ] *);
          ] ) ->
          simplify_atom (Atom.mk_psym_app psym [ t1; T_real.mk_rneg t2 ])
      | ( Predicate.Psym (T_real.(RLt | RLeq) as op),
          [ Term.FunApp (T_real.RAbs, [ t1 ], _); t2 ] ) ->
          Formula.mk_and
            (simplify_atom @@ Atom.mk_psym_app op [ T_real.mk_rneg t2; t1 ])
            (Formula.mk_atom @@ Atom.mk_psym_app op [ t1; t2 ])
      | ( Predicate.Psym (T_real.(RGt | RGeq) as op),
          [ t1; Term.FunApp (T_real.RAbs, [ t2 ], _) ] ) ->
          Formula.mk_and
            (Formula.mk_atom @@ Atom.mk_psym_app op [ t1; t2 ])
            (simplify_atom @@ Atom.mk_psym_app op [ t2; T_real.mk_rneg t1 ])
      | ( Predicate.Psym T_bool.Eq,
          [
            Term.FunApp (T_array.AConst _, [ t1 ], _);
            Term.FunApp (T_array.AConst _, [ t2 ], _);
          ] ) ->
          simplify @@ Formula.eq t1 t2
      | ( Predicate.Psym T_bool.Eq,
          ( [
              (Term.FunApp (T_array.AConst _, [ t1 ], _) as t);
              Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
            ]
          | [
              Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
              (Term.FunApp (T_array.AConst _, [ t1 ], _) as t);
            ] ) )
        when T_array.non_stored t21 t22 ->
          simplify @@ Formula.mk_and (Formula.eq t1 t23) (Formula.eq t t21)
      | ( Predicate.Psym T_bool.Eq,
          [
            Term.FunApp (T_array.AStore _, [ t11; t12; t13 ], _);
            Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
          ] )
        when T_array.non_stored t11 t12 && T_array.non_stored t21 t22
             && Stdlib.(t12 = t22) ->
          simplify @@ Formula.mk_and (Formula.eq t11 t21) (Formula.eq t13 t23)
      | ( Predicate.Psym T_bool.Eq,
          [ (Term.FunApp (T_array.AStore _, [ t11; t12; t13 ], _) as t1); t2 ] )
        when T_array.non_stored t11 t12 && T_array.non_stored t2 t12 -> (
          match T_array.eval_select t2 t12 with
          | Some te ->
              simplify @@ Formula.mk_and (Formula.eq t13 te) (Formula.eq t11 t2)
          | None -> Formula.eq t1 t2)
      | ( Predicate.Psym T_bool.Eq,
          [ t1; (Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _) as t2) ] )
        when T_array.non_stored t21 t22 && T_array.non_stored t1 t22 -> (
          match T_array.eval_select t1 t22 with
          | Some te ->
              simplify @@ Formula.mk_and (Formula.eq te t23) (Formula.eq t1 t21)
          | None -> Formula.eq t1 t2)
      | ( Predicate.Psym T_bool.Neq,
          [
            Term.FunApp (T_array.AConst _, [ t1 ], _);
            Term.FunApp (T_array.AConst _, [ t2 ], _);
          ] ) ->
          simplify @@ Formula.neq t1 t2
      | ( Predicate.Psym T_bool.Neq,
          ( [
              (Term.FunApp (T_array.AConst _, [ t1 ], _) as t);
              Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
            ]
          | [
              Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
              (Term.FunApp (T_array.AConst _, [ t1 ], _) as t);
            ] ) )
        when T_array.non_stored t21 t22 ->
          simplify @@ Formula.mk_or (Formula.neq t1 t23) (Formula.neq t t21)
      | ( Predicate.Psym T_bool.Neq,
          [
            Term.FunApp (T_array.AStore _, [ t11; t12; t13 ], _);
            Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
          ] )
        when T_array.non_stored t11 t12 && T_array.non_stored t21 t22
             && Stdlib.(t12 = t22) ->
          simplify @@ Formula.mk_or (Formula.neq t11 t21) (Formula.neq t13 t23)
      | ( Predicate.Psym T_bool.Neq,
          [ (Term.FunApp (T_array.AStore _, [ t11; t12; t13 ], _) as t1); t2 ] )
        when T_array.non_stored t11 t12 && T_array.non_stored t2 t12 -> (
          match T_array.eval_select t2 t12 with
          | Some te ->
              simplify
              @@ Formula.mk_or (Formula.neq t13 te) (Formula.neq t11 t2)
          | None -> Formula.neq t1 t2)
      | ( Predicate.Psym T_bool.Neq,
          [ t1; (Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _) as t2) ] )
        when T_array.non_stored t21 t22 && T_array.non_stored t1 t22 -> (
          match T_array.eval_select t1 t22 with
          | Some te ->
              simplify
              @@ Formula.mk_or (Formula.neq te t23) (Formula.neq t1 t21)
          | None -> Formula.neq t1 t2)
      | ( Predicate.Psym (T_tuple.IsTuple _),
          [ Term.FunApp (T_tuple.TupleCons _, _, _) ] ) ->
          Formula.mk_true ()
      | ( Predicate.Psym (T_tuple.NotIsTuple _),
          [ Term.FunApp (T_tuple.TupleCons _, _, _) ] ) ->
          Formula.mk_false ()
      | ( Predicate.Psym T_bool.Eq,
          [
            Term.FunApp (T_tuple.TupleCons _, ts1, _);
            Term.FunApp (T_tuple.TupleCons _, ts2, _);
          ] ) ->
          simplify @@ Formula.and_of @@ List.map2_exn ts1 ts2 ~f:Formula.eq
      | ( Predicate.Psym T_bool.Eq,
          [ Term.FunApp (T_tuple.TupleCons sorts, ts, _); t ] )
      | ( Predicate.Psym T_bool.Eq,
          [ t; Term.FunApp (T_tuple.TupleCons sorts, ts, _) ] ) ->
          simplify @@ Formula.and_of
          @@ List.mapi ts ~f:(fun i ti ->
                 Formula.eq ti @@ T_tuple.mk_tuple_sel sorts t i)
      | ( Predicate.Psym T_bool.Neq,
          [
            Term.FunApp (T_tuple.TupleCons _, ts1, _);
            Term.FunApp (T_tuple.TupleCons _, ts2, _);
          ] ) ->
          simplify @@ Formula.or_of @@ List.map2_exn ts1 ts2 ~f:Formula.neq
      | ( Predicate.Psym T_bool.Neq,
          [ Term.FunApp (T_tuple.TupleCons sorts, ts, _); t ] )
      | ( Predicate.Psym T_bool.Neq,
          [ t; Term.FunApp (T_tuple.TupleCons sorts, ts, _) ] ) ->
          simplify @@ Formula.or_of
          @@ List.mapi ts ~f:(fun i ti ->
                 Formula.neq ti @@ T_tuple.mk_tuple_sel sorts t i)
      | ( Predicate.Psym (T_dt.IsCons (name, _)),
          [ Term.FunApp (T_dt.DTCons (name1, _, _), _, _) ] ) ->
          Formula.mk_bool @@ String.(name1 = name)
      | Predicate.Psym (T_dt.IsCons (name, dt)), [ t ]
        when Datatype.is_base dt name ->
          Formula.eq t (T_dt.mk_cons dt name [])
      | ( Predicate.Psym (T_dt.NotIsCons (name, _)),
          [ Term.FunApp (T_dt.DTCons (name1, _, _), _, _) ] ) ->
          Formula.mk_bool @@ String.(name1 <> name)
      | Predicate.Psym (T_dt.NotIsCons (name, dt)), [ t ]
        when Datatype.is_base dt name ->
          Formula.neq t (T_dt.mk_cons dt name [])
      | ( Predicate.Psym T_bool.Eq,
          [
            Term.FunApp (T_dt.DTCons (name1, _, _), ts1, _);
            Term.FunApp (T_dt.DTCons (name2, _, _), ts2, _);
          ] ) ->
          if String.(name1 <> name2) then Formula.mk_false ()
          else simplify @@ Formula.and_of @@ List.map2_exn ts1 ts2 ~f:Formula.eq
      | ( Predicate.Psym T_bool.Neq,
          [
            Term.FunApp (T_dt.DTCons (name1, _, _), ts1, _);
            Term.FunApp (T_dt.DTCons (name2, _, _), ts2, _);
          ] ) ->
          if String.(name1 <> name2) then Formula.mk_true ()
          else simplify @@ Formula.or_of @@ List.map2_exn ts1 ts2 ~f:Formula.neq
      | pred', ts' -> (
          try Formula.mk_bool @@ eval_atom (App (pred', ts', info))
          with _ -> Formula.mk_atom (App (pred', ts', info))))

(*val simplify_atom_neg: Atom.t -> Formula.t*)
and simplify_atom_neg = function
  | Atom.True _ -> Formula.mk_false ()
  | False _ -> Formula.mk_true ()
  | App (Predicate.Var (pvar, sorts), args, _info) ->
      Formula.mk_neg @@ Formula.mk_atom
      @@ Atom.mk_pvar_app pvar sorts
      @@ List.map ~f:simplify_term args
  | App (pred, args, info) as atom -> (
      match simplify_pred_neg pred with
      | None -> Formula.mk_neg @@ Formula.mk_atom atom
      | Some neg_pred ->
          simplify_atom @@ Atom.mk_app ~info neg_pred
          @@ List.map ~f:simplify_term args)

and simplify_and_theory (psym1, t11, t12) (psym2, t21, t22) =
  let open Formula in
  (* simplification rules for background theories *)
  if Predicate.is_included_psym psym1 psym2 then
    mk_atom @@ Atom.mk_psym_app psym1 [ t11; t12 ]
  else if Predicate.is_included_psym psym2 psym1 then
    mk_atom @@ Atom.mk_psym_app psym2 [ t21; t22 ]
  else if Predicate.is_included_psym psym1 (Predicate.negate_psym psym2) then
    (* <> =
       = <>
       = <
       = >
       < =
       < >
       < >=
       > =
       > <
       > <=
       <= >
       >= < *)
    mk_false ()
  else
    match (psym1, psym2) with
    | T_bool.Neq, T_int.Leq
    | T_int.Leq, T_bool.Neq
    | T_bool.Neq, T_real.RLeq
    | T_real.RLeq, T_bool.Neq ->
        (* <> <=
           <= <> *)
        simplify @@ lt t11 t12
    | T_bool.Neq, T_int.Geq
    | T_int.Geq, T_bool.Neq
    | T_bool.Neq, T_real.RGeq
    | T_real.RGeq, T_bool.Neq ->
        (* <> >=
           >= <> *)
        simplify @@ gt t11 t12
    | T_int.Leq, T_int.Geq
    | T_int.Geq, T_int.Leq
    | T_real.RLeq, T_real.RGeq
    | T_real.RGeq, T_real.RLeq ->
        (* <= >=
           >= <= *)
        simplify @@ eq t11 t12
    | _ ->
        (*not reachable*)
        mk_binop And
          (Formula.mk_atom @@ Atom.mk_psym_app psym1 [ t11; t12 ])
          (Formula.mk_atom @@ Atom.mk_psym_app psym2 [ t21; t22 ])

and simplify_and phis =
  if Set.exists phis ~f:Formula.is_false then Formula.mk_false ()
  else
    let phis =
      Set.Poly.filter_map phis ~f:(fun phi ->
          if Formula.is_true phi then None
          else
            match phi with
            | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _)
              when Stdlib.(t1 > t2) && Predicate.is_flippable_psym psym ->
                Some
                  (Formula.mk_atom
                  @@ Atom.mk_psym_app (Predicate.flip_psym psym) [ t2; t1 ])
            | _ -> Some phi)
    in
    let phis1, phis =
      List.partition_map (Set.to_list phis) ~f:(function
        | Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) ->
            First (psym, t1, t2)
        | phi -> Second phi)
    in
    let phis2, phis3 =
      List.partition_map phis ~f:(function
        | BinaryOp (Or, Atom (atm1, _), Atom (atm2, _), _) ->
            First (simplify_atom atm1, simplify_atom atm2)
        | phi -> Second phi)
    in
    let phis1' =
      phis1
      |> List.classify (fun (psym1, t11, t12) (psym2, t21, t22) ->
             Stdlib.(t11 = t21 && t12 = t22)
             && Predicate.is_negatable_psym psym1
             && Predicate.is_negatable_psym psym2)
      |> List.concat_map ~f:(function
           | [] -> (*not reachable*) []
           | (psym, t1, t2) :: rest -> (
               match rest with
               | [] -> [ Formula.mk_atom @@ Atom.mk_psym_app psym [ t1; t2 ] ]
               | _ -> List.map rest ~f:(simplify_and_theory (psym, t1, t2))))
    in
    let phis2' =
      phis2
      |> List.classify (fun (atm11, atm12) (atm21, atm22) ->
             Stdlib.(
               (atm11 = atm21 && atm12 = atm22)
               || (atm11 = simplify_neg atm21 && atm12 = simplify_neg atm22)))
      |> List.concat_map ~f:(function
           | [] -> (*not reachable*) []
           | (atm11, atm12) :: rest ->
               if
                 List.exists rest ~f:(fun (atm21, atm22) ->
                     Stdlib.(
                       atm11 = simplify_neg atm21 && atm12 = simplify_neg atm22))
               then
                 (* (a \/ b) /\ (not a \/ not b) iff (a <> b) *)
                 [
                   simplify
                   @@ Formula.neq (T_bool.of_formula atm11)
                        (T_bool.of_formula atm12);
                 ]
               else [ Formula.or_of [ atm11; atm12 ] ])
    in
    Formula.and_of (phis1' @ phis2' @ phis3)

and simplify_or_theory (psym1, t11, t12) (psym2, t21, t22) =
  let open Formula in
  (* simplification rules for background theories *)
  if Predicate.is_included_psym psym1 psym2 then
    mk_atom @@ Atom.mk_psym_app psym2 [ t21; t22 ]
  else if Predicate.is_included_psym psym2 psym1 then
    mk_atom @@ Atom.mk_psym_app psym1 [ t11; t12 ]
  else if Predicate.is_included_psym (Predicate.negate_psym psym1) psym2 then
    (* = <>
       <> =
       <> <=
       <> >=
       < >=
       <= >
       <= >=
       > <=
       >= <
       >= <= *)
    mk_true ()
  else
    match (psym1, psym2) with
    | T_bool.Eq, T_int.Lt
    | T_int.Lt, T_bool.Eq
    | T_bool.Eq, T_real.RLt
    | T_real.RLt, T_bool.Eq ->
        (* = <
           < = *)
        simplify @@ leq t11 t12
    | T_bool.Eq, T_int.Gt
    | T_int.Gt, T_bool.Eq
    | T_bool.Eq, T_real.RGt
    | T_real.RGt, T_bool.Eq ->
        (* = >
           > = *)
        simplify @@ geq t11 t12
    | T_int.Lt, T_int.Gt
    | T_int.Gt, T_int.Lt
    | T_real.RLt, T_real.RGt
    | T_real.RGt, T_real.RLt ->
        (* < >
           > < *)
        simplify @@ neq t11 t12
    | _ ->
        (*not reachable*)
        mk_binop Or
          (mk_atom @@ Atom.mk_psym_app psym1 [ t11; t12 ])
          (mk_atom @@ Atom.mk_psym_app psym2 [ t21; t22 ])

and simplify_or phis =
  if Set.exists phis ~f:Formula.is_true then Formula.mk_true ()
  else
    let phis =
      Set.Poly.filter_map phis ~f:(fun phi ->
          if Formula.is_false phi then None
          else
            match phi with
            | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _)
              when Stdlib.(t1 > t2) && Predicate.is_flippable_psym psym ->
                Some
                  (Formula.mk_atom
                  @@ Atom.mk_psym_app (Predicate.flip_psym psym) [ t2; t1 ])
            | _ -> Some phi)
    in
    let phis1, phis =
      List.partition_map (Set.to_list phis) ~f:(function
        | Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) ->
            First (psym, t1, t2)
        | phi -> Second phi)
    in
    let phis2, phis3 =
      List.partition_map phis ~f:(function
        | BinaryOp (And, Atom (atm1, _), Atom (atm2, _), _) ->
            First (simplify_atom atm1, simplify_atom atm2)
        | phi -> Second phi)
    in
    let phis1' =
      phis1
      |> List.classify (fun (psym1, t11, t12) (psym2, t21, t22) ->
             Stdlib.(t11 = t21 && t12 = t22)
             && Predicate.is_negatable_psym psym1
             && Predicate.is_negatable_psym psym2)
      |> List.concat_map ~f:(function
           | [] -> (*not reachable*) []
           | (psym, t1, t2) :: rest -> (
               match rest with
               | [] -> [ Formula.mk_atom @@ Atom.mk_psym_app psym [ t1; t2 ] ]
               | _ -> List.map rest ~f:(simplify_or_theory (psym, t1, t2))))
    in
    let phis2' =
      phis2
      |> List.classify (fun (atm11, atm12) (atm21, atm22) ->
             Stdlib.(
               (atm11 = atm21 && atm12 = atm22)
               || (atm11 = simplify_neg atm21 && atm12 = simplify_neg atm22)))
      |> List.concat_map ~f:(function
           | [] -> (*not reachable*) []
           | (atm11, atm12) :: rest ->
               if
                 List.exists rest ~f:(fun (atm21, atm22) ->
                     Stdlib.(
                       atm11 = simplify_neg atm21 && atm12 = simplify_neg atm22))
               then
                 (* (a /\ b) \/ (not a /\ not b) iff (a = b) *)
                 [
                   simplify
                   @@ Formula.eq (T_bool.of_formula atm11)
                        (T_bool.of_formula atm12);
                 ]
               else [ Formula.and_of [ atm11; atm12 ] ])
    in
    Formula.or_of (phis1' @ phis2' @ phis3)

(*val simplify: Formula.t -> Formula.t*)
and simplify ?(next = Fn.id) = function
  | Formula.Atom (atom, _) -> next @@ simplify_atom atom
  | UnaryOp (Not, phi, _) -> simplify_neg phi ~next
  | BinaryOp (Imply, phi1, phi2, info) ->
      simplify (BinaryOp (Or, UnaryOp (Not, phi1, Dummy), phi2, info)) ~next
  | BinaryOp (Iff, phi1, phi2, info) ->
      (*simplify (BinaryOp (And, BinaryOp (Imply, phi1, phi2, Dummy), BinaryOp (Imply, phi2, phi1, Dummy), info)) ~next*)
      simplify phi1 ~next:(fun phi1' ->
          simplify phi2 ~next:(fun phi2' ->
              next @@ Formula.mk_iff phi1' phi2' ~info))
  | BinaryOp (Xor, phi1, phi2, info) ->
      simplify phi1 ~next:(fun phi1' ->
          simplify phi2 ~next:(fun phi2' ->
              next @@ Formula.mk_xor phi1' phi2' ~info))
  | BinaryOp (And, phi1, phi2, _info) ->
      simplify phi1 ~next:(fun phi1' ->
          simplify phi2 ~next:(fun phi2' ->
              next
              @@ simplify_and
                   (Set.union
                      (Formula.conjuncts_of phi1')
                      (Formula.conjuncts_of phi2'))))
  | BinaryOp (Or, phi1, phi2, _info) ->
      simplify phi1 ~next:(fun phi1' ->
          simplify phi2 ~next:(fun phi2' ->
              next
              @@ simplify_or
                   (Set.union
                      (Formula.disjuncts_of phi1')
                      (Formula.disjuncts_of phi2'))))
  | Bind (binder, bounds, phi, info) ->
      simplify phi ~next:(function
        | Bind (binder', bounds', phi'', _) as phi' ->
            next
            @@
            if Stdlib.(binder' = binder) then
              Bind (binder, bounds' @ bounds, phi'', info)
            else Bind (binder, bounds, phi', info)
        | phi' -> next @@ Bind (binder, bounds, phi', info))
  | LetRec (funcs, phi, info) ->
      if true then assert false
      else
        simplify phi ~next:(fun phi' ->
            next
            @@ LetRec (Formula.map_funcs ~f:(*ToDo*) simplify funcs, phi', info))
  | LetFormula (var, sort, def, body, info) ->
      let def' = simplify_term def in
      simplify body ~next:(fun body' ->
          let size =
            Term.ast_size def'
            (*ToDo*)
          in
          let count = Formula.occur_times var body' in
          if
            size <= size_threshold || count <= count_threshold
            || size * count <= prod_threshold
          then simplify (Formula.apply_pred (var, body') def') ~next
          else next @@ LetFormula (var, sort, def', body', info))

(*val simplify_neg: Formula.t -> Formula.t*)
and simplify_neg ?(next = Fn.id) = function
  | Formula.Atom (atom, _) -> next @@ simplify_atom_neg atom
  | UnaryOp (Not, phi, _) -> simplify phi ~next
  | BinaryOp (Imply, phi1, phi2, info) ->
      simplify_neg (BinaryOp (Or, UnaryOp (Not, phi1, Dummy), phi2, info)) ~next
  | BinaryOp (Iff, phi1, phi2, info) ->
      (*simplify_neg (BinaryOp (And, BinaryOp (Imply, phi1, phi2, Dummy), BinaryOp (Imply, phi2, phi1, Dummy), info)) ~next*)
      simplify phi1 ~next:(fun phi1' ->
          simplify phi2 ~next:(fun phi2' ->
              next @@ Formula.mk_xor phi1' phi2' ~info))
  | BinaryOp (Xor, phi1, phi2, info) ->
      simplify phi1 ~next:(fun phi1' ->
          simplify phi2 ~next:(fun phi2' ->
              next @@ Formula.mk_iff phi1' phi2' ~info))
  | BinaryOp (And, phi1, phi2, _info) ->
      simplify_neg phi1 ~next:(fun phi1' ->
          simplify_neg phi2 ~next:(fun phi2' ->
              next
              @@ simplify_or
                   (Set.union
                      (Formula.disjuncts_of phi1')
                      (Formula.disjuncts_of phi2'))))
  | BinaryOp (Or, phi1, phi2, _info) ->
      simplify_neg phi1 ~next:(fun phi1' ->
          simplify_neg phi2 ~next:(fun phi2' ->
              next
              @@ simplify_and
                   (Set.union
                      (Formula.conjuncts_of phi1')
                      (Formula.conjuncts_of phi2'))))
  | Bind (binder, bounds, phi, info) ->
      simplify
        (Bind (Formula.flip_quantifier binder, bounds, Formula.mk_neg phi, info))
        ~next
  | LetRec (funcs, phi, info) ->
      if true then assert false (* ToDo: check *)
      else
        let f =
          let pvars = List.map funcs ~f:(fun def -> def.name) in
          fun phi ->
            List.fold
              ~f:(fun phi pvar -> Formula.subst_neg pvar phi)
              ~init:phi pvars
        in
        simplify_neg phi ~next:(fun phi' ->
            next
            @@ LetRec
                 ( List.map funcs ~f:(fun def ->
                       {
                         def with
                         kind = Predicate.flip_fop def.kind;
                         body = simplify_neg @@ f def.body;
                       }),
                   f phi',
                   info ))
  | LetFormula (var, sort, def, body, info) ->
      let def' = simplify_term def in
      simplify_neg body ~next:(fun body' ->
          let size =
            Term.ast_size def'
            (*ToDo*)
          in
          let count = Formula.occur_times var body' in
          if
            size <= size_threshold || count <= count_threshold
            || size * count <= prod_threshold
          then simplify (Formula.apply_pred (var, body') def') ~next
          else next @@ LetFormula (var, sort, def', body', info))

and simplify_keep_imply phi =
  Formula.fold phi
    ~f:
      (object
         method fatom atom = simplify_atom atom

         method fand p1 p2 =
           simplify_and
             (Set.union (Formula.conjuncts_of p1) (Formula.conjuncts_of p2))

         method for_ p1 p2 =
           simplify_or
             (Set.union (Formula.disjuncts_of p1) (Formula.disjuncts_of p2))

         method fnot p1 = simplify_neg_keep_imply p1
         method fbind binder senv p1 = Formula.mk_bind binder senv p1
         method fletrec funcs p1 = Formula.mk_letrec funcs p1
         method fimply p1 p2 = Formula.mk_imply p1 p2
         method fiff p1 p2 = Formula.mk_iff p1 p2
         method fxor p1 p2 = Formula.mk_xor p1 p2

         method flet var sort def body =
           Formula.mk_let_formula var sort def body
      end)

and simplify_neg_keep_imply phi =
  Formula.fold phi
    ~f:
      (object
         method fatom atom = simplify_atom_neg atom

         method fand p1 p2 =
           simplify_or
             (Set.union (Formula.disjuncts_of p1) (Formula.disjuncts_of p2))

         method for_ p1 p2 =
           simplify_and
             (Set.union (Formula.conjuncts_of p1) (Formula.conjuncts_of p2))

         method fnot p1 = simplify_keep_imply p1
         method fbind binder senv p1 = Formula.mk_bind binder senv p1
         method fletrec funcs p1 = Formula.mk_letrec funcs p1
         method fimply p1 p2 = Formula.mk_imply p1 p2
         method fiff p1 p2 = Formula.mk_iff p1 p2
         method fxor p1 p2 = Formula.mk_xor p1 p2

         method flet var sort def body =
           Formula.mk_let_formula var sort def body
      end)

let is_sat is_sat phi =
  try eval phi
  with _ -> (* reachable here if phi may cause division by 0 *) is_sat phi

let valid_check_records = Hashtbl.Poly.create ()
let clean () = Hashtbl.Poly.clear valid_check_records

let rec local_is_valid is_valid = function
  | Formula.Atom (atom, _) as phi -> (
      match is_valid_atom atom with Some ret -> ret | None -> is_valid phi)
  | Formula.UnaryOp (_, phi1, _) as phi -> (
      match simplify_neg phi1 with
      | Formula.UnaryOp (_, _, _) -> is_valid phi
      | phi_neg -> local_is_valid is_valid phi_neg)
  | Formula.BinaryOp (Formula.And, phi1, phi2, _) ->
      local_is_valid is_valid phi1 && local_is_valid is_valid phi2
  | Formula.Bind (Formula.Forall, _, phi, _) -> local_is_valid is_valid phi
  | phi -> is_valid phi

(* cons x y = tl z*)
and is_valid_atom (*ToDo: check if this is correct*) = function
  | Atom.True _ -> Some true
  | Atom.False _ -> Some false
  | Atom.App
      (Predicate.Psym (T_int.(Gt | Lt) | T_real.(RGt | RLt)), [ t1; t2 ], _) ->
      if Stdlib.(t1 = t2) then Some false
      else if Term.is_pathexp t1 then
        if Set.mem (Term.pathexps_of t2) t1 then Some false else None
      else if Term.is_pathexp t2 then
        if Set.mem (Term.pathexps_of t1) t2 then Some false else None
      else None
  | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) ->
      if Stdlib.(t1 = t2) then Some false
      else if Term.is_pathexp t1 then
        if Set.mem (Term.pathexps_of t2) t1 then Some false else None
      else if Term.is_pathexp t2 then
        if Set.mem (Term.pathexps_of t1) t2 then Some false else None
      else None
  | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) ->
      if Stdlib.(t1 = t2) then Some true
      else if Term.is_pathexp t1 then
        if Set.mem (Term.pathexps_of t2) t1 then Some false else None
      else if Term.is_pathexp t2 then
        if Set.mem (Term.pathexps_of t1) t2 then Some false else None
      else None
  | Atom.App (Predicate.Psym (T_dt.IsCons _), [ t1 ], _) ->
      if Term.is_pathexp t1 then Some false else None
  | _ -> None

let is_valid_aux is_valid phi =
  let phi = Formula.nnf_of phi in
  match Hashtbl.Poly.find valid_check_records phi with
  | Some rcd -> rcd
  | None ->
      let ret = is_valid phi in
      Hashtbl.Poly.set valid_check_records ~key:phi ~data:ret;
      ret

let is_valid is_valid phi =
  try eval phi
  with _ ->
    (* reachable here if phi may cause division by 0 *)
    is_valid_aux is_valid phi

(* return
   Some true if cond => phi is valid
   Some false if cond => not phi is valid
   None otherwise *)
let check ?(cond = Formula.mk_true ()) is_valid_fun phi =
  let is_valid phi =
    try eval phi
    with _ ->
      (* reachable here if phi may cause division by 0 *)
      is_valid_aux is_valid_fun phi
  in
  if is_valid @@ simplify @@ Formula.mk_imply cond phi then Some true
  else if is_valid @@ simplify @@ Formula.mk_imply cond @@ Formula.mk_neg phi
  then Some false
  else None
