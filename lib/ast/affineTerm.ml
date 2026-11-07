open Core
open Common.Ext
open Common.Util
open Common.Combinator
open LogicOld

(* ToDo: merge with affine.ml *)

let find_var_monomial varterm monomials =
  match Map.Poly.find monomials (Some varterm) with
  | Some c -> Some (c, Map.Poly.remove monomials (Some varterm))
  | None -> None

let int_mul monomials n =
  let n = Value.int_of n in
  Map.Poly.map monomials ~f:(fun c -> Value.Int Z.(Value.int_of c * n))

let real_mul monomials r =
  let r = Value.real_of r in
  Map.Poly.map monomials ~f:(fun c -> Value.Real Q.(Value.real_of c * r))

let real_div monomials r =
  let r = Value.real_of r in
  Map.Poly.map monomials ~f:(fun c -> Value.Real Q.(Value.real_of c / r))

let mk_int_term monomials =
  if Map.is_empty monomials then T_int.zero ()
  else
    let l =
      Map.Poly.fold monomials ~init:[] ~f:(fun ~key:term ~data:c l ->
          match term with
          | Some t -> (T_int.mk_mul t @@ Term.of_value (get_dtenv ()) c) :: l
          | None -> Term.of_value (get_dtenv ()) c :: l)
    in
    if List.length l = 1 then List.hd_exn l
    else T_int.mk_sum (List.hd_exn l) (List.tl_exn l)

let mk_real_term monomials =
  if Map.is_empty monomials then T_real.rzero ()
  else
    let l =
      Map.Poly.fold monomials ~init:[] ~f:(fun ~key:term ~data:c l ->
          match term with
          | Some t -> (T_real.mk_rmul t @@ Term.of_value (get_dtenv ()) c) :: l
          | None -> Term.of_value (get_dtenv ()) c :: l)
    in
    if List.length l = 1 then List.hd_exn l
    else T_real.mk_rsum (List.hd_exn l) (List.tl_exn l)

let to_affine =
  Map.change_keys ~f:(fun m ->
      if Map.Poly.is_empty m then None
      else if Map.Poly.length m = 1 then
        let t, c = Map.Poly.min_elt_exn m in
        if c = 1 then Some t else failwith "non-linear"
      else failwith "non-linear")

let int_to_real =
  Map.Poly.fold ~init:Map.Poly.empty ~f:(fun ~key ~data map ->
      let data = Value.Real (Q.of_bigint @@ Value.int_of data) in
      let key =
        match key with
        | Some (Term.Var (tvar, T_int.SInt, _)) ->
            Some (Term.mk_var tvar T_real.SReal)
        | None -> None
        | _ -> assert false
      in
      Map.Poly.add_exn map ~key ~data)

let real_to_int monomials =
  let lcm =
    Q.of_bigint
    @@ Map.Poly.fold monomials ~init:Z.one ~f:(fun ~key:_ ~data n ->
        Z.lcm n @@ Q.den @@ Value.real_of data)
  in
  Map.Poly.fold (real_mul monomials (Value.Real lcm)) ~init:Map.Poly.empty
    ~f:(fun ~key ~data map ->
      let data = Value.Int (Q.to_bigint @@ Value.real_of data) in
      let key =
        match key with
        | Some (Term.Var (tvar, T_real.SReal, _)) ->
            Some (Term.mk_var tvar T_int.SInt)
        | None -> None
        | _ -> assert false
      in
      Map.Poly.add_exn map ~key ~data)

(* subst_eqterm is substitution of int term.
   atom is already normalized.
   example for cx = t, ax + u = 0 -> at + cu = 0 *)
let subst_eqterm cterm eqterm tvar atom monomials_of =
  let open T_int in
  match atom with
  | Atom.App (Predicate.Psym (T_bool.(Eq | Neq) as sym), [ t; t0 ], _) -> (
      match
        find_var_monomial (Term.mk_var tvar SInt)
        @@ monomials_of (Value.Int Z.one) t
      with
      | Some (a, rest) ->
          let term =
            mk_add
              (mk_mul (Term.of_value (get_dtenv ()) a) eqterm)
              (mk_mul cterm (mk_int_term rest))
          in
          Atom.mk_psym_app sym [ term; t0 ]
      | None -> atom)
  | Atom.App (Predicate.Psym T_int.Geq, [ t; t0 ], _) -> (
      match
        find_var_monomial (Term.mk_var tvar SInt)
        @@ monomials_of (Value.Int Z.one) t
      with
      | Some (a, rest) ->
          let term =
            mk_add
              (mk_mul (Term.of_value (get_dtenv ()) a) eqterm)
              (mk_mul cterm (mk_int_term rest))
          in
          if Value.geq (Term.value_of cterm) (Value.Int Z.zero) then
            mk_geq term t0
          else mk_leq term t0
      | None -> atom)
  | Atom.App (Predicate.Psym ((PDiv | NotPDiv) as sym), [ d; t ], _) -> (
      match
        find_var_monomial (Term.mk_var tvar SInt)
        @@ monomials_of (Value.Int Z.one) t
      with
      | Some (a, rest) ->
          let term =
            mk_add
              (mk_mul (Term.of_value (get_dtenv ()) a) eqterm)
              (mk_mul cterm (mk_int_term rest))
          in
          Atom.mk_psym_app sym [ mk_mul cterm d; term ]
      | None -> atom)
  | _ -> atom

let str_of =
  Map.Poly.to_alist
  >> List.to_string ~f:(function
    | Some term, v -> sprintf "%s*%s" (Term.str_of term) (Value.str_of v)
    | None, v -> Value.str_of v)

(* ToDo: merge the code below with the code above *)

let is_affine term =
  Set.for_all (Term.funsyms_of term) ~f:(function
    | T_int.(Int _ | Neg | Add | Sub | Mul) -> true (*ToDo*)
    | _ -> false)

(* The coefficient [extract_term] reads by default: that of the first subterm
   a bottom-up traversal meets that is [v], [-v] or [k * v].  [Term.iter_term]
   visits [v] itself before any term containing it, so this is 1 whenever [v]
   occurs, whatever its coefficient, and the [Neg] and [Mul] arms are never
   reached.  Kept as the default because candidate terms
   and so the search depend on it; [exact_coeff_of] is the true
   coefficient. *)
let coeff_of v t =
  let ret = ref None in
  Term.iter_term t ~f:(fun t ->
      if Option.is_none !ret then
        match t with
        | Term.Var (v', T_int.SInt, _) when Stdlib.(v = v') ->
            ret := Some (Value.Int Z.one)
        | Term.Var (v', T_real.SReal, _) when Stdlib.(v = v') ->
            ret := Some (Value.Real Q.one)
        | Term.Var (v', T_bv.SBV size, _) when Stdlib.(v = v') ->
            ret := Some (Value.BV (size, Z.one))
        | Term.FunApp (T_int.Neg, [ Term.Var (v', _, _) ], _)
          when Stdlib.(v = v') ->
            ret := Some (Value.Int Z.minus_one)
        | Term.FunApp (T_real.RNeg, [ Term.Var (v', _, _) ], _)
          when Stdlib.(v = v') ->
            ret := Some (Value.Real Q.minus_one)
        | Term.FunApp (T_bv.BVNeg size, [ Term.Var (v', _, _) ], _)
          when Stdlib.(v = v') ->
            ret := Some (Value.BV (size, Z.minus_one))
        | Term.FunApp
            ( (T_int.Mul | T_real.RMul | T_bv.BVMul _),
              [ t; Term.Var (v', _, _) ],
              _ )
          when Stdlib.(v = v') -> (
            try ret := Some (Evaluator.eval_term t)
            with exn_ when not (Common.Timer.is_async exn_) -> ())
        | _ -> ());
  !ret

(* [exact_coeff_of v sret t] is [Some c] when [t] is affine in [v] -- that is,
   [t] equals [c * v + t'] for a constant [c] and a term [t'] without [v] --
   and [None] when [v] occurs under an operator this does not read through
   (a product of two terms both depending on [v], or of [v] with a non-constant
   factor, a division, a conversion between sorts, an uninterpreted function).
   [c] is zero when [v] does not occur.  Read top-down, so a [v] under a
   negation or a constant factor contributes that factor and the contributions
   of several occurrences add up.  The result is a value of [sret], [v]'s sort;
   a bit-vector coefficient is reduced modulo two to the width. *)
let exact_coeff_of v sret t =
  let num_of = function
    | Value.Int n -> Some (Q.of_bigint n)
    | Value.Real q -> Some q
    | Value.BV (_, n) -> Some (Q.of_bigint n)
    | _ -> None
  in
  let has_v t = Set.mem (Term.tvs_of t) v in
  let const_of t =
    try num_of (Evaluator.eval_term t)
    with exn_ when not (Common.Timer.is_async exn_) -> None
  in
  let rec coeff t =
    if not (has_v t) then Some Q.zero
    else
      match t with
      | Term.Var (v', _, _) when Stdlib.(v = v') -> Some Q.one
      | Term.FunApp (T_int.Nop, [ t1 ], _) -> coeff t1
      | Term.FunApp ((T_int.Neg | T_real.RNeg | T_bv.BVNeg _), [ t1 ], _) ->
          Option.map (coeff t1) ~f:Q.neg
      | Term.FunApp ((T_int.Add | T_real.RAdd | T_bv.BVAdd _), [ t1; t2 ], _) ->
          Option.map2 (coeff t1) (coeff t2) ~f:Q.add
      | Term.FunApp ((T_int.Sub | T_real.RSub | T_bv.BVSub _), [ t1; t2 ], _) ->
          Option.map2 (coeff t1) (coeff t2) ~f:Q.sub
      | Term.FunApp ((T_int.Mul | T_real.RMul | T_bv.BVMul _), [ t1; t2 ], _) ->
          if not (has_v t1) then Option.map2 (const_of t1) (coeff t2) ~f:Q.mul
          else if not (has_v t2) then
            Option.map2 (coeff t1) (const_of t2) ~f:Q.mul
          else None
      | _ -> None
  in
  Option.bind (coeff t) ~f:(fun c ->
      match sret with
      | T_int.SInt ->
          if Z.Compare.(Q.den c = Z.one) then Some (Value.Int (Q.num c))
          else None
      | T_real.SReal -> Some (Value.Real c)
      | T_bv.SBV size ->
          if Z.Compare.(Q.den c = Z.one) then
            Some
              (Value.BV (size, Common.Util.int2bv (T_bv.bits_of size) (Q.num c)))
          else None
      | _ -> None)

(* The solutions for [vret] of [affine = 0], as a set of at most one term over
   the other variables of [affine]: [-t'/c] where [affine] is [c * vret + t'].
   An integer or bit-vector root is offered only for [c] = 1 or -1 (another
   [c] has no root in general).

   [exact_coeff = false] (the default) reads [c] with [coeff_of], which
   reports the first occurrence of [vret] met by a bottom-up traversal; that
   is [vret] itself even inside [-1 * vret] or [2 * vret], so [c] is taken to
   be 1 whatever it is, and the term returned is a root only when the true
   coefficient is 1: from [-1 + y - x = 0] it returns [x := 1 - y].  When
   [vret] does not occur, or occurs under a context [coeff_of] does not read,
   [c] is also taken to be 1.  [exact_coeff = true] reads [c] with
   [exact_coeff_of], so the term returned is always a root, and nothing is
   returned when [vret] does not occur or [affine] is not affine in it. *)
let extract_term ?(exact_coeff = false) (vret, sret) simplify_term affine =
  try
    let ret =
      Term.map_term true affine ~f:(function
        | Term.Var (x, _, _) when Ident.tvar_equal vret x -> T_irb.zero_of sret
        | t -> t)
    in
    if false then print_endline @@ sprintf "ret: %s" @@ Term.str_of ret;
    let coeff =
      if exact_coeff then exact_coeff_of vret sret affine
      else coeff_of vret affine
    in
    match coeff with
    | None when exact_coeff -> Set.Poly.empty
    | None
    (* ToDo: [v] does not occur in [affine] or occurs under unsupported context *)
      ->
        Set.Poly.singleton (simplify_term @@ T_int.mk_neg ret)
    | Some (Value.Int c) when Z.(Compare.(c = one)) ->
        Set.Poly.singleton (simplify_term @@ T_int.mk_neg ret)
    | Some (Value.Int c) when Z.(Compare.(c = minus_one)) ->
        Set.Poly.singleton (simplify_term ret)
    | Some (Value.Real c) when Q.(c <> zero) ->
        Set.Poly.singleton
          (simplify_term @@ T_real.mk_rdiv ret (T_real.mk_real Q.(-c)))
    | Some (Value.BV (size, c)) when Z.(Compare.(c = one)) ->
        Set.Poly.singleton (simplify_term @@ T_bv.mk_bvneg ~size ret)
    | Some (Value.BV (siz, c))
      when Z.(Compare.(c = int2bv (T_bv.bits_of siz) minus_one)) ->
        Set.Poly.singleton (simplify_term ret)
    | Some _ -> Set.Poly.empty
  with exn_ when not (Common.Timer.is_async exn_) -> Set.Poly.empty

(* An atom is solved for [vret] only where it compares values of [vret]'s own
   sort: the difference is built at [sret], so an atom over another sort --
   a bit-vector of another width, where [vret] occurs under an extension --
   would give a term whose operator claims [sret]'s width while its operand
   has the other, and Z3 refuses such a term when a candidate is checked.

   With [exact_coeff], an integer atom [e rem k = 0], [e div k = 0],
   [e div k >= 0] or [e div k <= 0] over a nonzero constant [k] (any rounding
   mode) is solved through its argument: a root [rho] of [e = 0] makes [e]
   zero, and zero's remainder and quotient by [k] are zero, so [rho] satisfies
   the atom.  For the remainder atom, [rho erem |k|] is offered as well when
   [rho] is not a constant: [e] is [c * vret + t'] with [c] = 1 or -1, so a
   value congruent to [rho] modulo [k] makes [e] a multiple of [k], and this
   is the root that lies in [0, |k|).  Without this arm the exact reading
   finds no root of such an atom ([vret] is under [rem] or [div], not affine)
   and the qualifier is handed to quantifier elimination instead, which drops
   it (the elimination of [exists r. (t + r) rem k = 0] is [true]) or keeps a
   disjunction over the [k] residues as a new qualifier; the default reading
   substituted zero for [vret] and offered [-(t' rem k)] or [-(t' div k)], not
   a root in general, which this arm replaces by roots.  Only the shape the
   normaliser produces, the operator on the left and [0] on the right, is
   read. *)
let extract_terms_from_formula ?(exact_coeff = false) (vret, sret) simplify_term
    simplify_formula phi =
  let extract_term = extract_term ~exact_coeff in
  let same_sort t = Stdlib.(Term.sort_of t = sret) in
  let nonzero_int = function
    | Term.FunApp (T_int.Int n, [], _) -> not (Z.equal n Z.zero)
    | _ -> false
  in
  match simplify_formula phi with
  | Formula.Atom
      ( Atom.App
          ( Predicate.Psym ((T_bool.Eq | T_int.(Leq | Geq)) as psym),
            [
              Term.FunApp (((T_int.Rem _ | T_int.Div _) as fsym), [ e; k ], _);
              z;
            ],
            _ ),
        _ )
    when exact_coeff && Term.is_int_sort sret && nonzero_int k
         && T_int.is_zero z
         && Set.mem (Term.tvs_of e) vret ->
      let roots = extract_term (vret, sret) simplify_term e in
      let rem_eq =
        (match psym with T_bool.Eq -> true | _ -> false)
        && match fsym with T_int.Rem _ -> true | _ -> false
      in
      if rem_eq then
        let m = T_int.mk_int (Z.abs (T_int.let_int k)) in
        Set.union roots
          (Set.Poly.filter_map roots ~f:(fun rho ->
               if Set.is_empty (Term.tvs_of rho) then None
               else Some (simplify_term (T_int.mk_rem Value.Euclidean rho m))))
      else roots
  | Formula.Atom
      ( Atom.App
          ( Predicate.Psym
              ( T_bool.Eq
              | T_int.(Leq | Geq)
              | T_real.(RLeq | RGeq)
              | T_bv.(BVLeq _ | BVGeq _) ),
            [ t1; t2 ],
            _ ),
        _ )
    when T_irb.is_sirb t1 && same_sort t1 ->
      extract_term (vret, sret) simplify_term (T_irb.sub_of sret t1 t2)
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _)
    when T_irb.is_sirb t1 && same_sort t1 ->
      let t = T_irb.sub_of sret t1 t2 in
      Set.union
        (extract_term (vret, sret) simplify_term
           (simplify_term @@ T_irb.add_of sret t (T_irb.one_of sret)))
        (extract_term (vret, sret) simplify_term
           (simplify_term @@ T_irb.sub_of sret t (T_irb.one_of sret)))
  | Formula.Atom
      ( Atom.App
          (Predicate.Psym (T_int.Lt | T_real.RLt | T_bv.BVLt _), [ t1; t2 ], _),
        _ )
    when T_irb.is_sirb t1 && same_sort t1 ->
      let t = T_irb.sub_of sret t1 t2 in
      extract_term (vret, sret) simplify_term
        (simplify_term @@ T_irb.add_of sret t (T_irb.one_of sret))
  | Formula.Atom
      ( Atom.App
          (Predicate.Psym (T_int.Gt | T_real.RGt | T_bv.BVGt _), [ t1; t2 ], _),
        _ )
    when T_irb.is_sirb t1 && same_sort t1 ->
      let t = T_irb.sub_of sret t1 t2 in
      extract_term (vret, sret) simplify_term
        (simplify_term @@ T_irb.sub_of sret t (T_irb.one_of sret))
  | _ -> Set.Poly.empty
