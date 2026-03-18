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
          if
            Value.compare true Z.Compare.( >= ) Q.( >= ) (Term.value_of cterm)
              (Value.Int Z.zero)
          then mk_geq term t0
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
            try ret := Some (Evaluator.eval_term t) with _ -> ())
        | _ -> ());
  !ret

let extract_term (vret, sret) simplify_term affine =
  try
    let ret =
      Term.map_term true affine ~f:(function
        | Term.Var (x, _, _) when Ident.tvar_equal vret x -> T_irb.zero_of sret
        | t -> t)
    in
    if false then print_endline @@ sprintf "ret: %s" @@ Term.str_of ret;
    match coeff_of vret affine with
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
  with _ -> Set.Poly.empty

let extract_terms_from_formula (vret, sret) simplify_term simplify_formula phi =
  match simplify_formula phi with
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
    when T_irb.is_sirb t1 ->
      extract_term (vret, sret) simplify_term (T_irb.sub_of sret t1 t2)
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _)
    when T_irb.is_sirb t1 ->
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
    when T_irb.is_sirb t1 ->
      let t = T_irb.sub_of sret t1 t2 in
      extract_term (vret, sret) simplify_term
        (simplify_term @@ T_irb.add_of sret t (T_irb.one_of sret))
  | Formula.Atom
      ( Atom.App
          (Predicate.Psym (T_int.Gt | T_real.RGt | T_bv.BVGt _), [ t1; t2 ], _),
        _ )
    when T_irb.is_sirb t1 ->
      let t = T_irb.sub_of sret t1 t2 in
      extract_term (vret, sret) simplify_term
        (simplify_term @@ T_irb.sub_of sret t (T_irb.one_of sret))
  | _ -> Set.Poly.empty
