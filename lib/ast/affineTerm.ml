open Core
open Common.Ext
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
            Value.compare Z.Compare.( >= ) Q.( >= ) (Term.value_of cterm)
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
  >> List.to_string ~f:(fun (t, v) ->
         match t with
         | Some term -> Term.str_of term ^ "*" ^ Value.str_of v
         | None -> Value.str_of v)

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
        | Term.FunApp (T_int.Neg, [ Term.Var (v', _, _) ], _)
          when Stdlib.(v = v') ->
            ret := Some (-1)
        | Term.FunApp (T_int.Mul, [ t; Term.Var (v', _, _) ], _)
          when Stdlib.(v = v') -> (
            try
              ret :=
                Some (Z.to_int (*ToDo*) @@ Value.int_of @@ Evaluator.eval_term t)
            with _ -> ())
        | _ -> ());
  !ret

let extract_term_from_affine v simplify affine =
  let ret =
    Term.map_term true affine ~f:(function
      | Term.Var (x, _, _) when Stdlib.(v = x) -> T_int.zero ()
      | t -> t)
  in
  if false then
    print_endline @@ sprintf "affine after elim var: %s" @@ Term.str_of ret;
  match coeff_of v affine with
  | None ->
      (* [v] does not occur in [affine] *)
      Some (simplify @@ T_int.mk_neg ret)
  | Some 1 -> Some (simplify @@ T_int.mk_neg ret)
  | Some -1 -> Some (simplify ret)
  | Some _ -> None

let extract_affine_term_from v simplify_term simplify_formula phi =
  match simplify_formula phi with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; _ ], _), _)
    when T_int.is_sint t1 && is_affine t1 -> (
      try extract_term_from_affine v simplify_term t1 with _ -> None)
  | _ -> None
