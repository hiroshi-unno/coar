open Core
open Common.Ext
open LogicOld

module NonLinear = struct
  let add_update m t c =
    Map.Poly.update m t ~f:(function None -> c | Some c' -> Value.add c c')

  let add_monomials m1 m2 =
    Map.Poly.fold m1 ~init:m2 ~f:(fun ~key ~data m -> add_update m key data)

  let mult_update m t c =
    Map.Poly.update m t ~f:(function None -> c | Some c' -> c + c')

  let mult_monomials (m1 : (Term.t, int) Map.Poly.t)
      (m2 : (Term.t, int) Map.Poly.t) =
    Map.Poly.fold m1 ~init:m2 ~f:(fun ~key ~data m -> mult_update m key data)

  let int_simplify =
    Map.Poly.filter ~f:(fun c -> Stdlib.(c <> Value.Int Z.zero))

  let real_simplify =
    Map.Poly.filter ~f:(fun c -> Stdlib.(c <> Value.Real Q.zero))

  let int_prod m =
    Map.Poly.to_alist m
    |> List.concat_map ~f:(fun (t, n) -> List.init n ~f:(fun _ -> t))
    |> function
    | [] -> failwith "int_prod"
    | [ t ] -> t
    | t :: ts -> T_int.mk_prod t ts

  let real_prod m =
    Map.Poly.to_alist m
    |> List.concat_map ~f:(fun (t, n) -> List.init n ~f:(fun _ -> t))
    |> function
    | [] -> failwith "real_prod"
    | [ t ] -> t
    | t :: ts -> T_real.mk_rprod t ts

  let div_by_gcd m =
    match Map.Poly.data m with
    | c :: cs ->
        let lcm_ =
          List.fold
            ~init:(Z.abs @@ Value.int_of c)
            cs
            ~f:(fun c1 c2 -> Z.gcd c1 (Z.abs @@ Value.int_of c2))
        in
        Map.Poly.map m ~f:(fun c -> Value.Int Z.(ediv (Value.int_of c) lcm_))
    | _ -> m
end

module Linear = struct
  let find_var_monomial varterm monomials =
    match Map.Poly.find monomials (Some varterm) with
    | Some c -> Some (c, Map.Poly.remove monomials (Some varterm))
    | None -> None

  let int_mult monomials n =
    let n = Value.int_of n in
    Map.Poly.map monomials ~f:(fun c -> Value.Int Z.(Value.int_of c * n))

  let real_mult monomials r =
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
            | Some t -> (T_int.mk_mult t @@ Term.of_value c) :: l
            | None -> Term.of_value c :: l)
      in
      if List.length l = 1 then List.hd_exn l
      else T_int.mk_sum (List.hd_exn l) (List.tl_exn l)

  let mk_real_term monomials =
    if Map.is_empty monomials then T_real.rzero ()
    else
      let l =
        Map.Poly.fold monomials ~init:[] ~f:(fun ~key:term ~data:c l ->
            match term with
            | Some t -> (T_real.mk_rmult t @@ Term.of_value c) :: l
            | None -> Term.of_value c :: l)
      in
      if List.length l = 1 then List.hd_exn l
      else T_real.mk_rsum (List.hd_exn l) (List.tl_exn l)

  let to_linear nonlinear =
    Map.change_keys nonlinear ~f:(fun m ->
        if Map.Poly.is_empty m then None
        else if Map.Poly.length m = 1 then
          let t, c = Map.Poly.min_elt_exn m in
          if c = 1 then Some t else failwith "non-linear"
        else failwith "non-linear")

  let int_to_real monomials =
    Map.Poly.fold monomials ~init:Map.Poly.empty
      ~f:(fun ~key:op ~data:value map ->
        let value = Value.Real (Q.of_bigint @@ Value.int_of value) in
        match op with
        | Some (Term.Var (tvar, T_int.SInt, _)) ->
            Map.Poly.add_exn map
              ~key:(Some (Term.mk_var tvar T_real.SReal))
              ~data:value
        | None -> Map.Poly.add_exn map ~key:None ~data:value
        | _ -> assert false)

  let real_to_int monomials =
    let lcm =
      Q.of_bigint
      @@ Map.Poly.fold monomials ~init:Z.one ~f:(fun ~key:_ ~data:value n ->
             Z.lcm n @@ Q.den @@ Value.real_of value)
    in
    Map.Poly.fold (real_mult monomials (Value.Real lcm)) ~init:Map.Poly.empty
      ~f:(fun ~key:op ~data:value map ->
        let value = Value.Int (Q.to_bigint @@ Value.real_of value) in
        match op with
        | Some (Term.Var (tvar, T_real.SReal, _)) ->
            Map.Poly.add_exn map
              ~key:(Some (Term.mk_var tvar T_int.SInt))
              ~data:value
        | None -> Map.Poly.add_exn map ~key:None ~data:value
        | _ -> assert false)

  (* subst_eqterm is substitution of int term.
     atom is already normalized.
     example for cx = t, ax + u = 0 -> at + cu = 0 *)
  let subst_eqterm cterm eqterm tvar atom monomials_of =
    let open T_int in
    match atom with
    | Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as sym), [ t; t0 ], _)
      -> (
        match
          find_var_monomial (Term.mk_var tvar SInt)
          @@ monomials_of (Value.Int Z.one) t
        with
        | Some (a, rest) ->
            let term =
              mk_add
                (mk_mult (Term.of_value a) eqterm)
                (mk_mult cterm (mk_int_term rest))
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
                (mk_mult (Term.of_value a) eqterm)
                (mk_mult cterm (mk_int_term rest))
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
                (mk_mult (Term.of_value a) eqterm)
                (mk_mult cterm (mk_int_term rest))
            in
            Atom.mk_psym_app sym [ mk_mult cterm d; term ]
        | None -> atom)
    | _ -> atom

  let str_of monomials =
    List.to_string (Map.Poly.to_alist monomials) ~f:(fun (t, v) ->
        match t with
        | Some term -> Term.str_of term ^ "*" ^ Value.str_of v
        | None -> Value.str_of v)
end
