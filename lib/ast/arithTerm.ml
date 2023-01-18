open Core
open Common.Ext
open LogicOld

module NonLinear = struct
  let add_update m t c =
    Map.Poly.update m t ~f:(function None -> c | Some c' -> Value.add c c')
  let add_monomials m1 m2 = Map.Poly.fold m1 ~init:m2 ~f:(fun ~key ~data m -> add_update m key data)
  let mult_update m t c =
    Map.Poly.update m t ~f:(function None -> c | Some c' -> c + c')
  let mult_monomials (m1 : (Term.t, int) Map.Poly.t) (m2 : (Term.t, int) Map.Poly.t) =
    Map.Poly.fold m1 ~init:m2 ~f:(fun ~key ~data m -> mult_update m key data)

  let int_simplify = Map.Poly.filter ~f:(fun c -> Stdlib.(c <> Value.Int Z.zero))
  let real_simplify = Map.Poly.filter ~f:(fun c -> Stdlib.(c <> Value.Real Q.zero))

  let int_prod m =
    Map.Poly.to_alist m
    |> List.concat_map ~f:(fun (t, n) -> List.init n ~f:(fun _ -> t))
    |> (function [] -> failwith "int_prod" | [t] -> t | t::ts -> T_int.mk_prod t ts)
  let real_prod m =
    Map.Poly.to_alist m
    |> List.concat_map ~f:(fun (t, n) -> List.init n ~f:(fun _ -> t))
    |> (function [] -> failwith "real_prod" | [t] -> t | t::ts -> T_real.mk_rprod t ts)
end

module Linear = struct
  let find_var_monomial varterm monomials =
    match Map.Poly.find monomials (Some varterm) with
    | Some c -> Some (c, Map.Poly.remove monomials (Some varterm))
    | None -> None

  let int_mult monomials n =
    let n = Value.int_of n in
    Map.Poly.map monomials ~f:(fun c ->
                                let c = Value.int_of c in
                                Value.Int Z.(c*n))
  let real_mult monomials r =
    let r = Value.real_of r in
    Map.Poly.map monomials ~f:(fun c ->
                                let c = Value.real_of c in
                                Value.Real Q.(c*r))
  let real_div monomials r =
    let r = Value.real_of r in
    Map.Poly.map monomials ~f:(fun c ->
                                let c = Value.real_of c in
                                Value.Real Q.(c/r))

  let mk_int_term monomials =
    if Map.is_empty monomials then T_int.zero ()
    else let l = Map.Poly.fold monomials ~init:[] ~f:(fun ~key:term ~data:c l ->
      match term with
      | Some t -> (T_int.mk_mult t @@Term.of_value c)::l
      | None -> (Term.of_value c)::l) in
    if (List.length l) = 1 then List.hd_exn l
    else T_int.mk_sum (List.hd_exn l) (List.tl_exn l)
  let mk_real_term monomials =
    if Map.is_empty monomials then T_real.rzero ()
    else let l = Map.Poly.fold monomials ~init:[] ~f:(fun ~key:term ~data:c l ->
      match term with
      | Some t -> (T_real.mk_rmult t @@Term.of_value c)::l
      | None -> (Term.of_value c)::l) in
    if (List.length l) = 1 then List.hd_exn l
    else T_real.mk_rsum (List.hd_exn l) (List.tl_exn l)

  let to_linear nonlinear =
    Map.change_keys nonlinear ~f:(fun m ->
    if Map.Poly.is_empty m then None
    else if Map.Poly.exists m ~f:(fun i -> i <> 1) then failwith "non-linear"
    else let l = Map.Poly.keys m in
    if (List.length l) = 1 then Some (List.hd_exn l) else failwith "non-linear")

  let int_to_real monomials =
    Map.Poly.fold monomials ~init:Map.Poly.empty
      ~f:(fun ~key:op ~data:value map ->
          let value = Value.Real (Q.of_bigint @@Value.int_of value) in
          match op with
          | Some (Term.Var (tvar, T_int.SInt, _)) ->
            let term = Term.mk_var tvar T_real.SReal in
            Map.Poly.add_exn map ~key:(Some term) ~data:value
          | None -> Map.Poly.add_exn map ~key:None ~data:value
          | _ -> assert false)
  let real_to_int monomials =
    let lcm = Map.Poly.fold monomials ~init:Z.one
            ~f:(fun ~key:_ ~data:value n ->
                let den = Q.den @@Value.real_of value in
                Z.lcm n den) in
    let lcm = Value.Real (Q.of_bigint lcm) in
    let monomials = real_mult monomials lcm in
    Map.Poly.fold monomials ~init:Map.Poly.empty
      ~f:(fun ~key:op ~data:value map ->
          let value = Value.Int (Q.to_bigint @@Value.real_of value) in
          match op with
          | Some (Term.Var (tvar, T_real.SReal, _)) ->
            let term = Term.mk_var tvar T_int.SInt in
            Map.Poly.add_exn map ~key:(Some term) ~data:value
          | None -> Map.Poly.add_exn map ~key:None ~data:value
          | _ -> assert false)

  (* subst_eqterm is substitution of int term.
  atom is already normalized.
  example for cx = t, ax + u = 0 -> at + cu = 0 *)
  let subst_eqterm cterm eqterm tvar atom monomials_of =
    let open T_int in
    match atom with
    | Atom.App (Predicate.Psym sym, [t; t0], _)
     when (match sym with | T_bool.Eq | T_bool.Neq -> true | _ -> false) ->
     let monomial = monomials_of (Value.Int Z.one) t in
     let varterm = Term.mk_var tvar SInt in
     (match find_var_monomial varterm monomial with
      | Some (a, rest) ->
        let term = mk_add (mk_mult (Term.of_value a) eqterm) (mk_mult cterm (mk_int_term rest)) in
        Atom.mk_psym_app sym [term; t0]
      | None -> atom)
    | Atom.App (Predicate.Psym T_int.Geq, [t; t0], _) ->
     let monomial = monomials_of (Value.Int Z.one) t in
     let varterm = Term.mk_var tvar SInt in
     (match find_var_monomial varterm monomial with
      | Some (a, rest) ->
        let term = mk_add (mk_mult (Term.of_value a) eqterm) (mk_mult cterm (mk_int_term rest)) in
        if Value.compare Z.Compare.(>=) Q.(>=) (Term.value_of cterm) (Value.Int Z.zero)
        then mk_geq term t0
        else mk_leq term t0
      | None -> atom)
    | Atom.App (Predicate.Psym sym, [d; t], _)
     when (match sym with | PDiv | NPDiv -> true | _ -> false) ->
     let monomial = monomials_of (Value.Int Z.one) t in
     let varterm = Term.mk_var tvar SInt in
     (match find_var_monomial varterm monomial with
      | Some (a, rest) ->
        let term = mk_add (mk_mult (Term.of_value a) eqterm) (mk_mult cterm (mk_int_term rest)) in
        Atom.mk_psym_app sym [(mk_mult cterm d); term]
      | None -> atom)
    | _ -> atom

  let str_of monomials =
    let l = Map.Poly.to_alist monomials in
    List.to_string l ~f:(fun (t, v) ->
      match t with
      | Some term -> (Term.str_of term) ^ "*" ^ (Value.str_of v)
      | None -> Value.str_of v)

end