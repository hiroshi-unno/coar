open Core
open Common
open Util
open LogicOld

module NonLinear = struct
  let add_update m t c =
    Map.Poly.update m t ~f:(function | None -> c | Some c' -> Value.add c c')
  let add_monomials m1 m2 = Map.Poly.fold m1 ~init:m2 ~f:(fun ~key ~data m -> add_update m key data)
  let mult_update m t c =
    Map.Poly.update m t ~f:(function | None -> c | Some c' -> c + c')
  let mult_monomials (m1 : (Term.t, int) Map.Poly.t) (m2 : (Term.t, int) Map.Poly.t) =
    Map.Poly.fold m1 ~init:m2 ~f:(fun ~key ~data m -> mult_update m key data)

  let int_simplify = Map.Poly.filter ~f:(fun c -> Stdlib.(<>) c (Value.Int Z.zero))
  let real_simplify = Map.Poly.filter ~f:(fun c -> Stdlib.(<>) c (Value.Real Q.zero))

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

  let str_of monomials =
    let l = Map.Poly.to_alist monomials in
    List.to_string l ~f:(fun (t, v) ->
      match t with
      | Some term -> (Term.str_of term) ^ "*" ^ (Value.str_of v)
      | None -> Value.str_of v)

end