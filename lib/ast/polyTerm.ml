open Core
open Common.Ext
open Common.Combinator
open LogicOld

let int_add_update m t c =
  Map.Poly.update m t ~f:(function None -> c | Some c' -> Value.add c c')
  let real_add_update m t c =
    Map.Poly.update m t ~f:(function None -> c | Some c' -> Value.radd c c')
  
let int_add_monomials m1 m2 =
  Map.Poly.fold m1 ~init:m2 ~f:(fun ~key ~data m -> int_add_update m key data)
  let real_add_monomials m1 m2 =
    Map.Poly.fold m1 ~init:m2 ~f:(fun ~key ~data m -> real_add_update m key data)
  
let mul_update m t c =
  Map.Poly.update m t ~f:(function None -> c | Some c' -> c + c')

let mul_monomials (m1 : (Term.t, int) Map.Poly.t)
    (m2 : (Term.t, int) Map.Poly.t) =
  Map.Poly.fold m1 ~init:m2 ~f:(fun ~key ~data m -> mul_update m key data)

let int_simplify = Map.Poly.filter ~f:(fun c -> Stdlib.(c <> Value.Int Z.zero))

let real_simplify =
  Map.Poly.filter ~f:(fun c -> Stdlib.(c <> Value.Real Q.zero))

let int_prod =
  Map.Poly.to_alist
  >> List.concat_map ~f:(fun (t, n) -> List.init n ~f:(fun _ -> t))
  >> function
  | [] -> failwith "int_prod"
  | [ t ] -> t
  | t :: ts -> T_int.mk_prod t ts

let real_prod =
  Map.Poly.to_alist
  >> List.concat_map ~f:(fun (t, n) -> List.init n ~f:(fun _ -> t))
  >> function
  | [] -> failwith "real_prod"
  | [ t ] -> t
  | t :: ts -> T_real.mk_rprod t ts

let div_by_gcd m =
  match Map.Poly.data m with
  | c :: cs ->
      let lcm_ =
        List.fold cs
          ~init:(Z.abs @@ Value.int_of c)
          ~f:(fun c1 c2 -> Z.gcd c1 (Z.abs @@ Value.int_of c2))
      in
      Map.Poly.map m ~f:(fun c -> Value.Int Z.(ediv (Value.int_of c) lcm_))
  | _ -> m
