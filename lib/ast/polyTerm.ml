(* Polynomials as maps from a monomial to its coefficient, and monomials as
   maps from a term to its exponent: the arithmetic behind the normalizer's
   linear and polynomial normal forms.  [int_simplify]/[real_simplify] drop
   zero coefficients, [div_by_gcd] divides an integer polynomial by the gcd
   of its coefficients, and [canon_sign] fixes an overall sign -- which is
   meaning-preserving only for an equation or a disequation, never for an
   inequality.  The maps are [Map.Poly] keyed by terms, so their key order is
   polymorphic comparison of terms. *)
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

(* An equation's sign is free -- [e = 0] and [-e = 0] are the same constraint, and so are
   [e <> 0] and [-e <> 0] -- while an inequality's is not, so this is applied only where the
   caller knows the comparison is an equality or a disequality.

   Its use is deliberately narrow: see the comment on the function that applies it.  Without
   it, two spellings of one equation reach a consumer as two, which is not cosmetic where the
   consumer is a synthesizer's hypothesis space -- one template was offered [-1 + x = 0]
   beside [1 - x = 0] and [x1 - x2 = 0] beside [x2 - x1 = 0], and the search over conjunctions
   of qualifiers is exponential in how many there are.

   The sign is fixed by the first coefficient in the map's own key order.  Any total order
   would do; [min_elt] reads that binding without building the list of every value, and two
   maps that differ only by negation have the same keys in the same order and therefore make
   the same choice. *)
let canon_sign m =
  let is_negative = function
    | Value.Int i -> Z.sign i < 0
    | Value.Real r -> Q.sign r < 0
    | _ -> false
  in
  match Map.Poly.min_elt m with
  | Some (_, c) when is_negative c -> Map.Poly.map m ~f:Value.neg
  | _ -> m

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
