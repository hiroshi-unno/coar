open Core
open Ast
open Ast.LogicOld

let mult = function
  | T_int.SInt -> T_int.mk_mult
  | T_real.SReal -> T_real.mk_rmult
  | sort -> failwith ("not supported: " ^ Term.str_of_sort sort)

let sum = function
  | T_int.SInt -> T_int.mk_sum
  | T_real.SReal -> T_real.mk_rsum
  | sort -> failwith ("not supported: " ^ Term.str_of_sort sort)

let zero = function
  | T_int.SInt -> T_int.zero ()
  | T_real.SReal -> T_real.rzero ()
  | sort -> failwith ("not supported: " ^ Term.str_of_sort sort)

let geq = function
  | T_int.SInt -> T_int.mk_geq
  | T_real.SReal -> T_real.mk_rgeq
  | sort -> failwith ("not supported: " ^ Term.str_of_sort sort)

let eq = function
  | T_int.SInt | T_real.SReal -> T_bool.mk_eq
  | sort -> failwith ("not supported: " ^ Term.str_of_sort sort)

let cast = function
  | T_int.SInt, T_int.SInt | T_real.SReal, T_real.SReal -> Fn.id
  | T_int.SInt, T_real.SReal -> fun t -> T_irb.mk_int_to_real t
  | T_real.SReal, T_int.SInt -> fun t -> T_irb.mk_real_to_int t
  | sort1, sort2 ->
      failwith
        ("not supported: " ^ Term.str_of_sort sort1 ^ ", "
       ^ Term.str_of_sort sort2)

let sum_of sort term ts =
  let coeffs, terms =
    List.unzip
    @@ List.map ts ~f:(fun (t, s) ->
           let coeff = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
           (coeff, cast (s, sort) (mult s (cast (T_int.SInt, s) coeff) t)))
  in
  (coeffs, sum sort term terms)

let ineq_of sort ts =
  let negb = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
  let term = cast (T_int.SInt, sort) negb in
  let coeffs, term' = sum_of sort term ts in
  ((coeffs, negb), geq sort term' (zero sort))

let eq_of sort ts =
  let negb = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
  let term = cast (T_int.SInt, sort) negb in
  let coeffs, term' = sum_of sort term ts in
  ((coeffs, negb), eq sort term' (zero sort))

let sort_of ts =
  let sorts = Set.Poly.of_list @@ List.map ~f:snd ts in
  if Set.mem sorts T_real.SReal then T_real.SReal
  else if Set.mem sorts T_int.SInt then T_int.SInt
  else T_int.SInt (* failwith "no int/real term" *)

let conj_with_bool_of ts =
  let sort = sort_of ts in
  let bool_ts =
    List.filter ts ~f:(function _, T_bool.SBool -> true | _, _ -> false)
  in
  let num_ts =
    List.filter ts ~f:(function
      | _, T_int.SInt | _, T_real.SReal -> true
      | _, _ -> false)
  in
  let rec aux = function
    | [] ->
        let params, templ = ineq_of sort num_ts in
        ([ params ], Formula.mk_atom templ)
    | (t, _) :: ts ->
        let params1, tmpl1 = aux ts in
        let params2, tmpl2 = aux ts in
        ( params1 @ params2,
          Formula.or_of
            [
              Formula.and_of [ Formula.of_bool_term t; tmpl1 ];
              Formula.and_of [ Formula.mk_neg @@ Formula.of_bool_term t; tmpl2 ];
            ] )
  in
  aux bool_ts
