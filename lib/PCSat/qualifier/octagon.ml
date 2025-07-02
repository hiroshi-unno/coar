open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

let make seeds =
  Set.union
    (Set.concat_map seeds ~f:(fun (l, _, r) ->
         Set.Poly.of_list [ (l, r); (T_int.mk_neg l, T_int.mk_neg r) ]))
    (Set.fold_distinct_pairs seeds ~init:Set.Poly.empty
       ~f:(fun acc (l1, _, r1) (l2, _, r2) ->
         Set.union acc
         @@ Set.Poly.of_list
              [
                (T_int.mk_add l1 l2, T_int.mk_add r1 r2);
                ( T_int.mk_add (T_int.mk_neg l1) l2,
                  T_int.mk_add (T_int.mk_neg r1) r2 );
                ( T_int.mk_add l1 (T_int.mk_neg l2),
                  T_int.mk_add r1 (T_int.mk_neg r2) );
                ( T_int.mk_add (T_int.mk_neg l1) (T_int.mk_neg l2),
                  T_int.mk_add (T_int.mk_neg r1) (T_int.mk_neg r2) );
              ]))
  |> Set.Poly.filter_map ~f:(fun (left, right) ->
         let qual =
           Normalizer.normalize
           @@ Formula.geq left
                (Term.of_value (get_dtenv ()) @@ Evaluator.eval_term right)
         in
         if Set.is_empty @@ Formula.fvs_of qual then None else Some qual)

let octagon_half_spaces_of sorts examples =
  let params = LogicOld.sort_env_list_of_sorts sorts in
  ( params,
    Set.union
      (Set.Poly.of_list params
      |> Set.Poly.filter_map ~f:(function
           | x, T_bool.SBool -> Some (Term.mk_var x T_bool.SBool)
           | _, T_int.SInt -> None
           | _, T_real.SReal -> failwith "real"
           | _, s -> failwith ("not supported" ^ Term.str_of_sort s))
      |> Set.Poly.map ~f:(fun x -> Formula.eq x (T_bool.mk_true ())))
      (Set.concat_map examples ~f:(fun terms ->
           List.map2_exn params terms ~f:(fun (x, s) t ->
               (Term.mk_var x s, s, t))
           |> List.filter ~f:(Triple.snd >> Fn.non Term.is_bool_sort)
           |> Set.Poly.of_list |> make)) )

let qualifiers_of _pvar sorts labeled_atoms _examples =
  let params, quals =
    octagon_half_spaces_of sorts
    @@ Set.Poly.filter_map labeled_atoms
         ~f:(fst >> ExAtom.instantiate >> ExAtom.args_of)
  in
  Set.Poly.map quals ~f:(fun qual -> (params, qual))

let str_of_domain = "Octagon"
