open Core
open Common.Ext
open Ast
open Ast.LogicOld
open PCSatCommon

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
           @@ Formula.geq left (Evaluator.eval_term right |> Term.of_value)
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
           |> List.filter ~f:(fun (_, s, _) -> Fn.non Term.is_bool_sort s)
           |> Set.Poly.of_list |> make)) )

let qualifiers_of _pvar sorts labeled_atoms _examples =
  let examples =
    Set.Poly.filter_map labeled_atoms ~f:(fun (atom, _) ->
        match ExAtom.instantiate atom with
        | ExAtom.PApp (_, terms) -> Some terms
        | ExAtom.PPApp (_, (_, terms)) -> Some terms
        | _ -> None)
  in
  let params, quals = octagon_half_spaces_of sorts examples in
  Set.Poly.map ~f:(fun qual -> (params, qual)) quals

let str_of_domain = "Octagon"
