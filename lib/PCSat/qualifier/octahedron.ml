open Core
open Common.Ext
open Ast
open Ast.LogicOld
open PCSatCommon

let make seeds =
  Set.fold
    ~init:(Set.Poly.singleton (T_int.zero (), T_int.zero ()))
    seeds
    ~f:(fun acc (x, _, t) ->
      Set.Poly.union_list
        [
          acc;
          Set.Poly.map acc ~f:(fun (left, right) ->
              (T_int.mk_add x left, T_int.mk_add t right));
          Set.Poly.map acc ~f:(fun (left, right) ->
              ( T_int.mk_add (T_int.mk_neg x) left,
                T_int.mk_add (T_int.mk_neg t) right ));
        ])
  |> Set.Poly.filter_map ~f:(fun (left, right) ->
         let qual =
           Normalizer.normalize
           @@ Formula.geq left (Evaluator.eval_term right |> Term.of_value)
         in
         if Set.is_empty @@ Formula.fvs_of qual then None else Some qual)

let octahedron_half_spaces_of sorts examples =
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
  let params, quals = octahedron_half_spaces_of sorts examples in
  Set.Poly.map ~f:(fun qual -> (params, qual)) quals

let str_of_domain = "Octahedron"
