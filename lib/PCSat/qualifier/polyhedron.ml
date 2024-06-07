open Core
open Common.Ext
open Ast
open Ast.LogicOld
open PCSatCommon

let make n seeds =
  Set.fold
    ~init:(Set.Poly.singleton (n, []))
    seeds
    ~f:(fun acc (x, _, t) ->
      Set.Poly.union_list
        [
          acc;
          Set.concat_map acc ~f:(fun (n, xts) ->
              Set.Poly.of_list
              @@ List.init n ~f:(fun i ->
                     (n - (i + 1), List.init (i + 1) ~f:(fun _ -> (x, t)) @ xts)));
          Set.concat_map acc ~f:(fun (n, xts) ->
              Set.Poly.of_list
              @@ List.init n ~f:(fun i ->
                     ( n - (i + 1),
                       List.init (i + 1) ~f:(fun _ ->
                           (T_int.mk_neg x, T_int.mk_neg t))
                       @ xts )));
        ])
  |> Set.Poly.filter_map ~f:(fun (_, lrs) ->
         let ls, rs = List.unzip lrs in
         let left, right =
           (T_int.mk_sum (T_int.zero ()) ls, T_int.mk_sum (T_int.zero ()) rs)
         in
         let qual =
           Normalizer.normalize
           @@ Formula.geq left (Evaluator.eval_term right |> Term.of_value)
         in
         if Set.is_empty @@ Formula.fvs_of qual then None else Some qual)

let polyhedron_half_spaces_of n sorts examples =
  let params = LogicOld.sort_env_list_of_sorts sorts in
  ( params,
    Set.union
      (Set.Poly.of_list params
      |> Set.Poly.filter_map ~f:(function
           | x, T_bool.SBool -> Some (Term.mk_var x T_bool.SBool)
           | _, T_int.SInt -> None
           | _, T_real.SReal -> failwith "real"
           | _, s -> failwith ("not supported: " ^ Term.str_of_sort s))
      |> Set.Poly.map ~f:(fun x -> Formula.eq x (T_bool.mk_true ())))
      (Set.concat_map examples ~f:(fun terms ->
           List.map2_exn params terms ~f:(fun (x, s) t ->
               (Term.mk_var x s, s, t))
           |> List.filter ~f:(fun (_, s, _) -> Fn.non Term.is_bool_sort s)
           |> Set.Poly.of_list |> make n)) )

module Make (Config : sig
  val upper_bound : int
end) =
struct
  let qualifiers_of _pvar sorts labeled_atoms _examples =
    let examples =
      Set.Poly.filter_map labeled_atoms ~f:(fun (atom, _) ->
          match ExAtom.instantiate atom with
          | ExAtom.PApp (_, terms) -> Some terms
          | ExAtom.PPApp (_, (_, terms)) -> Some terms
          | _ -> None)
    in
    let params, quals =
      polyhedron_half_spaces_of Config.upper_bound sorts examples
    in
    Set.Poly.map ~f:(fun qual -> (params, qual)) quals

  let str_of_domain =
    "Polyhedron with upper bound " ^ string_of_int Config.upper_bound
end
