(* Interval qualifier domain: for each integer parameter [x] and each value
   [v] it takes in a labelled example, the halfspaces [x >= v] and
   [-x >= -v]; a Bool parameter [b] gives [b = true], and a parameter of any
   other sort gives nothing. *)
open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

let make seeds =
  Set.concat_map seeds ~f:(fun (l, _, r) ->
      Set.Poly.of_list [ (l, r); (T_int.mk_neg l, T_int.mk_neg r) ])
  |> Set.Poly.filter_map ~f:(fun (left, right) ->
         let qual =
           Normalizer.normalize
           @@ Formula.geq left
                (Term.of_value (get_dtenv ()) @@ Evaluator.eval_term right)
         in
         if Formula.is_ground qual then None else Some qual)

let interval_half_spaces_of sorts examples =
  let params = LogicOld.sort_env_list_of_sorts sorts in
  ( params,
    Set.union
      (Set.Poly.of_list params
      |> Set.Poly.filter_map ~f:(function
           | x, T_bool.SBool -> Some (Term.mk_var x T_bool.SBool)
           | _, T_int.SInt -> None
           | _, _ ->
               (* an integer abstract domain: a parameter of any other sort
                  (real, bit-vector, datatype, ...) gets no qualifier from
                  it, the same as an integer one, instead of a crash *)
               None)
      |> Set.Poly.map ~f:(fun x -> Formula.eq x (T_bool.mk_true ())))
      (Set.concat_map examples ~f:(fun terms ->
           List.map2_exn params terms ~f:(fun (x, s) t ->
               (Term.mk_var x s, s, t))
           |> List.filter ~f:(snd3 >> Term.is_int_sort)
           |> Set.Poly.of_list |> make)) )

let qualifiers_of _pvar sorts labeled_atoms _examples =
  let params, quals =
    interval_half_spaces_of sorts
    @@ Set.Poly.filter_map labeled_atoms
         ~f:(fst >> ExAtom.instantiate >> ExAtom.args_of)
  in
  Set.Poly.map quals ~f:(fun qual -> (params, qual))

let str_of_domain = "Interval"
