open Core
open Common.Ext
open LogicOld

let is_affine term =
  Set.for_all (Term.funsyms_of term) ~f:(function
    | T_int.Int _ | T_int.Neg | T_int.Add | T_int.Sub | T_int.Mult ->
        true (*ToDo*)
    | _ -> false)

let coeff_of is_v t =
  let ret = ref None in
  Term.iter_term t ~f:(fun t ->
      if Option.is_none !ret then
        match t with
        | Term.FunApp (T_int.Neg, [ t ], _) when is_v t -> ret := Some (-1)
        | Term.FunApp (T_int.Mult, [ t1; t2 ], _) when is_v t2 ->
            ret :=
              Some (Z.to_int (*ToDo*) @@ Value.int_of @@ Evaluator.eval_term t1)
        | _ -> ());
  match !ret with Some i -> i | None -> 1

let extract_term_from_affine is_unused_term affine =
  let ret =
    Term.map_term true affine ~f:(fun t11 ->
        if is_unused_term t11 then T_int.zero () else t11)
  in
  (* print_endline @@ sprintf "affine after elim var: %s" @@ Term.str_of ret; *)
  let coeff = coeff_of is_unused_term affine in
  (if coeff = 1 then Some (T_int.mk_neg ret)
   else if coeff = -1 then Some ret
   else None)
  |> Option.map ~f:Evaluator.simplify_term
  |> Option.map ~f:Normalizer.normalize_term

let extract_affine_term_from is_unused_term phi =
  match Normalizer.normalize phi with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; _ ], _), _)
    when T_int.is_sint t1 && is_affine t1 -> (
      try extract_term_from_affine is_unused_term t1 with _ -> None)
  | _ -> None
