open Core
open Common.Ext
open Common.Combinator
open LogicOld

type t = ClauseOld.t Set.Poly.t

let pvs_of = Set.concat_map ~f:ClauseOld.pvs_of

let count_pvar_apps pvs cls =
  let pos_nonlin = ref Set.Poly.empty in
  let neg_nonlin = ref Set.Poly.empty in
  (* One pass over the clauses, accumulating the counts of every predicate of
     interest as they are met.  Asking the question the other way round --
     for each predicate, scan the whole clause set -- costs a factor of the
     number of predicates and re-materialises the clause list once per
     predicate; on a problem with a hundred predicates and a few hundred
     clauses that is the difference between a scan and a quadratic sweep, and
     the caller repeats the whole thing after every single elimination. *)
  let acc = Hashtbl.Poly.create () in
  Set.iter cls ~f:(fun (_, ps, ns, _) ->
      let local = Hashtbl.Poly.create () in
      Set.iter ps ~f:(fun atm ->
          let pvar = Atom.pvar_of atm in
          if Set.mem pvs pvar then
            Hashtbl.update local pvar ~f:(function
              | None -> (1, 0)
              | Some (pc, nc) -> (pc + 1, nc)));
      Set.iter ns ~f:(fun atm ->
          let pvar = Atom.pvar_of atm in
          if Set.mem pvs pvar then
            Hashtbl.update local pvar ~f:(function
              | None -> (0, 1)
              | Some (pc, nc) -> (pc, nc + 1)));
      Hashtbl.iteri local ~f:(fun ~key:pvar ~data:(pc, nc) ->
          if pc >= 2 then pos_nonlin := Set.add !pos_nonlin pvar;
          if nc >= 2 then neg_nonlin := Set.add !neg_nonlin pvar;
          let d, p, n = if pc > 0 && nc > 0 then (1, 0, 0) else (0, pc, nc) in
          Hashtbl.update acc pvar ~f:(function
            | None -> (d, p, n)
            | Some (dc, pc', nc') -> (dc + d, pc' + p, nc' + n))));
  let pvs =
    Set.Poly.of_list
    @@ List.filter_map (Hashtbl.to_alist acc) ~f:(fun (pvar, (dc, pc, nc)) ->
           if dc = 0 && pc = 0 && nc = 0 then None
           else Some (pvar, (dc, pc, nc)))
  in
  (pvs, Set.inter !pos_nonlin !neg_nonlin)

(* val simplify_with: Atom.t Set.Poly.t -> Atom.t Set.Poly.t -> t -> t *)
let simplify_with positive negative =
  Set.Poly.filter_map ~f:(ClauseOld.simplify_with positive negative)

let simplify ?check_sat_forall unknowns check_valid =
  Set.Poly.filter_map
    ~f:(ClauseOld.simplify ?check_sat_forall unknowns check_valid)

let reduce_sort_map = Set.Poly.map ~f:ClauseOld.reduce_sort_map

(* val resolve_one_step_all: Atom.t Set.Poly.t -> Atom.t Set.Poly.t -> t -> t *)
let resolve_one_step_all positive negative =
  Set.concat_map ~f:(ClauseOld.resolve_one_step_all positive negative)

(* val has_only_pure : t Set.Poly.t -> bool *)
let has_only_pure = Set.for_all ~f:ClauseOld.has_only_pure
let to_formulas cls = Set.Poly.map cls ~f:(ClauseOld.to_formula >> snd)
let to_formula cls = cls |> to_formulas |> Set.to_list |> Formula.and_of

let of_formulas exi_senv phis : t =
  Set.concat_map phis ~f:(fun (uni_senv, phi) ->
      Set.Poly.map ~f:(fun (ps, ns, phi) -> (uni_senv, ps, ns, phi))
      @@ Formula.cnf_of exi_senv phi)

let str_of cls =
  String.concat_map_set ~sep:"\n" ~f:(fun c -> "  " ^ ClauseOld.str_of c) cls
