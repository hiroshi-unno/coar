(* Opening the parameters of a resolution-derived example.

   A derived example is [cond => (+-)P(t[sub])], where [sub] is one model of a
   PREMISE: the formula whose truth licenses the example (for a resolution step,
   the matching condition of the resolvent together with the equations tying
   each parameter of the resolved atom to the clause term it was unified with;
   for a unit clause [pure \/ P(t)], the negation of [pure]).  A solver picks a
   value for every variable of the premise whether or not the premise forces
   it, so the example can carry values that are no part of what was derived.

   [open_classes] replaces some of those values by fresh parameters.  A CLASS is
   the set of keys [sub] maps to one non-variable value (structurally equal,
   same sort) among which at least one is a variable of the atom; replacing the
   whole class by one fresh parameter [p] gives [sub'].

   Contract.
   - Assumes: [premise] mentions every variable whose value the derivation
     depends on; in particular every variable of the atom is either in
     [premise] or determined by an equation in it.  A premise that omits the
     link between an atom variable and the clause term it stands for makes that
     variable look unconstrained: that is the defect this contract excludes,
     and the caller must supply the link.
   - Guarantees: a class is opened only when [premise[sub']] simplifies to
     [true] with [p] free, i.e. the premise holds for EVERY value of [p]; so the
     generalised example follows from the same derivation for every value of
     the new parameter, and the model's point [p = v] is one instance.  The
     decision is made by the evaluator, never by satisfiability, and no solver
     is called.  Where nothing is opened, [sub] is returned physically
     unchanged.
   - Greedy in class order; one evaluator pass over [premise] per class. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

let holds premise sub =
  Formula.is_true (Evaluator.simplify (Formula.subst sub premise))

(* the classes of [sub]: keys grouped by their (non-variable) value, keeping
   only groups with a variable of [open_vars] *)
let classes_of ~open_vars sub =
  Map.Poly.to_alist sub
  |> List.filter ~f:(fun (_, v) -> not (Term.is_var v))
  |> List.map ~f:(fun (x, v) ->
      (Term.str_of_sort (Term.sort_of v) ^ " " ^ Term.str_of v, x))
  |> List.sort_and_group ~compare:(fun (k1, _) (k2, _) -> String.compare k1 k2)
  |> List.map ~f:(List.map ~f:snd)
  |> List.filter ~f:(List.exists ~f:(Set.mem open_vars))

let open_classes ?(on_class = fun _ _ _ -> ()) ~open_vars ~premise sub =
  if Set.is_empty open_vars || not (holds premise sub) then sub
  else
    List.fold (classes_of ~open_vars sub) ~init:sub ~f:(fun sub cls ->
        let value = Map.Poly.find_exn sub (List.hd_exn cls) in
        let p = Term.mk_var (Ident.mk_fresh_dontcare "kop") (Term.sort_of value) in
        let cand =
          List.fold cls ~init:sub ~f:(fun m x -> Map.Poly.set m ~key:x ~data:p)
        in
        let ok = holds premise cand in
        on_class cls value ok;
        if ok then cand else sub)

(* the equations tying each resolved-atom variable to the clause term it was
   unified with: [x = theta(x)] for every [x] in [params] that [theta] maps to a
   term other than itself *)
let link_of ~params theta =
  Formula.and_of
  @@ Set.to_list
  @@ Set.Poly.filter_map params ~f:(fun x ->
      match Map.Poly.find theta x with
      | None -> None
      | Some t -> (
          match t with
          | Term.Var (y, _, _) when Ident.tvar_equal x y -> None
          | _ -> Some (Formula.eq (Term.mk_var x (Term.sort_of t)) t)))
