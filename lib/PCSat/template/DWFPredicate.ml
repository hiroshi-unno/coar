(* Template for a disjunctively well-founded predicate [DWF(x, y)]: the union
   of [Members.number] independent instances of the well-founded ranking
   template ([WFPredicate]).

   A relation is disjunctively well-founded when it is contained in a finite
   union of well-founded relations (Podelski and Rybalchenko, "Transition
   Invariants", LICS 2004).  Every member here is an instance of the
   well-founded template, which is well-founded whatever values its
   parameters take, so every instance of this template is such a union by
   construction: as for the well-founded template, a solution needs no
   separate check of its kind, and a wrong model from the solver can cost an
   answer but cannot make the solution ill-kinded.  The certificate is the
   list of the members' ranking certificates, read by a kind checker as the
   union of their decrease relations.

   What the union adds over one member: a relation two rankings of opposite
   direction cover, such as [x > y /\ x >= 0  \/  x < y /\ x <= 0], which no
   single (piecewise lexicographic) ranking contains, since it holds the
   cycle [(1,0), (0,1)].  What it does not add: each member is the
   well-founded template at the members' common shape and bounds, and the
   number of members is fixed (it does not grow).  Every instance is
   irreflexive, as every disjunctively well-founded relation is.

   Each member's parameters and qualifier holes are its own (each functor
   application below evaluates the well-founded template's body again, and
   each generation draws fresh names).  The members share the hypothesis
   space and grow together: every update label and every restart is applied
   to every member, so they keep one shape and one set of bounds.  The bound
   constraints of one label are the conjunction of the members' constraints
   of that label. *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

module type MembersType = sig
  val number : int
  (** how many well-founded members the union has; at least 1 *)
end

module Make
    (Cfg : WFPredicate.Config.ConfigType)
    (Members : MembersType)
    (Arg : WFPredicate.ArgType) : Function.Type = struct
  let () =
    if Members.number < 1 then
      failwith
        (sprintf
           "DWFPredicate: the number of members must be at least 1, not %d"
           Members.number)

  let members : (module Function.Type) list =
    List.init Members.number ~f:(fun _ ->
        (module WFPredicate.Make (Cfg) (Arg) : Function.Type))

  let iter f = List.iter members ~f
  let name_of () = Arg.name
  let kind_of () = Kind.str_of Kind.DWF
  let kind = Kind.DWF
  let flexible = false
  let sort_of () = Sort.mk_fun @@ Arg.sorts @ [ T_bool.SBool ]
  let params_of () = sort_env_list_of_sorts Arg.sorts

  let show_state ?config labels =
    iter (fun (module M : Function.Type) -> M.show_state ?config labels)

  let str_of () =
    String.concat ~sep:""
    @@ List.mapi members ~f:(fun i (module M : Function.Type) ->
        sprintf "member %d of %d:\n%s\n" (i + 1) Members.number (M.str_of ()))

  let in_space () =
    List.for_all members ~f:(fun (module M : Function.Type) -> M.in_space ())

  (* the members have one configuration and one shape, so the first one's
     reading of the hypothesis space is every member's *)
  let first () = List.hd_exn members

  let adjust_quals_terms qt =
    let (module M : Function.Type) = first () in
    M.adjust_quals_terms qt

  let update_hspace hspace =
    let (module M : Function.Type) = first () in
    M.update_hspace hspace

  let last_certs : Templ.kind_cert_templ list option ref = ref None
  let kind_cert_template () = !last_certs

  (* Contract: the result is the members' templates joined -- the predicate
     is the disjunction of the members' bodies under the binders they share
     (the hypothesis space's parameters), the parameters and holes are the
     members' (pairwise disjoint), and each label's bound constraint is the
     conjunction of the members' constraints of that label.  The certificate
     is recorded only when every member recorded one. *)
  let gen_template ~ucore hspace =
    let gens =
      List.map members ~f:(fun (module M : Function.Type) ->
          let gen = M.gen_template ~ucore hspace in
          (gen, M.kind_cert_template ()))
    in
    let ((label, pred0), cs0, _, _), _ = List.hd_exn gens in
    let binders, _ = Logic.Term.let_lam pred0 in
    let bodies =
      List.map gens ~f:(fun (((_, pred), _, _, _), _) ->
          let xs, body = Logic.Term.let_lam pred in
          if
            not
              (List.equal
                 (fun (x, _) (y, _) -> Ident.tvar_equal x y)
                 xs binders)
          then failwith "DWFPredicate: the members bind different parameters";
          body)
    in
    let pred =
      Logic.Term.mk_lambda binders (Logic.BoolTerm.or_of bodies)
    in
    let constrs =
      List.mapi cs0 ~f:(fun i (hard, l, _) ->
          ( hard,
            l,
            Logic.BoolTerm.and_of
              (List.map gens ~f:(fun ((_, cs, _, _), _) ->
                   let _, _, c = List.nth_exn cs i in
                   c)) ))
    in
    let senv =
      List.fold gens ~init:Map.Poly.empty ~f:(fun acc ((_, _, senv, _), _) ->
          Map.force_merge acc senv)
    in
    let holes = List.concat_map gens ~f:(fun ((_, _, _, holes), _) -> holes) in
    last_certs :=
      Option.map ~f:List.concat (Option.all (List.map gens ~f:snd));
    ((label, pred), constrs, senv, holes)

  let actions_of labels =
    List.concat_map members ~f:(fun (module M : Function.Type) ->
        M.actions_of labels)

  let update_with_labels labels =
    iter (fun (module M : Function.Type) -> M.update_with_labels labels)

  (* the reinforcement-learning channel: each member reads its own action
     list from standard input, in member order *)
  let rl_action labels =
    iter (fun (module M : Function.Type) -> M.rl_action labels)

  (* every member is the well-founded template, so they accept one set of
     labels, which is this template's; [members] is non-empty (checked above) *)
  let coeff_labels, const_labels =
    let (module M : Function.Type) = List.hd_exn members in
    (M.coeff_labels, M.const_labels)

  let restart () = iter (fun (module M : Function.Type) -> M.restart ())
  let update_with_solution _ = assert false
  let sync _thre = assert false
end
