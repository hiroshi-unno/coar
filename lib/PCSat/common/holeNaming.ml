open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* Naming the instantiated groups of a template's hole qualifiers, and the
   compound arguments they are instantiated at, so that what repeats across
   the atoms of one example clause is written once.

   A template instantiated at an atom applies every hole to the atom's
   arguments, and a hole's body is a conjunction with one entry per
   qualifier: a literal on the qualifier's selector parameter when the truth
   table decided the qualifier there, or the qualifier itself kept symbolic
   ([key > 0 => q] and [key < 0 => not q]) when the atom's cells are read at a
   universally quantified index.  The entry of a qualifier depends on the
   atom only through the arguments the qualifier reads.  So the entries of
   one hole split into GROUPS by the argument positions their qualifiers read,
   and a group's instance -- the hole, the positions and the arguments there
   -- recurs in every atom of a clause that passes the same arguments at
   those positions.  Within a symbolic entry, the arguments themselves are
   copied once per occurrence of a parameter: on the cell route an array's
   [store] chain and its read at the universal index, an [ite] chain.  An
   exact step example of the cell route has dozens of atoms differing in one
   cell, and a template of six disjuncts over 84 qualifiers made one
   example's constraint 0.5-1.2 million nodes where its distinct subterms
   were 41-71 thousand.

   [hole_map] gives a hole the body [b1 /\ .. /\ bk], one fresh Boolean name
   per group instance, recording in [table] each name with its definition:
   the conjunction of the group's entries at the atom's arguments.  With
   [~name_args], each compound argument (neither a variable nor a constant,
   of integer, real or array sort) is itself replaced by a fresh name [v]
   with the definition [t] before the entries are instantiated.  A hole with
   no qualifiers keeps the body [true].

   [guards table terms] lists the names [terms] mention, directly or through
   the definitions of names they mention, and [guard] is the disjunct that
   binds one: [b xor def] for a Boolean name, [v <> def] otherwise.  For a
   clause constraint [forall xs. D1 \/ .. \/ Dn] whose disjuncts were built
   from such hole maps,

     forall xs ns. guard(n1) \/ .. \/ guard(nm) \/ D1 \/ .. \/ Dn

   (the names [ns] that [guards] lists, one guard each) is EQUIVALENT to the
   constraint with every hole body written out: for each name the values
   different from its definition make its guard true, and the value equal to
   it leaves the rest with the definition in place of the name (the one-point
   rule), applied first to the group names, whose definitions mention
   argument names, then to the argument names, whose definitions mention no
   name.  The names are fresh, so no variable is captured.  Hence the
   synthesis query has the same models over its free variables, the template
   parameters among them, and the names, bound inside the constraint, reach
   no model or candidate.

   Precondition, which the caller checks: the template applies each hole
   only to its own lambda parameters in their order, and every hole with
   qualifiers takes those parameters, so that the hole's value at the atom is
   its body with the atom's arguments for the parameters.  [None] from
   [hole_map] where a hole's parameter list does not match the arguments;
   the caller then builds the hole map as before. *)

type table = {
  defs : (string, Ident.tvar) Hashtbl.t;
  names : (Ident.tvar, Logic.Sort.t * Logic.term) Hashtbl.t;
}

let create () =
  { defs = Hashtbl.create (module String); names = Hashtbl.Poly.create () }

(* the name [key] stands for, drawn and recorded with the definition [def ()]
   at the first request *)
let name_of table key sort def =
  match Hashtbl.find table.defs key with
  | Some n -> n
  | None ->
      let n = Ident.mk_fresh_tvar () in
      Hashtbl.set table.defs ~key ~data:n;
      Hashtbl.set table.names ~key:n ~data:(sort, def ());
      n

(* the positions of [qsenv] that [phi] reads *)
let positions_read qsenv phi =
  let fvs = Formula.fvs_of phi in
  List.filter_mapi qsenv ~f:(fun i (x, _) ->
      if Set.mem fvs x then Some i else None)

(* [quals] grouped by the positions they read, groups in the order of their
   first qualifier and qualifiers in their given order *)
let groups_of qsenv quals =
  List.fold quals ~init:[] ~f:(fun acc ((_, (_, _, phi)) as q) ->
      let pos = positions_read qsenv phi in
      match List.Assoc.find acc pos ~equal:(List.equal Int.equal) with
      | Some qs ->
          List.Assoc.add acc pos (q :: qs) ~equal:(List.equal Int.equal)
      | None -> acc @ [ (pos, [ q ]) ])
  |> List.map ~f:(fun (pos, qs) -> (pos, List.rev qs))

let nameable t =
  (not (Term.is_var t))
  && (match t with Term.FunApp (_, [], _) -> false | _ -> true)
  && (match Term.sort_of t with
    | T_int.SInt | T_real.SReal -> true
    | s -> T_array.is_sarray s)
  && Set.is_empty (Term.fvar_apps_of t)

(* [hole_map table ~prefix ~subst ~name_args args hole_qualifiers_map ~f]:
   the hole map [hole_map_of hole_qualifiers_map ~f] would build at [args],
   with each hole's body replaced by the names of its group instances.
   [prefix] identifies everything else the entries depend on (the predicate,
   the polarity, the reading), and [subst] is a capture-avoiding
   substitution.  Arguments are identified by their printed form and sort. *)
let hole_map table ~prefix ~subst ~name_args (args : Term.t list)
    hole_qualifiers_map ~f =
  let n = List.length args in
  let arg_keys =
    List.map args ~f:(fun t ->
        sprintf "%s : %s" (Term.str_of t) (Term.str_of_sort (Term.sort_of t)))
  in
  let largs =
    List.map2_exn args arg_keys ~f:(fun t key ->
        if name_args && nameable t then
          let sort = Logic.ExtTerm.of_old_sort (Term.sort_of t) in
          Logic.Term.mk_var
          @@ name_of table ("arg\x00" ^ key) sort (fun () ->
              Logic.ExtTerm.of_old_term t)
        else Logic.ExtTerm.of_old_term t)
  in
  (* a hole with no qualifiers takes its parameters from a sibling, as
     [hole_map_of] does *)
  let sibling =
    List.find_map hole_qualifiers_map ~f:(function
      | _, (_, (_, qsenv, _)) :: _ -> Some (Logic.of_old_sort_env_list qsenv)
      | _ -> None)
  in
  Option.all
  @@ List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
      match quals with
      | [] -> (
          match sibling with
          | Some senv when List.length senv = n ->
              Some
                (hole, Logic.Term.mk_lambda senv (Logic.BoolTerm.mk_bool true))
          | _ -> None)
      | (_, (_, qsenv, _)) :: _ when List.length qsenv <> n -> None
      | (_, (_, qsenv, _)) :: _ ->
          let senv = Logic.of_old_sort_env_list qsenv in
          let sub =
            Map.Poly.of_alist_exn
              (List.map2_exn senv largs ~f:(fun (x, _) t -> (x, t)))
          in
          let names =
            List.map (groups_of qsenv quals) ~f:(fun (pos, qs) ->
                let key =
                  String.concat ~sep:"\x00"
                    (prefix :: Ident.name_of_tvar hole
                    :: String.concat ~sep:"," (List.map pos ~f:Int.to_string)
                    :: Bool.to_string name_args
                    :: List.map pos ~f:(List.nth_exn arg_keys))
                in
                name_of table key Logic.BoolTerm.SBool (fun () ->
                    subst sub (Logic.BoolTerm.and_of (List.map qs ~f))))
          in
          Some
            ( hole,
              Logic.Term.mk_lambda senv
              @@ Logic.BoolTerm.and_of (List.map names ~f:Logic.Term.mk_var) ))

(* the names [terms] mention, directly or through the definitions of names
   they mention, each with its sort and definition, in name order *)
let guards table terms =
  let rec close seen = function
    | [] -> seen
    | x :: rest when Map.Poly.mem seen x -> close seen rest
    | x :: rest -> (
        match Hashtbl.find table.names x with
        | None -> close seen rest
        | Some ((_, def) as d) ->
            close
              (Map.Poly.set seen ~key:x ~data:d)
              (Set.to_list (Logic.Term.fvs_of def) @ rest))
  in
  Map.Poly.to_alist @@ close Map.Poly.empty @@ Set.to_list
  @@ Set.Poly.union_list (List.map terms ~f:Logic.Term.fvs_of)

let guard (n, (sort, def)) =
  match sort with
  | Logic.BoolTerm.SBool ->
      Logic.Term.mk_apps (Logic.BoolTerm.mk_xor ()) [ Logic.Term.mk_var n; def ]
  | _ -> Logic.BoolTerm.neq_of sort (Logic.Term.mk_var n) def
