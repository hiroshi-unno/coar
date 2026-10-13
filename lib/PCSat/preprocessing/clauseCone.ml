(* Two cheap answers to "does this clause force [l = r]", for passes that would
   otherwise ask a solver about a whole clause.

   A clause here is given by its pure part [phi] (a disjunction: the clause
   holds when [phi] does or some head atom does) and premises the caller adds
   (equalities assumed of the body atoms).  The premises of the clause are the
   negations of [phi]'s disjuncts.

   - [Normal]: a syntactic proof.  Two terms are rewritten with the clause's own
     definitions [x = t] (a disjunct [x != t] of [phi], [x] not free in [t]),
     a selector applied to its own constructor is reduced, and every subterm
     that one of the premise equalities puts in a class is replaced by the
     class's representative.  Each step replaces a term by one equal to it in
     every model satisfying the premises, so when the two results are the same
     term, [premises => l = r] is valid.  Different results prove nothing.

   - [slice]: the premises a validity question about a goal needs to keep.  It
     keeps the premises connected to the goal's free variables through shared
     free variables, and every premise with no free variable.  Dropping a
     premise only makes [premises => goal] harder to prove, so a proof of the
     sliced question is a proof of the whole one; the converse can fail (the
     dropped premises may be jointly unsatisfiable, or share with the kept ones
     a term whose value the theory leaves open, such as a selector applied to
     the wrong constructor), so a caller that wants the whole question's answer
     asks the whole question when the slice is not proved. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* The clause's definitions: for each disjunct [x != t] (or [not (x = t)]) of
   [phi], with [x] a variable not free in [t] after the earlier definitions,
   [x |-> t].  Idempotent and acyclic: each new definition is normalised by the
   earlier ones and substituted into them, and the first definition of a
   variable wins.  Every definition holds in every model satisfying the
   clause's premises. *)
let definitions phi =
  List.fold (Formula.disjuncts_list_of phi) ~init:Map.Poly.empty ~f:(fun m d ->
      let def =
        match d with
        | Formula.UnaryOp
            ( Formula.Not,
              Formula.Atom
                (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
              _ )
        | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _)
          -> (
            match (t1, t2) with
            | Term.Var (x, _, _), t | t, Term.Var (x, _, _) -> Some (x, t)
            | _ -> None)
        | _ -> None
      in
      match def with
      | Some (x, t) when not (Map.Poly.mem m x) ->
          let t = Term.subst m t in
          if Set.mem (Term.tvs_of t) x then m
          else
            let one = Map.Poly.singleton x t in
            Map.Poly.set ~key:x ~data:t (Map.Poly.map m ~f:(Term.subst one))
      | _ -> m)

(* the premise equalities among [phi]'s negated disjuncts: [t1 = t2] for each
   disjunct [t1 != t2] or [not (t1 = t2)] *)
let premise_equalities phi =
  List.filter_map (Formula.disjuncts_list_of phi) ~f:(function
    | Formula.UnaryOp
        ( Formula.Not,
          Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
          _ )
    | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _) ->
        Some (t1, t2)
    | _ -> None)

(* structural equality that answers [false] rather than raising on a value
   polymorphic comparison cannot handle *)
let same t1 t2 = try Stdlib.(t1 = t2) with Invalid_argument _ -> false

(* a selector applied to an application of the constructor that has it,
   reduced to that argument; anything else unchanged.  Exact: a selector of
   its own constructor is total and returns that field. *)
let reduce_sel_of_cons t =
  match t with
  | Term.FunApp
      ( T_dt.DTSel (sname, _, _),
        [ Term.FunApp (T_dt.DTCons (cname, _, dt), args, _) ],
        _ ) -> (
      match Datatype.look_up_cons dt cname with
      | None -> t
      | Some cons -> (
          match
            List.findi (Datatype.sels_of_cons cons) ~f:(fun _ s ->
                String.equal (Datatype.name_of_sel s) sname)
          with
          | Some (i, _) when i < List.length args -> List.nth_exn args i
          | _ -> t))
  | _ -> t

module Normal = struct
  (* [defs] the clause's definitions; [classes] lists of terms known equal
     under the premises, each led by its representative *)
  type t = {
    defs : (Ident.tvar, Term.t) Map.Poly.t;
    classes : Term.t list list;
  }

  (* rewrite without the classes: the definitions, then selectors of
     constructors bottom up; never under a binder, whose variables are not the
     clause's *)
  let base defs t =
    Term.map_term_no_binders ~f:reduce_sel_of_cons (Term.subst defs t)

  let rep classes t =
    match List.find classes ~f:(List.exists ~f:(same t)) with
    | Some (r :: _) -> r
    | _ -> t

  (* [eqs] are equalities that hold under the premises: the clause's premise
     equalities and those the caller assumes of the body atoms *)
  let make phi eqs =
    let defs = definitions phi in
    let classes =
      List.fold
        (premise_equalities phi @ eqs)
        ~init:[]
        ~f:(fun classes (a, b) ->
          let a = base defs a and b = base defs b in
          if same a b then classes
          else
            let has t = List.exists ~f:(same t) in
            let ca, rest = List.partition_tf classes ~f:(has a) in
            let cb, rest = List.partition_tf rest ~f:(has b) in
            let ca = match ca with c :: _ -> c | [] -> [ a ] in
            let cb = match cb with c :: _ -> c | [] -> [ b ] in
            (ca @ cb) :: rest)
    in
    { defs; classes }

  let normal nf t =
    Term.map_term_no_binders
      ~f:(fun t -> rep nf.classes (reduce_sel_of_cons t))
      (Term.subst nf.defs t)

  (* [true] only when [l = r] holds in every model of the premises *)
  let proves nf l r = same (normal nf l) (normal nf r)
end

(* The premises among [premises] connected to [goal]'s free variables through
   shared free variables, plus every premise without a free variable, in their
   order.  See the head of this file for why proving [slice => goal] proves
   [premises => goal]. *)
let slice premises goal =
  let parent = Hashtbl.Poly.create () in
  let rec find x =
    match Hashtbl.find parent x with
    | None -> x
    | Some p ->
        let r = find p in
        if not (Ident.tvar_equal r p) then Hashtbl.set parent ~key:x ~data:r;
        r
  in
  let union x y =
    let rx = find x and ry = find y in
    if not (Ident.tvar_equal rx ry) then Hashtbl.set parent ~key:rx ~data:ry
  in
  let vs =
    List.map premises ~f:(fun p -> (p, Set.to_list (Formula.tvs_of p)))
  in
  List.iter vs ~f:(fun (_, xs) ->
      match xs with x :: rest -> List.iter rest ~f:(union x) | [] -> ());
  let roots = Set.Poly.map (Formula.tvs_of goal) ~f:find in
  List.filter_map vs ~f:(fun (p, xs) ->
      match xs with
      | [] -> Some p
      | x :: _ -> if Set.mem roots (find x) then Some p else None)
