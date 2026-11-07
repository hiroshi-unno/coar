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

(* A scalar premise does not identify a same-spelled function head. Unsafe
   substitution is left symbolic; this may lose a proof, never create one. *)
let substitute_scalar_definitions defs t =
  if Map.Poly.is_empty defs then t
  else if Evaluator.scalar_substitution_is_safe_in_scope
    (Evaluator.scalar_substitution_scope_of t) defs then Term.subst defs t
  else t

(* The clause's definitions: for each disjunct [x != t] (or [not (x = t)]) of
   [phi], with [x] a variable not free in [t] after the earlier definitions,
   [x |-> t]. Each new definition and earlier right-hand sides are normalised
   only when scalar substitution is admitted; otherwise they stay symbolic.
   The first definition of a variable wins.  Every definition holds in every model satisfying the
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
          let t = substitute_scalar_definitions m t in
          if Set.mem (Term.fvs_of t) x then m
          else
            let one = Map.Poly.singleton x t in
            Map.Poly.set ~key:x ~data:t (Map.Poly.map m ~f:(substitute_scalar_definitions one))
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

  (* Rewrite by admitted scalar definitions, then reduce selectors bottom
     up. Selector and congruence traversals do not enter binders. *)
  let base defs t =
    Term.map_term_no_binders ~f:reduce_sel_of_cons (substitute_scalar_definitions defs t)

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
      (substitute_scalar_definitions nf.defs t)

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

(* Two independent scalar copies of premises, with distinct copied values.
   A refused substitution supplies no evidence of two values. In particular,
   an inner binder of another sort must not mask a free Boolean alias. *)
let two_value_query ~premises v srt =
  let copy () =
    let w = Term.mk_var (Ident.mk_fresh_tvar ()) srt in
    let sub = Map.Poly.singleton v w in
    if List.for_all premises ~f:(Evaluator.scalar_substitution_is_safe sub)
    then Some (w, List.map premises ~f:(Formula.subst sub))
    else None
  in
  match copy (), copy () with
  | Some (w1, ps1), Some (w2, ps2) ->
      Some ((Formula.mk_neg (Formula.eq w1 w2) :: ps1) @ ps2)
  | _ -> None

(* Variables the premises cannot see.

   [unseen_var_why ~premises ~other t srt]: [`Unseen] only when [t] is a
   variable, or a chain of selectors of single-constructor datatypes applied
   to a variable (a field of a record, say), and, for every model [M] of
   [premises], changing [t]'s value in [M] can falsify [t = other] while
   leaving every premise true.  Then [premises => t = other] is valid exactly
   when the premises are unsatisfiable, so the question about the equality
   can be replaced by the question [premises => false], which is the same for
   every such equality of one clause.  A field is changed by changing the
   variable at that field alone: with one constructor at each level every
   value is that constructor applied to its fields, so the variable can be
   rebuilt with one field different, and every other chain of selectors from
   it keeps its value.

   Two cases are recognised.

   - [t] does not occur in the premises: every occurrence of its variable
     there is a chain of selectors that leaves [t]'s path (another field).
     Any value can be given to [t], and its sort has at least two values in
     every structure ([two_valued]), so a value different from the value of
     [other] exists.

   - [t : Array Int E], [E] two-valued, and every occurrence of [t] in the
     premises is a read [select t j] of a variable [j] bound by a binder
     (universal or existential, at any polarity) whose body has a top-level
     disjunct mentioning only [j] that is true at [j = -1] (a guard [j < 0]
     of a universal, say) or a top-level conjunct mentioning only [j] that is
     false there (a guard [j >= 0] of an existential).  Changing [t] at index
     -1 alone changes no premise: a read at an index other than -1 reads the
     same value, and wherever [j] is -1 the body of [j]'s binder has the same
     truth value whatever [t] holds, so the binder's formula has the same
     truth value.  Giving [t] at -1 a value different from that of [other]
     at -1 makes [t <> other].

   - [t] is a variable and the premises that mention it mention nothing else
     (bounds such as [0 <= t]) and no symbol the theory leaves open, and
     [two_values] says that they admit two different values of [t] (a
     caller's solver question about those premises alone).  Every model then
     has, besides [t]'s value, another value satisfying them; one of the two
     differs from [other]'s value, and giving it to [t] keeps every premise.

   A side that is a selector applied to its own constructor is first reduced
   to that field, which is the same term in every model.

   In all cases [other] must be independent of [t] in the same sense.  The
   test is syntactic and conservative: any other occurrence of the variable
   (whole, under a selector of a datatype with several constructors, under a
   [let] or a binder that rebinds it, in a recursive definition, inside a
   fixpoint predicate, under a sampling binder) answers [`Seen]. *)
let rec two_valued = function
  | T_bool.SBool | T_int.SInt | T_real.SReal | T_seq.SSeq _ -> true
  | T_array.SArray (_, e) -> two_valued e
  | _ -> false

(* [t] as a variable and the names of the selectors applied to it, innermost
   first, when every selector is of a datatype with one constructor *)
let rec access_path = function
  | Term.Var (v, _, _) -> Some (v, [])
  | Term.FunApp (T_dt.DTSel (name, dt, _), [ t ], _) -> (
      match Datatype.conses_of dt with
      | [ _ ] -> Option.map (access_path t) ~f:(fun (v, p) -> (v, p @ [ name ]))
      | _ -> None)
  | _ -> None

(* a selector applied to its own constructor reduced, at the head and below
   it along a chain of selectors *)
let rec reduce_sel_chain t =
  match t with
  | Term.FunApp (T_dt.DTSel (name, dt, _), [ u ], _) ->
      let u' = reduce_sel_chain u in
      reduce_sel_of_cons (if phys_equal u u' then t else T_dt.mk_sel dt name u')
  | _ -> t

let unseen_var_why ?(two_values = fun _ _ _ -> false) ~premises ~other target
    srt =
  let target = reduce_sel_chain target in
  let other = reduce_sel_chain other in
  match access_path target with
  | None -> `Not_a_variable
  | Some (v, tpath) -> (
      let is_v y = Ident.tvar_equal v y in
      let rec is_prefix p q =
        match (p, q) with
        | [], _ -> true
        | a :: p', b :: q' -> String.equal a b && is_prefix p' q'
        | _ :: _, [] -> false
      in
      (* how an access path from [v] relates to [target]'s *)
      let relate path =
        if List.equal String.equal path tpath then `Target
        else if is_prefix path tpath || is_prefix tpath path then `Overlap
        else `Apart
      in
      (* [d] mentions only [j] and has the truth value [b] at [j = -1] *)
      let guard b j d =
        Set.is_subset (Formula.fvs_of d) ~of_:(Set.Poly.singleton j)
        &&
          try
            let sub = Map.Poly.singleton j (T_int.from_int (-1)) in
            if not (Evaluator.scalar_substitution_is_safe sub d) then false
            else
              let v = Evaluator.simplify (Formula.subst sub d) in
              if b then Formula.is_true v else Formula.is_false v
          with exn_ when not (Common.Timer.is_async exn_) -> false
      in
      (* a read of the target at a guarded index leaves it unseen only for an
     integer-indexed array of a two-valued sort *)
      let reads_ok =
        match srt with
        | T_array.SArray (T_int.SInt, e) -> two_valued e
        | _ -> false
      in
      let path_of t =
        match access_path t with
        | Some (v', p) when is_v v' -> Some (relate p)
        | _ -> None
      in
      let rec term g t =
        match path_of t with
        | Some `Apart -> true
        | Some (`Target | `Overlap) -> false
        | None -> (
            match t with
            | Term.Var (y, _, _) -> not (is_v y)
            | Term.FunApp
                (T_array.ASelect (T_int.SInt, _), [ a; Term.Var (j, _, _) ], _)
              when Option.equal Stdlib.( = ) (path_of a) (Some `Target) ->
                reads_ok && Set.mem g j
            | Term.FunApp (T_array.ALambda ((b, _), _), args, _) ->
                (not (is_v b)) && List.for_all args ~f:(term (Set.remove g b))
            | Term.FunApp (T_bool.Formula phi, args, _) ->
                formula g phi && List.for_all args ~f:(term g)
            | Term.FunApp (_, args, _) -> List.for_all args ~f:(term g)
            | Term.LetTerm (y, _, def, body, _) ->
                (not (is_v y)) && term g def && term (Set.remove g y) body)
      and formula g = function
        | Formula.Atom (Atom.App (Predicate.Var (p, _), args, _), _) ->
            not (is_v (Ident.pvar_to_tvar p)) && List.for_all args ~f:(term g)
        | Formula.Atom (Atom.App (Predicate.Psym _, args, _), _) ->
            List.for_all args ~f:(term g)
        | Formula.Atom ((Atom.True _ | Atom.False _), _) -> true
        | Formula.Atom (atm, _) -> not (Set.mem (Atom.fvs_of atm) v)
        | Formula.UnaryOp (_, f, _) -> formula g f
        | Formula.BinaryOp (_, f1, f2, _) -> formula g f1 && formula g f2
        | Formula.Bind ((Formula.Forall | Formula.Exists), senv, body, _) ->
            (not (List.exists senv ~f:(fun (y, _) -> is_v y)))
            &&
            let bound = List.map senv ~f:fst in
            let g = List.fold bound ~init:g ~f:Set.remove in
            let nnf = Formula.nnf_of body in
            let ds = Formula.disjuncts_list_of nnf in
            let cs = Formula.conjuncts_list_of nnf in
            let g =
              List.fold senv ~init:g ~f:(fun g (j, s) ->
                  if
                    Stdlib.(s = T_int.SInt)
                    && (List.exists ds ~f:(guard true j)
                       || List.exists cs ~f:(guard false j))
                  then Set.add g j
                  else g)
            in
            formula g body
        | Formula.LetFormula (y, _, def, body, _) ->
            (not (is_v y)) && term g def && formula (Set.remove g y) body
        | (Formula.Bind _ | Formula.LetRec _) as phi ->
            not (Set.mem (Formula.fvs_of phi) v)
      in
      let mentions p = Set.mem (Formula.fvs_of p) v in
      let sees p = mentions p && not (formula Set.Poly.empty p) in
      (* premises about [v] alone, when the target is [v] itself *)
      let unary p =
        List.is_empty tpath
        && Set.equal (Formula.fvs_of p) (Set.Poly.singleton v)
        && not (ClauseOld.interpretation_dependent p)
      in
      if not (term Set.Poly.empty other) then `Other
      else if not (two_valued srt) then `Sort
      else
        let seeing = List.filter premises ~f:sees in
        match List.find seeing ~f:(fun p -> not (unary p)) with
        | Some p -> `Seen p
        | None -> (
            match seeing with
            | [] -> `Unseen
            | p :: _ -> if two_values seeing v srt then `Unseen else `Seen p))

let unseen_var ?two_values ~premises ~other target srt =
  match unseen_var_why ?two_values ~premises ~other target srt with
  | `Unseen -> true
  | `Not_a_variable | `Other | `Sort | `Seen _ -> false

(* [unseen_side ~premises (l, r)]: [true] when one side of [l = r] is a
   variable or a field [unseen_var] accepts against the other side *)
let unseen_side ?two_values ~premises (l, r) =
  unseen_var ?two_values ~premises ~other:r l (Term.sort_of l)
  || unseen_var ?two_values ~premises ~other:l r (Term.sort_of r)
