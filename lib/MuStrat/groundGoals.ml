(* A counter-play of a strategy check whose goals are conjunctions of ground
   atoms, found by deciding each ground atom's derivability on its own.

   The shape.  A strategy check is a CHC system; its goal clauses (no head)
   ask whether the query is derivable.  When the checked side's strategy
   offers several terms for a key, the check names each alternative by a
   nullary predicate, and a goal reads [G <= Alt_1 /\ .. /\ Alt_m] with each
   [Alt_i] defined by clauses without variables whose body atoms are ground,
   such as [U(1, 1) => Alt_1].  Call such a nullary predicate, all of whose
   defining clauses are closed (no variable at all), a LAYER predicate, and an
   atom without variables that occurs in the body of a goal or of a layer
   clause and is not a layer predicate a LEAF.

   The claim.  In the least model of the system, a layer predicate holds iff
   one of its clauses has a satisfied constraint and every body atom derivable;
   the query holds iff some closed goal does.  So the query is derivable iff
   the propositional Horn system over the layer, with each leaf replaced by
   whether it is derivable, derives it.  Every leaf is a separate question,
   and a derivation of the query is the goal's clause instance over the layer
   clauses' instances over the leaves' derivations: a tree whose subtrees share
   no variable, since every atom in it is ground.

   What is built here.  [split] decides each leaf by a ground top-down search
   ([derive]): from a ground atom, try each clause whose head has its
   predicate, fix the head to the atom's arguments, and take the body atoms'
   arguments from the head's equations (by evaluation when the head binds every
   variable, else from one Z3 model); recurse on the body atoms, skipping an
   atom already open on the current path (a minimal derivation never repeats
   an atom along a path), and backtrack to the next clause on failure.  Every
   clause instance it keeps is re-checked by evaluation: the instance's
   constraint simplifies to [true] and its head's arguments to the atom's.  So
   a returned tree is a derivation of the system whatever the search did, and
   only found derivations are used.  The search is incomplete -- one model per
   clause, a budget of clause-instance attempts per leaf -- so failing to find
   a derivation says nothing, and is never read as a win.

   [to_cex] writes a derivation in the form Z3's Spacer reports one and the
   strategy refinement reads: [mp (hyper-res (asserted <clause>) <children..>
   <conclusion>) (asserted <query!0 => false>) <false> = true], each clause the
   universally closed implication [body atoms /\ constraint => head], with the
   body atoms in the order of the children, and the goal's head the query
   predicate [query!0].  The head is the clause's own under [own_heads], as
   Spacer states it; otherwise the node's ground conclusion. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

type atom = Ident.pvar * Sort.t list * Term.t list

type clause = {
  senv : sort_env_list;
  head : atom option;  (** [None] for a goal *)
  body : atom list;
  constr : Formula.t;
      (** where the clause applies: the negation of its pure disjuncts *)
}

type node = {
  pvar : Ident.pvar;
  sorts : Sort.t list;
  args : Term.t list;  (** ground *)
  clause : clause;
      (** the clause applied; its body in the order of [children] *)
  children : node list;
}

let query_pvar = Ident.Pvar "query!0"

(* The clauses of a CHC system in the form above; [None] when a clause has
   two head atoms or an atom is not a predicate variable application. *)
let clauses_of_problem chc =
  try
    let exi_senv = PCSP.Problem.senv_of chc in
    let app = function
      | Atom.App (Predicate.Var (p, sorts), args, _) -> (p, sorts, args)
      | _ -> raise Exit
    in
    Some
      (PCSP.Problem.clauses_of (PCSP.Problem.to_cnf chc)
      |> Set.to_list
      |> List.map ~f:(fun c ->
          let senv, ps, ns, phi = Clause.to_old_clause exi_senv c in
          let head =
            match Set.to_list ps with
            | [] -> None
            | [ a ] -> Some (app a)
            | _ -> raise Exit
          in
          {
            senv = Map.Poly.to_alist (Logic.to_old_sort_env_map senv);
            head;
            body = List.map (Set.to_list ns) ~f:app;
            constr = Evaluator.simplify_neg phi;
          }))
  with exn when not (Common.Timer.is_async exn) -> None

let closed_term t = Set.is_empty (Term.tvs_of t)

let closed_clause c =
  Set.is_empty (Formula.tvs_of c.constr)
  && List.for_all c.body ~f:(fun (_, _, args) ->
      List.for_all args ~f:closed_term)
  && Option.for_all c.head ~f:(fun (_, _, args) ->
      List.for_all args ~f:closed_term)

let value t =
  let t = Evaluator.simplify_term t in
  if closed_term t then Some t else None

let key p args =
  sprintf "%s(%s)" (Ident.name_of_pvar p)
    (String.concat_map_list ~sep:"," args ~f:Term.str_of)

(* [instance ~ask c vals]: the body atoms' ground arguments of an instance of
   [c] whose head has the arguments [vals], or [None].  [ask phi] is a model
   of [phi] (variable, value) or [None]; it is asked only when the head does
   not bind every variable of the clause.  Whatever produced the substitution,
   the instance is kept only when its constraint and its head equations
   simplify to [true] and every body argument to a closed term. *)
let instance ~ask c vals =
  match c.head with
  | None -> None
  | Some (_, _, hargs) when List.length hargs <> List.length vals -> None
  | Some (_, _, hargs) -> (
      let check sub =
        let heq =
          Evaluator.simplify @@ Formula.and_of
          @@ List.map2_exn hargs vals ~f:(fun t v ->
              Formula.eq (Term.subst sub t) v)
        in
        let constr = Evaluator.simplify (Formula.subst sub c.constr) in
        if Formula.is_true heq && Formula.is_true constr then
          Option.all
            (List.map c.body ~f:(fun (_, _, args) ->
                 Option.all
                   (List.map args ~f:(fun t -> value (Term.subst sub t)))))
        else None
      in
      let direct =
        Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
        @@ List.filter_map (List.zip_exn hargs vals) ~f:(fun (t, v) ->
            if Term.is_var t then
              let (x, _), _ = Term.let_var t in
              Some (x, v)
            else None)
      in
      let open_vars =
        List.filter c.senv ~f:(fun (x, _) -> not (Map.Poly.mem direct x))
      in
      if List.is_empty open_vars then check direct
      else
        let phi =
          Formula.and_of
            (Formula.subst direct c.constr
            :: List.map2_exn hargs vals ~f:(fun t v ->
                Formula.eq (Term.subst direct t) v))
        in
        match ask phi with
        | None -> None
        | Some model ->
            let sub =
              List.fold open_vars ~init:direct ~f:(fun sub (x, s) ->
                  let v =
                    match model_value model (x, s) with
                    | Some v -> v
                    | None -> Term.mk_dummy s
                  in
                  Map.Poly.set sub ~key:x ~data:v)
            in
            check sub)

(* [head_fixes c]: every variable of [c] -- of its sort environment, its head
   arguments and its constraint -- is a head argument, so that a head atom
   fixes the one candidate substitution.  A function of [c] alone: which
   variables the substitution binds is read off which head arguments are
   variables, not off the values they are given. *)
let head_fixes c =
  match c.head with
  | None -> false
  | Some (_, _, hargs) ->
      let head_vars =
        List.filter_map hargs ~f:(fun t ->
            if Term.is_var t then
              let (x, _), _ = Term.let_var t in
              Some x
            else None)
      in
      let bound x = List.mem head_vars x ~equal:Ident.tvar_equal in
      not
        (List.exists c.senv ~f:(fun (x, _) -> not (bound x))
        || List.exists hargs ~f:(fun t ->
            Set.exists (Term.tvs_of t) ~f:(Fn.non bound))
        || Set.exists (Formula.tvs_of c.constr) ~f:(Fn.non bound))

(* [instance_exact ~ask c vals]: [instance]'s answer, with its "no" split in
   two.  [`Accepted argss] is [instance]'s [Some argss].  [`Refuted] only when
   the clause has no instance at all with the head arguments [vals]: the head
   has another arity, or every variable of [c] occurs as a head argument (so
   the head fixes the one candidate substitution) and the head equations or
   the constraint at that substitution simplify to [false].  [`Unknown]
   otherwise -- a variable the head leaves open (whose value [instance] can
   only take from one model), or a formula that simplifies to neither [true]
   nor [false] (a term the theory leaves open, such as a division by zero),
   or a body argument that does not evaluate to a closed term.  So a
   [`Refuted] is a proof, over the theory's evaluation of closed terms, that
   no ground instance of [c] concludes the atom.

   [?fixes] is [head_fixes c], given by a caller that tries [c] many times
   and computed it once; computed here otherwise. *)
let instance_exact ?fixes ~ask c vals =
  match c.head with
  | None -> `Unknown
  | Some (_, _, hargs) when List.length hargs <> List.length vals -> `Refuted
  | Some (_, _, hargs) -> (
      let fixes = match fixes with Some b -> b | None -> head_fixes c in
      if not fixes then
        match instance ~ask c vals with
        | Some argss -> `Accepted argss
        | None -> `Unknown
      else
        let direct =
          Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
          @@ List.filter_map (List.zip_exn hargs vals) ~f:(fun (t, v) ->
              if Term.is_var t then
                let (x, _), _ = Term.let_var t in
                Some (x, v)
              else None)
        in
        let heq =
          Evaluator.simplify @@ Formula.and_of
          @@ List.map2_exn hargs vals ~f:(fun t v ->
              Formula.eq (Term.subst direct t) v)
        in
        let constr = Evaluator.simplify (Formula.subst direct c.constr) in
        if Formula.is_false heq || Formula.is_false constr then `Refuted
        else if Formula.is_true heq && Formula.is_true constr then
          (* [instance ~ask c vals] here, without simplifying the two
             formulas again: every variable of [c] is a head argument, so
             [instance] asks nothing and checks the substitution [direct], whose
             head equations and constraint are [heq] and [constr] *)
          match
            Option.all
              (List.map c.body ~f:(fun (_, _, args) ->
                   Option.all
                     (List.map args ~f:(fun t -> value (Term.subst direct t)))))
          with
          | Some argss -> `Accepted argss
          | None -> `Unknown
        else `Unknown)

(* [derive ~ask ~budget ~memo by_head atom]: a derivation of the ground
   [atom] from the clauses [by_head] (keyed by head predicate name), or
   [None].  [budget] counts clause-instance attempts and is decremented by
   each; [memo] keeps the derivations found (by [key]) and may be shared
   between calls on the same clauses.  Each atom tries its clauses in the
   order [by_head] lists them, and the first derivation found is returned. *)
let derive ~ask ~budget ~memo by_head ((p, sorts, vals) : atom) =
  let rec go path (p, sorts, vals) =
    let k = key p vals in
    match Hashtbl.find memo k with
    | Some n -> Some n
    | None ->
        if Set.mem path k then None
        else
          let path = Set.add path k in
          let cs =
            Option.value ~default:[]
              (Map.Poly.find by_head (Ident.name_of_pvar p))
          in
          List.find_map cs ~f:(fun c ->
              if !budget <= 0 then None
              else (
                decr budget;
                match instance ~ask c vals with
                | None -> None
                | Some argss ->
                    let rec kids acc = function
                      | [] -> Some (List.rev acc)
                      | ((q, qsorts, _), qargs) :: rest -> (
                          match go path (q, qsorts, qargs) with
                          | None -> None
                          | Some n -> kids (n :: acc) rest)
                    in
                    Option.map
                      (kids [] (List.zip_exn c.body argss))
                      ~f:(fun children ->
                        let n =
                          { pvar = p; sorts; args = vals; clause = c; children }
                        in
                        Hashtbl.set memo ~key:k ~data:n;
                        n)))
  in
  go Set.Poly.empty (p, sorts, vals)

(* The tries of one clause set, kept across the explorations of its leaves:
   per ground atom (by [key]), the atom's arguments and the outcome of each
   clause tried on it, the clause compared by physical identity, an accepted
   instance's body atoms with their keys.

   Why: the split explores each leaf from scratch, and the leaves of one
   check are states of one game a few moves apart, so their explorations
   reach mostly the same atoms; each try simplifies the clause's constraint
   at the atom (a tenth of a millisecond), and one check of a two-dimensional
   grid game spent 30 s in tries that earlier leaves had already made.

   Exact: a try is recorded only when [ask] was not called while it was
   made, and then its outcome is a function of the clause and the atom's
   arguments ([instance_exact] evaluates closed formulas and asks nothing
   else); it is reused only for the same clause and arguments structurally
   equal to the recorded ones.  So a reused outcome is the one a new try
   would compute, and the exploration -- the budget spent, the atoms reached,
   the instances recorded -- is the one without the record. *)
type tries =
  ( string,
    Term.t list
    * (clause
      * [ `Refuted | `Unknown | `Accepted of (string * atom) list ])
      list
      ref )
  Hashtbl.t

let create_tries () : tries = Hashtbl.create (module String)

(* the argument lists [a] and [b] are the same values: structurally equal, an
   argument that cannot be compared structurally counting as different *)
let same_args a b =
  phys_equal a b
  || (try Stdlib.( = ) a b
      with exn when not (Common.Timer.is_async exn) -> false)

(* [derive_smallest ~ask ~budget ~memo by_head atom]: a derivation of the ground
   [atom] from the clauses [by_head] with the fewest nodes counted as a tree,
   among the clause instances explored, or [None].

   Explored: the ground atoms reachable from [atom] through clause instances,
   breadth first, each atom's clauses tried once ([instance], as by [derive]);
   [budget] counts these tries and exploration stops when it runs out.  An
   atom with an accepted body-free instance stops there: its other clauses
   are not tried.  That loses no least derivation -- in a least tree such an
   atom is a leaf, since replacing its subtree by the leaf would make the tree
   smaller -- and it keeps the exploration to the atoms a least tree can
   use: on an elevator check, a move its constraint settles is not followed
   into the states it leads to.  Then a
   derivation of least tree size is computed bottom up over the explored
   instances, as Knuth's generalisation of Dijkstra's algorithm to grammars
   (D. E. Knuth, A generalization of Dijkstra's algorithm, Information
   Processing Letters 6(1), 1977): an instance's size is one plus its body
   atoms' sizes, an atom's the least over its instances, and atoms are
   settled in order of size, an instance becoming available when all its body
   atoms are settled.  Sizes saturate at [Int.max_value].

   Postcondition: the returned tree's nodes are instances [instance] accepted
   (so each is re-checked as by [derive]), every node's children are its
   clause's body atoms in order, and no atom is its own descendant (a node is
   settled after its children, at a larger size).  Over the explored
   instances the atom is derivable iff a tree is returned, and the tree has
   the least size of any derivation built from them; in particular an atom
   with an accepted body-free instance is a leaf.  Each settled atom is one
   node, shared by all its parents, so building and [size] take time linear
   in the explored instances however large the tree is.  [memo] holds the
   nodes built so far and may be shared between calls on the same clauses: an
   atom found there is reused as it is (a derivation of it, least over the
   instances explored when it was built), so that one call's tree and
   another's never hold two nodes for one atom.  [tries], when given, holds
   the clause instances tried so far on the same clauses ([tries] above): a
   try found there is not made again, which changes nothing but the time.

   Returns [`Found] with the tree, [`Underivable] when no derivation was found
   and the exploration was complete -- every try of every explored atom was
   accepted or refuted by [instance_exact] and none was cut by [budget] --
   and [`Not_found] otherwise.  [`Underivable] is a proof that [atom] is not
   derivable from the clauses: were it derivable, a least derivation would
   exist, every node of it an atom the exploration reached (by induction from
   the root: an explored atom's instance in the tree is the one ground
   instance its clause has there, which a complete exploration tried and
   accepted, so its body atoms were explored -- and an atom stopped at its
   body-free instance is a leaf of any least tree), so the settling would
   have reached [atom].  [`Not_found] proves nothing.

   Why: [derive] keeps the first derivation its depth-first search meets and
   remembers no failure, so on a check whose step conjoins one atom per move
   of a branching player it both explores the same atoms along many paths
   and returns a tree over every move: twenty million nodes on one check,
   where a move its constraint settles needs none. *)
(* What the last [derive_smallest] call explored, for a census line: the atoms
   reached, the tries [instance_exact] answered [`Unknown], and whether the
   budget cut the exploration.  Read nowhere but in reports. *)
let last_smallest_stats = ref (0, 0, false)

(* The number of [derive_smallest] explorations whose attempt budget ran out
   before their queue was empty (their [cut]), since the program started.  A
   caller that wants to know whether some exploration of a given stretch was
   cut compares two readings. *)
let smallest_cuts = ref 0

(* The number of [derive_smallest] explorations, since the program started,
   that reached an atom outside their literal box ([escapes] below), whether
   or not they were stopped there.  Read as [smallest_cuts] is. *)
let smallest_escapes = ref 0

(* [literal_bound clauses]: the largest absolute value of an integer literal
   anywhere in [clauses] -- constraints, head and body arguments, so the
   arguments of every leaf of a ground-goal check -- and at least 1; [None]
   when the clauses cannot be read (then no box is used).

   The box [-m, m] it gives is the region a game whose positions are bounded
   by guards against its literals stays in.  Why: the smallest-derivation
   exploration of a game whose positions are unbounded never empties its
   queue, so a pass at a large attempt budget spends the whole budget and
   keeps every atom it reached; on a factorial loop the values in the atoms
   grow without bound, and one pass at 200,000 tries per leaf ran for 77 s at
   about 30 MB/s.  An atom outside the box is the observation that the game
   explored is not one whose positions the guards bound by its literals. *)
let literal_bound clauses =
  let m = ref Z.one in
  let note n = if Z.gt (Z.abs n) !m then m := Z.abs n in
  let rec term t =
    match t with
    | Term.FunApp (T_int.Int n, [], _) -> note n
    | Term.FunApp (_, args, _) -> List.iter args ~f:term
    | _ -> ()
  in
  let atom (_, _, args) = List.iter args ~f:term in
  try
    List.iter clauses ~f:(fun c ->
        Option.iter c.head ~f:atom;
        List.iter c.body ~f:atom;
        Set.iter (Formula.funsyms_of c.constr) ~f:(function
          | T_int.Int n -> note n
          | _ -> ()));
    Some !m
  with exn when not (Common.Timer.is_async exn) -> None

(* [escapes m args]: some argument holds an integer literal of absolute value
   above [m] *)
let escapes m args =
  let rec term t =
    match t with
    | Term.FunApp (T_int.Int n, [], _) -> Z.gt (Z.abs n) m
    | Term.FunApp (_, args, _) -> List.exists args ~f:term
    | _ -> false
  in
  List.exists args ~f:term

(* An instance's body atoms, each once, by their interned ids in increasing
   order: what the settling counts down and the stop at the root waits on.
   The order is immaterial: each instance contributes a body atom to a
   waiting or parent list at most once, and those lists are built in
   instance order. *)
let distinct_ids body_ids = List.dedup_and_sort ~compare:Int.compare body_ids

(* (size, instance index) pairs ordered by size, then index -- the order the
   polymorphic compare gives an int pair -- and a binary min-heap of them,
   the settling's priority queue.  [pop] returns the least pair under that
   order, so on distinct pairs the pops come in the order a set's [min_elt]
   and [remove] would give them. *)
module Size_index = struct
  let less (s1, i1) (s2, i2) = s1 < s2 || (s1 = s2 && i1 < i2)

  module Heap = struct
    type t = { mutable data : (int * int) array; mutable size : int }

    let create () = { data = Array.create ~len:16 (0, 0); size = 0 }

    let push h x =
      if h.size = Array.length h.data then (
        let d = Array.create ~len:(2 * h.size) (0, 0) in
        Array.blit ~src:h.data ~src_pos:0 ~dst:d ~dst_pos:0 ~len:h.size;
        h.data <- d);
      (* sift up *)
      let rec up j =
        if j > 0 then
          let p = (j - 1) / 2 in
          if less x h.data.(p) then (
            h.data.(j) <- h.data.(p);
            up p)
          else h.data.(j) <- x
        else h.data.(j) <- x
      in
      up h.size;
      h.size <- h.size + 1

    let pop h =
      if h.size = 0 then None
      else
        let top = h.data.(0) in
        h.size <- h.size - 1;
        let n = h.size in
        if n > 0 then (
          let x = h.data.(n) in
          (* sift down *)
          let rec down j =
            let l = (2 * j) + 1 in
            if l >= n then h.data.(j) <- x
            else
              let c =
                if l + 1 < n && less h.data.(l + 1) h.data.(l) then l + 1 else l
              in
              if less h.data.(c) x then (
                h.data.(j) <- h.data.(c);
                down c)
              else h.data.(j) <- x
          in
          down 0);
        Some top
  end
end

let derive_smallest ?(stop_at_root = false) ?tries ?box ~ask ~budget ~memo
    by_head ((p0, sorts0, vals0) : atom) =
  let unknown_tries = ref 0 and cut = ref false in
  (* [box = Some (m, stop)]: an atom first reached through an accepted
     instance with an integer argument above [m] in absolute value is an
     escape ([escapes]); it is counted in [smallest_escapes] (once per call),
     and with [stop] the exploration ends there, as if the attempt budget
     had run out at that try: [cut] and not complete.  Only when the search
     gives up changes, never what an accepted instance is, so a returned tree
     is the same kind of derivation and [`Underivable] is still read only
     from a complete exploration (one with no stop). *)
  let escaped = ref false and halted = ref false in
  let module H = Hashtbl in
  let add a b = if a > Int.max_value - b then Int.max_value else a + b in
  (* instances: (head id, head atom, clause, body atoms with their keys, body
     ids in body order, distinct body ids) *)
  let insts = ref [] in
  (* each clause with [head_fixes] of it, computed once per call rather than
     once per try *)
  let by_head_fixes =
    Map.Poly.map by_head ~f:(List.map ~f:(fun c -> (c, head_fixes c)))
  in
  (* each head predicate's clauses split into the body-free ones and the
     rest, each part in [by_head]'s order: the partition the exploration
     makes of an atom's clauses, a function of the predicate alone, so made
     once per predicate here rather than once per explored atom; keyed by
     name in a string table rather than looked up in a polymorphic map *)
  let clauses_of_pred = H.create (module String) in
  Map.Poly.iteri by_head_fixes ~f:(fun ~key ~data ->
      H.set clauses_of_pred ~key
        ~data:(List.partition_tf data ~f:(fun (c, _) -> List.is_empty c.body)));
  (* every try of every explored atom refuted or accepted, none cut by the
     budget: the explored instances are then all the ground instances whose
     heads are explored atoms (up to the clauses a leaf's body-free instance
     made untried) *)
  let complete = ref true in
  (* The atoms explored, interned: [ids] maps an atom's key to its id, ids
     are given in the order atoms are first reached (the root is 0), and
     [keys] holds each id's key.  Every table of this call below is keyed by
     id, so a key string is hashed once, when it is interned, rather than
     once per table it is looked up in; [memo] and [tries], shared with other
     calls, stay keyed by string.  An atom is interned exactly when the
     string-keyed version added it to its table of explored atoms, so the
     queue, and with it the exploration, is the same. *)
  let ids = H.create (module String) in
  let keys = ref (Array.create ~len:64 "") in
  let n_ids = ref 0 in
  (* [intern k]: [Some id] for a key not seen before, [None] otherwise *)
  let intern k =
    match H.find ids k with
    | Some _ -> None
    | None ->
        let id = !n_ids in
        incr n_ids;
        if id = Array.length !keys then (
          let a = Array.create ~len:(2 * id) "" in
          Array.blit ~src:!keys ~src_pos:0 ~dst:a ~dst_pos:0 ~len:id;
          keys := a);
        !keys.(id) <- k;
        H.set ids ~key:k ~data:id;
        Some id
  in
  let id_exn k = H.find_exn ids k in
  let queue = Queue.create () in
  let k0 = key p0 vals0 in
  let id0 = Option.value_exn (intern k0) in
  (* [stop_at_root]: the atoms derivable from the instances accepted so far,
     kept incrementally as for propositional Horn clauses (per instance the
     number of its distinct body atoms not yet derivable, per atom the
     instances waiting on it), and the exploration stopped as soon as the
     root is derivable -- or at once when [memo] already holds the root, whose
     node is then returned as it would be after any exploration.
     Derivability over the explored instances only grows as exploration goes
     on, so the root is derivable at some point of the full exploration iff
     it is at its end: the outcome ([`Found], [`Underivable], [`Not_found]) is
     the one the full exploration gives, never more tries are spent, and only
     the tree returned may differ -- the least over the instances explored
     until the root became derivable, still a derivation every node of which
     an accepted instance.  [`Underivable] needs no change: it is read only
     when the root never became derivable, so the exploration ran to its
     end exactly as without the field. *)
  (* Indexed by atom id ([derivable], [waiting]) and by instance number
     ([waiting_count]), grown on demand: ids and instance numbers are dense
     from 0, so an array cell stands for a table entry; [waiting]'s lists are
     consed in insertion order, the order a table's [add_multi] keeps. *)
  let derivable = ref (Array.create ~len:64 false) in
  let waiting = ref (Array.create ~len:64 []) in
  let waiting_count = ref (Array.create ~len:64 0) in
  let grow a i default =
    if i >= Array.length !a then (
      let b = Array.create ~len:(max (i + 1) (2 * Array.length !a)) default in
      Array.blit ~src:!a ~src_pos:0 ~dst:b ~dst_pos:0 ~len:(Array.length !a);
      a := b)
  in
  let is_derivable k = k < Array.length !derivable && !derivable.(k) in
  let n_insts = ref 0 in
  let rooted = ref (stop_at_root && H.mem memo k0) in
  let rec mark k =
    if not (is_derivable k) then (
      grow derivable k false;
      !derivable.(k) <- true;
      if k = id0 then rooted := true;
      let ws = if k < Array.length !waiting then !waiting.(k) else [] in
      List.iter ws ~f:(fun (j, hk) ->
          let r = !waiting_count.(j) - 1 in
          !waiting_count.(j) <- r;
          if r = 0 then mark hk);
      if k < Array.length !waiting then !waiting.(k) <- [])
  in
  (* [bks]: the instance's distinct body ids ([distinct_ids]) *)
  let note_instance hk bks =
    let j = !n_insts in
    incr n_insts;
    let pending = List.filter bks ~f:(fun bk -> not (is_derivable bk)) in
    if List.is_empty pending then mark hk
    else (
      grow waiting_count j 0;
      !waiting_count.(j) <- List.length pending;
      List.iter pending ~f:(fun bk ->
          grow waiting bk [];
          !waiting.(bk) <- (j, hk) :: !waiting.(bk)))
  in
  Queue.enqueue queue (id0, (p0, sorts0, vals0));
  let rec explore () =
    match if !rooted || !halted then None else Queue.dequeue queue with
    | None -> ()
    | Some (id, (p, sorts, vals)) ->
        let k = !keys.(id) in
        (* body-free clauses first: an accepted body-free instance makes the
           atom a leaf of size 1, the least any derivation has, so the atom's
           other clauses are not tried and their body atoms not explored (a
           least tree never uses them, see below) *)
        let free, rest =
          Option.value ~default:([], [])
            (H.find clauses_of_pred (Ident.name_of_pvar p))
        in
        (* [instance_exact ~ask c vals], an accepted instance's body atoms
           with their keys; reused from [tries] or recorded there *)
        (* the atom's record in [tries], looked up (or made) at its first
           try and shared by its later tries: every try of one atom looks up
           the same key with the same arguments, so each would find what the
           first found or made *)
        let entry =
          lazy
            (match tries with
            | None -> None
            | Some tries -> (
                match Hashtbl.find tries k with
                | Some (vals', outcomes) ->
                    if same_args vals' vals then Some outcomes else None
                | None ->
                    let outcomes = ref [] in
                    Hashtbl.set tries ~key:k ~data:(vals, outcomes);
                    Some outcomes))
        in
        let try_on (c, fixes) vals =
          let fresh () =
            let asked = ref false in
            let ask phi =
              asked := true;
              ask phi
            in
            let r =
              match instance_exact ~fixes ~ask c vals with
              | (`Refuted | `Unknown) as r -> r
              | `Accepted argss ->
                  `Accepted
                    (List.map2_exn c.body argss
                       ~f:(fun (q, qsorts, _) qargs ->
                         (key q qargs, (q, qsorts, qargs))))
            in
            (r, not !asked)
          in
          match Lazy.force entry with
          | None -> fst (fresh ())
          | Some outcomes -> (
              match List.Assoc.find !outcomes c ~equal:phys_equal with
              | Some r -> r
              | None ->
                  let r, recordable = fresh () in
                  if recordable then outcomes := (c, r) :: !outcomes;
                  r)
        in
        let try_clause ((c, _) as cf) =
          if !halted then false
          else if !budget <= 0 then (
            complete := false;
            cut := true;
            false)
          else (
            decr budget;
            match try_on cf vals with
            | `Refuted -> false
            | `Unknown ->
                complete := false;
                incr unknown_tries;
                false
            | `Accepted body ->
                let body_ids =
                  List.map body ~f:(fun (bk, b) ->
                      match intern bk with
                      | Some bid ->
                          (match box with
                          | Some (m, stop) ->
                              let _, _, bargs = b in
                              if escapes m bargs then (
                                escaped := true;
                                if stop then (
                                  complete := false;
                                  cut := true;
                                  halted := true))
                          | None -> ());
                          Queue.enqueue queue (bid, b);
                          bid
                      | None -> id_exn bk)
                in
                let bks = distinct_ids body_ids in
                insts := (id, (p, sorts, vals), c, body, body_ids, bks) :: !insts;
                if stop_at_root then note_instance id bks;
                true)
        in
        if not (List.exists free ~f:try_clause) then
          List.iter rest ~f:(fun c -> ignore (try_clause c : bool));
        explore ()
  in
  explore ();
  last_smallest_stats := (!n_ids, !unknown_tries, !cut);
  if !cut then incr smallest_cuts;
  if !escaped then incr smallest_escapes;
  let insts = Array.of_list (List.rev !insts) in
  (* per instance, the number of distinct body atoms not yet settled; per
     atom, the instances it is a body atom of (once each) *)
  let remaining =
    Array.map insts ~f:(fun (_, _, _, _, _, bks) -> List.length bks)
  in
  (* [parents] and [settled] indexed by atom id (dense from 0, fewer than
     [!n_ids]); [parents]' lists consed in instance order, the order a
     table's [add_multi] keeps; [settled_at.(id)] the instance that settled
     the atom and [settled_size.(id)] its size, [-1] while unsettled *)
  let parents = Array.create ~len:!n_ids [] in
  Array.iteri insts ~f:(fun i (_, _, _, _, _, bks) ->
      List.iter bks ~f:(fun bk -> parents.(bk) <- i :: parents.(bk)));
  let settled_size = Array.create ~len:!n_ids (-1) in
  let settled_at = Array.create ~len:!n_ids (-1) in
  let is_settled id = settled_size.(id) >= 0 in
  (* the instances offered, by size then index: a priority queue.  Each
     instance is offered at most once (when its count of unsettled body atoms
     reaches zero), so the pairs are distinct and the order on them is total:
     any priority queue pops them in the one same order *)
  let heap = Size_index.Heap.create () in
  let offer i =
    let _, _, _, _, body_ids, _ = insts.(i) in
    let s =
      List.fold body_ids ~init:1 ~f:(fun acc bk ->
          add acc settled_size.(bk))
    in
    Size_index.Heap.push heap (s, i)
  in
  (* Settling stops once the root is settled: [build] reads [settled] only
     at the root and at the body atoms of settled instances, all of which
     were settled before the root (an instance is offered only after its body
     atoms are settled), and the outcome reads only whether the root is
     settled.  It is skipped when [memo] holds the root, whose node is then
     returned without reading [settled]. *)
  let rec settle () =
    if not (is_settled id0) then
      match Size_index.Heap.pop heap with
      | None -> ()
      | Some (s, i) ->
          let hk, _, _, _, _, _ = insts.(i) in
          if not (is_settled hk) then (
            settled_size.(hk) <- s;
            settled_at.(hk) <- i;
            List.iter parents.(hk) ~f:(fun j ->
                remaining.(j) <- remaining.(j) - 1;
                if remaining.(j) = 0 then offer j));
          settle ()
  in
  if not (H.mem memo k0) then (
    Array.iteri remaining ~f:(fun i r -> if r = 0 then offer i);
    settle ());
  let rec build (k, id) =
    match H.find memo k with
    | Some n -> n
    | None ->
        let i = settled_at.(id) in
        let _, (p, sorts, vals), c, body, body_ids, _ = insts.(i) in
        let n =
          { pvar = p; sorts; args = vals; clause = c;
            children =
              List.map2_exn body body_ids ~f:(fun (bk, _) bid ->
                  build (bk, bid)) }
        in
        H.set memo ~key:k ~data:n;
        n
  in
  match H.find memo k0 with
  | Some n -> `Found n
  | None ->
      if is_settled id0 then `Found (build (k0, id0))
      else if !complete then `Underivable
      else `Not_found

type outcome =
  | Not_shape  (** the goals are not over ground atoms of layer clauses *)
  | Undecided of { leaves : int; derived : int; tried : int }
      (** no goal has every leaf of some body derived; [tried] leaves were
          searched (fewer than [leaves] only under [stop_when_doomed]) *)
  | Derived of { leaves : int; derived : int; root : node }
      (** [root] derives [query!0] by a goal clause *)
  | Underivable of { leaves : int; proven : int; asked : int }
      (** [proven] leaves were shown underivable by [split]'s [prove], and with
          them false and every other leaf true no goal is derived: the query is
          not derivable ([asked] proofs were attempted) *)
  | Won of { leaves : int; proved : int }
      (** only under [~smallest]: no goal is derivable even with every leaf
          not [proved] underivable taken as derivable, so the query is not
          derivable from the clauses *)

let by_head_of clauses =
  Map.Poly.of_alist_multi
  @@ List.filter_map clauses ~f:(fun c ->
      Option.map c.head ~f:(fun (p, _, _) -> (Ident.name_of_pvar p, c)))

(* [split ?stop_when_doomed ~ask ~budget clauses]: decide the query of
   [clauses] through its ground layer, each leaf by [derive] under its own
   [budget] of attempts.  Leaves are tried in the order they first occur.
   Without [stop_when_doomed] all are tried, so the counts report how many
   were derived.  With it, the search stops as soon as the leaves not found so
   far make the query underivable even if every leaf not yet tried were
   derived: the propositional least model over the layer, with each failed
   leaf false and every other leaf true, derives no goal ([doomed]).

   Exact (the outcome is the same, only [tried] and [derived] change): the
   leaves found derived are a subset of those not failed, and the least model
   is monotone in its leaves, so a goal that the final model derives is
   derived by the optimistic model too; when the optimistic model derives no
   goal, the outcome without the stop is [Undecided] as well.  Why: on a check
   with 523 named alternatives of two leaves each, none of which the search
   derives, every leaf costs its whole attempt budget (5000 clause instances,
   each simplifying the clause's constraint), and the split ran past a 60 s
   run while the first alternative's two failures already decided it.

   With [prove = (prove, rounds)], a split that derives no goal goes on to the
   converse: [prove atom secs] is [true] only when [atom] is shown not
   derivable in the least model of [clauses] (asked of a solver within [secs]
   seconds), and the leaves the search did not derive are asked in rounds,
   round [i] at the budget [rounds i] until it is [None], each leaf until it is
   proven.  As soon as the proven leaves, false, with every other leaf true,
   make the least model over the layer derive no goal, the outcome is
   [Underivable]: the query is not derivable, since the true leaves are a
   subset of the leaves not proven and the least model is monotone in them
   (the claim above, read in the other direction).  A proof not found says
   nothing; the outcome is then [Undecided] as without [prove]. *)
let split ?(stop_when_doomed = false) ?(smallest = false)
    ?(stop_at_root = false) ?(share_tries = true) ?budget_after_cut ?literal_box
    ?prove ~ask ~budget clauses =
  (* [literal_box], read only under [smallest]: [`Record], each leaf's
     exploration counts an atom outside the clauses' literal box
     ([literal_bound]) in [smallest_escapes]; [`Stop], it also ends there
     ([derive_smallest]'s [box]).  [None]: no box. *)
  let box =
    match literal_box with
    | None -> None
    | Some mode ->
        Option.map (literal_bound clauses) ~f:(fun m ->
            (m, match mode with `Stop -> true | `Record -> false))
  in
  (* [budget_after_cut]: once a leaf's smallest exploration has been cut by
     [budget], the later leaves of this split are searched with this budget
     instead; [None], every leaf with [budget].  Only when a search gives up
     changes. *)
  let leaf_budget = ref budget in
  let goals = List.filter clauses ~f:(fun c -> Option.is_none c.head) in
  let by_head = by_head_of clauses in
  (* [smallest]: each leaf is derived by [derive_smallest] rather than
     [derive]; which derivation is found, and whether one is found within
     [budget], change -- every node is an instance [instance] accepted, as
     without it -- and a leaf can be proved underivable, which only the
     outcome [Won] reads.  The layer's least model below reads the derived
     leaves only, so it is computed the same way either way. *)
  let is_layer name =
    match Map.Poly.find by_head name with
    | Some (c :: _ as cs) ->
        Option.value_map c.head ~default:false ~f:(fun (_, _, args) ->
            List.is_empty args)
        && List.for_all cs ~f:closed_clause
    | _ -> false
  in
  if List.is_empty goals || not (List.for_all goals ~f:closed_clause) then
    Not_shape
  else
    (* the layer predicates reachable from the goals, and the leaves *)
    let layer = Hash_set.create (module String) in
    let leaves = ref [] in
    let leaf_keys = Hash_set.create (module String) in
    let rec visit_body body =
      List.iter body ~f:(fun (p, sorts, args) ->
          let name = Ident.name_of_pvar p in
          if is_layer name then (
            if not (Hash_set.mem layer name) then (
              Hash_set.add layer name;
              List.iter (Map.Poly.find_exn by_head name) ~f:(fun c ->
                  visit_body c.body)))
          else
            match Option.all (List.map args ~f:value) with
            | None -> raise Exit
            | Some vals ->
                let k = key p vals in
                if not (Hash_set.mem leaf_keys k) then (
                  Hash_set.add leaf_keys k;
                  leaves := (k, (p, sorts, vals)) :: !leaves))
    in
    match List.iter goals ~f:(fun c -> visit_body c.body) with
    | exception Exit -> Not_shape
    | () when List.is_empty !leaves -> Not_shape
    | () -> (
        let leaves = List.rev !leaves in
        let memo = Hashtbl.create (module String) in
        (* [share_tries]: the clause instances tried under [smallest], shared
           by the leaves' explorations ([tries]); the outcome is the same
           without it *)
        let tries = if share_tries then Some (create_tries ()) else None in
        let derived = Hashtbl.create (module String) in
        let failed = Hash_set.create (module String) in
        (* under [smallest]: the leaves [derive_smallest] proved underivable,
           a subset of [failed] *)
        let proved = Hash_set.create (module String) in
        (* Each goal and layer clause as its constraint's truth and its body:
           a layer predicate by name, or a leaf by key ([None]: an atom whose
           arguments do not evaluate, which no model makes true). *)
        let body_items c =
          List.map c.body ~f:(fun (p, _, args) ->
              let name = Ident.name_of_pvar p in
              if Hash_set.mem layer name then `Layer name
              else
                match Option.all (List.map args ~f:value) with
                | Some vals -> `Leaf (Some (key p vals))
                | None -> `Leaf None)
        in
        let opt_holds c = Formula.is_true (Evaluator.simplify c.constr) in
        let opt_layer =
          lazy
            (Hash_set.to_list layer
            |> List.concat_map ~f:(fun name ->
                List.filter_map (Map.Poly.find_exn by_head name) ~f:(fun c ->
                    if opt_holds c then Some (name, body_items c) else None)))
        in
        let opt_goals =
          lazy
            (List.filter_map goals ~f:(fun c ->
                 if opt_holds c then Some (body_items c) else None))
        in
        (* the least model with every leaf of [off] false and every other
           leaf true derives no goal *)
        let doomed_by off =
          let model = Hash_set.create (module String) in
          let sat items =
            List.for_all items ~f:(function
              | `Layer name -> Hash_set.mem model name
              | `Leaf (Some k) -> not (Hash_set.mem off k)
              | `Leaf None -> false)
          in
          let rec fix () =
            let changed = ref false in
            List.iter (Lazy.force opt_layer) ~f:(fun (name, items) ->
                if (not (Hash_set.mem model name)) && sat items then (
                  Hash_set.add model name;
                  changed := true));
            if !changed then fix ()
          in
          fix ();
          not (List.exists (Lazy.force opt_goals) ~f:sat)
        in
        (* the optimistic least model derives no goal *)
        let doomed () = doomed_by failed in
        let tried = ref 0 in
        (try
           List.iter leaves ~f:(fun (k, atom) ->
               incr tried;
               match
                 if smallest then (
                   let cuts0 = !smallest_cuts in
                   let r =
                     derive_smallest ~stop_at_root ?tries ?box ~ask
                       ~budget:(ref !leaf_budget) ~memo by_head atom
                   in
                   (match budget_after_cut with
                   | Some b when !smallest_cuts > cuts0 -> leaf_budget := b
                   | _ -> ());
                   r)
                 else
                   match derive ~ask ~budget:(ref budget) ~memo by_head atom with
                   | Some n -> `Found n
                   | None -> `Not_found
               with
               | `Found n -> Hashtbl.set derived ~key:k ~data:n
               | (`Underivable | `Not_found) as r ->
                   (match r with
                   | `Underivable -> Hash_set.add proved k
                   | `Not_found -> ());
                   Hash_set.add failed k;
                   if stop_when_doomed && doomed () then raise Exit)
         with Exit -> ());
        (* [smallest]: the query is not derivable when, with every leaf proved
           underivable false and every other leaf true -- whether found,
           failed or untried -- no goal is derivable over the layer.  Unlike
           [doomed], a layer or goal clause whose constraint simplifies to
           neither [true] nor [false], and a body atom whose arguments do not
           evaluate, count as holding: the model only over-approximates the
           least one.  Sound by the decomposition above: a derivation of the
           query is one over the layer with derivations of its leaves, and
           the leaves it uses are all derivable, so none proved underivable. *)
        let won () =
          let model = Hash_set.create (module String) in
          let holds_opt c =
            not (Formula.is_false (Evaluator.simplify c.constr))
          in
          let item_opt (p, _, args) =
            let name = Ident.name_of_pvar p in
            if Hash_set.mem layer name then Hash_set.mem model name
            else
              match Option.all (List.map args ~f:value) with
              | Some vals -> not (Hash_set.mem proved (key p vals))
              | None -> true
          in
          let rec fix () =
            let changed = ref false in
            Hash_set.iter layer ~f:(fun name ->
                if
                  (not (Hash_set.mem model name))
                  && List.exists (Map.Poly.find_exn by_head name) ~f:(fun c ->
                      holds_opt c && List.for_all c.body ~f:item_opt)
                then (
                  Hash_set.add model name;
                  changed := true));
            if !changed then fix ()
          in
          fix ();
          not
            (List.exists goals ~f:(fun c ->
                 holds_opt c && List.for_all c.body ~f:item_opt))
        in
        let tried = !tried in
        let n_leaves = List.length leaves
        and n_derived = Hashtbl.length derived in
        (* the propositional least model over the layer *)
        let holds c = Formula.is_true (Evaluator.simplify c.constr) in
        let layer_nodes = Hashtbl.create (module String) in
        let node_of (p, _, args) =
          let name = Ident.name_of_pvar p in
          if Hash_set.mem layer name then Hashtbl.find layer_nodes name
          else
            match Option.all (List.map args ~f:value) with
            | Some vals -> Hashtbl.find derived (key p vals)
            | None -> None
        in
        let children_of c = Option.all (List.map c.body ~f:node_of) in
        let rec fix () =
          let changed = ref false in
          Hash_set.iter layer ~f:(fun name ->
              if not (Hashtbl.mem layer_nodes name) then
                List.iter (Map.Poly.find_exn by_head name) ~f:(fun c ->
                    if (not (Hashtbl.mem layer_nodes name)) && holds c then
                      match (children_of c, c.head) with
                      | Some children, Some (p, sorts, args) ->
                          Hashtbl.set layer_nodes ~key:name
                            ~data:
                              { pvar = p; sorts; args; clause = c; children };
                          changed := true
                      | _ -> ()));
          if !changed then fix ()
        in
        fix ();
        match
          List.find_map goals ~f:(fun c ->
              if holds c then
                Option.map (children_of c) ~f:(fun children ->
                    {
                      pvar = query_pvar;
                      sorts = [];
                      args = [];
                      clause = c;
                      children;
                    })
              else None)
        with
        | Some root -> Derived { leaves = n_leaves; derived = n_derived; root }
        | None when smallest && won () ->
            Won { leaves = n_leaves; proved = Hash_set.length proved }
        | None -> (
            let undecided () =
              Undecided { leaves = n_leaves; derived = n_derived; tried }
            in
            match prove with
            | None -> undecided ()
            | Some (prove, rounds) ->
                (* the leaves the search did not derive, asked in rounds:
                   [rounds i] is round [i]'s budget per leaf, [None] ending
                   them *)
                let candidates =
                  List.filter leaves ~f:(fun (k, _) ->
                      not (Hashtbl.mem derived k))
                in
                let proven = Hash_set.create (module String) in
                let asked = ref 0 in
                let rec round i =
                  match rounds i with
                  | None -> undecided ()
                  | Some secs ->
                      let won =
                        List.exists candidates ~f:(fun (k, atom) ->
                            (not (Hash_set.mem proven k))
                            && (incr asked;
                                if prove atom secs then (
                                  Hash_set.add proven k;
                                  doomed_by proven)
                                else false))
                      in
                      if won then
                        Underivable
                          {
                            leaves = n_leaves;
                            proven = Hash_set.length proven;
                            asked = !asked;
                          }
                      else if
                        List.for_all candidates ~f:(fun (k, _) ->
                            Hash_set.mem proven k)
                      then undecided ()
                      else round (i + 1)
                in
                round 0))

let atom_formula (p, sorts, args) =
  Formula.mk_atom (Atom.mk_pvar_app p sorts args)

(* The clause [c] as the derivation states it, with [head] its head atom. *)
let clause_formula c head =
  Formula.mk_forall_if_bounded c.senv
  @@ Formula.mk_imply
       (Formula.and_of (List.map c.body ~f:atom_formula @ [ c.constr ]))
       head

let fvar name ts =
  Term.mk_fvar_app (Ident.Tvar name)
    (List.map ts ~f:Term.sort_of)
    T_bool.SBool ts

let asserted phi = fvar "asserted" [ T_bool.of_formula phi ]

(* With [own_heads], each clause is stated with its own head atom, so the
   stated clause is the clause of the system and the node's ground conclusion
   is the instance of it the derivation takes (the head's variables are bound
   by the clause's universal closure, the body's through them).  Without it
   the conclusion replaces the head: that stated clause holds the body's
   variables apart from the head's ground arguments, so anything that reads
   the clause instance as a relation between the conclusion and the premises
   (a chain-pair region) loses that relation.  A goal has no head and is
   stated with the conclusion [query!0] either way.  [stated_clause] is the
   clause [hyper_res] asserts at the node [n]. *)
let stated_clause ~own_heads n =
  let head =
    match n.clause.head with
    | Some a when own_heads -> atom_formula a
    | _ -> atom_formula (n.pvar, n.sorts, n.args)
  in
  clause_formula n.clause head

(* [hyper_res ~own_heads n]: the derivation rooted at [n] as a [hyper-res]
   term, built once per node.  The search's memo returns one node per ground
   atom, so a node used by several parents is reached along several paths; a
   term built per path made the derivation a tree in memory, as large as the
   number of paths (a counter-play with a few hundred distinct nodes was a
   term of several gigabytes and took tens of seconds to build).  Here a node
   met again (the same node, physically) gets the term built for it the first
   time, so the result is a graph sharing what [n] shares.
   Postcondition: the result is structurally equal to the term built path by
   path (the same function of the same node), so a reader that walks it as a
   tree sees exactly the same term; only its physical sharing differs.
   Precondition: none beyond [n] being a finite acyclic node graph, which the
   search guarantees (it never repeats an atom along a path). *)
let hyper_res ~own_heads root =
  let memo = Hashtbl.create (module String) in
  let rec go n =
    let k = key n.pvar n.args in
    let kept = Option.value ~default:[] (Hashtbl.find memo k) in
    match List.Assoc.find kept n ~equal:phys_equal with
    | Some t -> t
    | None ->
        let conc = atom_formula (n.pvar, n.sorts, n.args) in
        let t =
          fvar "hyper-res"
            (asserted (stated_clause ~own_heads n)
             :: List.map n.children ~f:go
            @ [ T_bool.of_formula conc ])
        in
        Hashtbl.set memo ~key:k ~data:((n, t) :: kept);
        t
  in
  go root

(* [to_cex ?own_heads root]: the derivation rooted at a node deriving
   [query!0], in the form Spacer reports a refutation of a CHC query; see
   [hyper_res] for [own_heads] (default [false]). *)
let to_cex ?(own_heads = false) root =
  let q = atom_formula (query_pvar, [], []) in
  Formula.eq
    (fvar "mp"
       [
         hyper_res ~own_heads root;
         asserted (Formula.mk_imply q (Formula.mk_false ()));
         T_bool.of_formula (Formula.mk_false ());
       ])
    (T_bool.mk_true ())

(* The size of a derivation, its nodes counted with repetition, saturating at
   [Int.max_value].  Computed once per distinct conclusion (see [shared_size]):
   the search's memo makes every occurrence of a ground atom the same node, so
   a subtree's size is a function of its conclusion, and counting it by
   walking the tree took as long as the tree is large (twenty million nodes
   on one check). *)
let size n =
  let memo = Hashtbl.create (module String) in
  let add a b = if a > Int.max_value - b then Int.max_value else a + b in
  let rec go n =
    let k = key n.pvar n.args in
    match Hashtbl.find memo k with
    | Some s -> s
    | None ->
        let s = List.fold n.children ~init:1 ~f:(fun acc c -> add acc (go c)) in
        Hashtbl.set memo ~key:k ~data:s;
        s
  in
  go n

(* The height of a derivation: the most nodes on a path from the root to a
   leaf (a leaf alone has height 1).  Memoised by conclusion as [size] is, so
   linear in the distinct conclusions.  Pre: the derivation is finite and
   acyclic, as every derivation the search builds is (a node is built only
   from children settled before it). *)
let height n =
  let memo = Hashtbl.create (module String) in
  let rec go n =
    let k = key n.pvar n.args in
    match Hashtbl.find memo k with
    | Some h -> h
    | None ->
        let h =
          1 + List.fold n.children ~init:0 ~f:(fun acc c -> Int.max acc (go c))
        in
        Hashtbl.set memo ~key:k ~data:h;
        h
  in
  go n

(* The number of distinct conclusions of a derivation: a ground atom derived
   once and used by several parents (the search's memo returns one node per
   ground atom) is counted once, so this is the size of the derivation as a
   graph, against [size]'s as a tree.  Linear in the graph: a conclusion
   already counted is not descended into again. *)
let shared_size n =
  let seen = Hash_set.create (module String) in
  let rec go n =
    let k = key n.pvar n.args in
    if not (Hash_set.mem seen k) then (
      Hash_set.add seen k;
      List.iter n.children ~f:go)
  in
  go n;
  Hash_set.length seen

(* [bounded_ask ?max ask]: [ask] behind a counter, and the counter.  Each
   call made while fewer than [max] calls have been passed on is passed to
   [ask] and counted; after that every call answers [None] without asking.
   [max = None] passes every call.  [None] is what [instance] reads as "no
   instance found", so a bound only removes derivations the search could
   find and never adds one: whatever is returned is still re-checked by
   evaluation. *)
let bounded_ask ?max ask =
  let n = ref 0 in
  let ask' phi =
    match max with
    | Some m when !n >= m -> None
    | _ ->
        incr n;
        ask phi
  in
  (ask', n)

(* [ask_z3 phi]: one model of [phi] from Z3, or [None] (unsatisfiable,
   undecided within 1 s, or an error).  The model is returned as the solver
   gave it, sorts included: its reader looks each variable up by name and
   sort, since a pooled context can offer a name at another sort. *)
let ask_z3 phi =
  try
    match
      Z3Smt.Z3interface.check_sat ~timeout:(Some 1000) ~id:None (get_fenv ())
        [ phi ]
    with
    | `Sat model -> Some model
    | _ -> None
  with exn when not (Common.Timer.is_async exn) -> None

(* [dump_smt2 file clauses]: write [clauses] to [file] as an SMT-LIB CHC
   system (one [declare-fun] per predicate, one universally closed assertion
   per clause, a goal's head [false]), so that the split can be replayed on
   them outside a solving run: read back by the CHC reader and turned into
   clauses again by [clauses_of_problem].  The clauses read back are the same
   system up to the reader's normalisation (names, clause order, the form of
   each constraint), which is what a replay that times the split needs.  A
   diagnostic aid: nothing in a solving run reads the file. *)
let dump_smt2 file clauses =
  (* no [let] aliases in the printed terms: the CHC reader takes a predicate
     application bound by a [let] for a term *)
  let alias = Z3.get_global_param "pp.min_alias_size" in
  let depth = Z3.get_global_param "pp.max_depth" in
  Z3.set_global_param "pp.min_alias_size" "1000000000";
  Z3.set_global_param "pp.max_depth" "1000000000";
  Exn.protect
    ~finally:(fun () ->
      Option.iter alias ~f:(Z3.set_global_param "pp.min_alias_size");
      Option.iter depth ~f:(Z3.set_global_param "pp.max_depth"))
    ~f:(fun () ->
  let ctx = Z3.mk_context [] in
  let dtenv = Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx (get_dtenv ()) in
  let sort_str s =
    Z3.Sort.to_string
    @@ Z3Smt.Z3interface.of_sort ctx dtenv s
  in
  let preds = Hashtbl.create (module String) in
  let note (p, sorts, _) =
    Hashtbl.set preds ~key:(Ident.name_of_pvar p) ~data:sorts
  in
  List.iter clauses ~f:(fun c ->
      Option.iter c.head ~f:note;
      List.iter c.body ~f:note);
  Out_channel.with_file file ~f:(fun oc ->
      fprintf oc "(set-logic HORN)\n";
      Hashtbl.iteri preds ~f:(fun ~key ~data ->
          fprintf oc "(declare-fun |%s| (%s) Bool)\n" key
            (String.concat_map_list ~sep:" " data ~f:sort_str));
      List.iter clauses ~f:(fun c ->
          let head =
            match c.head with
            | Some a -> atom_formula a
            | None -> Formula.mk_false ()
          in
          let phi =
            Formula.mk_imply
              (Formula.and_of (List.map c.body ~f:atom_formula @ [ c.constr ]))
              head
          in
          fprintf oc "(assert %s)\n"
            (Z3Smt.Z3interface.smtlib2_str_of_formula ~id:None ctx
               Map.Poly.empty dtenv
               (Formula.mk_forall_if_bounded c.senv phi)));
      fprintf oc "(check-sat)\n"))
