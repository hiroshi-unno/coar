(* The cone of influence of a set of Horn clauses: the clauses on which the
   derivability of a goal (a clause with no positive literal) depends.

   Read syntactically from the clauses' atoms, ignoring their pure parts:
   - [derivable] is the least set of unknowns such that a clause whose body
     unknowns are all in it puts its head unknown in it (an over-approximation
     of the unknowns some derivation reaches, since a pure part can only make
     a clause fire less often);
   - [needed] is the least set containing the body unknowns of every goal
     clause whose body is derivable, and the body unknowns of every definite
     clause whose head is needed and whose body is derivable.
   The cone is the goal clauses whose body is derivable and the definite
   clauses whose head is needed and whose body is derivable.

   Contract ([restrict]): for a set [cs] of Horn clauses (at most one
   positive literal each) over ordinary unknowns,
   (1) every derivation of a goal from [cs] uses only clauses of the cone --
       an atom of a derivation is derived, so its unknown is [derivable], and
       it is used towards the goal, so its unknown is [needed]; hence the cone
       has a derivation of a goal exactly when [cs] has, and a derivation
       found in the cone is one of [cs] clause by clause;
   (2) a solution [s] of the cone extends to a solution of [cs] by [lift]:
       an unknown of the cone keeps its value, a [derivable] unknown outside
       it becomes [true] and an underivable one [false].  A dropped clause
       either has an underivable body unknown (its body is [false]), or a
       derivable body and a head outside [needed], which is derivable and so
       [true]; a goal clause with a derivable body is never dropped.
   The pure parts are kept as they are, so (1) and (2) hold in every model of
   the background theory.  A clause with more than one positive literal is
   outside the contract, and [restrict] then returns the clauses unchanged. *)
open Core
open Common.Ext
open Logic

type stats = {
  clauses : int;
  goals : int;
  unknowns : int;
  derivable : int;
  needed : int;
  kept_clauses : int;
  kept_unknowns : int;
}

let heads ((_, ps, _, _) : Clause.t) = Set.Poly.map ps ~f:Term.pvar_of_atom
let bodies ((_, _, ns, _) : Clause.t) = Set.Poly.map ns ~f:Term.pvar_of_atom

(* the least fixpoint of [step] from [init], by rounds over the clauses: each
   round adds what the current set licenses, and a round adding nothing ends
   it; at most one round per unknown plus one *)
let fixpoint init step =
  let rec go s =
    let s' = step s in
    if Set.length s' = Set.length s then s else go s'
  in
  go init

let derivable (cs : Clause.t list) =
  fixpoint Set.Poly.empty (fun d ->
      List.fold cs ~init:d ~f:(fun d c ->
          if Set.is_subset (bodies c) ~of_:d then Set.union d (heads c) else d))

let needed ~derivable (cs : Clause.t list) =
  let fires c = Set.is_subset (bodies c) ~of_:derivable in
  let init =
    List.fold cs ~init:Set.Poly.empty ~f:(fun n c ->
        if Clause.is_goal c && fires c then Set.union n (bodies c) else n)
  in
  fixpoint init (fun n ->
      List.fold cs ~init:n ~f:(fun n c ->
          if
            (not (Clause.is_goal c))
            && fires c
            && not (Set.is_empty (Set.inter (heads c) n))
          then Set.union n (bodies c)
          else n))

let is_horn cs = List.for_all cs ~f:(fun (_, ps, _, _) -> Set.length ps <= 1)

(* [analyse cs] = (the cone's clauses in [cs]'s order, [derivable], [needed],
   stats); [None] when a clause has more than one positive literal *)
let analyse (cs : Clause.t list) =
  if not (is_horn cs) then None
  else
    let d = derivable cs in
    let n = needed ~derivable:d cs in
    let keep c =
      Set.is_subset (bodies c) ~of_:d
      && (Clause.is_goal c || not (Set.is_empty (Set.inter (heads c) n)))
    in
    let kept = List.filter cs ~f:keep in
    let all_pvs =
      List.fold cs ~init:Set.Poly.empty ~f:(fun s c ->
          Set.union s (Set.union (heads c) (bodies c)))
    in
    let kept_pvs =
      List.fold kept ~init:Set.Poly.empty ~f:(fun s c ->
          Set.union s (Set.union (heads c) (bodies c)))
    in
    Some
      ( kept,
        d,
        n,
        {
          clauses = List.length cs;
          goals = List.count cs ~f:Clause.is_goal;
          unknowns = Set.length all_pvs;
          derivable = Set.length d;
          needed = Set.length n;
          kept_clauses = List.length kept;
          kept_unknowns = Set.length kept_pvs;
        } )

(* [lift ~derivable ~kept_pvs ~senv sol]: the extension of (2) above, for a
   solution [sol] of the cone over the unknowns [senv] of the whole set *)
let lift ~derivable ~kept_pvs ~(senv : sort_env_map) sol =
  Map.Poly.mapi senv ~f:(fun ~key ~data ->
      if Set.mem kept_pvs key then
        match Map.Poly.find sol key with
        | Some t -> t
        | None ->
            let args, _ = Sort.args_ret_of data in
            ExtTerm.mk_lambda
              (sort_env_list_of_sorts args)
              (BoolTerm.mk_bool true)
      else
        let args, _ = Sort.args_ret_of data in
        ExtTerm.mk_lambda
          (sort_env_list_of_sorts args)
          (BoolTerm.mk_bool (Set.mem derivable key)))

let str_of_stats s =
  sprintf
    "clauses=%d goals=%d unknowns=%d derivable=%d needed=%d cone_clauses=%d \
     cone_unknowns=%d"
    s.clauses s.goals s.unknowns s.derivable s.needed s.kept_clauses
    s.kept_unknowns
