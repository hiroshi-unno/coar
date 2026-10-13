open Core
open Common.Ext
open Common.Combinator
open Ast

(** Cell abstraction of a constrained Horn problem.

    An unknown taking an array cannot be given a quantifier-free solution when
    the property it must satisfy speaks about every element -- "no element
    below [i] exceeds [bound]" is such a property, and no finite conjunction of
    facts about particular indices is inductive.  This replaces each array
    argument by [m] pairs of an index and the value the array holds there, so
    that the unknown's solution may again be quantifier free, and the quantifier
    reappears only when the solution is read back:

      P(a, x)  is defined as  forall j_1..j_m. P#(j_1, a[j_1], .., j_m, a[j_m], x)

    which is the concretization every statement below is relative to.  The
    abstraction is due to Monniaux and Gonnord, "Cell Morphing: From Array
    Programs to Array-Free Horn Clauses" (Static Analysis, 2016), and its
    general form to Braine, Gonnord and Monniaux, "Data Abstraction: A General
    Framework to Handle Program Verification of Data Structures" (Static
    Analysis, 2021), where a relative completeness result is proved for a
    symbolic finite instantiation of this kind.

    Each clause is rewritten so that

    - a **body** atom, which is a hypothesis, is assumed at every tuple of the
      index terms the clause reads the array at, together with the fresh
      indices the heads are proved at;
    - a **head** atom, which must be proved, is proved at [m] *fresh
      universally quantified* index variables, since that is what the
      concretization demands;
    - the pure part is untouched, and the array itself stays in the clause --
      only the unknown loses it.

    The fresh head indices must also be available to the body, or the induction
    cannot use its hypothesis at the index the head is about, which is the step
    an inductive array invariant always needs.

    **The direction this is sound in.** If the abstracted system has a solution
    then so does the original, by the concretization above: a body atom's
    instances are consequences of the concretized body, and the head is proved
    at an arbitrary index.  The converse does not hold -- the original may have
    a solution that no formula over [m] cells expresses -- so a caller may take
    a satisfiable answer from the abstracted system and must not take an
    unsatisfiable one.

    Over-approximating the index terms is therefore free: extra body instances
    are extra consequences of the same hypothesis. *)

(* The index terms at which a term reads an array, with the index sort of each.
   This is the read branch of the published heuristic below and nothing else: it
   is blind to which array is read, to the indices an argument STORES at, and to
   whether an index it collects is usable where the atom stands -- an index
   written under a lambda mentions that lambda's variable, and lifting it out
   leaves the variable free.  [relevant] is the whole rule; this is kept because
   it is the cheapest way to ask "does this clause read any array at all". *)
let index_terms_of (t : Logic.term) =
  let rec inner acc (t : Logic.term) =
    let acc =
      match Logic.Term.let_apps t with
      | Logic.Con (Logic.ArrayTerm.ASelect (si, _), _), [ _arr; idx ] ->
          Set.add acc (si, idx)
      | _ -> acc
    in
    match t with
    | Logic.App (t1, t2, _) -> inner (inner acc t1) t2
    | Logic.Bin (_, _, _, t1, _) -> inner acc t1
    | Logic.Let (_, _, t1, t2, _) -> inner (inner acc t1) t2
    | Logic.TyApp (t1, _, _) -> inner acc t1
    | Logic.TyLam (_, t1, _) -> inner acc t1
    | Logic.Var _ | Logic.Con _ -> acc
  in
  inner Set.Poly.empty t

(* {1 The published instantiation heuristic}

   Which indices a body atom is instantiated at decides what the abstraction can
   prove, and the source it is computed from is a design choice with a published
   answer.  Braine, Gonnord and Monniaux give it as two algorithms: a syntactic
   walk collecting the "relevant" indices of an array for a context -- those
   which, left unchanged, keep the context's value -- and a three-line wrapper
   turning that set into (index, value) pairs.  Their completeness result is
   stated CONDITIONALLY on that walk: the instantiation is strongly complete
   whenever the walk did not have to give up.

   That condition is the part worth having.  A collection function returns
   something and so gets written; the marker saying "I could not account for
   this shape" returns nothing on the happy path and reads as ceremony -- and
   without it a run on an input outside the hypothesis is indistinguishable from
   a run on one inside it, so a failure to answer can be neither attributed to
   the index set nor cleared of it.

   The walk gives up in three places, and each is a real shape here:
   - an index term mentioning a variable bound between it and the atom, which
     cannot be used outside that binder;
   - the array met as a bare variable rather than under a read, since the
     context may then depend on all of it;
   - an array ARGUMENT that is not a chain of stores over a variable -- an array
     written as a lambda, for instance, which is how a shifting slice reaches a
     predicate in Rust-derived input. *)

(* The base variable of an array expression together with the indices it stores
   at, or [None] when the expression is not a chain of stores over a variable.
   [None] is the give-up marker for the argument position. *)
let rec store_chain (t : Logic.term) =
  match Logic.Term.let_apps t with
  | Logic.Con (Logic.ArrayTerm.AStore (si, _), _), [ arr; idx; v ] -> (
      match store_chain arr with
      | Some (b, stores) -> Some (b, (si, idx, v) :: stores)
      | None -> None)
  | Logic.Var (x, _), [] -> Some (x, [])
  | _ -> None

(* The indices relevant to [ctx] for an array argument [a], and whether the walk
   had to give up.  [top] true means the completeness hypothesis is not met for
   this argument; the indices returned are still sound to instantiate at, since
   every instance of a body atom is a consequence of the concretized body -- what
   is lost is the guarantee that they are enough. *)
(* Why the walk gave up, when it did.  Keeping the three apart is not
   bookkeeping: they say different things about the input and they are repaired
   in different places.

   [Not_a_store_chain] is about the ARGUMENT -- an array written as a lambda, or
   returned by a function -- and no choice of indices helps, since the rule
   cannot see which array it is looking at.  [Opaque_use] is about the CONTEXT --
   the array handed whole to a constructor or another predicate -- and it is what
   a corpus of Rust-derived input produces by wrapping every array in a tuple.
   [Bound_index] is the narrow one: the index exists and is simply not usable
   where the atom stands, so a rule that could carry a binder outward would
   recover it. *)
type give_up = Bound_index | Opaque_use | Not_a_store_chain

let str_of_give_up = function
  | Bound_index -> "bound-index"
  | Opaque_use -> "opaque-use"
  | Not_a_store_chain -> "not-a-store-chain"

type relevant = {
  idxs : (Logic.Sort.t * Logic.term) list;
  gave_up : give_up list;  (** deduplicated; empty when the walk accounted for
                               the argument, which is the completeness
                               hypothesis *)
}

let top r = not (List.is_empty r.gave_up)

let relevant ~(arg : Logic.term) ~(ctx : Logic.term list) : relevant =
  match store_chain arg with
  | None -> { idxs = []; gave_up = [ Not_a_store_chain ] }
  | Some (avar, stores) ->
      let idxs = ref [] and gave_up = ref [] in
      let give_up g = gave_up := g :: !gave_up in
      let add si i = idxs := (si, i) :: !idxs in
      (* an index may only be used where every variable it mentions is in scope
         at the atom, which is what [bound] tracks *)
      let usable bound i = Set.is_empty (Set.inter (Logic.Term.fvs_of i) bound) in
      let offer si i =
        if usable Set.Poly.empty i then add si i else give_up Bound_index
      in
      (* [let_apps] strips the whole application spine, so [head] is never an
         application and each argument is visited once.  That matters here: a
         read of [avar] must NOT walk into its own array subterm, or the base
         variable is met bare and reads as the opaque case below. *)
      let rec walk bound (t : Logic.term) =
        let head, args = Logic.Term.let_apps t in
        match (head, args) with
        | Logic.Con (Logic.ArrayTerm.ASelect (si, _), _), [ arr; idx ]
          when match store_chain arr with
               | Some (b, _) -> Ident.tvar_equal b avar
               | None -> false ->
            if usable bound idx then add si idx else give_up Bound_index;
            (match store_chain arr with
             | Some (_, stores) ->
                 List.iter stores ~f:(fun (_, j, x) -> walk bound j; walk bound x)
             | None -> ());
            walk bound idx
        | Logic.Var (x, _), [] when Ident.tvar_equal x avar ->
            (* the array used whole rather than read: the context may depend on
               every index of it, and no finite set of indices covers that *)
            give_up Opaque_use
        | _ ->
            (match head with
             | Logic.Bin (_, var, _, t1, _) -> walk (Set.add bound var) t1
             | Logic.Let (var, _, t1, t2, _) ->
                 walk bound t1;
                 walk (Set.add bound var) t2
             | Logic.TyApp (t1, _, _) | Logic.TyLam (_, t1, _) -> walk bound t1
             | Logic.Var _ | Logic.Con _ | Logic.App _ -> ());
            List.iter args ~f:(walk bound)
      in
      List.iter ctx ~f:(walk Set.Poly.empty);
      (* the argument's own stored indices, which the context need not read *)
      List.iter stores ~f:(fun (si, i, v) ->
          offer si i;
          walk Set.Poly.empty i;
          walk Set.Poly.empty v);
      {
        idxs = List.dedup_and_sort ~compare:Stdlib.compare !idxs;
        gave_up = List.dedup_and_sort ~compare:Stdlib.compare !gave_up;
      }

(* {1 Cell width}

   What an [m]-cell abstraction can SAY is syntactic, and this is the number that
   says it.  A candidate over [m] cells of one array mentions at most [m] of its
   elements at once, so it can express exactly the atomic predicates that observe
   the array at at most [m] distinct indices: [a[i] = 0] has width 1, [a[i] <=
   a[j]] width 2, [a[i] + a[j] = a[k]] width 3.  A problem whose invariant needs
   a relation of width 2 and a configuration offering one cell per array do not
   meet, and today nothing says so -- the run simply does not answer, which is
   the outcome every other cause produces too.

   It is the same walk as the relevance rule above and is written as a call to
   it: the indices of one array inside one atomic predicate are what both count,
   the rule asking WHICH and this asking HOW MANY. *)

(* The atomic predicates of a boolean term -- the leaves under the connectives.
   A quantifier is descended through, since a cell relation under one is still a
   relation the candidate would have to state. *)
let rec atoms_of (t : Logic.term) =
  match Logic.Term.let_apps t with
  | Logic.Con (Logic.BoolTerm.(And | Or | Imply | Iff), _), args ->
      List.concat_map args ~f:atoms_of
  | Logic.Con (Logic.BoolTerm.Not, _), [ a ] -> atoms_of a
  | Logic.Bin (_, _, _, t1, _), _ -> atoms_of t1
  | _ -> [ t ]

(* How many distinct indices of [avar] one atomic predicate observes. *)
let width_of ~avar atom =
  List.length (relevant ~arg:(Logic.Term.mk_var avar) ~ctx:[ atom ]).idxs

(* The widest observation of any of [avars] in any atom of [t], with the atom
   that achieves it -- which is what a report names, since "width 3" without the
   predicate tells a reader nothing about what to do. *)
let max_width_of ~avars t =
  List.fold (atoms_of t) ~init:(0, None) ~f:(fun acc atom ->
      List.fold avars ~init:acc ~f:(fun (best, witness) avar ->
          let w = width_of ~avar atom in
          if w > best then (w, Some atom) else (best, witness)))

(* How many array arguments were instantiated without the completeness
   hypothesis.  It is a count and not a verdict: the abstraction still runs, and
   a caller that wants to report "this answer rests on an instantiation that is
   not known to be complete" reads it. *)
let incomplete_args = ref 0

let reset_incomplete () = incomplete_args := 0

(* One array argument's [m] index terms, following the published wrapper: the
   relevant set with the give-up marker dropped, made non-empty by [fallbacks]
   -- any value of the index type serves, and the fresh indices the heads are
   proved at are the ones this tree has to offer, since the induction needs its
   hypothesis exactly there. *)
let insts ~(si : Logic.Sort.t) ~arg ~ctx ~(fallbacks : Logic.term list) =
  let r = relevant ~arg ~ctx in
  if top r then incr incomplete_args;
  let here =
    List.filter_map r.idxs ~f:(fun (si', i) ->
        if Stdlib.(si' = si) then Some i else None)
  in
  match here @ fallbacks with [] -> [ Logic.IntTerm.zero () ] | l -> l

(* The abstracted sort of an unknown: [m] (index, value) pairs for each array
   argument, in the order the arrays appear, and then the arguments that were
   not arrays. *)
let abstract_sort ~m sort =
  let args = Logic.Sort.args_of sort in
  let arrays = List.filter args ~f:Logic.ArrayTerm.is_array_sort in
  if List.is_empty arrays then None
  else
    let cells =
      List.concat_map arrays ~f:(fun s ->
          let si = Logic.ArrayTerm.index_sort_of s in
          let se = Logic.ArrayTerm.elem_sort_of s in
          List.concat @@ List.init m ~f:(fun _ -> [ si; se ]))
    in
    let scalars =
      List.filter args ~f:(Logic.ArrayTerm.is_array_sort >> not)
    in
    Some (Logic.Sort.mk_fun (cells @ scalars @ [ Logic.ExtTerm.SBool ]))

(* Which unknowns this abstraction touches, with their new sorts. *)
let targets_of ~m exi_senv =
  Map.Poly.filter_map exi_senv ~f:(abstract_sort ~m)

(* One abstracted atom: the unknown applied to the cells chosen for each of its
   array arguments, then to the arguments that were not arrays.  [idxss] gives
   [m] index terms per array argument, in the arrays' own order. *)
let abstract_atom ~m exi_senv atom idxss =
  let pv, args = Logic.Term.let_var_app atom in
  let arg_sorts =
    Logic.Sort.args_of @@ Map.Poly.find_exn exi_senv pv
  in
  let pairs = List.zip_exn arg_sorts args in
  let arrays =
    List.filter pairs ~f:(fst >> Logic.ArrayTerm.is_array_sort)
  in
  let cells =
    List.concat
    @@ List.map2_exn arrays idxss ~f:(fun (s, arr) idxs ->
           let si = Logic.ArrayTerm.index_sort_of s in
           let se = Logic.ArrayTerm.elem_sort_of s in
           assert (List.length idxs = m);
           List.concat_map idxs ~f:(fun i ->
               [ i; Logic.Term.mk_apps (Logic.ArrayTerm.mk_select si se) [ arr; i ] ]))
  in
  let scalars =
    List.filter_map pairs ~f:(fun (s, t) ->
        if Logic.ArrayTerm.is_array_sort s then None else Some t)
  in
  Logic.Term.mk_var_app pv (cells @ scalars)

(* The index sorts an atom's array arguments read at, in order. *)
let index_sorts_of exi_senv atom =
  let pv, _ = Logic.Term.let_var_app atom in
  Logic.Sort.args_of (Map.Poly.find_exn exi_senv pv)
  |> List.filter ~f:Logic.ArrayTerm.is_array_sort
  |> List.map ~f:Logic.ArrayTerm.index_sort_of

let is_target targets atom =
  match Logic.Term.let_apps atom with
  | Logic.Var (pv, _), _ -> Map.Poly.mem targets pv
  | _ -> false

(* All [m]-tuples, one list per array argument, drawn from the terms available
   at that argument's index sort. *)
(* The array arguments of an atom, as (argument sort, argument term) pairs in
   the arrays' own order -- the order every consumer of the abstraction agrees
   on. *)
let array_args_of exi_senv atom =
  let pv, args = Logic.Term.let_var_app atom in
  let arg_sorts = Logic.Sort.args_of @@ Map.Poly.find_exn exi_senv pv in
  List.zip_exn arg_sorts args
  |> List.filter ~f:(fst >> Logic.ArrayTerm.is_array_sort)

(* The context an argument's relevance is computed against: the clause with every
   ABSTRACTED array occurrence removed.

   This is not a detail and getting it wrong makes the rule report nothing.  An
   array argument of an atom that is about to be abstracted does not survive the
   transformation -- the atom becomes the unknown applied to (index, value)
   pairs, so the array is read only at the chosen indices -- and leaving that
   occurrence in the context makes the walk meet the array bare, which is the
   give-up case.  Every argument then reports "cannot account for this" and the
   instantiation falls back to the fresh head indices alone, which is the rule
   producing nothing while appearing to run.  Measured before the fix: 4, 4, 8
   and 49 arguments over four inputs, and not one of them accounted for. *)
let context_of exi_senv targets ps ns phi =
  phi
  :: List.concat_map (Set.to_list ps @ Set.to_list ns) ~f:(fun atom ->
         if not (is_target targets atom) then [ atom ]
         else
           let pv, args = Logic.Term.let_var_app atom in
           let arg_sorts = Logic.Sort.args_of @@ Map.Poly.find_exn exi_senv pv in
           List.zip_exn arg_sorts args
           |> List.filter_map ~f:(fun (s, t) ->
                  if Logic.ArrayTerm.is_array_sort s then None else Some t))

(* All choices of [m] index terms for each array argument, the argument's own
   candidates coming from the published heuristic rather than from a pool shared
   by every array of the same index sort.  The distinction is the heuristic's
   own: it is defined on an array ARGUMENT and a context, so two arrays of one
   clause get different sets, and pooling them by sort offers each the other's
   indices -- sound, since every body instance is a consequence, and weaker as a
   statement about what the abstraction was shown to prove. *)
let tuples_for ~m ~ctx ~fallbacks args =
  let pick ts =
    let rec go k = if k <= 0 then [ [] ] else
      List.concat_map (go (k - 1)) ~f:(fun tl ->
          List.map ts ~f:(fun t -> t :: tl))
    in
    go m
  in
  List.fold_right args ~init:[ [] ] ~f:(fun (s, arg) acc ->
      let si = Logic.ArrayTerm.index_sort_of s in
      let ts = insts ~si ~arg ~ctx ~fallbacks:(fallbacks si) in
      List.concat_map (pick ts) ~f:(fun idxs ->
          List.map acc ~f:(fun tl -> idxs :: tl)))

let abstract_clause ~m exi_senv targets ((senv, ps, ns, phi) : Clause.t) :
    Clause.t =
  (* The fresh indices each head atom is proved at.  They are merged into the
     clause's universals, so each must be new to that environment (and to the
     unknowns): a name the input already binds would make the head be proved
     at that input variable rather than at an arbitrary index. *)
  let taken v = Map.Poly.mem senv v || Map.Poly.mem exi_senv v in
  let head_fresh =
    List.map (Set.to_list ps) ~f:(fun atom ->
        if not (is_target targets atom) then (atom, [])
        else
          ( atom,
            List.map (index_sorts_of exi_senv atom) ~f:(fun si ->
                List.init m ~f:(fun _ ->
                    ( Ident.mk_fresh_tvar_avoiding ~prefix:"cell_idx" ~taken (),
                      si ))) ))
  in
  let fresh_senv =
    List.concat_map head_fresh ~f:(snd >> List.concat)
    |> Map.Poly.of_alist_exn
  in
  (* The fresh head indices are offered as the fallback the
     wrapper needs, because the induction must be able to use its hypothesis at
     the index the head is about. *)
  let ctx = context_of exi_senv targets ps ns phi in
  let fallbacks si =
    Map.Poly.to_alist fresh_senv
    |> List.filter_map ~f:(fun (x, si') ->
           if Stdlib.(si' = si) then Some (Logic.Term.mk_var x) else None)
  in
  let ns' =
    Set.Poly.union_list
    @@ List.map (Set.to_list ns) ~f:(fun atom ->
           if not (is_target targets atom) then Set.Poly.singleton atom
           else
             Set.Poly.of_list
             @@ List.map
                  (tuples_for ~m ~ctx ~fallbacks (array_args_of exi_senv atom))
                  ~f:(abstract_atom ~m exi_senv atom))
  in
  let ps' =
    Set.Poly.of_list
    @@ List.map head_fresh ~f:(fun (atom, fresh) ->
           if List.is_empty fresh then atom
           else
             abstract_atom ~m exi_senv atom
               (List.map fresh ~f:(List.map ~f:(fst >> Logic.Term.mk_var))))
  in
  Clause.canon (Map.force_merge senv fresh_senv, ps', ns', phi)

(* The abstracted problem, and the map taking a solution of it back.

   [targets] is also what says which unknowns changed: an unknown with no array
   argument is untouched and its solution needs no adjustment. *)
let abstract ~m pcsp =
  let exi_senv = PCSP.Problem.senv_of pcsp in
  let targets = targets_of ~m exi_senv in
  if Map.Poly.is_empty targets then None
  else
    let clauses =
      Set.Poly.map (PCSP.Problem.clauses_of pcsp)
        ~f:(abstract_clause ~m exi_senv targets)
    in
    let params = PCSP.Problem.params_of pcsp in
    let senv' =
      Map.Poly.merge exi_senv targets ~f:(fun ~key:_ -> function
        | `Both (_, s') -> Some s'
        | `Left s -> Some s
        | `Right s -> Some s)
    in
    Some
      ( PCSP.Problem.of_clauses
          ~params:{ params with PCSP.Params.senv = senv' }
          clauses,
        targets )

(* [P(a, x) := forall j. sigma#(j, a[j], x)] -- the concretization, applied to
   the solution the abstracted problem came back with.  The solution of an
   abstracted unknown is a lambda whose first [2m] parameters per array are the
   cells; each value parameter becomes a read of the array that took its place,
   and each index parameter is closed with [forall]. *)
let concretize ~m exi_senv targets sol =
  Map.Poly.mapi sol ~f:(fun ~key ~data ->
      match Map.Poly.find targets key with
      | None -> data
      | Some _ ->
          let arg_sorts = Logic.Sort.args_of @@ Map.Poly.find_exn exi_senv key in
          let arrays = List.filter arg_sorts ~f:Logic.ArrayTerm.is_array_sort in
          let params, body = Logic.Term.let_lam data in
          let n_cells = 2 * m * List.length arrays in
          let cells, scalars = List.split_n params n_cells in
          (* the original parameter list, with a fresh name per argument *)
          let orig =
            let scalar_names = List.map scalars ~f:fst in
            let rec weave sorts scalars =
              match sorts with
              | [] -> []
              | s :: rest ->
                  if Logic.ArrayTerm.is_array_sort s then
                    (Ident.mk_fresh_tvar ~prefix:(Some "arr") (), s)
                    :: weave rest scalars
                  else (
                    match scalars with
                    | x :: tl -> (x, s) :: weave rest tl
                    | [] -> assert false)
            in
            weave arg_sorts scalar_names
          in
          let array_vars =
            List.filter_map (List.zip_exn arg_sorts (List.map orig ~f:fst))
              ~f:(fun (s, x) ->
                if Logic.ArrayTerm.is_array_sort s then Some (s, x) else None)
          in
          (* substitute [a[j]] for each value parameter, keeping the index
             parameters, which are then quantified *)
          let sub, idx_binds =
            let rec go cells arrays acc_sub acc_idx =
              match (cells, arrays) with
              | [], _ -> (acc_sub, List.rev acc_idx)
              | _, [] -> (acc_sub, List.rev acc_idx)
              | _, (s, arr) :: arest ->
                  let mine, crest = List.split_n cells (2 * m) in
                  let si = Logic.ArrayTerm.index_sort_of s in
                  let se = Logic.ArrayTerm.elem_sort_of s in
                  let rec pairs cs acc_sub acc_idx =
                    match cs with
                    | (j, _) :: (v, _) :: tl ->
                        pairs tl
                          (Map.Poly.set acc_sub ~key:v
                             ~data:
                               (Logic.Term.mk_apps
                                  (Logic.ArrayTerm.mk_select si se)
                                  [ Logic.Term.mk_var arr; Logic.Term.mk_var j ]))
                          ((j, si) :: acc_idx)
                    | _ -> (acc_sub, acc_idx)
                  in
                  let acc_sub, acc_idx = pairs mine acc_sub acc_idx in
                  go crest arest acc_sub acc_idx
            in
            go cells array_vars Map.Poly.empty []
          in
          let body = Logic.Term.subst sub body in
          let body =
            List.fold_right idx_binds ~init:body ~f:(fun (x, s) acc ->
                Logic.BoolTerm.forall [ (x, s) ] acc)
          in
          Logic.Term.mk_lambda orig body)
