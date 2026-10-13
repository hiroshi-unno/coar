(* The indices at which a goal example's own clause read its arrays, carried
   from the phase that knows them to the phase that expands the example into
   cells.

   A goal (negative) example [N(t)] is born as an instance of a clause
   [N(x, a) /\ psi => false] at a solver model.  Under the cell read-back
   [N(x, a) := forall k. phi(x, k, a[k])] the example means
   [exists k. not phi(t, k, t[k])], and the synthesis constraint that stands
   for it is a finite disjunction [\/ over k in S of not phi(t, k, t[k])] over
   some set [S] of cells.  Whatever [S] is, that disjunction implies the
   example, so a candidate meeting it meets the example: the choice of [S]
   can never make the loop accept a wrong candidate, and every [sat] still
   rests on the validator.

   What [S] decides is whether a SOLUTION can meet it.  If some state that
   every solution contains agrees with [t] on every cell of [S], every
   solution is excluded from the moment the example is added.  That happens
   whenever the clause refutes the state at an index [S] does not reach: the
   default offer set is the array's stored indices, their neighbours and
   [0..5], and a clause reading [b[i + k]] with the model's [i] in the
   thousands is refuted far outside it.  The index is in the model the
   example is built from -- the clause's read index terms are free variables
   of the counterexample query -- and it is lost when only the predicate's
   arguments are kept.  This module keeps it.  When [S] contains the cell
   tuple of the clause's reads, a state agreeing with [t] on [S] satisfies
   [psi] as [t] does, so it is not reachable unless the problem is
   unsatisfiable, and the exclusion above cannot happen.

   Where it lives, and why not on the example.  An example atom is a value
   the version space, the clause graph and the labeler compare and key on,
   and the labeler refutes from exactly those atoms; the concrete example
   must stay what the problem clause says, or refutations would be about
   something else.  Carrying the reads inside the atom or its guard would
   change that value (two instances of one example at different reads would
   become two atoms that never meet) and would put cell data where the
   labeler reads.  So the reads ride BESIDE the example, in this table, keyed
   by the atom's printed normal form: nothing that stores or refutes from
   examples reads it, and only the synthesizer's celled expansion does.  A key
   that fails to match -- an atom spelled differently by a later
   normalisation -- only means the expansion falls back to its default cells,
   which is what it did before; a key shared by two atoms that print the same
   only offers one atom the other's reads, which is sound by the argument
   above.

   The table is process-global and grows during a run, like the other
   channels between PCSat phases; it is guarded by compare-and-set so that
   domains running at once do not drop each other's entries. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* One array read of the clause at one instance: which array (the path from
   the predicate's argument, as the cell machinery names paths) and the index
   the model gave its index term. *)
type read = { param : int; selectors : string list; index : Z.t }

(* The reads of one clause instance.  [exact] says the clause was a goal
   clause (no predicate in its head), so that these reads are everything the
   clause's refutation depends on and the expansion may use them INSTEAD of
   its default cells.  From a clause with a head -- the resolver refuting a
   body atom because the head is already a decided negative -- the head's own
   witness index also matters (an untouched cell carries it across the step),
   and it is not among the reads, so such a record is offered IN ADDITION to
   the default cells. *)
type record = { exact : bool; reads : read list }

(* Equalities written out rather than polymorphic: the index is a [Z.t], and
   these state which fields decide sameness. *)
let equal_read a b =
  a.param = b.param
  && List.equal String.equal a.selectors b.selectors
  && Z.equal a.index b.index

let equal_record a b = Bool.equal a.exact b.exact && List.equal equal_read a.reads b.reads

let table : (string, record list) Map.Poly.t Atomic.t = Atomic.make Map.Poly.empty

let rec add_record key r =
  let old = Atomic.get table in
  let rs = Option.value (Map.Poly.find old key) ~default:[] in
  if List.mem rs r ~equal:equal_record then ()
  else
    let updated = Map.Poly.set old ~key ~data:(rs @ [ r ]) in
    if not (Atomic.compare_and_set table old updated) then add_record key r

let clear () = Atomic.set table Map.Poly.empty
let size () = Map.Poly.length (Atomic.get table)
let selector_names path = List.map path.CellQual.selectors ~f:snd

(* The key of an example atom: its predicate and its arguments after the
   normalisation every consumer applies ([ExAtom.instantiate] then
   [ExAtom.normalize], which evaluates ground arguments to values), printed.
   [None] for anything but a predicate application. *)
let key_of_atom (atom : ExAtom.t) : string option =
  match ExAtom.normalize (ExAtom.instantiate atom) with
  | ExAtom.PApp ((pvar, _), args) ->
      Some
        (sprintf "%s(%s)" (Ident.name_of_pvar pvar)
           (String.concat ~sep:", " (List.map args ~f:Term.str_of)))
  | _ -> None

let records_of_key key = Option.value (Map.Poly.find (Atomic.get table) key) ~default:[]

let records_of_atom atom =
  match key_of_atom atom with None -> [] | Some key -> records_of_key key

(* Whether a path is one this module records reads of: an array (not a
   sequence) with one integer index level.  Any other path keeps its default
   cells. *)
let supported (path : CellQual.array_path) =
  (match path.CellQual.container with CellQual.Array -> true | CellQual.Sequence -> false)
  &&
  match path.CellQual.index_sorts with [ si ] -> Term.is_int_sort si | _ -> false

(* The reads in [phi] of the arrays the predicate application [args] (of
   sorts [sorts]) carries, each index evaluated under [sub].

   A read counts when its array term is, after simplification, the path's
   array read off the argument ([CellArray.array_of_path]) and its index term
   mentions only variables free in [phi] -- an index under a binder names a
   bound variable, whose value no model gives.  A read whose index does not
   evaluate to an integer literal under [sub] is left out.  Leaving a read out
   is never unsound (the set of cells is free); it only means the reads do not
   cover the clause, and then the default cells are what the expansion has for
   that array. *)
let reads_of_app ~(sorts : Sort.t list) ~(args : Term.t list) ~(sub : TermSubst.t)
    (phi : Formula.t) : read list =
  let paths = List.filter (CellQual.array_paths sorts) ~f:supported in
  if List.is_empty paths || List.length sorts <> List.length args then []
  else
    let targets =
      List.map paths ~f:(fun path ->
          ( path,
            Term.str_of
              (CellArray.array_of_path path (List.nth_exn args path.CellQual.param)) ))
    in
    let fvs = Formula.tvs_of phi in
    let acc = ref [] in
    Formula.iter_term phi ~f:(fun t ->
        match t with
        | Term.FunApp (T_array.ASelect (si, _), [ arr; idx ], _)
          when Term.is_int_sort si && Set.is_subset (Term.tvs_of idx) ~of_:fvs -> (
            let key = Term.str_of (Evaluator.simplify_term arr) in
            match
              List.find targets ~f:(fun (_, k) -> String.equal k key)
            with
            | None -> ()
            | Some (path, _) -> (
                (* the index is kept in [Z]: the instance is a model's, and a
                   read at an index beyond a native int is a read like any other *)
                match
                  T_int.let_int (Evaluator.simplify_term (Term.subst sub idx))
                with
                | index ->
                    let r =
                      {
                        param = path.CellQual.param;
                        selectors = selector_names path;
                        index;
                      }
                    in
                    if not (List.mem !acc r ~equal:equal_read) then acc := r :: !acc
                | exception exn_ when not (Common.Timer.is_async exn_) -> ()))
        | _ -> ());
    List.rev !acc

(* Record the reads of one clause instance: [phi] is the whole clause as a
   formula (its predicate applications as literals) and [sub] the model's
   substitution for the clause's variables.  For every predicate application
   in the body, the application instantiated by [sub] is keyed as an example
   atom and the reads of its arrays are recorded under that key.

   A clause with a predicate in its head is recorded only when [allow_step],
   and then not as [exact] (see [record]).  [target], when given, restricts
   recording to the body applications whose key is that one -- the example
   actually derived -- so that a clause with two body atoms does not file one
   atom's reads under the other.  Returns how many records were added or
   already present. *)
(* The reads of the body application of [phi] whose key is [target], at the
   instance [sub], or [] when no body application has that key.  Unlike
   [record_instance] this records nothing and accepts a clause with a head. *)
let instance_reads ~target (phi : Formula.t) (sub : TermSubst.t) : read list =
  let _, neg = Formula.atoms_of phi in
  Set.to_list neg
  |> List.find_map ~f:(function
       | Atom.App (Predicate.Var (pvar, sorts), args, _) -> (
           match
             key_of_atom (ExAtom.PApp ((pvar, sorts), List.map args ~f:(Term.subst sub)))
           with
           | Some key when String.equal key target ->
               Some (reads_of_app ~sorts ~args ~sub phi)
           | _ -> None)
       | _ -> None)
  |> Option.value ~default:[]

let record_instance ?target ~allow_step (phi : Formula.t) (sub : TermSubst.t) : int =
  let pos, neg = Formula.atoms_of phi in
  let pvar_apps atoms =
    Set.to_list atoms
    |> List.filter_map ~f:(function
         | Atom.App (Predicate.Var (pvar, sorts), args, _) -> Some (pvar, sorts, args)
         | _ -> None)
  in
  let heads = pvar_apps pos in
  if (not allow_step) && not (List.is_empty heads) then 0
  else
    let exact = List.is_empty heads in
    List.count (pvar_apps neg) ~f:(fun (pvar, sorts, args) ->
        let atom =
          ExAtom.PApp ((pvar, sorts), List.map args ~f:(Term.subst sub))
        in
        match key_of_atom atom with
        | None -> false
        | Some key -> (
            match target with
            | Some t when not (String.equal t key) -> false
            | _ -> (
                match reads_of_app ~sorts ~args ~sub phi with
                | [] -> false
                | reads ->
                    add_record key { exact; reads };
                    true)))

(* Records for a negative example [N(t)] derived by resolving a clause's head
   [N(t')] against an already decided negative example [N(t')] -- a step
   clause, or a step example [N(t) => N(t')] the validator returned -- composed
   from the records of that negative example ([from], atoms of the derived
   atom's own predicate, so that a read's argument position means the same
   array in both) and the reads [own] of the resolved clause at the
   derivation's instance.

   Each record [r] of a source atom gives one record [{exact = r.exact; reads =
   r.reads @ own}] under [target].  Soundness is the contract of
   [cells_at_reads]: any set of cells of the derived atom's own arrays gives a
   constraint that implies the example.  Why the composition is the right set:
   [r]'s reads include an index [k] at which every solution's matrix fails on
   [t'] (for an exact record, all the indices its refutation read).  If a
   solution's matrix held on [t] at [k] and at every index the step reads, the
   cell-local step would carry it to [t'] at [k] -- so it fails on [t] at [k]
   or at a read of the step, and the tuples over [k] and [own] contain a cell
   that rejects [t].  This is the frame argument of the cell route's step
   encoding and rests on its clause-shape hypotheses, which this does not
   check; outside them the set is still sound and only possibly incomplete.
   Without the composition the derived atom has no record, or one offered
   beside the default cells, and an atom whose default product is over the
   bound is expanded at one sampled tuple, which on a reachable-looking cell
   excludes every solution.  Returns how many records were added or already
   present; 0 when no source atom has a record. *)
let inherit_records ~target ~(from : ExAtom.t list) ~(own : read list) : int =
  List.sum
    (module Int)
    from
    ~f:(fun atom ->
      List.count (records_of_atom atom) ~f:(fun r ->
          let reads =
            List.fold (r.reads @ own) ~init:[] ~f:(fun acc rd ->
                if List.mem acc rd ~equal:equal_read then acc else acc @ [ rd ])
          in
          add_record target { exact = r.exact; reads };
          true))

(* The cell tuples a goal example's body atom is expanded at, given its
   records: per record, the product over the atom's array paths of the cells
   at that record's read indices (for an [exact] record) or of those cells
   together with the path's default cells (otherwise); a path the record reads
   nothing of -- the clause does not read that array, or the path is a
   sequence or a curried array -- takes its default cells.  The union over the
   records is returned, deduplicated.

   CONTRACT.  Whatever this returns, the disjunction over the tuples of the
   candidate's negation implies the example [exists k. not phi(t, k, t[k])],
   because each tuple is a cell of the example's own arrays (its values are
   read off them by [CellArray.cell_tuples]); so nothing here can make the
   loop accept a candidate that violates the example.  What an [exact] record
   buys is completeness: when its reads are all of the clause's reads, a
   solution of the problem is not excluded by the constraint (under the
   clause-shape and extensibility hypotheses of the cell route's step
   encoding, which this does not check).

   [Over n] when some record's product or the union exceeds [bound], [Empty]
   when some array offers no cell; the caller then falls back to its ordinary
   expansion. *)
let cells_at_reads ~(paths : CellQual.array_path list)
    ~(arrays : (int * CellArray.cell_array) list)
    ~(default_cells : int -> CellQual.array_path -> (Logic.term list * Logic.term) list)
    ~bound (records : record list) : CellArray.product =
  let tuple_key tuple =
    List.map tuple ~f:(fun (is, v) ->
        (List.map is ~f:CellArray.term_key, CellArray.term_key v))
  in
  let dedup_cells cells =
    List.dedup_and_sort cells ~compare:(fun (is, v) (js, w) ->
        Stdlib.compare
          (List.map is ~f:CellArray.term_key, CellArray.term_key v)
          (List.map js ~f:CellArray.term_key, CellArray.term_key w))
  in
  let per_record r =
    let per_array =
      List.mapi paths ~f:(fun k path ->
          let idxs =
            if not (supported path) then []
            else
              List.filter_map r.reads ~f:(fun rd ->
                  if
                    rd.param = path.CellQual.param
                    && List.equal String.equal rd.selectors (selector_names path)
                  then Some rd.index
                  else None)
              |> List.dedup_and_sort ~compare:Z.compare
          in
          if List.is_empty idxs then default_cells k path
          else
            let at =
              CellArray.cell_tuples ~path (Stdlib.List.assoc k arrays)
                [ List.map idxs ~f:Logic.IntTerm.mk_int ]
            in
            if r.exact then at else dedup_cells (default_cells k path @ at))
    in
    CellArray.array_product ~bound per_array
  in
  let rec go acc = function
    | [] ->
        let tuples =
          List.dedup_and_sort acc ~compare:(fun a b ->
              Stdlib.compare (tuple_key a) (tuple_key b))
        in
        if List.length tuples > bound then CellArray.Over (List.length tuples)
        else CellArray.Tuples tuples
    | r :: rest -> (
        match per_record r with
        | CellArray.Tuples ts -> go (acc @ ts) rest
        | other -> other)
  in
  go [] records

(* The indices at which a candidate was found FALSE in the head of a clause,
   beside the positive example that refutation produced, keyed like the reads
   above by the example atom's printed normal form.

   A celled candidate is read back as [forall j. phi(x, j, a[j])], so a
   positive example [P(t)] means [forall j. phi(t, j, t[j])] and its synthesis
   constraint is the conjunction of [phi] over some set of cells of [t].  Any
   such set gives a constraint the example implies (each cell is an instance
   of the example's own universal), so a cell added here can only make the
   constraint stronger and closer to the example, and can never exclude a
   solution.  What the set decides is whether the loop makes progress: the
   default offer over a constant array -- what a solver returns for an array
   the clause leaves free -- is the prefix [0 .. 5], and a candidate false
   only below zero or past the prefix meets it, is refuted by the validator
   with the same point again, and the loop repeats that round without end.
   The index the refutation named is the cell the constraint lacked.

   Kept apart from the reads: those describe a goal example's body, and these
   a positive example's head, so a body atom never receives a head's witness.
   Process-global and growing, guarded by compare-and-set like the table above;
   an index already recorded for a key is not added twice. *)
let head_witness_table : (string, Z.t list) Map.Poly.t Atomic.t =
  Atomic.make Map.Poly.empty

let rec add_head_witnesses key (ws : Z.t list) =
  let old = Atomic.get head_witness_table in
  let known = Option.value (Map.Poly.find old key) ~default:[] in
  let fresh =
    List.dedup_and_sort ~compare:Z.compare
      (List.filter ws ~f:(fun w -> not (List.mem known w ~equal:Z.equal)))
  in
  if List.is_empty fresh then ()
  else
    let updated = Map.Poly.set old ~key ~data:(known @ fresh) in
    if not (Atomic.compare_and_set head_witness_table old updated) then
      add_head_witnesses key ws

(* Record [ws] for every positive atom of [atoms] that has a key; returns how
   many atoms were keyed. *)
let record_head_witnesses (atoms : ExAtom.t list) (ws : Z.t list) : int =
  if List.is_empty ws then 0
  else
    List.count atoms ~f:(fun atom ->
        match key_of_atom atom with
        | None -> false
        | Some key ->
            add_head_witnesses key ws;
            true)

let head_witnesses_of_atom atom =
  match key_of_atom atom with
  | None -> []
  | Some key ->
      Option.value (Map.Poly.find (Atomic.get head_witness_table) key) ~default:[]

let clear_head_witnesses () = Atomic.set head_witness_table Map.Poly.empty
