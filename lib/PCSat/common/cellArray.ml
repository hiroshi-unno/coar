(* The array a counterexample carries, read as CELLS.

   A cell is an index tuple -- one index per level of the array's sort, several
   for a curried array -- and the value at the end of the chain.  This module
   reads an array value the way a solver model writes it (a constant, a chain
   of stores over one, a lambda), keeps it as a TRIE, and answers the
   questions the cell route asks of it: what is stored at a level, what the
   array holds at a tuple, how a read at symbolic indices is written out.  It
   depends on no configuration, which is why it lives here rather than inside
   the synthesizer's functor: it can be pinned by a test that builds the terms
   directly, where the functor's own copy could not be reached without a
   harness.  The consumer is [SolutionTemplate], which [include]s it. *)

open Core
open Common.Ext
open Ast

(* The integer constants occurring in a term, plus 0.  This prints the term
   and re-reads it as an s-expression rather than folding over it, so it
   also collects any integer appearing inside a printed sort or symbol
   name; that is how the branch wrote it and it is kept, but a structural
   fold would be both cheaper and exact. *)
(* The indices a lambda body could be sampled at: the integer literals it
   mentions, and 0.  Zero is offered because an array's default is what a
   read outside the stored range returns, so it is always a cell worth
   asking about. *)
let collect_const (t : Logic.term) : Z.t list =
  (* in [Z] rather than native ints: a model may hold any integer, and an index
     beyond 63 bits is still a cell the body can be sampled at *)
  List.dedup_and_sort ~compare:Z.compare @@ List.cons Z.zero
  @@ Set.to_list @@ Logic.IntTerm.int_consts_of t

(* The arrays a predicate can reach from its arguments, in the order every
   consumer of the cell machinery agrees on.  Reached rather than taken
   directly: a predicate derived from a Rust program is declared over the
   tuple its arguments arrive in, so the array is a field. *)
let array_paths_of_sorts ?(sequences = false) (sorts : LogicOld.Sort.t list) =
  CellQual.array_paths ~sequences sorts

(* The array a path reaches, as a term, given the argument it starts at.  The
   selectors are applied and the result simplified, because an example's
   argument is a value built by the constructor the selector projects and the
   reader below wants the array itself. *)
let array_of_path path (arg : LogicOld.Term.t) =
  Evaluator.simplify_term @@ CellQual.read_path path arg

(* An array an example carries in a shape this reader does not cover.  It is
   an UNSUPPORTED INPUT and not an internal error: the cell route needs
   concrete cells, so where it cannot get them it has nothing to say, and the
   ordinary verdict for that is [unknown] with the reason beside it.  Raised
   as an assertion instead -- which it was -- it reaches the user as a
   backtrace with nothing on the verdict stream, which every harness here
   reads as the tool crashing. *)
let refuse_array t =
  (* The term's own printer is not used: it returns the empty string for the
     shapes that reach here, which turns the reason into a sentence that
     stops.  What a reader needs is which shape it was. *)
  let shape =
    match t with
    | Logic.Var (x, _) -> "a variable, " ^ Ident.name_of_tvar x
    | Logic.Con (_, _) -> "a constant this reader does not know"
    | Logic.App (_, _, _) -> (
        (* name the head symbol: that is which array operation is missing *)
        let rec head = function Logic.App (f, _, _) -> head f | t -> t in
        match head t with
        | Logic.Con (sym, _) -> (
            "an application of "
            ^ try Logic.ExtTerm.str_of_sym sym with exn_ when not (Common.Timer.is_async exn_) -> "a symbol")
        | _ -> "an application whose head is not a symbol")
    | Logic.Bin (_, _, _, _, _) -> "a binder"
    | Logic.Let (_, _, _, _, _) -> "a let"
    | Logic.TyApp (_, _, _) | Logic.TyLam (_, _, _) -> "a type abstraction"
  in
  raise
    (PCSP.Problem.NoTemplate
       (sprintf
          "the index/value cell route needs an example's array argument to \
           be a constant array, a chain of stores over one, or a lambda, and \
           this one is %s"
          shape))

(* Read an array-valued term as (its default value, its stored cells).  Only
   the shapes an example atom can carry are covered: a constant array, a
   chain of [store]s over one, and a lambda, whose value is sampled at each
   integer constant the body mentions.

   It finds, in the array a counterexample model carries, the indices worth
   saying something about.  The intended design takes its indices from the
   CLAUSE instead -- the terms whose reads of the array the clause's pure
   part performs -- and needs neither this reader nor an array of known
   length; but an example atom records only the predicate's arguments, so by
   the time the cells are chosen the clause's terms are gone and the array is
   what is left.  Until the index travels with the example, this is where the
   candidate cells come from. *)
(* A value an array holds, as the term it is, not a number: a cell column
   takes the array's element sort, so an element of any sort has a column to
   go to.  Reading only integers would leave every array of another element
   sort without cells, and such an input would end in an ordinary [unknown].

   The INDEX stays an integer.  The candidate cells are built by counting --
   an index, its neighbours, a short prefix -- which is an arithmetic
   operation, so an array indexed by anything else has no candidate set at
   all.  That is decided upstream, in the function that reports which arrays a
   predicate has cells for, which does not report such an array: the rule is
   about ONE ARRAY and a refusal here would be about the whole atom, and an
   atom can carry a cellable array beside one that is not. *)
(* An array value as a TRIE.  A cell is a tuple of indices -- one per level
   of the array's sort, several for a curried array -- and the value at the
   end of the chain, so an array is read as a node holding what it stores at
   each index and what it holds elsewhere, each of which is itself a node or
   a leaf.  A leaf is any term not built by an array constructor: an
   element, or an array-sorted VARIABLE -- a parameter of the example --
   which a cell reaching it reads at the remaining indices by an ordinary
   [select] chain. *)
type cell_node =
  | Leaf of Logic.term
  | Node of cell_array
  | Lam of (Logic.term -> cell_node)
      (** an array given as a [lambda] over an index that cannot be counted:
          it stores nothing enumerable, so it is kept as the function it is
          and applied to whatever index a consumer asks about -- the body,
          an [ite] chain over equalities between the bound variable and the
          example's parameters, then becomes a value that is itself an [ite]
          over those parameters, which a cell may hold.  It appears as the
          DEFAULT of a node, and a node whose default is a function applies
          it at that node's own level: [{ defv = Lam f; stored }] holds the
          stored values where they are stored and [f i] everywhere else,
          which is also what a [store] over such a lambda means. *)

and cell_array = {
  defv : cell_node;  (** what the array holds at any index not stored *)
  stored : (string * (Logic.term * cell_node)) list;
      (** keyed by the index's printed form; the index term kept beside it *)
  params : Logic.sort_env_map;
      (** the example's parameters with their sorts, which every index and
          value here may mention; carried so that a conversion back to the
          first-order representation can sort them -- with an empty
          environment that conversion raises on any parameter that is not a
          [dummy_]-named one, which a run never produces and a test does *)
  seq_len : int option;
      (** for a SEQUENCE, its length; [None] for an array.  A sequence is read
          as a one-level node storing its first elements at [0, 1, ...] (at
          most [seq_cell_cap] of them) whose default is the read [seq.nth s i]
          itself: a function, so no level of it is ever taken for constant,
          and a read at an index nothing stores stays the read it is.  Which
          indices of it may be offered as cells is bounded by this length --
          outside it the read denotes nothing the theory fixes.  [None] also
          for an OPEN sequence, one whose elements and length the term does
          not state; [seq_term] tells the two apart. *)
  seq_term : Logic.term option;
      (** for a sequence, the sequence term itself; [None] for an array.  It
          is what a range guard over an open sequence is written against:
          such a sequence has no known length, so the only statement of which
          positions are cells is [0 <= j < seq.len s]. *)
}

(* The conversion back to the first-order representation, with the example's
   parameters in its environment: every index and value here may mention them. *)
let to_old_in (arr : cell_array) t = Logic.ExtTerm.to_old_trm Map.Poly.empty arr.params t
(* The key is the Logic-level printed form and NOT the first-order conversion:
   a conversion with empty environments raises on a free variable that is not
   a [dummy_]-named parameter, which the instantiation happens to produce for
   every parameter that survives -- so a key built through it worked in a run
   and failed on the first hand-built parameter a test supplied.  Integer keys
   print the same either way, so the order candidate cells are offered in on
   integer arrays does not move. *)
let term_key (t : Logic.term) = Logic.ExtTerm.str_of t

(* An integer literal is keyed by its value, in [Z] since a model can hold
   any integer, so cells sort numerically; any other term by its printed
   form, and a printed key comes before every integer one.  The comparison is
   written out because the key holds a [Z.t]; over integers that fit a native
   int it orders exactly as [Int.compare] does. *)
let term_cell_key (t : Logic.term) : Z.t option * string =
  match t with
  | Logic.Con (Logic.IntTerm.Int z, _) -> (Some z, "")
  | _ -> (None, term_key t)

let compare_term_cell_key (z1, s1) (z2, s2) =
  match (z1, z2) with
  | Some a, Some b -> Z.compare a b
  | None, Some _ -> -1
  | Some _, None -> 1
  | None, None -> String.compare s1 s2

let cell_key ((idxs, v) : Logic.term list * Logic.term) =
  (List.map idxs ~f:term_cell_key, term_cell_key v)

let compare_cell_key (i1, v1) (i2, v2) =
  match List.compare compare_term_cell_key i1 i2 with
  | 0 -> compare_term_cell_key v1 v2
  | c -> c

let dedup_cells cells =
  List.dedup_and_sort cells ~compare:(fun a b ->
      compare_cell_key (cell_key a) (cell_key b))

(* A value is usable as a cell's index or content when every variable in it
   is a PARAMETER of the example it belongs to: the expanded atom keeps those
   parameters, so a cell at [$1] is a cell at whatever [$1] denotes, exactly
   as the example itself is.  Anything else free would be a variable the
   example does not bind.  Requiring a CLOSED term instead would refuse every
   example over a quantified sort -- whose parameters survive instantiation
   by design -- and so every input whose array is a trait predicate over
   such a sort. *)
let usable ~(params : Logic.sort_env_map) (t : Logic.term) =
  Set.is_subset (Logic.Term.fvs_of t) ~of_:(Map.key_set params)

(* [usable], or a DUMMY constant: the value the instantiation of a parametric
   example puts a parameter at ([ExAtom.instantiate] grounds a parameter of a
   sort with no chosen point at a registered [dummy_] constant).  Such a
   constant stands for an arbitrary value of its sort -- the synthesis query
   quantifies every dummy universally -- so a cell read from it is a read of
   an arbitrary array or sequence, exactly as a cell read from a parameter is.
   It is already an argument of the atom the cells are appended to, so a cell
   mentioning it brings no new free symbol into any query. *)
let usable_or_dummy ~(params : Logic.sort_env_map) (t : Logic.term) =
  Set.for_all (Logic.Term.fvs_of t) ~f:(fun x ->
      Map.Poly.mem params x || LogicOld.is_dummy_term x None)

let is_array_expr (t : Logic.term) =
  let open Logic in
  match t with
  | App (Con (ArrayTerm.AConst _, _), _, _)
  | App (Con (ArrayTerm.ALambda _, _), _, _) ->
      true
  | App (App (App (Con (ArrayTerm.AStore _, _), _, _), _, _), _, _) -> true
  | _ -> false

(* [params] is the example's parameters WITH their sorts, because the
   simplifier that evaluates a lambda's body at an index converts through the
   first-order representation and needs a sort for every free variable it
   meets; with an empty environment it raises on the first parameter that is
   not a [dummy_]-named one -- which every parameter the instantiation leaves
   behind happens to be, so a run never saw it and a test did at once. *)
let eval_array_expr ~(params : Logic.sort_env_map) (t : Logic.term) : cell_array =
  let open Logic in
  let rec node (t : term) : cell_node =
    if is_array_expr t then Node (inner t)
    else if usable_or_dummy ~params t then Leaf t
    else refuse_array t
  and inner (t : term) : cell_array =
    match t with
    | App (Con (ArrayTerm.AConst _, _), default_value, _) ->
        { defv = node default_value; stored = []; params; seq_len = None; seq_term = None }
    | App (Con (ArrayTerm.ALambda (si, _), _), Bin (Lambda, x, _, body, _), _)
      -> (
        (* sampled at the integer literals the body mentions and at 0; only
           an integer index has literals to sample at *)
        match si with
        | IntTerm.SInt ->
            let sample idx =
              node
              @@ ExtTerm.simplify_term Map.Poly.empty params
              @@ ExtTerm.subst
                   (Map.Poly.singleton x (IntTerm.mk_int idx)
                     : Logic.term_subst_map)
                   body
            in
            let stored =
              List.filter_map (collect_const body) ~f:(fun idx ->
                  if Z.equal idx Z.zero then None
                  else
                    let it = IntTerm.mk_int idx in
                    Some (term_key it, (it, sample idx)))
            in
            { defv = sample Z.zero; stored; params; seq_len = None; seq_term = None }
        | _ ->
            (* no literal to sample at: keep the function and apply it to
               the index a consumer asks about.  Wrapped as a one-level
               array whose default is the closure, so that the levels below
               stay addressable by the same walk *)
            {
              defv =
                Lam
                  (fun i ->
                    node
                    @@ ExtTerm.simplify_term Map.Poly.empty params
                    @@ ExtTerm.subst
                         (Map.Poly.singleton x i : Logic.term_subst_map)
                         body);
              stored = [];
              params;
              seq_len = None;
              seq_term = None;
            })
    (* store (a, idx, v) is the array that holds v at idx and agrees with a
       everywhere else *)
    | App (App (App (Con (ArrayTerm.AStore _, _), array, _), idx, _), value, _)
      ->
        let arr = inner array in
        if not (usable ~params idx) then refuse_array t
        else
          let k = term_key idx in
          {
            arr with
            stored =
              (k, (idx, node value))
              :: List.filter arr.stored ~f:(fun (k', _) ->
                     not (String.equal k k'));
          }
    | _ -> refuse_array t
  in
  inner t

(* --- Sequences ------------------------------------------------------------

   A sequence value as a solver model writes it -- [seq.empty], [seq.unit] and
   [seq.++] -- is a finite list of elements, and its cells are the pairs
   (i, element i) for [0 <= i < length].  There is no default: nothing beyond
   the length is part of the value. *)

(* At most this many of a sequence's leading positions are offered as cells.
   The array reader's candidate set is bounded by what the model stores (each
   stored index, its neighbours, a prefix of six); a sequence stores every
   position below its length, so without a bound a long counterexample would
   multiply the celled clauses by its length.  Eight covers the prefix and the
   first stored positions the array reader would offer. *)
let seq_cell_cap = 8

(* The elements of a sequence term whose structure fixes them, in order:
   [seq.empty], [seq.unit e], a concatenation of such, and a store at a literal
   index (which replaces the element there when the index is inside and changes
   nothing otherwise).  [None] for anything else -- a variable, an extraction,
   a store at a symbolic index -- whose elements the term does not state. *)
let rec seq_elements_old (t : LogicOld.Term.t) : LogicOld.Term.t list option =
  let open LogicOld in
  match t with
  | Term.FunApp (T_seq.SqEmpty _, [], _) -> Some []
  | Term.FunApp (T_seq.SqUnit _, [ e ], _) -> Some [ e ]
  | Term.FunApp (T_seq.SqConcat _, [ s1; s2 ], _) -> (
      match (seq_elements_old s1, seq_elements_old s2) with
      | Some l1, Some l2 -> Some (l1 @ l2)
      | _ -> None)
  | Term.FunApp (T_seq.SqStore _, [ s; i; e ], _) -> (
      match (seq_elements_old s, T_int.let_int i) with
      | Some l, z ->
          (* compared in [Z]: a store at an index beyond a native int is
             outside every literal sequence and changes nothing *)
          Some (List.mapi l ~f:(fun n x -> if Z.equal (Z.of_int n) z then e else x))
      | None, _ -> None
      | exception exn_ when not (Common.Timer.is_async exn_) -> None)
  | _ -> None

(* The read [seq.nth s i] in the higher-order representation. *)
let seq_nth ~(elem_sort : LogicOld.Sort.t) (s : Logic.term) (i : Logic.term) :
    Logic.term =
  Logic.Term.mk_apps
    (Logic.SeqTerm.mk_nth (Logic.ExtTerm.of_old_sort elem_sort))
    [ s; i ]

(* The SENTINEL cell of a sequence: one extra cell at index [-1], outside every
   sequence's positions, holding a fixed value of the element sort.  With it the
   read-back of a candidate [phi] is

     phi(-1, d, x..) /\ forall j. 0 <= j < seq.len s => phi(j, seq.nth s j, x..)

   written as one universal, [forall j. (j = -1 \/ 0 <= j < seq.len s) =>
   phi(j, ite (j = -1) d (seq.nth s j), x..)], which is the same formula.

   What it buys is a statement about the predicate's other arguments that
   holds on the EMPTY sequence too.  Without it every candidate is true on
   [seq.empty], a universal over no positions, so a counterexample that makes
   the predicate false there -- [I(seq.empty, 0, -1) => false], the first one a
   loop over a sequence whose reads are not bounded by its length produces --
   is satisfied by no candidate at all and the synthesis query stays
   unsatisfiable however the shape grows.  The sentinel instance is where a
   scalar conjunct of [phi], such as [i < seq.len s], survives; a candidate
   that means to say nothing at the sentinel says [j < 0] there, one disjunct.

   The value never reads the sequence, so no read outside the length enters
   the read-back or an example: the formula is range-guarded, the sentinel's
   instance mentioning no read at all.  Only an index nothing else can hold is
   usable, which is why it is negative. *)
let seq_sentinel_index = -1

(* The sentinel's value: the element sort's plain constant ([0], [false], the
   zero bit-vector).  Any theory-fixed value would do; one fixed value is what
   makes the example side and the read-back agree. *)
let seq_sentinel_value (elem_sort : LogicOld.Sort.t) : Logic.term =
  Logic.ExtTerm.of_old_term (LogicOld.Term.mk_dummy elem_sort)

let is_sentinel_index = function
  | Logic.Con (Logic.IntTerm.Int z, _) -> Z.equal z (Z.of_int seq_sentinel_index)
  | _ -> false

(* Does this sequence reading carry the sentinel cell?  Only the sequence
   reader stores an index below zero, and only when asked to. *)
let has_seq_sentinel (arr : cell_array) =
  Option.is_some arr.seq_term
  && List.exists arr.stored ~f:(fun (_, (i, _)) -> is_sentinel_index i)

(* A sequence term, read as cells.  [t] is the sequence as the example holds
   it, already simplified.  With [sentinel] the sentinel cell is stored beside
   the positions.

   A sequence whose elements the term does not state -- a parameter of the
   example, the dummy constant the instantiation put one at, an extraction --
   is OPEN: its length is unknown, so no position can be offered as a cell
   without a range premise the ground expansion has no place for (a read past
   the length is a value the theory leaves open, and demanding a candidate at
   it would be a demand the example does not make).  With the sentinel it is
   read as the sentinel cell alone, with the read [seq.nth s i] as the default
   for any symbolic index a parametric cell asks about; that offers exactly the
   one cell every sequence has whatever its length.  Without the sentinel there
   is no cell to offer and the term is refused, as it always was: an atom whose
   predicate's template has cell columns cannot be left without them.  Also
   refused when the term mentions a variable that is neither a parameter nor a
   dummy constant, since a cell at it would be a cell at nothing. *)
let eval_seq_expr ?(sentinel = false) ~(params : Logic.sort_env_map)
    ~(elem_sort : LogicOld.Sort.t) (t : LogicOld.Term.t) : cell_array =
  match seq_elements_old t with
  | None ->
      let s = Logic.ExtTerm.of_old_term t in
      if not (sentinel && usable_or_dummy ~params s) then refuse_array s
      else
        let it = Logic.IntTerm.mk_from_int seq_sentinel_index in
        {
          defv = Lam (fun i -> Leaf (seq_nth ~elem_sort s i));
          stored = [ (term_key it, (it, Leaf (seq_sentinel_value elem_sort))) ];
          params;
          seq_len = None;
          seq_term = Some s;
        }
  | Some elems ->
      let s = Logic.ExtTerm.of_old_term t in
      let stored =
        List.filter_mapi (List.take elems seq_cell_cap) ~f:(fun i e ->
            let e = Logic.ExtTerm.of_old_term e in
            if not (usable ~params e) then None
            else
              let it = Logic.IntTerm.mk_from_int i in
              Some (term_key it, (it, Leaf e)))
      in
      let stored =
        if not sentinel then stored
        else
          let it = Logic.IntTerm.mk_from_int seq_sentinel_index in
          (term_key it, (it, Leaf (seq_sentinel_value elem_sort))) :: stored
      in
      {
        defv = Lam (fun i -> Leaf (seq_nth ~elem_sort s i));
        stored;
        params;
        seq_len = Some (List.length elems);
        seq_term = Some s;
      }

(* Does the example's value at this path offer no cell at all because it is an
   EMPTY sequence?  Such a sequence has no position, so the celled reading of
   any predicate over it, [forall j. 0 <= j < seq.len s => phi], holds
   whatever [phi] is: the atom is true under every candidate the template can
   read back.  The expansion uses this to drop the atom (a body assumption that
   always holds) or the clause (a head that always holds) instead of declining
   to expand it.  A sequence carrying the sentinel cell is never vacuous: the
   sentinel is a cell it offers whatever its length. *)
let vacuous_sequence (arr : cell_array) =
  match arr.seq_len with Some 0 -> List.is_empty arr.stored | _ -> false

(* [arr] read at [idxs], one [select] per level, each at the sort of the
   levels that remain below it. *)
let select_chain ~(index_sorts : LogicOld.Sort.t list) ~elem_sort
    (arr : Logic.term) (idxs : Logic.term list) : Logic.term =
  let rec sel arr sorts idxs =
    match (sorts, idxs) with
    | si :: rest, i :: irest ->
        let se = CellQual.curried_sort_of rest elem_sort in
        sel
          (Logic.Term.mk_app
             (Logic.Term.mk_app
                (Logic.Term.mk_con
                   (Logic.ArrayTerm.ASelect
                      ( Logic.ExtTerm.of_old_sort si,
                        Logic.ExtTerm.of_old_sort se )))
                arr)
             i)
          rest irest
    | _ -> arr
  in
  sel arr index_sorts idxs

(* An array the term does not construct -- a parameter of the example, or the
   dummy constant the instantiation put one at -- read as cells.  Its value at
   an index [i] is the read [select v i] and nothing else: no index is stored,
   so every index reads through the default, which is that read as a function
   of the index (at the outermost level; a curried array's read is itself an
   array, which [value_at] reads on by a select chain as it does any
   array-sorted leaf).  Nothing about it is guessed, so it is exact in the same
   sense as a lambda kept as a function; the candidate indices then come from
   the prefix, the atom's arguments and any witnesses, as for an array that
   stores nothing.  The sorts come from the PATH, because a higher-order
   variable carries no sort of its own.  Refusing it instead would end the
   whole run with [unknown], although the cells of every other example are
   readable. *)
let eval_open_array ~(params : Logic.sort_env_map) ~(path : CellQual.array_path)
    (v : Logic.term) : cell_array =
  match path.CellQual.index_sorts with
  | [] -> refuse_array v
  | si :: rest ->
      let se = CellQual.curried_sort_of rest path.CellQual.elem_sort in
      {
        defv =
          Lam (fun i -> Leaf (select_chain ~index_sorts:[ si ] ~elem_sort:se v [ i ]));
        stored = [];
        params;
        seq_len = None;
        seq_term = None;
      }

(* The cells of the value a path reaches in an example's argument: the array
   reader for an array, the sequence reader for a sequence. *)
let eval_path ?(sentinel = false) ~(params : Logic.sort_env_map)
    (path : CellQual.array_path) (value : LogicOld.Term.t) : cell_array =
  match path.CellQual.container with
  | CellQual.Array -> (
      let t = Logic.ExtTerm.of_old_term value in
      match t with
      | Logic.Var _ when usable_or_dummy ~params t -> eval_open_array ~params ~path t
      | _ -> eval_array_expr ~params t)
  | CellQual.Sequence ->
      eval_seq_expr ~sentinel ~params ~elem_sort:path.CellQual.elem_sort value

(* The array's value at an index tuple, as a term of the element sort.  A
   leaf met before the tuple is spent is an array-sorted parameter and is
   read at the remaining indices by [select]s. *)
let rec value_at ~(index_sorts : LogicOld.Sort.t list) ~elem_sort
    (n : cell_node) (idxs : Logic.term list) : Logic.term =
  match (n, idxs) with
  | Leaf v, [] -> v
  | Leaf v, _ -> select_chain ~index_sorts ~elem_sort v idxs
  | Lam f, i :: rest -> value_at ~index_sorts:(List.tl_exn index_sorts) ~elem_sort (f i) rest
  | Lam _, [] -> assert false
  | Node arr, i :: rest ->
      let next =
        match List.Assoc.find arr.stored ~equal:String.equal (term_key i) with
        | Some (_, n) -> n
        | None -> ( match arr.defv with Lam f -> f i | d -> d)
      in
      value_at ~index_sorts:(List.tl_exn index_sorts) ~elem_sort next rest
  | Node _, [] ->
      (* the tuple is shorter than the array is deep: the path and the value
         disagree about the array's sort, which the path's construction
         excludes *)
      assert false

(* The same read following the DEFAULT at every level: what the array holds
   at a tuple none of whose indices is stored. *)
let rec default_read ~index_sorts ~elem_sort (n : cell_node) idxs =
  match (n, idxs) with
  | Leaf _, _ -> value_at ~index_sorts ~elem_sort n idxs
  | Lam f, i :: rest ->
      (* a function stores nothing, so its "default" at an index is its value
         there *)
      default_read ~index_sorts:(List.tl_exn index_sorts) ~elem_sort (f i) rest
  | Lam _, [] -> assert false
  | Node arr, i :: rest ->
      default_read ~index_sorts:(List.tl_exn index_sorts) ~elem_sort
        (match arr.defv with Lam f -> f i | d -> d)
        rest
  | Node _, [] -> assert false

(* The indices stored at level [k] anywhere in the trie, deduplicated by
   printed form: level 0 is the array's own stored indices, level 1 those of
   every array it holds, stored or default, and so on. *)
let stored_at_level (arr : cell_array) k : Logic.term list =
  let rec go n k acc =
    match n with
    | Leaf _ -> acc
    (* a function's stores cannot be enumerated; the levels below it take
       their candidates from the atom's arguments and the sort's elements *)
    | Lam _ -> acc
    | Node arr ->
        if k = 0 then
          List.fold arr.stored ~init:acc ~f:(fun acc (key, (i, _)) ->
              if List.Assoc.mem acc ~equal:String.equal key then acc
              else (key, i) :: acc)
        else
          List.fold
            (arr.defv :: List.map arr.stored ~f:(fun (_, (_, n)) -> n))
            ~init:acc
            ~f:(fun acc n -> go n (k - 1) acc)
  in
  List.rev_map (go (Node arr) k []) ~f:snd

(* The candidate indices of one array, PER LEVEL.

   An INTEGER level offers every stored index, its two neighbours and a short
   prefix -- the neighbours because a region holding the default is
   indistinguishable from the inside and distinguishable only at a boundary, so
   stored indices alone can miss the very cell that refutes an example -- plus
   the [witnesses] a refutation named and whatever [extra] the caller collected
   from the atom; with [from_array] false only the extra, which is the
   "candidates from the arguments only" setting.  A level of a sort that cannot
   be counted offers what the array stores there, the [extra] terms of that
   sort, and every element of a finite enumeration; nothing else can propose an
   index.  Each level is deduplicated and sorted, integers numerically and
   other terms by printed form, so the order cells are offered in is a function
   of the input alone. *)
let level_candidates ~(path : CellQual.array_path) ~(extra : Logic.term list list)
    ~from_array ~(witnesses : Z.t list) (array : cell_array) :
    Logic.term list list =
  if CellQual.is_sequence path then
    (* a sequence offers exactly the positions it stores, which are inside
       its length by construction; the filter restates that, because an index
       outside it would be a cell whose value no model agrees on.  The one
       exception is the sentinel, whose value is stored rather than read. *)
    let len = Option.value array.seq_len ~default:0 in
    [
      List.filter (stored_at_level array 0) ~f:(function
        | Logic.Con (Logic.IntTerm.Int z, _) ->
            (Z.leq Z.zero z && Z.lt z (Z.of_int len))
            || Z.equal z (Z.of_int seq_sentinel_index)
        | _ -> false)
      |> List.dedup_and_sort ~compare:(fun a b ->
             String.compare (term_key a) (term_key b))
      |> List.sort ~compare:(fun a b ->
             match (a, b) with
             | Logic.Con (Logic.IntTerm.Int x, _), Logic.Con (Logic.IntTerm.Int y, _) ->
                 Z.compare x y
             | _ -> 0);
    ]
  else
  List.mapi path.CellQual.index_sorts ~f:(fun k si ->
      let stored = stored_at_level array k in
      let extra = Option.value (List.nth extra k) ~default:[] in
      if LogicOld.Term.is_int_sort si then
        (* in [Z]: a model may store at an index beyond a native int, and that
           index and its neighbours are candidates like any other; [Z.compare]
           orders the ones that fit exactly as [Int.compare] did *)
        let ints ts =
          List.filter_map ts ~f:(function
            | Logic.Con (Logic.IntTerm.Int z, _) -> Some z
            | _ -> None)
        in
        let cands =
          (if not from_array then []
           else
             List.concat_map (ints stored) ~f:(fun i -> [ Z.pred i; i; Z.succ i ])
             @ List.init 6 ~f:Z.of_int @ witnesses)
          @ ints extra
        in
        List.map (List.dedup_and_sort cands ~compare:Z.compare)
          ~f:Logic.IntTerm.mk_int
      else
        let elements =
          Option.value ~default:[] (CellQual.enum_elements si)
          |> List.map ~f:Logic.ExtTerm.of_old_term
        in
        List.dedup_and_sort (stored @ extra @ elements) ~compare:(fun a b ->
            String.compare (term_key a) (term_key b)))

(* Every combination of the per-level candidates, with the value the array
   holds there.  A level with no candidate makes the array offer no cell, which
   the callers report and fall back from. *)
let cell_tuples ~(path : CellQual.array_path) (array : cell_array)
    (per_level : Logic.term list list) : (Logic.term list * Logic.term) list =
  if List.exists per_level ~f:List.is_empty then []
  else
    let tuples =
      List.fold_right per_level ~init:[ [] ] ~f:(fun cands acc ->
          List.concat_map cands ~f:(fun c -> List.map acc ~f:(fun rest -> c :: rest)))
    in
    List.map tuples ~f:(fun idxs ->
        ( idxs,
          value_at ~index_sorts:path.CellQual.index_sorts
            ~elem_sort:path.CellQual.elem_sort (Node array) idxs ))

(* The integer VALUES other arrays hold at their offered cells, as candidate
   indices for an integer level of one more array.

   [cells] is one cell list per other array (for a sequence, its cells are its
   in-range stored positions, so every value here is one the model fixes).
   Only a value that is an integer literal is taken.  The result is
   deduplicated, keeps the first occurrence's order -- the arrays in the order
   given, each array's cells in its offer order -- and holds at most [limit]
   values; [limit <= 0] gives none.

   What it is for: an invariant may read one array at a value another holds,
   [q(c, v[k])] for a sequence [v]; the witness cell is then at the index
   [v[k]], which neither the reading array's own offer nor the atom's integer
   arguments contain, since the value is inside another array. *)
let int_values_of_cells ~limit (cells : (Logic.term list * Logic.term) list list) :
    Logic.term list =
  if limit <= 0 then []
  else
    let _, rev =
      List.fold (List.concat cells) ~init:(Set.Poly.empty, [])
        ~f:(fun ((seen, acc) as st) (_, v) ->
          match v with
          | Logic.Con (Logic.IntTerm.Int z, _) when not (Set.mem seen z) ->
              (Set.add seen z, v :: acc)
          | _ -> st)
    in
    List.take (List.rev rev) limit

(* [extra] (one term list per level of [path]) with [values] added at every
   INTEGER level; a level of any other sort is left as it is, since an integer
   value cannot index it. *)
let add_at_int_levels ~(path : CellQual.array_path) (extra : Logic.term list list)
    (values : Logic.term list) : Logic.term list list =
  if List.is_empty values then extra
  else
    List.mapi path.CellQual.index_sorts ~f:(fun k si ->
        let e = Option.value (List.nth extra k) ~default:[] in
        if LogicOld.Term.is_int_sort si then e @ values else e)

(* Whether an example clause's celled body atoms get [goal_cell_variants]:
   [limit] variants are asked for, and the clause is a goal (no positive atom)
   or [step_bodies] extends the offer to the body of a clause with a head.
   Either way only body atoms get variants: an added body tuple is one more
   disjunct [not phi] of the clause's constraint, which only weakens it, while
   an added head tuple would strengthen it. *)
let offers_value_variants ~limit ~step_bodies ~has_positive =
  limit > 0 && ((not has_positive) || step_bodies)

(* The extra cells a GOAL example's celled body atom is worth offering, as
   variants of one atom's cells [slots] -- one [(path index, (indices, value))]
   per cell column, in the order the atom carries them.  Each variant changes
   at most two cells of [slots], one of them at up to two levels, and keeps
   the rest:
   - a SEQUENCE cell moved to another in-range position of that sequence (its
     length known, at most [seq_cell_cap] positions);
   - then, from [slots] and from each of those, one index level of an ARRAY
     cell replaced: an integer level by a value the variant's own cells hold
     (an integer literal) or by one of [extra_values], in that order; a level
     of any other sort by one of [level_terms] of that sort (the terms the
     atom's arguments reach, which is all that can index such a level);
   - last, a second level of the array cell just moved, the same way.
   The value of a changed cell is read off the array at its new indices, so
   every variant is a true cell tuple of the counterexample.  The result is
   deduplicated, excludes [slots] itself, and holds at most [limit] variants;
   per variant, [Some cell] for a changed column and [None] for one kept.

   Why: a goal example [N(t)] under the read-back [forall cells. phi] means
   [exists cells. not phi], and its synthesis constraint is the disjunction of
   [not phi] over the offered tuples.  A solution is excluded when it holds at
   every offered tuple while failing at one not offered, and the tuple where
   an invariant [q(c, v[k])] fails pairs a position [k] of one sequence with
   the index [v[k]] of another array -- a value another cell holds, which no
   array's own offer contains -- an invariant bounding an index from below
   fails only at a negative index, which a constant array never offers, and a
   read [q(cur y)] fails at the argument term [cur y], which a sampled tuple
   holds only by luck.
   Adding tuples to a goal's body only adds disjuncts, so it cannot make the
   loop accept a candidate the example refutes. *)
let goal_cell_variants ?(linked_first = false) ~(paths : CellQual.array_path list)
    ~(arrays : (int * cell_array) list) ~(extra_values : Logic.term list)
    ~(level_terms : LogicOld.Sort.t -> Logic.term list) ~limit
    (slots : (int * (Logic.term list * Logic.term)) list) :
    (Logic.term list * Logic.term) option list list =
  if limit <= 0 then []
  else
    let path_of k = List.nth_exn paths k in
    let array_of k = List.Assoc.find_exn arrays ~equal:Int.equal k in
    let read k idxs =
      let path = path_of k in
      value_at ~index_sorts:path.CellQual.index_sorts
        ~elem_sort:path.CellQual.elem_sort (Node (array_of k)) idxs
    in
    let same a b = String.equal (term_key a) (term_key b) in
    let replace v i cell =
      List.mapi v ~f:(fun j ((k, _, _) as s) -> if j = i then (k, cell, true) else s)
    in
    let base = List.map slots ~f:(fun (k, c) -> (k, c, false)) in
    let seq_moves v =
      List.concat_mapi v ~f:(fun i (k, (idxs, _), _) ->
          let path = path_of k in
          if not (CellQual.is_sequence path) then []
          else
            match ((array_of k).seq_len, idxs) with
            | Some n, [ cur ] ->
                List.filter_map (List.init (min n seq_cell_cap) ~f:Fn.id) ~f:(fun j ->
                    let j = Logic.IntTerm.mk_from_int j in
                    if same cur j then None else Some (replace v i ([ j ], read k [ j ])))
            | _ -> [])
    in
    let held v =
      let _, rev =
        List.fold
          (List.map v ~f:(fun (_, (_, value), _) -> value) @ extra_values)
          ~init:(Set.Poly.empty, [])
          ~f:(fun ((seen, acc) as st) t ->
            match t with
            | Logic.Con (Logic.IntTerm.Int z, _) when not (Set.mem seen z) ->
                (Set.add seen z, t :: acc)
            | _ -> st)
      in
      List.rev rev
    in
    let level_moves ?(only_changed = false) v =
      let ws = held v in
      List.concat_mapi v ~f:(fun i (k, (idxs, _), changed) ->
          let path = path_of k in
          if CellQual.is_sequence path || (only_changed && not changed) then []
          else
            List.concat_mapi path.CellQual.index_sorts ~f:(fun l si ->
                let ws = if LogicOld.Term.is_int_sort si then ws else level_terms si in
                List.filter_map ws ~f:(fun w ->
                    if same (List.nth_exn idxs l) w then None
                    else
                      let idxs = List.mapi idxs ~f:(fun l' x -> if l' = l then w else x) in
                      Some (replace v i (idxs, read k idxs)))))
    in
    let moved = seq_moves base in
    let key v =
      List.map v ~f:(fun (k, (idxs, value), _) ->
          (k, List.map idxs ~f:term_key, term_key value))
    in
    let singles = List.concat_map (base :: moved) ~f:(level_moves ~only_changed:false) in
    (* a second level of a cell already moved: the tuple [(cur it, -1)] is two
       levels away from a base cell [(c, 2)] *)
    let doubles =
      List.concat_map singles ~f:(fun v ->
          if List.exists v ~f:(fun (k, _, ch) -> ch && not (CellQual.is_sequence (path_of k)))
          then level_moves ~only_changed:true v
          else [])
    in
    let _, rev =
      List.fold
        (moved @ singles @ doubles)
        ~init:(Set.Poly.singleton (key base), [])
        ~f:(fun ((seen, acc) as st) v ->
          let kv = key v in
          if Set.mem seen kv then st else (Set.add seen kv, v :: acc))
    in
    (* [linked_first]: the variants in which a changed ARRAY cell has an
       integer index equal to the value a SEQUENCE cell of the same variant
       holds come first, in their order, before [limit] cuts the list.  That
       pair is the tuple where [q(c, v[k])] fails; it is two or three moves
       from a base tuple (the sequence cell, the integer level, and the other
       level to [c]), so it is generated late, and with several arrays and
       argument terms the plain order fills the limit before it. *)
    let all = List.rev rev in
    let all =
      if not linked_first then all
      else
        let linked v =
          let seq_values =
            List.filter_map v ~f:(fun (k, (idxs, value), _) ->
                match idxs with
                | [ Logic.Con (Logic.IntTerm.Int z, _) ]
                  when CellQual.is_sequence (path_of k)
                       && not (Z.equal z (Z.of_int seq_sentinel_index)) ->
                    Some (term_key value)
                | _ -> None)
          in
          (not (List.is_empty seq_values))
          && List.exists v ~f:(fun (k, (idxs, _), changed) ->
                 changed
                 && (not (CellQual.is_sequence (path_of k)))
                 && List.exists2_exn idxs (path_of k).CellQual.index_sorts ~f:(fun x si ->
                        LogicOld.Term.is_int_sort si
                        && List.mem seq_values (term_key x) ~equal:String.equal))
        in
        let first, rest = List.partition_tf all ~f:linked in
        first @ rest
    in
    List.map (List.take all limit) ~f:(fun v ->
        List.map v ~f:(fun (_, c, changed) -> if changed then Some c else None))

(* The read [a[j1]..[jn]] at SYMBOLIC indices, written out against the
   concrete array the counterexample gave: at each level, [ite (j = i1) ...
   (... default)].  It has to be written out rather than left as [select a j],
   because the evaluator cannot reduce a select at a variable index and the
   term would then carry an array into a universally quantified query -- the
   one shape this tree has measured not to come back: the input that answers
   [sat,14] with the array left in place ran past 120 s.  The expansion is
   exact, since [eval_array_expr] refuses any array it cannot read, a parameter
   met as a leaf is read by a [select] chain at the remaining indices, and a
   function default is applied to the symbolic index at its own level. *)
let read_at_symbolic ~(path : CellQual.array_path) (array : cell_array)
    (js : LogicOld.Term.t list) : LogicOld.Term.t =
  (* the symbolic indices are in scope too: a function default applied to one
     -- a sequence's read past its stored positions, a lambda over an index
     that cannot be counted -- returns a term mentioning it *)
  let to_old =
    let senv =
      List.fold js ~init:array.params ~f:(fun acc j ->
          Set.fold (LogicOld.Term.term_sort_env_of j) ~init:acc ~f:(fun acc (x, srt) ->
              Map.Poly.set acc ~key:x ~data:(Logic.ExtTerm.of_old_sort srt)))
    in
    Logic.ExtTerm.to_old_trm Map.Poly.empty senv
  in
  let rec go n js sorts =
    match (n, js) with
    | Leaf _, _ ->
        to_old
        @@ value_at ~index_sorts:sorts ~elem_sort:path.CellQual.elem_sort n
             (List.map js ~f:Logic.ExtTerm.of_old_term)
    | Lam f, j :: rest -> go (f (Logic.ExtTerm.of_old_term j)) rest (List.tl_exn sorts)
    | Lam _, [] -> assert false
    | Node arr, j :: rest ->
        let sorts' = List.tl_exn sorts in
        let dflt =
          match arr.defv with Lam f -> f (Logic.ExtTerm.of_old_term j) | d -> d
        in
        List.fold arr.stored ~init:(go dflt rest sorts') ~f:(fun acc (_, (i, n)) ->
            LogicOld.T_bool.mk_if_then_else
              (LogicOld.T_bool.of_formula @@ LogicOld.Formula.eq j (to_old i))
              (go n rest sorts') acc)
    | Node _, [] -> assert false
  in
  go (Node array) js path.CellQual.index_sorts

(* The tuples of the exhaustive expansion over SEVERAL arrays: every combination
   of one cell per array.  With one array it is that array's cells; with two it
   is the pairs, and that is the case a per-array draw hid -- an invariant
   relating two arrays is refuted at a PAIR of indices, so an expansion that
   draws each array's cell independently has the witness only by luck
   (measured on a slice walk whose witness pair is (0, 0): the drawn pairs were
   (5,2), (2,1), (3,2), (1,1), and the correct invariant was rejected by all).

   The product is bounded because it is a product; past [bound] the caller
   keeps the sampled path, which is weaker and sound, and an array with no cell
   offers nothing.  With [related] given, a tuple is kept only when the first
   INTEGER index of every cell lies within one of those offsets of the first
   cell's -- the offsets being 0 and the atom's own integer arguments -- and a
   cell with no integer level is never excluded. *)
type product =
  | Empty  (** some array offered no cell *)
  | Over of int  (** the product's size, above the bound *)
  | Tuples of (Logic.term list * Logic.term) list list
      (** one cell per array, in the arrays' order *)

let array_product ~bound ?(related : Z.t list option) (per_array : (Logic.term list * Logic.term) list list) : product =
  if List.exists per_array ~f:List.is_empty then Empty
  else
    let size = List.fold per_array ~init:1 ~f:(fun a l -> a * List.length l) in
    if size > bound then Over size
    else
      let all =
        List.fold_right per_array ~init:[ [] ] ~f:(fun cells acc ->
            List.concat_map cells ~f:(fun c -> List.map acc ~f:(fun rest -> c :: rest)))
      in
      match related with
      | None -> Tuples all
      | Some _ when List.length per_array < 2 -> Tuples all
      | Some offsets ->
          (* indices and offsets in [Z]: either may be a model integer beyond a
             native int, and the difference of two that fit need not fit *)
          let first_int (idxs, _) =
            List.find_map idxs ~f:(function
              | Logic.Con (Logic.IntTerm.Int z, _) -> Some z
              | _ -> None)
          in
          Tuples
            (List.filter all ~f:(fun tuple ->
                 match List.map tuple ~f:first_int with
                 | Some i1 :: rest ->
                     List.for_all rest ~f:(function
                       | Some i2 ->
                           List.exists offsets ~f:(fun o ->
                               Z.equal (Z.sub i2 i1) o || Z.equal (Z.sub i1 i2) o)
                       | None -> true)
                 | _ -> true))

(* The tuples of the SWEEP that stands in for the product when the product is
   over its bound: every array held at the cell of [base] (one cell per array,
   in the arrays' order) except one, which ranges over all of its candidates
   [per_array.(k)], for each [k] in turn.  [base] itself comes first, and no
   tuple is listed twice.

   Size: when every cell of [base] is among its array's candidates, the base is
   one of the varied tuples of every array, so the list has exactly
   [sum_k |C_k| - (m - 1)] tuples for [m] arrays; a base cell outside its
   candidates adds the base itself once more.  Contents: the base always, and,
   when the base's cells are candidates, only tuples of the product.  So with
   [S] the base, [W] this list and [P] the product,
   [S <= W <= P] -- what the caller's contract rests on.

   With [related] (see [array_product]) a varied tuple is kept only when it is
   related as the product would require; the base is kept regardless, since
   the caller's single-sample fallback offers it unfiltered. *)
let array_sweep ?(related : Z.t list option) ~(base : (Logic.term list * Logic.term) list)
    (per_array : (Logic.term list * Logic.term) list list) :
    (Logic.term list * Logic.term) list list =
  let keep =
    match related with
    | Some (_ :: _ as offsets) when List.length per_array >= 2 -> (
        fun tuple ->
          match array_product ~bound:Int.max_value ~related:offsets (List.map tuple ~f:(fun c -> [ c ])) with
          | Tuples [ _ ] -> true
          | _ -> false)
    | _ -> fun _ -> true
  in
  let varied =
    List.concat_mapi per_array ~f:(fun k cells ->
        List.filter_map cells ~f:(fun c ->
            let tuple = List.mapi base ~f:(fun k' b -> if k' = k then c else b) in
            if keep tuple then Some tuple else None))
  in
  let key tuple = List.map tuple ~f:cell_key in
  let compare_key = List.compare compare_cell_key in
  let seen = ref [] in
  List.filter (base :: varied) ~f:(fun tuple ->
      let k = key tuple in
      if List.mem !seen k ~equal:(fun a b -> compare_key a b = 0) then false
      else (
        seen := k :: !seen;
        true))

(* A head atom's cells as PARAMETERS rather than samples: per cell, one fresh
   index variable per level and the value the atom's own array holds at that
   symbolic tuple.  The result is what a parametric example needs -- the fresh
   variables with their sorts, the appended column sorts and arguments, and a
   guard -- and the caller binds it with [forall], meaning to state what the
   concretization says the example means, [forall j. P#(j, a[j], x..)].  It
   does not reach the solver in that form: a template hole is evaluated at the
   atom's truth-table row, which puts every parameter, [j] among them, at its
   default, so a hole sees the atom at one index; and the array read here is
   the one the example was grounded at, not the array it quantifies over.
   [exact_parametric_cells] below is the form that keeps both.

   Two forms.  [~full:true] writes the read out against the concrete array, an
   [ite] chain over the stored indices ending in the default, and needs no
   guard.  [~full:false] covers only the tuples at which NOTHING is stored: the
   guard says each index differs from every index stored at its level, and the
   value is what the defaults hold there -- the stored tuples are then covered
   by the exhaustive expansion, which is why a caller emits both. *)
let parametric_cells ~full ~(path : CellQual.array_path) (array : cell_array)
    ~(qpa : int) :
    (Ident.tvar * LogicOld.Sort.t) list
    * LogicOld.Sort.t list
    * LogicOld.Term.t list
    * LogicOld.Formula.t list =
  let params = ref [] and extra_sorts = ref [] and extra_args = ref [] in
  let conds = ref [] in
  List.iter (List.init qpa ~f:Fn.id) ~f:(fun _ ->
      let jts =
        List.map path.CellQual.index_sorts ~f:(fun si ->
            let j = Ident.mk_fresh_tvar () in
            params := (j, si) :: !params;
            LogicOld.Term.mk_var j si)
      in
      extra_sorts := !extra_sorts @ path.CellQual.index_sorts @ [ path.CellQual.elem_sort ];
      (* a sequence cell is a cell only inside the sequence: the parametric
         index ranges over [0, length), and the example says nothing outside
         it -- the read there is a value the theory leaves open.  With the
         sentinel the range starts at its index, where the value is the stored
         constant and not a read (the [ite] chain below takes it from the
         stored cells) *)
      (match (path.CellQual.container, array.seq_len, jts) with
      | CellQual.Sequence, Some len, [ j ] ->
          let lo = if has_seq_sentinel array then seq_sentinel_index else 0 in
          conds :=
            !conds
            @ [
                LogicOld.Formula.leq (LogicOld.T_int.from_int lo) j;
                LogicOld.Formula.lt j (LogicOld.T_int.from_int len);
              ]
      (* an open sequence: the same range, with its length the symbolic
         [seq.len s] *)
      | CellQual.Sequence, None, [ j ] -> (
          match array.seq_term with
          | Some s ->
              let lo = if has_seq_sentinel array then seq_sentinel_index else 0 in
              conds :=
                !conds
                @ [
                    LogicOld.Formula.leq (LogicOld.T_int.from_int lo) j;
                    LogicOld.Formula.lt j
                      (LogicOld.T_seq.mk_len path.CellQual.elem_sort
                         (to_old_in array s));
                  ]
          | None -> ())
      | _ -> ());
      let value =
        if full then Evaluator.simplify_term @@ read_at_symbolic ~path array jts
        else (
          List.iteri jts ~f:(fun lvl jt ->
              conds :=
                !conds
                @ List.map (stored_at_level array lvl) ~f:(fun i ->
                      LogicOld.Formula.neq jt (to_old_in array i)));
          to_old_in array
          @@ default_read ~index_sorts:path.CellQual.index_sorts
               ~elem_sort:path.CellQual.elem_sort (Node array)
               (List.map jts ~f:Logic.ExtTerm.of_old_term))
      in
      extra_args := !extra_args @ jts @ [ value ]);
  (List.rev !params, !extra_sorts, !extra_args, !conds)

(* A head atom's cells read against the atom's OWN array argument, which may be
   a parameter of the example -- an array the example quantifies over -- and is
   never evaluated to a concrete array.  Per cell, one fresh index variable per
   level, and a value column.

   What the caller gets is the exact statement of a parametric head under the
   cell reading of a candidate: a candidate [phi] over cell columns is read back
   as [P(x..) := forall j. phi(x.., j, a[j])], so the example
   [forall p. P(t(p))] holds of that candidate iff
   [forall p j. phi(t(p), j, t(p)[j])] does, which is the atom built here once
   the caller binds [p] and the returned variables universally.

   The value column takes one of two forms.
   - [~fresh_values:false]: the [select] chain on [arg], through the path's
     selectors, at the cell's indices.  Exact whatever the candidate reads.
   - [~fresh_values:true], meant for an [arg] that is a parameter of the
     example: a fresh variable per cell, returned among the variables to bind,
     with the premise that two cells of this array whose indices agree hold
     the same value.  An array quantified universally and observed only at
     finitely many cells is, at those cells, any values subject to exactly that
     premise, so the two forms agree on every candidate that reads the array
     only through its cells.  A candidate that also reads the array argument
     itself sees it disconnected from the values, which makes the demand
     STRONGER than the example, never weaker: it can reject a solution, and
     cannot admit a candidate the example rules out.  The point of the form is
     the solver: a universal over an array sort in a synthesis query is one an
     SMT solver rarely decides, and over integers alone it often does.

   [None] for a sequence cell: its read-back carries a range premise and a
   sentinel, and this helper does not state them. *)
let exact_parametric_cells ?(fresh_values = false) ~(path : CellQual.array_path)
    (arg : LogicOld.Term.t) ~(qpa : int) :
    ((Ident.tvar * LogicOld.Sort.t) list
    * LogicOld.Sort.t list
    * LogicOld.Term.t list
    * LogicOld.Formula.t list)
    option =
  match path.CellQual.container with
  | CellQual.Sequence -> None
  | CellQual.Array ->
      let arr = CellQual.read_path path arg in
      let rec select arr sorts js =
        match (sorts, js) with
        | si :: rest, j :: jrest ->
            let se = CellQual.curried_sort_of rest path.CellQual.elem_sort in
            select (LogicOld.T_array.mk_select si se arr j) rest jrest
        | _ -> arr
      in
      let cells =
        List.init qpa ~f:(fun _ ->
            let js =
              List.map path.CellQual.index_sorts ~f:(fun si ->
                  (Ident.mk_fresh_tvar (), si))
            in
            let jts = List.map js ~f:(fun (j, si) -> LogicOld.Term.mk_var j si) in
            let vs, value =
              if fresh_values then
                let v = Ident.mk_fresh_tvar () in
                ( [ (v, path.CellQual.elem_sort) ],
                  LogicOld.Term.mk_var v path.CellQual.elem_sort )
              else ([], select arr path.CellQual.index_sorts jts)
            in
            (js @ vs, jts, value))
      in
      let consistency =
        if not fresh_values then []
        else
          List.concat_mapi cells ~f:(fun n (_, js1, v1) ->
              List.map (List.drop cells (n + 1)) ~f:(fun (_, js2, v2) ->
                  LogicOld.Formula.mk_imply
                    (LogicOld.Formula.and_of
                       (List.map2_exn js1 js2 ~f:LogicOld.Formula.eq))
                    (LogicOld.Formula.eq v1 v2)))
      in
      Some
        ( List.concat_map cells ~f:(fun (vars, _, _) -> vars),
          List.concat_map cells ~f:(fun _ ->
              path.CellQual.index_sorts @ [ path.CellQual.elem_sort ]),
          List.concat_map cells ~f:(fun (_, jts, v) -> jts @ [ v ]),
          consistency )

(* The exact cells of a STEP example [N(u1) => P(u2)], both atoms celled.

   Under the cell reading a candidate is [N(x, a) := forall k. phi_N(x, k,
   a[k])], so the example means
     (forall k. phi_N(x1, k, t1[k]))  =>  forall j. phi_P(x2, j, t2[j]).
   What is built here states it with the head's quantifier kept and the body's
   instantiated:
     forall j. (/\ over k in K(j) of phi_N(x1, k, t1[k])) => phi_P(x2, j, t2[j])
   where every body cell column ranges over K(j) = the head's index variables
   [j] followed by [literals], and a tuple of one choice per column is one
   body instance.

   - Returned: the head's index variables with their sorts (the caller binds
     them universally), the head's appended arguments (per path, per cell:
     the index, then the value [t2[j]]), and per body instance its appended
     arguments in the same layout.
   - The implication holds in one direction for EVERY candidate: the body
     instances are instances of the premise's universal, so the formula above
     implies the example.  A candidate meeting it therefore meets the example
     exactly.
   - The other direction is not a property of the example but of the problem:
     a solution whose candidate is extensible -- every partial assignment of
     the arrays on K that meets the instances extends to total arrays meeting
     the universal -- meets it, provided every index at which the step clause
     reads the body's arrays evaluates, at the example, into K.  The frame
     instances [k = j] are what carry an untouched cell's fact across; the
     literals stand in for the clause's reads, which the example no longer
     states.
   - Values are read through the concrete array at the symbolic index, an
     [ite] over its stored indices, so no array-sorted term is left for the
     solver; an array that is open (read through a parameter or a dummy of
     array sort) gives [None], as do a sequence, a curried or non-integer
     index, a side with no path, and a product of instances above [bound]. *)
let exact_step_cells ~(body : (CellQual.array_path * cell_array) list)
    ~(qpa_body : int) ~(head : (CellQual.array_path * cell_array) list)
    ~(qpa_head : int) ~(literals : Z.t list) ~(bound : int) :
    ((Ident.tvar * LogicOld.Sort.t) list
    * LogicOld.Term.t list
    * LogicOld.Term.t list list)
    option =
  let supported ((path : CellQual.array_path), _) =
    match (path.container, path.index_sorts) with
    | CellQual.Array, [ LogicOld.T_int.SInt ] -> true
    | _ -> false
  in
  let closed t =
    not
      (Set.exists (LogicOld.Term.term_sort_env_of t) ~f:(fun (_, s) ->
           LogicOld.T_array.is_sarray s))
  in
  let read path arr j = Evaluator.simplify_term (read_at_symbolic ~path arr [ j ]) in
  if
    List.is_empty body || List.is_empty head || qpa_body <= 0 || qpa_head <= 0
    || not (List.for_all (body @ head) ~f:supported)
  then None
  else
    let head_cells =
      List.concat_map head ~f:(fun (path, arr) ->
          List.init qpa_head ~f:(fun _ ->
              let j = Ident.mk_fresh_tvar () in
              let jt = LogicOld.Term.mk_var j LogicOld.T_int.SInt in
              (j, [ jt; read path arr jt ])))
    in
    let js = List.map head_cells ~f:fst in
    let ks =
      List.map js ~f:(fun j -> LogicOld.Term.mk_var j LogicOld.T_int.SInt)
      @ List.map (List.dedup_and_sort literals ~compare:Z.compare)
          ~f:LogicOld.T_int.mk_int
    in
    let columns =
      List.concat_map body ~f:(fun cell -> List.init qpa_body ~f:(fun _ -> cell))
    in
    let size =
      List.fold columns ~init:1 ~f:(fun acc _ ->
          if acc > bound then acc else acc * List.length ks)
    in
    if size > bound then None
    else
      let tuples =
        List.fold_right columns ~init:[ [] ] ~f:(fun (path, arr) rest ->
            List.concat_map ks ~f:(fun k ->
                List.map rest ~f:(fun r -> (k :: read path arr k :: r))))
      in
      let head_args = List.concat_map head_cells ~f:snd in
      if not (List.for_all (head_args @ List.concat tuples) ~f:closed) then None
      else
        Some
          ( List.map js ~f:(fun j -> (j, LogicOld.T_int.SInt)),
            head_args,
            tuples )

(* Where a grounding dummy should vary for a clause whose atoms are [atoms]: the
   integer argument values of those atoms and their pairwise sums, ascending,
   at most eight.  For [I(a, b, i, k)] that is [i], [k] and [i+k], the positions
   an invariant [a[k] = b[i+k]] relates -- which is the point: a dummy varying at
   fixed leading indices gives the learner varying arrays that say nothing about
   such a relation.  An argument that is not an integer literal after
   simplification (a parameter, an array, a datatype) contributes nothing, and
   the result is empty when nothing does, which the caller reads as "use the
   leading indices".  It depends only on the atoms, so every atom of a clause
   sees the same indices and a parameter is grounded with one array throughout
   the clause. *)
let argument_indices ?(cap = 8) (atoms : ExAtom.t list) : Z.t list =
  (* in [Z]: an argument is a model integer and may exceed a native int, and a
     sum of two that fit need not fit *)
  let args =
    List.concat_map atoms ~f:(function
      | ExAtom.PPApp (_, (_, terms)) | ExAtom.PApp (_, terms) ->
          List.filter_map terms ~f:(fun t ->
              match LogicOld.T_int.let_int (Evaluator.simplify_term t) with
              | z -> Some z
              | exception exn_ when not (Common.Timer.is_async exn_) -> None)
      | ExAtom.FCon _ -> [])
    |> List.dedup_and_sort ~compare:Z.compare
  in
  let sums =
    List.concat_mapi args ~f:(fun n x ->
        List.map (List.drop args (n + 1)) ~f:(fun y -> Z.add x y))
  in
  List.take (List.dedup_and_sort (args @ sums) ~compare:Z.compare) cap

(* --- Collapsing the indices of a constant level into classes -------------

   Over a level at which the array stores nothing, every cell holds the same
   value and two cells differ only by their index there.  A candidate can
   then tell two such indices apart only through a formula that mentions the
   index column, so when every such formula is a comparison
   [a * j + b <op> 0] with integer literals [a] and [b] -- the rest of the
   atom already evaluated at the example -- the truth of every one of them at
   an index [i] is fixed by the sign of [a * i + b].  Two indices with the
   same sign vector over all of those forms are indistinguishable to every
   candidate, so a cell list keeping one representative per class states
   exactly what the whole list states: on the body side the removed cells are
   repeated disjuncts, on the head side repeated conjuncts.

   What the caller must establish, and what these functions cannot see: that
   the forms are ALL the ways the candidate space reads the index column --
   in particular that no affine atom with a coefficient to be synthesized
   mentions it, since such an atom separates any two distinct integers. *)

(* Does level [k] of the array hold the same thing at every index?  True when
   every node reached at depth [k] stores nothing and its default is not a
   function, and nothing above depth [k] is a leaf or a function: a leaf met
   early is an array-sorted parameter read by [select] at the index, and a
   function is applied to it, so in both cases the value depends on the index
   symbolically. *)
let constant_level (arr : cell_array) k =
  let rec go n d =
    match n with
    | Leaf _ | Lam _ -> false
    | Node a -> (
        match a.defv with
        | Lam _ -> false
        | defv ->
            if d = k then List.is_empty a.stored
            else
              go defv (d + 1)
              && List.for_all a.stored ~f:(fun (_, (_, n)) -> go n (d + 1)))
  in
  k >= 0 && go (Node arr) 0

(* The forms [(a, b)] -- meaning [a * idx + b] compared with zero -- through
   which [phi] reads the variable [idx], after [subst] has replaced every other
   variable it may mention by its value; [None] when some occurrence of [idx]
   is not in such a comparison: a non-linear term, a divisibility atom, an
   atom still mentioning another variable, a binder or a let around it.  Only
   the atoms that mention [idx] are inspected, so a qualifier about the other
   columns alone contributes nothing and refuses nothing.  The result is
   conservative in the one direction that matters: [Some] is returned only
   when the truth of [phi] at any index is a function of the signs of the
   listed forms there. *)
let index_forms ~(idx : Ident.tvar) ~(subst : (Ident.tvar, LogicOld.Term.t) Map.Poly.t)
    (phi : LogicOld.Formula.t) : (Z.t * Z.t) list option =
  let open LogicOld in
  let mentions tvs = Set.mem tvs idx in
  let rec fml acc (phi : Formula.t) =
    if not (mentions (Formula.tvs_of phi)) then Some acc
    else
      match phi with
      | Formula.Atom (a, _) -> atom acc a
      | Formula.UnaryOp (_, p, _) -> fml acc p
      | Formula.BinaryOp (_, p1, p2, _) ->
          Option.bind (fml acc p1) ~f:(fun acc -> fml acc p2)
      | Formula.Bind _ | Formula.LetRec _ | Formula.LetFormula _ -> None
  and atom acc (a : Atom.t) =
    match a with
    | Atom.App
        ( Predicate.Psym (T_bool.Eq | T_bool.Neq | T_int.Lt | T_int.Leq | T_int.Gt | T_int.Geq),
          [ t1; t2 ],
          _ )
      when Term.is_int_sort (Term.sort_of t1) -> (
        match Evaluator.affine_in idx (Evaluator.simplify_term (T_int.mk_sub t1 t2)) with
        | Some ab -> Some (ab :: acc)
        | None -> None)
    | _ -> None
  in
  let phi = Formula.subst (Map.Poly.remove subst idx) phi in
  Option.map (fml [] phi) ~f:List.rev

(* Does [body] mention the variable [x] anywhere other than inside an
   application of one of [holes]?  A qualifier hole is applied to every column,
   so its occurrence of [x] is accounted for by the qualifiers it stands for;
   any other occurrence is an atom the candidate space reads [x] through
   directly -- in the templates here an affine atom whose coefficients are
   synthesized -- and no finite set of forms describes it. *)
let mentions_outside_holes ~(holes : Ident.tvar Set.Poly.t) ~(x : Ident.tvar)
    (body : Logic.term) : bool =
  let open Logic in
  let rec go t =
    match Term.let_apps t with
    | Var (h, _), _ :: _ when Set.mem holes h -> false
    | _ -> (
        match t with
        | Var (y, _) -> Stdlib.( = ) x y
        | Con _ -> false
        | App (t1, t2, _) -> go t1 || go t2
        | Bin (_, y, _, t1, _) -> (not (Stdlib.( = ) x y)) && go t1
        | Let (y, _, t1, t2, _) -> go t1 || ((not (Stdlib.( = ) x y)) && go t2)
        | TyApp (t1, _, _) | TyLam (_, t1, _) -> go t1)
  in
  go body

(* Keep one cell per class.  [forms] has one entry per level of the path: the
   forms through which the candidate space reads that level's index, or [None]
   when it reads it some other way.  A level is collapsed only when it has
   forms AND the array is constant there; every other level keeps its index
   exactly, and the value is always kept exactly, so two cells merge only when
   everything but a constant level's index agrees and those indices share a
   class.  An index at a collapsed level that is not an integer literal keeps
   its identity.  The first cell of each class is kept and the input order is
   preserved, so over the ascending candidate list [cell_tuples] builds the
   representative is the least index of its class and the result is a function
   of the input alone. *)
let collapse_constant_levels ~(forms : (Z.t * Z.t) list option list)
    (arr : cell_array) (cells : (Logic.term list * Logic.term) list) :
    (Logic.term list * Logic.term) list =
  let classify =
    List.mapi forms ~f:(fun k f ->
        match f with Some fs when constant_level arr k -> Some fs | _ -> None)
  in
  if List.for_all classify ~f:Option.is_none then cells
  else
    let key (idxs, v) =
      ( List.mapi idxs ~f:(fun k i ->
            match (Option.join (List.nth classify k), i) with
            | Some fs, Logic.Con (Logic.IntTerm.Int z, _) ->
                `Class (List.map fs ~f:(fun (a, b) -> Z.sign Z.(add (mul a z) b)))
            | _ -> `Exact (term_key i)),
        term_key v )
    in
    let seen = Hashtbl.Poly.create () in
    List.filter cells ~f:(fun c ->
        let k = key c in
        if Hashtbl.mem seen k then false
        else (
          Hashtbl.set seen ~key:k ~data:();
          true))

(* --- The same collapse over a level that STORES values ---------------------

   Over a level that stores values at some indices, every candidate index that
   is not stored there reads the level's default, so among the non-stored
   indices two cells differ only by their index, exactly as over a constant
   level, and the same sign-vector criterion makes them indistinguishable.  A
   stored index holds its own value and keeps its own cell; a non-stored index
   is never merged with a stored one, since only non-stored indices are given
   a class at all.  The argument extends to several collapsed levels by
   induction on depth: two cells that agree exactly at every uncollapsed level
   and share a class at every collapsed one reach the same node at each depth,
   because a class is only ever given to an index that follows the node's
   default. *)

(* May level [k] be collapsed among its non-stored indices?  As
   [constant_level] requires of what lies above and at the level -- no leaf and
   no function above depth [k], no function as a default at depth [k] -- but a
   node at depth [k] may store values, provided every index it stores is an
   integer literal.  A stored index that is a parameter could denote any
   literal, so a literal candidate could not be said with certainty to read the
   default; such a level is refused rather than reasoned about.  Every constant
   level qualifies. *)
let default_level (arr : cell_array) k =
  let is_lit = function Logic.Con (Logic.IntTerm.Int _, _) -> true | _ -> false in
  let rec go n d =
    match n with
    | Leaf _ | Lam _ -> false
    | Node a -> (
        match a.defv with
        | Lam _ -> false
        | defv ->
            if d = k then List.for_all a.stored ~f:(fun (_, (i, _)) -> is_lit i)
            else
              go defv (d + 1)
              && List.for_all a.stored ~f:(fun (_, (_, n)) -> go n (d + 1)))
  in
  k >= 0 && go (Node arr) 0

(* The one leaf every non-stored index at level [k] reads, when every node at
   depth [k] defaults to a leaf and all of those leaves print alike; [None]
   otherwise.  It is what a non-stored cell of the LAST level holds, which is
   what lets a caller substitute it for the value column when it computes the
   forms of that level.  At a level above the last a leaf default is an
   array-sorted parameter read at the deeper indices, which is not one value,
   so a caller asks this of the last level only. *)
let default_value (arr : cell_array) k : Logic.term option =
  let rec defaults n d =
    match n with
    | Leaf _ | Lam _ -> None
    | Node a ->
        if d = k then Some [ a.defv ]
        else
          Option.map ~f:List.concat @@ Option.all
          @@ List.map (a.defv :: List.map a.stored ~f:(fun (_, (_, n)) -> n))
               ~f:(fun n -> defaults n (d + 1))
  in
  if k < 0 then None
  else
    match defaults (Node arr) 0 with
    | Some (Leaf v :: rest)
      when List.for_all rest ~f:(function
             | Leaf w -> String.equal (term_key v) (term_key w)
             | _ -> false) ->
        Some v
    | _ -> None

(* Is the [k]-th index of [idxs] stored at the node the first [k] indices
   reach?  [None] when the walk cannot say: a leaf or a function met on the
   way, or a tuple too short -- which [default_level] excludes for a level it
   admits, and which a caller treats as "keep this index exactly". *)
let stored_in_tuple (arr : cell_array) (idxs : Logic.term list) k : bool option =
  let rec go n idxs d =
    match (n, idxs) with
    | Node a, i :: rest ->
        let found = List.Assoc.find a.stored ~equal:String.equal (term_key i) in
        if d = k then Some (Option.is_some found)
        else (
          match (found, a.defv) with
          | Some (_, n'), _ -> go n' rest (d + 1)
          | None, Lam _ -> None
          | None, defv -> go defv rest (d + 1))
    | _ -> None
  in
  if k < 0 then None else go (Node arr) idxs 0

(* Keep one cell per class among the NON-STORED indices of every admitted
   level, and every stored index as its own cell.  [forms] is as for
   [collapse_constant_levels], one entry per level; [values], when given, has
   one entry per level too: the value a level's forms were computed with
   substituted for the value column, if any.  A cell then gets a class at that
   level only when it holds exactly that value, since its forms say nothing
   about a cell holding another -- a guard that cannot fire when the value is
   the level's [default_value] and the cell is non-stored, and that is kept
   because it costs nothing and makes the key depend on nothing it does not
   check.  A level is collapsed only when it has forms and [default_level]
   admits it.  The first cell of each class is kept and the input order is
   preserved. *)
let collapse_default_levels ~(forms : (Z.t * Z.t) list option list)
    ?(values : Logic.term option list = []) (arr : cell_array)
    (cells : (Logic.term list * Logic.term) list) :
    (Logic.term list * Logic.term) list =
  let classify =
    List.mapi forms ~f:(fun k f ->
        match f with Some fs when default_level arr k -> Some fs | _ -> None)
  in
  if List.for_all classify ~f:Option.is_none then cells
  else
    let key (idxs, v) =
      ( List.mapi idxs ~f:(fun k i ->
            let value_ok =
              match Option.join (List.nth values k) with
              | None -> true
              | Some w -> String.equal (term_key w) (term_key v)
            in
            match (Option.join (List.nth classify k), i) with
            | Some fs, Logic.Con (Logic.IntTerm.Int z, _)
              when value_ok
                   && Option.equal Bool.equal (stored_in_tuple arr idxs k) (Some false) ->
                `Class (List.map fs ~f:(fun (a, b) -> Z.sign Z.(add (mul a z) b)))
            | _ -> `Exact (term_key i)),
        term_key v )
    in
    let seen = Hashtbl.Poly.create () in
    List.filter cells ~f:(fun c ->
        let k = key c in
        if Hashtbl.mem seen k then false
        else (
          Hashtbl.set seen ~key:k ~data:();
          true))

(* The read a cell's value column stands for, in the higher-order
   representation: a [select] chain for an array and one [seq.nth] for a
   sequence.  The candidate learned over cells is rewritten with it, so for a
   sequence it is only half of the read-back: the other half is
   [cell_read_guard]. *)
let cell_read ?(sentinel = false) ~(path : CellQual.array_path) (arr : Logic.term)
    (idxs : Logic.term list) : Logic.term =
  match (path.CellQual.container, idxs) with
  | CellQual.Sequence, [ j ] when sentinel ->
      (* the sentinel's value at its index, the read everywhere else *)
      let esort = Logic.ExtTerm.of_old_sort path.CellQual.elem_sort in
      Logic.BoolTerm.ite_of esort
        (Logic.BoolTerm.eq_of Logic.IntTerm.SInt j
           (Logic.IntTerm.mk_from_int seq_sentinel_index))
        (seq_sentinel_value path.CellQual.elem_sort)
        (seq_nth ~elem_sort:path.CellQual.elem_sort arr j)
  | CellQual.Sequence, [ j ] -> seq_nth ~elem_sort:path.CellQual.elem_sort arr j
  | CellQual.Sequence, _ -> failwith "cell_read: a sequence cell has one index"
  | CellQual.Array, _ ->
      select_chain ~index_sorts:path.CellQual.index_sorts
        ~elem_sort:path.CellQual.elem_sort arr idxs

(* The premise under which a cell's read denotes something, for the read-back
   [forall j. guard => phi(j, read j)]: [0 <= j < seq.len s] for a sequence,
   and nothing for an array.  Without it the read-back of a candidate would
   state [phi] at positions past the end, where the read is a value fixed
   within a model and different across models -- a candidate the validator
   could then accept or refute according to what one model chose there. *)
let cell_read_guard ?(sentinel = false) ~(path : CellQual.array_path)
    (arr : Logic.term) (idxs : Logic.term list) : Logic.term option =
  match (path.CellQual.container, idxs) with
  | CellQual.Sequence, [ j ] ->
      (* built here rather than converted from [CellQual.seq_cell_guard]: the
         sequence is a lambda binder of the candidate, which a conversion to
         the first-order representation has no sort for *)
      let len =
        Logic.Term.mk_apps
          (Logic.SeqTerm.mk_len (Logic.ExtTerm.of_old_sort path.CellQual.elem_sort))
          [ arr ]
      in
      let in_range =
        Logic.BoolTerm.and_of
          [ Logic.ExtTerm.leq_of (Logic.IntTerm.zero ()) j; Logic.ExtTerm.lt_of j len ]
      in
      Some
        (if not sentinel then in_range
         else
           (* the sentinel's index is the one position outside the range the
              universal also covers; [cell_read] gives it the stored value *)
           Logic.BoolTerm.or_of
             [
               Logic.BoolTerm.eq_of Logic.IntTerm.SInt j
                 (Logic.IntTerm.mk_from_int seq_sentinel_index);
               in_range;
             ])
  | _ -> None

(* The closed condition [exists j. guard j] for the guard [cell_read_guard]
   gives, [None] standing for [true].  A read-back universal whose body does
   not mention its index, [forall j. guard j => phi], is equivalent to
   [(exists j. guard j) => phi], and this is that premise: [0 < seq.len s] for
   a sequence without the sentinel, and always satisfiable otherwise -- an
   array's index sort is non-empty, and the sentinel's index satisfies the
   sentinel guard whatever the sequence. *)
let cell_read_guard_satisfiable ?(sentinel = false)
    ~(path : CellQual.array_path) (arr : Logic.term) : Logic.term option =
  match path.CellQual.container with
  | CellQual.Sequence when not sentinel ->
      Some
        (Logic.ExtTerm.lt_of (Logic.IntTerm.zero ())
           (Logic.Term.mk_apps
              (Logic.SeqTerm.mk_len
                 (Logic.ExtTerm.of_old_sort path.CellQual.elem_sort))
              [ arr ]))
  | _ -> None

(* The contents of a VARYING dummy array: the values stored at its [count]
   indices, in order, and its default.  A varying dummy replaces an array
   parameter of a parametric example when the example is grounded, so every
   choice here is sound -- an instantiation of an example is a consequence of
   it -- and what the choice decides is only which candidates the grounded
   example can still be fitted by.

   The seed comes from the parameter's name, so one parameter receives one
   array everywhere in a clause, and the instance index shifts it, so two
   instances differ in every parameter at once.

   [growing] off: stored [seed + n], default [0] -- small, positive and the
   same on every round.  [growing] on:
   - the [n]-th stored value is [(seed + n) * (round + 1)], negated at odd [n];
   - the default is [(seed + count + 1) * (round + 1)], negated at odd
     instances, since it is read at every index not stored -- the neighbours
     of the stored ones among them, where a boundary is tested -- and a default
     of 0 lets a bound [a[j] <= 0] fit exactly the cells an index atom should
     cover;
   - every third instance ([inst mod 3 = 2]) ignores the name, so all the array
     parameters of a clause receive the SAME array there: an atom that must hold
     for every pair of arrays must hold for a pair of equal ones. *)
let varying_contents ~growing ~round ~inst ~name ~count : int list * int =
  let seed =
    if growing && inst % 3 = 2 then 1 + (13 * inst)
    else
      String.foldi name ~init:(1 + (13 * inst)) ~f:(fun i acc c ->
          acc + ((Char.to_int c + i) % 7))
  in
  let sign k = if k % 2 = 1 then -1 else 1 in
  if not growing then (List.init count ~f:(fun n -> seed + n), 0)
  else
    ( List.init count ~f:(fun n -> sign n * (seed + n) * (round + 1)),
      sign inst * (seed + count + 1) * (round + 1) )

(* --- Sequences that carry information --------------------------------------

   A sequence cell reads a position below the length, so a sequence with no
   position -- the value a parametric sequence falls back to, and the one a
   solver returns first whenever the clause leaves the length open -- gives
   an atom no cell at all, and a sequence whose positions all hold one value
   gives cells that cannot tell one position from another.  Either way the
   example says nothing about the relation between positions a quantified
   invariant is made of.  The two helpers below are the sequence counterparts
   of the array side's varying dummy and its re-ask for a varying
   counterexample; both only CHOOSE which consequence or which counterexample
   is used, never what is true. *)

(* A short non-empty sequence literal, [seq.unit e0 ++ (seq.unit e1 ++ ..)],
   whose elements all differ, for grounding the parametric sequence parameter
   [name] of an example clause.

   Why this is sound: an example clause means "for every instantiation of its
   parameters", so any value substituted uniformly for a parameter the
   clause's conditions do not mention gives an instance, which is a
   consequence of the example.  The choice only decides which consequence the
   learner is shown.

   The policy mirrors the varying array's.  The values are [seed + n], the
   seed drawn from the parameter's NAME and the instance number, so one
   parameter receives one sequence in every atom of a clause (the link the
   clause asserts between its atoms) and two parameters receive different
   ones (an equation between them must not hold by accident).  The length is
   [width] positions, at least one, extended to cover every non-negative index
   in [indices] (the clause's integer arguments, where the array side stores
   at them) and by one more position on odd instances, so that two instances
   also differ in length; it never exceeds [seq_cell_cap], the number of
   positions the reader offers as cells, so every position the literal has is
   one the cells see and no cell is ever at or past its length.  Integer and
   Boolean elements only: those are the sorts with a ladder of distinct values
   here, and [None] leaves the parameter to the ordinary dummy, as the array
   side does for a non-integer element sort. *)
let varying_sequence ~width ?(indices : Z.t list = []) ~inst (Ident.Tvar name)
    (elem_sort : LogicOld.Sort.t) : LogicOld.Term.t option =
  let open LogicOld in
  let seed =
    String.foldi name ~init:(1 + (13 * inst)) ~f:(fun i acc c ->
        acc + ((Char.to_int c + i) % 7))
  in
  let len =
    let base = max 1 width in
    (* the positions are model integers, so they are compared in [Z] and the
       covering length is clamped to the cap before it becomes a native int *)
    let covering =
      List.fold indices ~init:(Z.of_int base) ~f:(fun acc k ->
          if Z.geq k Z.zero then Z.max acc (Z.succ k) else acc)
    in
    let covering = Z.to_int (Z.min covering (Z.of_int seq_cell_cap)) in
    max 1 (min seq_cell_cap (covering + (inst % 2)))
  in
  let element n =
    if Term.is_int_sort elem_sort then Some (T_int.mk_int (Z.of_int (seed + n)))
    else if Term.is_bool_sort elem_sort then
      Some (if (seed + n) % 2 = 0 then T_bool.mk_true () else T_bool.mk_false ())
    else None
  in
  match Option.all (List.init len ~f:element) with
  | None | Some [] -> None
  | Some elems ->
      let units = List.map elems ~f:(T_seq.mk_unit elem_sort) in
      let rec concat = function
        | [] -> T_seq.mk_empty elem_sort
        | [ u ] -> u
        | u :: rest -> T_seq.mk_concat elem_sort u (concat rest)
      in
      Some (concat units)

(* Does a model's sequence value give a cell abstraction too little to learn
   from: no position, one position, or positions that all hold the same
   term?  A term that does not state its elements is not judged ([false]),
   as a lambda is taken to vary on the array side: nothing here can
   enumerate it. *)
let sequence_lacks_variety (t : LogicOld.Term.t) : bool =
  match seq_elements_old t with
  | None -> false
  | Some ([] | [ _ ]) -> true
  | Some (e :: rest) ->
      let key = LogicOld.Term.str_of e in
      List.for_all rest ~f:(fun u -> String.equal key (LogicOld.Term.str_of u))

(* The index terms a formula reads the sequence variable [x] at, through
   [seq.nth x i], keeping only those whose variables are the formula's own
   free variables (an index under a binder names nothing the model fixes), in
   the order [Formula.iter_term] visits them, without repeats. *)
let seq_read_indices (phi : LogicOld.Formula.t) (x : Ident.tvar) : LogicOld.Term.t list =
  let open LogicOld in
  let fvs = Formula.tvs_of phi in
  let acc = ref [] in
  Formula.iter_term phi ~f:(fun t ->
      match t with
      | Term.FunApp (T_seq.SqNth _, [ Term.Var (y, _, _); idx ], _)
        when Ident.tvar_equal x y && Set.is_subset (Term.tvs_of idx) ~of_:fvs ->
          if
            not
              (List.exists !acc ~f:(fun u ->
                   String.equal (Term.str_of u) (Term.str_of idx)))
          then acc := idx :: !acc
      | _ -> ());
  List.rev !acc

(* The condition a re-asked counterexample is required to meet so that the
   sequence [s] (a variable of the query) is non-empty and holds two
   different elements, at two of the indices the query reads it at when there
   are at least two ([read_indices], at most six of them taken), and at
   positions 0 and 1 otherwise.  Every read in it is conjoined with its own
   range premise [0 <= i < seq.len s], so the condition never depends on the
   value a model chooses for a read past the end: it is quantifier-free and
   its truth is fixed by the sequence the model gives. *)
let sequence_vary_condition ~(elem_sort : LogicOld.Sort.t)
    ~(read_indices : LogicOld.Term.t list) (s : LogicOld.Term.t) :
    LogicOld.Formula.t =
  let open LogicOld in
  let len = T_seq.mk_len elem_sort s in
  let in_range i = Formula.and_of [ Formula.leq (T_int.zero ()) i; Formula.lt i len ] in
  let differ t u =
    Formula.and_of
      [ in_range t; in_range u; Formula.neq (T_seq.mk_nth elem_sort s t) (T_seq.mk_nth elem_sort s u) ]
  in
  match List.take read_indices 6 with
  | _ :: _ :: _ as idxs ->
      let rec pairs = function
        | [] -> []
        | t :: rest -> List.map rest ~f:(fun u -> (t, u)) @ pairs rest
      in
      Formula.or_of @@ List.map (pairs idxs) ~f:(fun (t, u) -> differ t u)
  | _ -> differ (T_int.zero ()) (T_int.one ())

(* A small array that holds [width] different things (at the leading indices,
   or at [indices] where given) and a default elsewhere -- 0, or under
   [growing] what [varying_contents] says -- for grounding the parametric
   array parameter [name] of an example clause.  Only integer elements: any
   other element sort has no natural ladder of distinct values here, and
   falling back to the dummy is what this did before.

   Seeding by the NAME is what keeps this sound across a clause, and it is
   load bearing rather than convenient: an example clause means "for every
   instantiation of its parameters", so one parameter must receive one value
   in every atom of the clause, and the atoms are grounded one at a time. A
   seed drawn from anything else -- a counter, the atom, the order of
   traversal -- would give one parameter two arrays in one clause and break
   the link the clause asserts between its atoms. The grounding this sits in
   front of relies on exactly the same property, its dummies being keyed by
   the parameter's name. *)
let varying_array ~width ?(growing = false) ?(round = 0) ?indices ~inst
    (Ident.Tvar name) index_sort elem_sort =
  let open LogicOld in
  if not (Term.is_int_sort elem_sort) then None
  else
    let indices =
      match indices with
      | Some (_ :: _ as is) -> is
      | _ -> List.init (max 1 width) ~f:Z.of_int
    in
    (* the parameter's name decides the array, so one parameter receives one
       array everywhere in a clause; the instance index shifts the whole
       family, so two instances of one clause differ in every parameter at
       once rather than in one of them -- [varying_contents] holds the values,
       and [growing] its alternative *)
    let stored, default =
      varying_contents ~growing ~round ~inst ~name ~count:(List.length indices)
    in
    Option.return
    @@ List.fold2_exn indices stored
         ~init:
           (T_array.mk_const_array index_sort elem_sort
              (T_int.mk_int (Z.of_int default)))
         ~f:(fun arr k v ->
           T_array.mk_store index_sort elem_sort arr
             (T_int.mk_int k)
             (T_int.mk_int (Z.of_int v)))

(* Ground an example clause's parametric arrays (when [arrays]) and
   sequences (when [sequences]) at values that VARY, uniformly across the
   whole clause.  With both off the clause is returned as it is.

   An example clause means "for every instantiation of its parameters", so
   grounding it at any instantiation its conditions admit is sound -- the
   result is an instance and therefore a consequence. The standard grounding
   substitutes the dummy, which for an array sort is a CONSTANT array, and a
   constant array is the one value a learner reading what the array holds can
   learn nothing from: it holds the same thing at every index, so no example
   over it distinguishes one index from another, and an invariant whose
   content is a relation between indices is unreachable from such data.  The
   dummy of a sequence parameter is a constant whose elements nothing states,
   which the cell reader cannot read at all, and the empty sequence offers no
   cell; so a sequence is grounded at [varying_sequence]'s short non-empty
   literal instead.

   Two conditions make this an instance rather than a different clause, and
   both are why it is done HERE rather than atom by atom. A clause's
   parameters are the UNION of its atoms' -- one name is one variable of the
   clause -- so substituting in one atom while another keeps the variable
   bound yields a clause that is not an instance of the original and demands
   something the original does not. And a parameter any atom's condition
   mentions is left alone, so no condition's truth at the instance changes.
   Each parameter gets a different value, since giving two of them the same
   one makes an equation between them hold for the wrong reason.  With
   [at_args] the values vary at the clause's integer arguments (the array
   stores there; the sequence is long enough to have those positions). *)
let ground_varying ~arrays ~sequences ~width ~at_args ?growing ?round ~inst
    (clause : ExClause.t) :
    ExClause.t =
  let open LogicOld in
  if not (arrays || sequences) then clause
  else
    let atoms = Set.union clause.ExClause.positive clause.ExClause.negative in
    let cond_vars =
      Set.fold atoms ~init:Set.Poly.empty ~f:(fun acc a ->
          match a with
          | ExAtom.FCon (_, phi) -> Set.union acc (Formula.tvs_of phi)
          | ExAtom.PPApp ((_, cond), _) -> Set.union acc (Formula.tvs_of cond)
          | ExAtom.PApp _ -> acc)
    in
    let indices =
      if not at_args then None else Some (argument_indices (Set.to_list atoms))
    in
    let sub =
      Map.Poly.filter_map ~f:Fn.id
      @@ Map.Poly.filter_mapi (ExClause.params_of clause) ~f:(fun ~key ~data ->
             if Set.mem cond_vars key then None
             else
               match data with
               | T_array.SArray (si, se) when arrays && Term.is_int_sort si ->
                   Option.return
                   @@ varying_array ~width ?growing ?round ?indices ~inst key si
                        se
               | T_seq.SSeq se when sequences ->
                   (* never longer than the cells the reader offers, so every
                      cell read off it is below its length *)
                   Option.return @@ varying_sequence ~width ?indices ~inst key se
               | _ -> None)
    in
    if Map.Poly.is_empty sub then clause
    else
      let apply = function
        | ExAtom.PApp _ as a -> a
        | ExAtom.FCon (senv, phi) ->
            ExAtom.mk_fcon
              ( Map.Poly.filter_keys senv ~f:(fun x -> not (Map.Poly.mem sub x)),
                Evaluator.simplify @@ Formula.subst sub phi )
        | ExAtom.PPApp ((senv, cond), ((pvar, sorts), terms)) ->
            ExAtom.mk_ppapp
              (Map.Poly.filter_keys senv ~f:(fun x -> not (Map.Poly.mem sub x)), cond)
              pvar sorts
              (List.map terms ~f:(fun t -> Evaluator.simplify_term (Term.subst sub t)))
      in
      ExClause.canon
        {
          ExClause.positive = Set.Poly.map clause.ExClause.positive ~f:apply;
          ExClause.negative = Set.Poly.map clause.ExClause.negative ~f:apply;
        }

(* ------------------------------------------------------------------
   Keeping the cell route inert where it has nothing to act on.

   A predicate from which no array or sequence is reachable gets no cell
   columns in its template, however the cells are configured, and on such a
   predicate every celled step must be the identity: the cell settings are
   meant to be switchable on for a whole problem without changing what happens
   to its other predicates.  The steps are driven by configuration switches,
   not by the predicate, so each asks the one question below before acting --
   and the question is asked of the TEMPLATE, which is where the decision
   whether a predicate has cells is actually taken.  Without it, the celled
   example expansion split and instantiated every parametric atom of every
   example, so an example over lists that meant "for every element" became
   its instance at one default element, and a problem the plain
   configuration answers in under a second went unanswered for two minutes. *)

(* Whether a template took cell columns: its leading lambda binders outnumber
   the predicate's declared arguments.  [arity] must be the DECLARED arity: a
   celled example atom carries its cell columns among its own sorts. *)
let has_cell_columns ~arity (term : Logic.term) =
  List.length (fst (Logic.Term.let_lam term)) > arity

(* Whether any predicate application of an example clause belongs to a
   predicate with cell columns. *)
let clause_has_celled_atom ~celled (clause : ExClause.t) =
  Set.exists (Set.union clause.ExClause.positive clause.ExClause.negative)
    ~f:(fun atom ->
      match ExAtom.pvar_of atom with Some pvar -> celled pvar | None -> false)

(* The celled expansion of an example clause, applied only where it has
   something to act on.  Contract: a clause none of whose atoms belongs to a
   celled predicate is returned as the one-element list of itself, unchanged
   -- in particular its parametric atoms stay parametric.  A clause that mixes
   celled and uncelled atoms is expanded whole, because its atoms may share
   parameters, and grounding them in one atom but not another would make the
   clause claim more than any instance of the example says. *)
let expand_if_celled ~celled ~expand (clause : ExClause.t) : ExClause.t list =
  if clause_has_celled_atom ~celled clause then expand clause else [ clause ]

(* The key of the truth table a predicate's rows live in.  The extended table
   (the predicate's name with a [#cells] suffix) holds rows that carry cell
   columns, and serves only a predicate whose template has them; every other
   predicate keeps its ordinary table, whose rows, columns and parameter list
   are the ones the labeler and the resolver see. *)
let table_key ~celled_examples ~celled (Ident.Pvar name as pvar) =
  if celled_examples > 0 && celled then Ident.Pvar (name ^ "#cells") else pvar

(* An example atom split for the cell expansion: the application its arrays
   are read from, the function that puts a rebuilt application back under the
   atom's parameters and guard, and those parameters.

   The atom is instantiated at the default point first, so that a parameter
   of a sort variable becomes its dummy constant and the arrays are ground
   where they can be.  Where the instance keeps parameters, the application
   is returned bare and [wrap] restores them with the instance's guard.

   Where the instance keeps NO parameter, its guard can still be non-trivial:
   a dummy constant stands for any element of its sort, so a guard such as
   [$1 <> $2] survives as [dummy_$1 <> dummy_$2], undecided.  Returning the
   bare application then drops it, and the expansion demands [P(t)] for every
   value of the constants, equal ones included -- which the example does not
   say.  With [keep_instance_guards] such an atom is split in its parametric
   form instead (before instantiation, normalised the same way), so the
   parameters and the guard come back with [wrap]; when that form has no
   parameter either, [wrap] carries the guard alone.  Guarantees: [wrap core]
   claims no more than [atom] whenever [keep_instance_guards] is set, for
   every [core] the expansion builds from [core]'s own arrays. *)
let split_example_atom ?(keep_instance_guards = false) (atom : ExAtom.t) :
    ExAtom.t * (ExAtom.t -> ExAtom.t) * Logic.sort_env_map =
  let wrap_with senv cond = function
    | ExAtom.PApp ((pvar, sorts), args) ->
        ExAtom.mk_ppapp (senv, cond) pvar sorts args
    | ExAtom.PPApp ((senv', cond'), ((pvar, sorts), args)) ->
        (* a parametric expansion binds parameters of its own; both sets bind
           the one atom *)
        ExAtom.mk_ppapp
          ( Map.Poly.fold senv' ~init:senv ~f:(fun ~key ~data acc ->
                Map.Poly.set acc ~key ~data),
            LogicOld.Formula.mk_and cond cond' )
          pvar sorts args
    | a -> a
  in
  let split = function
    | ExAtom.PApp _ as a -> (a, Fn.id, Map.Poly.empty)
    | ExAtom.PPApp ((senv, cond), papp) ->
        if Map.Poly.is_empty senv then (ExAtom.PApp papp, Fn.id, Map.Poly.empty)
        else (ExAtom.PApp papp, wrap_with senv cond, Logic.of_old_sort_env_map senv)
    (* an atom that is not a predicate application -- a pure literal an example
       clause carries -- has no array argument and so needs no cells; it is
       left as it is rather than refused, since refusing it would throw away
       every problem whose examples happen to contain one *)
    | ExAtom.FCon _ as a -> (a, Fn.id, Map.Poly.empty)
  in
  let normalized = ExAtom.(normalize @@ instantiate atom) in
  match normalized with
  | ExAtom.PPApp ((senv, cond), papp)
    when keep_instance_guards && Map.Poly.is_empty senv
         && not (LogicOld.Formula.is_true cond) -> (
      match ExAtom.normalize atom with
      | ExAtom.PPApp ((senv', _), _) as parametric
        when not (Map.Poly.is_empty senv') ->
          split parametric
      | _ -> (ExAtom.PApp papp, wrap_with Map.Poly.empty cond, Map.Poly.empty))
  | _ -> split normalized
