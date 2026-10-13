open Core
open Ast
open Ast.LogicOld

(** Cell qualifiers: qualifiers about an array argument's contents, written
    before the columns that will hold those contents exist.

    A predicate over an array is given extra parameters -- a fixed number of
    (index, value) pairs per array-sorted parameter, its cells -- and its body
    is a statement about those pairs, read back as a universally quantified
    statement about the array.  The clauses are where the useful atoms about an
    array's contents are written, and they are written with an array read at a
    clause variable ([a[j] > bound] under [0 <= j /\ j <= i]).  Extraction runs
    long before a template exists, so the cell columns it would have to name
    have not been created yet, and their names are freshly drawn when they are.

    So extraction emits a SCHEMA instead: for the array parameter [a] it names
    two placeholder variables, the index column [#cidx@a] and the value column
    [#cval@a], and the template instantiates the schema once per cell it
    actually generates.  One qualifier per array becomes one per cell.

    A placeholder is a variable of an ordinary sort with a name no input can
    write (SMT-LIB symbols here never begin with [#]), so a consumer that does
    not know about cells sees an ordinary qualifier mentioning a variable
    outside the predicate's parameters, which is exactly the condition template
    generation already has to reject.  That rejection is what keeps a schema
    from leaking into a template that cannot instantiate it.

    The scheme is not array-specific: the same two columns describe a position
    and the element at it in a sequence or a string, which is why nothing here
    mentions the array sort. *)

let idx_prefix = "#cidx@"
let val_prefix = "#cval@"
let idx_of (Ident.Tvar a) = Ident.Tvar (idx_prefix ^ a)
let val_of (Ident.Tvar a) = Ident.Tvar (val_prefix ^ a)

let is_placeholder (Ident.Tvar x) =
  String.is_prefix x ~prefix:idx_prefix || String.is_prefix x ~prefix:val_prefix

(** The parameter a placeholder belongs to, or [None] for an ordinary
    variable. *)
let base_of (Ident.Tvar x) =
  match String.chop_prefix x ~prefix:idx_prefix with
  | Some b -> Some (Ident.Tvar b)
  | None ->
      Option.map ~f:(fun b -> Ident.Tvar b)
      @@ String.chop_prefix x ~prefix:val_prefix

(** Extend a renaming of parameters to the cell columns those parameters
    carry, so that a qualifier about one predicate's array argument can be
    transplanted onto another predicate applied to the same array. *)
let extend_renaming sub =
  Map.Poly.fold sub ~init:sub ~f:(fun ~key ~data acc ->
      Map.Poly.set ~key:(val_of key) ~data:(val_of data)
      @@ Map.Poly.set acc ~key:(idx_of key) ~data:(idx_of data))

(** Whether [sub] renames every placeholder [phi] mentions.  One it does not
    would arrive at the other predicate naming a parameter position that need
    not even be an array there. *)
let renaming_covers sub phi =
  Set.for_all (Formula.tvs_of phi) ~f:(fun v ->
      match base_of v with None -> true | Some b -> Map.Poly.mem sub b)

let mentions_placeholder phi = Set.exists (Formula.tvs_of phi) ~f:is_placeholder

(** The index and value columns of [a], as terms.

    The schema names ONE integer index column: it is extracted from reads
    [select a j] with an integer [j] and an integer element, which is the shape
    the clause-level extraction collects.  A curried array, whose cell is an
    index tuple, gets no schema and takes its qualifiers from the template's
    own cell families instead. *)
let idx_term a = Term.mk_var (idx_of a) T_int.SInt

let val_term a sort = Term.mk_var (val_of a) sort

(** Instantiate a schema at concrete cells.  [cells] gives, per array-sorted
    parameter, the (index, value) column pairs the template generated for it;
    the result is one qualifier per combination, and a schema mentioning an
    array with no cells yields nothing.  A qualifier that mentions no
    placeholder at all is returned unchanged, once. *)
let instantiate ~(cells : (Ident.tvar * (Term.t list * Term.t) list) list) phi
    =
  if not (mentions_placeholder phi) then [ phi ]
  else
    let mentioned =
      List.filter cells ~f:(fun (a, _) ->
          let tvs = Formula.tvs_of phi in
          Set.mem tvs (idx_of a) || Set.mem tvs (val_of a))
    in
    List.fold mentioned ~init:[ phi ] ~f:(fun acc (a, pairs) ->
        List.concat_map acc ~f:(fun phi ->
            List.filter_map pairs ~f:(fun (idxs, value) ->
                (* the schema names ONE index column; a cell of a curried array
                   has several and no schema is extracted for it, so such a
                   cell instantiates nothing rather than the wrong column *)
                match idxs with
                | [ idx ] ->
                    Some
                      (Formula.subst
                         (Map.Poly.of_alist_exn
                            [ (idx_of a, idx); (val_of a, value) ])
                         phi)
                | _ -> None)))
    |> List.filter ~f:(Fn.non mentions_placeholder)

(** {1 Where a predicate's arrays are}

    The cells a predicate gets are one group per array it can *reach*, not per
    array-sorted parameter.  The difference is the whole corpus this is for: a
    Rust function's arguments arrive as a tuple, so an input derived from one
    declares its unknowns over a datatype holding the array and never over the
    array, and a rule that counts array-sorted parameters gives such a
    predicate no cells at all -- the mechanism then runs, is called, and
    produces nothing.

    A path is followed only through a datatype with ONE constructor.  A
    selector of a datatype with several is partial: applied to a value built by
    another constructor it denotes something the theory does not fix, and an
    example built on such a term is a term that denotes nothing.  A tuple, a
    record and a reference wrapper are single-constructor, which is exactly the
    shape the corpus has, so the restriction costs nothing there and keeps this
    out of the underspecified-term question entirely. *)

(** What a path reaches: an array, whose every index holds a value, or a
    sequence, which holds a value only below its length.  A read of a sequence
    outside its length is a term the theory leaves open -- its value is fixed
    within a model and different across models -- so every consumer that reads
    a sequence's cell must keep the index inside [0 <= j < seq.len s]: the
    example side offers only such indices, and the read-back puts that range
    in front of the cell's universal as a premise ([seq_cell_guard]). *)
type container = Array | Sequence

type array_path = {
  container : container;
      (** [Sequence] only when [array_paths] was asked for sequences; its
          [index_sorts] is then [\[Int\]] *)
  param : int;  (** which parameter of the predicate it starts at *)
  selectors : (Datatype.t * string) list;
      (** the selectors to apply, outermost first; empty when the parameter is
          itself the array *)
  index_sorts : Sort.t list;
      (** one per level, outermost first.  A single entry for an ordinary
          array; several for a CURRIED one -- an array whose elements are
          arrays, which is how a universal function of several arguments is
          encoded here -- whose cell is then an index TUPLE and the value at
          the end of the chain, [q_p\[i1\]\[i2\]\[i3\]].  Never empty. *)
  elem_sort : Sort.t;  (** the sort at the end of the chain; never an array *)
}

(** How many columns one cell of this array takes: its indices and its value.
    Every consumer that slices a template's cell binders or an atom's appended
    arguments does so by this width, per path, so the widths and the order of
    [array_paths] are one contract. *)
let cell_width path = List.length path.index_sorts + 1

let total_cell_width paths = List.sum (module Int) paths ~f:cell_width

(** The array's own sort, rebuilt from the levels: [Array s1 (Array s2 ... e)]. *)
let rec curried_sort_of index_sorts elem_sort =
  match index_sorts with
  | [] -> elem_sort
  | si :: rest -> T_array.mk_array_sort si (curried_sort_of rest elem_sort)

let curried_sort path =
  match path.container with
  | Array -> curried_sort_of path.index_sorts path.elem_sort
  | Sequence -> T_seq.mk_seq_sort path.elem_sort

let is_sequence path =
  match path.container with Sequence -> true | Array -> false

(** The range a sequence cell's index must lie in, [0 <= j < seq.len s], for
    the sequence term [s] and the index [j].  It is what makes a sequence cell
    denote something: outside it [seq.nth s j] is a value the theory does not
    fix.  [None] for an array, whose every index is meaningful. *)
let seq_cell_guard path (s : Term.t) (j : Term.t) : Formula.t option =
  match path.container with
  | Array -> None
  | Sequence ->
      Some
        (Formula.and_of
           [
             Formula.leq (T_int.zero ()) j;
             Formula.lt j (T_seq.mk_len path.elem_sort s);
           ])

(** Does [q] mention a sequence, and every sequence it mentions only as the
    argument of [seq.len]?  Such a qualifier is a statement about the scalar
    part of a predicate's arguments -- [i < seq.len s] -- rather than about any
    element: every symbol in it is total and theory-fixed, and it reads no
    position.  Every other free variable must be of a scalar sort, so a
    qualifier over a datatype or an array is not one. *)
let speaks_of_sequence_length_only (q : Formula.t) : bool =
  let lens = ref 0 in
  let q' =
    Formula.map_term q ~f:(fun t ->
        match t with
        | Term.FunApp (T_seq.SqLen _, [ _ ], _) ->
            incr lens;
            T_int.zero ()
        | t -> t)
  in
  !lens > 0
  && Set.for_all (Formula.term_sort_env_of q') ~f:(fun (_, s) ->
         Term.is_int_sort s || Term.is_real_sort s || Term.is_bool_sort s
         || Term.is_bv_sort s)

(** [arr] read at one index per level, each [select] at the sort of the
    levels below it -- the first-order form of a cell's index tuple. *)
(* The first-order form of a cell's read: a [select] chain for an array, one
   [seq.nth] for a sequence.  The caller of the sequence form owns the range
   premise; see [seq_cell_guard]. *)
let rec read_cell_old path (arr : Term.t) (idxs : Term.t list) : Term.t =
  match (path.container, idxs) with
  | Sequence, [ j ] -> T_seq.mk_nth path.elem_sort arr j
  | Sequence, _ -> failwith "read_cell_old: a sequence cell has one index"
  | Array, _ ->
      select_chain_old ~index_sorts:path.index_sorts ~elem_sort:path.elem_sort
        arr idxs

and select_chain_old ~index_sorts ~elem_sort (arr : Term.t) (idxs : Term.t list)
    : Term.t =
  let rec sel arr sorts idxs =
    match (sorts, idxs) with
    | si :: rest, i :: irest ->
        sel (T_array.mk_select si (curried_sort_of rest elem_sort) arr i) rest irest
    | _ -> arr
  in
  sel arr index_sorts idxs

(** An array sort split into its levels and the sort at the end. *)
let rec uncurry_array_sort = function
  | T_array.SArray (si, se) ->
      let sis, e = uncurry_array_sort se in
      (si :: sis, e)
  | s -> ([], s)

(** Whether an array of these sorts can be given cells at all.

    Two conditions, and they are not symmetric.

    An INDEX must be a sort the example side can offer candidate cells at.  An
    integer: by counting -- a stored index, its two neighbours, a short prefix.
    A sort variable or an uninterpreted sort: from the indices the example's
    array stores and the terms of that sort the atom's own arguments reach,
    since there is no counting there; an array indexed by such a sort whose
    example stores nothing and whose atom mentions nothing of the sort simply
    offers no cell.  A finite enumeration -- which is what the finite
    instantiation substitutes for a quantified sort -- offers every element,
    a complete set.  The sort-variable case is what a trait predicate over a
    quantified sort is -- [q_p : a -> a -> Int -> Bool], an array of arrays
    indexed by the sort variable -- and refusing it would leave an input whose
    invariant is a universal over such a trait with a template that has no
    cell in it.  Anything else (a boolean, a real, a datatype) is
    refused as an index: nothing here can propose one.

    The VALUE may be of any sort the template can hold in an ordinary
    parameter and a qualifier can mention: an integer, a real, a boolean, a
    datatype, an element of a quantified sort.  What it may not be is a
    function, because a cell column of that sort is a higher-order parameter,
    and the candidate built over it does not survive the conversion back to a
    first-order formula -- observed as an uncaught [failed to convert term ...
    to old formula] carrying a [select] chain.  An ARRAY value never reaches
    this test: [array_paths] uncurries the chain first, so the value is always
    the sort at its end.

    It is applied HERE rather than at either consumer so that the template and
    the example expansion cannot disagree: an array without cells is an array
    this function does not report, and both sides then generate nothing for it.
    Refusing at a consumer instead throws away the whole atom, which is what
    an earlier version did -- one input carries a data array that is perfectly
    cellable beside a trait predicate that is not, and refusing on the second
    lost the first. *)
(** The name the finite instantiation of a quantified sort gives the
    [n]-element enumeration it substitutes for the sort variable [svar], and
    the test that recognises such a datatype again.  One definition for both,
    so the two cannot drift: a consumer that must treat the stand-in as the
    sort variable it replaces -- a policy decided per predicate from "does it
    reach an array over a sort variable" -- has only this name to go on, since
    after the substitution the sort IS an ordinary enumeration. *)
let finite_sort_instance_name n svar = sprintf "#fin%d_%s" n svar

let is_finite_sort_instance = function
  | T_dt.SDT dt ->
      let name = Datatype.name_of dt in
      String.length name > 4
      && String.is_prefix name ~prefix:"#fin"
      && Char.is_digit name.[4]
  | _ -> false

(** The elements of a FINITE ENUMERATION -- a datatype all of whose
    constructors are nullary -- or [None] for any other sort.  The finite
    instantiation of a quantified sort substitutes exactly such a datatype for
    the sort variable, so under it a trait predicate's index levels are
    enumerations, and their candidate cells can be EVERY element: an offer set
    that is complete rather than a guess. *)
let enum_elements = function
  (* a boolean index is a two-element enumeration by another name: the
     predicate-polymorphism encodings instantiate a universal predicate as an
     array over Bool, and such an array had no cells while an enumeration
     datatype with two nullary constructors did *)
  | T_bool.SBool -> Some [ T_bool.mk_true (); T_bool.mk_false () ]
  | T_dt.SDT dt when Datatype.is_dt dt -> (
      match Datatype.conses_of dt with
      | [] -> None
      | conses ->
          if List.for_all conses ~f:(fun c -> List.is_empty (Datatype.sels_of_cons c))
          then
            Some
              (List.map conses ~f:(fun c ->
                   T_dt.mk_cons dt (Datatype.name_of_cons c) []))
          else None)
  | _ -> None

let index_cellable = function
  | T_int.SInt -> true
  | Sort.SVar _ | T_dt.SUS _ -> true
  | s -> Option.is_some (enum_elements s)

let cellable ~index_sorts ~elem_sort =
  (not (List.is_empty index_sorts))
  && List.for_all index_sorts ~f:index_cellable
  &&
  match elem_sort with
  (* what a template can hold in an ordinary parameter and a qualifier can
     mention: the scalars, a datatype, an uninterpreted sort, an element of a
     quantified one *)
  | T_int.SInt | T_real.SReal | T_bool.SBool -> true
  | T_bv.SBV _ -> true
  | T_dt.SDT _ | T_dt.SUS _ -> true
  | Sort.SVar _ -> true
  (* Anything else is refused, and the DEFAULT is the point: [Sort.t] is an
     extensible variant, so a sort added elsewhere produces no compiler error
     here.  A list of what is rejected would silently admit it; a list of what
     is accepted silently refuses it, which costs an answer nobody had rather
     than a crash far away.  What is knowingly outside today is a function, a
     sequence, a tuple, a reference and a polymorphic sort -- none of them
     reached by any input this route runs on, and each one a separate question
     about what a cell column of that sort would mean. *)
  | _ -> false

(** Whether a sequence holding [elem_sort] can be given cells: a scalar
    element only.  An element of a datatype or of a quantified sort would be
    cellable as an array's is, but no input this has been measured on has one,
    and the read-back's range premise is the only part of it that has been
    checked. *)
let seq_cellable elem_sort =
  match elem_sort with
  | T_int.SInt | T_real.SReal | T_bool.SBool | T_bv.SBV _ -> true
  | _ -> false

(** The arrays reachable from a list of parameter sorts, in a fixed order, so
    that every consumer of this agrees on which cell group belongs to which
    array.  [depth] bounds the search, which a recursive datatype would
    otherwise not terminate on.  An array that cannot carry cells is not
    reported; see [cellable].

    With [sequences], a sequence of a scalar is reported too, as a path with
    one integer index level ([Sequence]).  Off, the default, a sequence is not
    a path, which is what every consumer saw before sequences could carry
    cells -- and since the template and the example expansion must agree on
    the list, both must be given the same value. *)
let array_paths ?(depth = 3) ?(sequences = false) (sorts : Sort.t list) :
    array_path list =
  let rec walk param sels d sort =
    match sort with
    | T_seq.SSeq elem_sort when sequences && seq_cellable elem_sort ->
        [
          {
            container = Sequence;
            param;
            selectors = List.rev sels;
            index_sorts = [ T_int.SInt ];
            elem_sort;
          };
        ]
    | T_array.SArray _ as sort ->
        (* the whole chain at once: an array of arrays is ONE array with a
           tuple index, not an array whose elements happen to be arrays *)
        let index_sorts, elem_sort = uncurry_array_sort sort in
        if not (cellable ~index_sorts ~elem_sort) then []
        else
          [
            {
              container = Array;
              param;
              selectors = List.rev sels;
              index_sorts;
              elem_sort;
            };
          ]
    | T_dt.SDT dt when d > 0 -> (
        match Datatype.conses_of dt with
        | [ cons ] ->
            List.concat_map (Datatype.sels_of_cons cons) ~f:(fun sel ->
                walk param
                  ((dt, Datatype.name_of_sel sel) :: sels)
                  (d - 1)
                  (Datatype.sort_of_sel dt sel))
        | _ -> [])
    | _ -> []
  in
  List.concat_mapi sorts ~f:(fun i s -> walk i [] depth s)

(** Whether an array is reachable from a value of [sort]: the sort is an
    array, or one reaches through the fields of a tuple or of a datatype (any
    of its constructors), to [depth] datatype levels, which a recursive
    datatype would otherwise not terminate on.  Unlike [array_paths] this
    reports every array, cellable or not, and looks through tuples and
    multi-constructor datatypes too: it answers "does this predicate see an
    array at all", not "which cell groups does it get".  A sequence is not an
    array here. *)
let rec reaches_array ?(depth = 3) (sort : Sort.t) =
  match sort with
  | T_array.SArray _ -> true
  | T_tuple.STuple sorts -> List.exists sorts ~f:(reaches_array ~depth)
  | T_dt.SDT dt when depth > 0 ->
      List.exists (Datatype.conses_of dt) ~f:(fun cons ->
          List.exists (Datatype.sels_of_cons cons) ~f:(fun sel ->
              reaches_array ~depth:(depth - 1) (Datatype.sort_of_sel dt sel)))
  | _ -> false

(* The positions of [params] whose sort is an array with [Bool] elements --
   a relation, the only kind of universal function a dependency set can
   name -- and which every clause passes on unchanged: in each formula of
   [phis] that applies [pvar] (to as many arguments as [params]), every such
   application has one and the same term variable at the position.  Empty
   when [pvar] is applied nowhere.

   What this stands for, and why it is read off the clauses: a universal
   function in a dependency set is an array-sorted free variable of each
   clause, handed to the predicate as an extra argument at every application,
   and the constraint problem keeps no record of which free variables came
   from a [declare-forall-fun].  Names do not help either: clause variables
   are renamed per clause, so the universal is [x0] in one clause and [x4] in
   another.  What does survive is that it is never changed along a clause.
   A Bool array of the program that no clause writes is caught too; it is
   likewise a universal of every clause. *)
let universal_array_positions ~pvar ~(params : sort_env_list)
    (phis : Formula.t list) : int list =
  let apps_per_formula =
    List.filter_map phis ~f:(fun phi ->
        let pos, neg = Formula.atoms_of (Formula.elim_let phi) in
        match
          List.filter_map (Set.to_list (Set.union pos neg)) ~f:(function
            | Atom.App (Predicate.Var (pv, _), args, _)
              when Ident.pvar_equal pv pvar
                   && List.length args = List.length params ->
                Some args
            | _ -> None)
        with
        | [] -> None
        | apps -> Some apps)
  in
  if List.is_empty apps_per_formula then []
  else
    List.filter_mapi params ~f:(fun i (_, s) ->
        match s with
        | T_array.SArray (_, T_bool.SBool)
          when List.for_all apps_per_formula ~f:(fun apps ->
                   match
                     List.map apps ~f:(fun args ->
                         match List.nth_exn args i with
                         | Term.Var (y, _, _) -> Some y
                         | _ -> None)
                   with
                   | Some y :: rest ->
                       List.for_all rest ~f:(function
                         | Some y' -> Ident.tvar_equal y y'
                         | None -> false)
                   | _ -> false) ->
            Some i
        | _ -> None)

(** Whether a predicate over argument sorts [sorts] reaches an array that is
    program state rather than a universal relation: some position not in
    [universal] (the result of [universal_array_positions] for that
    predicate) has a sort from which [reaches_array] reaches an array.  A
    position in [universal] holds a relation every clause passes on
    unchanged, so whatever a loop does it does not change that array; the
    predicate reaches no array of the program through it.  With [universal]
    empty this is [List.exists sorts ~f:reaches_array]. *)
let reaches_program_array ~(universal : int list) (sorts : Sort.t list) =
  List.existsi sorts ~f:(fun i s ->
      (not (List.mem universal i ~equal:Int.equal)) && reaches_array s)

(** The array itself, as a term, given the term at the path's parameter. *)
let read_path path term =
  List.fold path.selectors ~init:term ~f:(fun t (dt, name) ->
      T_dt.mk_sel dt name t)

(** The terms of [sort] that a list of (argument, sort) pairs reaches: the
    arguments themselves and their projections through single-constructor
    datatypes, to [depth], compared by printed sort and deduplicated by printed
    term.  This is where a cell over an index sort that cannot be counted --
    a sort variable, an uninterpreted sort -- takes its candidate indices from
    besides the ones the array stores: an invariant [forall b. q_p(cur x, b, v)]
    pins two of the three indices to terms the predicate's own arguments reach,
    [cur x] and [v], and a cell at any other index says nothing about it. *)
let terms_of_sort ?(depth = 3) (sort : Sort.t) (args : (Term.t * Sort.t) list) :
    Term.t list =
  let target = Term.str_of_sort sort in
  let rec walk t s d acc =
    let acc =
      if String.equal (Term.str_of_sort s) target then t :: acc else acc
    in
    match s with
    | T_dt.SDT dt when d > 0 -> (
        match Datatype.conses_of dt with
        | [ cons ] ->
            List.fold (Datatype.sels_of_cons cons) ~init:acc ~f:(fun acc sel ->
                walk
                  (T_dt.mk_sel dt (Datatype.name_of_sel sel) t)
                  (Datatype.sort_of_sel dt sel)
                  (d - 1) acc)
        | _ -> acc)
    | _ -> acc
  in
  List.fold args ~init:[] ~f:(fun acc (t, s) -> walk t s depth acc)
  |> List.rev
  |> List.dedup_and_sort ~compare:(fun a b ->
         String.compare (Term.str_of a) (Term.str_of b))

(** A name for the array a path reaches, used for the placeholder columns.  Two
    arrays reachable from one parameter must not share it. *)
let name_of_path path base =
  List.fold path.selectors ~init:(Ident.name_of_tvar base) ~f:(fun acc (_, sel) ->
      acc ^ "." ^ sel)

(** {1 Placeholders for an array reached through selectors}

    The columns are named after the array, and an array reached through a
    record is named after the parameter it starts at followed by the selectors:
    [#cidx@x1.unbox].  The extraction meets that array as a TERM in a clause and
    the template meets it as a PATH from a parameter, and they have to agree on
    the name, which is what these two functions are for. *)

let path_name base sels =
  List.fold sels ~init:(Ident.name_of_tvar base) ~f:(fun acc s -> acc ^ "." ^ s)

(** {1 Sequence reads and writes met in a clause}

    The clause-level extraction lifts an atom about an array's contents to one
    about that array's cell columns, and it recognises a read as [select a j]
    with an integer index and element.  The same two columns describe a
    sequence position and its element, so a [seq.nth s j] over a sequence of
    integers is lifted the same way.  What differs is that a sequence read is
    meaningful only inside [0 <= j < seq.len s]: outside it the value is one the
    theory leaves open.  A lifted qualifier is safe because a cell of a sequence
    exists only at an index inside that range (or at the sentinel, whose value
    is a constant and not a read), and the read-back puts the range in front of
    the cell's universal.  What would not be safe is a lifted qualifier that
    still contains a [seq.nth]: that read carries no range premise, so every
    lifted result is required to contain none ([mentions_seq_read]). *)

(** A read [seq.nth s j] of a sequence of integers at an integer index, with
    [s] reached by [access_path] from a variable the unknowns are applied to:
    the placeholder name of that sequence, the index and the read itself.
    [None] for any other term, including a read of a sequence whose elements
    are not integers, since the value column a schema names is integer-sorted. *)
let seq_nth_read ~access_path (t : Term.t) :
    (Ident.tvar * Term.t * Term.t) option =
  match t with
  | Term.FunApp (T_seq.SqNth se, [ s; idx ], _)
    when Term.is_int_sort se && Term.is_int_sort (Term.sort_of idx) -> (
      match access_path s with
      | Some (base, sels) -> Some (Ident.Tvar (path_name base sels), idx, t)
      | None -> None)
  | _ -> None

let mentions_seq_read_atom atm =
  not @@ Set.is_empty @@ Atom.filtered_terms_of ~f:T_seq.is_nth atm

(** Whether [phi] still reads a sequence.  A lifted qualifier must not: the read
    would be one with no range premise. *)
let mentions_seq_read phi =
  not @@ Set.is_empty @@ Formula.filtered_terms_of ~f:T_seq.is_nth phi

(** Lift an atom that reads the sequence [a] at an out-of-scope variable to one
    about [a]'s cell: each read in [reads] whose sequence is [a] and whose index
    is one of the variables [out_of_scope] becomes the value column, and those
    variables become the index column.  The caller rejects the result when a
    variable that is neither an argument nor a column is left, or when a
    sequence read is left ([mentions_seq_read_atom]). *)
let lift_seq_index_atom ~(reads : (Ident.tvar * Term.t * Term.t) list)
    ~(out_of_scope : Ident.tvar list) (a : Ident.tvar) (atm : Atom.t) : Atom.t =
  let atm =
    Atom.map_term_no_binders atm ~f:(fun t ->
        if
          List.exists reads ~f:(fun (a', idx, t') ->
              Ident.tvar_equal a a'
              && Stdlib.(t = t')
              &&
              match idx with
              | Term.Var (j, _, _) ->
                  List.mem out_of_scope j ~equal:Ident.tvar_equal
              | _ -> false)
        then val_term a T_int.SInt
        else t)
  in
  Atom.rename
    (Map.Poly.of_alist_exn
    @@ List.map (List.dedup_and_sort ~compare:Ident.tvar_compare out_of_scope)
         ~f:(fun v -> (v, idx_of a)))
    atm

(** The equalities [x = seq.store s i v] offered to an unknown from the
    sequence writes of one clause.  A write is taken only when every variable
    it mentions is an argument of the unknown ([args]), and it is paired with
    each argument of the write's sort that the write does not mention.  So the
    vocabulary is bounded by the writes the problem contains times the
    unknown's sequence arguments; nothing is enumerated over index or element
    terms, and a problem with no write contributes nothing. *)
let seq_store_equalities ~(args : sort_env_list) (stores : Term.t list) :
    Formula.t list =
  List.concat_map stores ~f:(fun st ->
      match st with
      | Term.FunApp (T_seq.SqStore _, _, _) ->
          let fvs = Term.fvs_of st in
          if
            Set.is_empty fvs
            || not
                 (Set.for_all fvs ~f:(fun v ->
                      List.Assoc.mem args ~equal:Ident.tvar_equal v))
          then []
          else
            let srt = Term.sort_of st in
            List.filter_map args ~f:(fun (x, s) ->
                if Stdlib.(s = srt) && not (Set.mem fvs x) then
                  Some (Formula.eq (Term.mk_var x s) st)
                else None)
      | _ -> [])
  |> List.dedup_and_sort ~compare:Stdlib.compare

(** Whether [q] is an equality between a sequence variable and a sequence
    write, in either orientation: the shape [seq_store_equalities] offers. *)
let is_seq_store_equality (q : Formula.t) : bool =
  match q with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ l; r ], _), _) -> (
      match (l, r) with
      | Term.Var (_, T_seq.SSeq _, _), Term.FunApp (T_seq.SqStore _, _, _)
      | Term.FunApp (T_seq.SqStore _, _, _), Term.Var (_, T_seq.SSeq _, _) ->
          true
      | _ -> false)
  | _ -> false

(** Whether [q] is an equality between two sequence-sorted terms that reads
    no position: [x = y], [x = seq.extract y i n], [x = seq.store y i v],
    [x = y ++ z].  Every sequence operation other than [seq.nth] is total and
    fixed by the theory, so such a qualifier has one truth value in every
    model at every ground row, and it relates whole sequences -- a statement
    no cell qualifier can make, a cell being one position of one sequence.
    [is_seq_store_equality] is the special case of a single write. *)
let is_sequence_equality (q : Formula.t) : bool =
  match q with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ l; r ], _), _) ->
      T_seq.is_sseq (Term.sort_of l)
      && T_seq.is_sseq (Term.sort_of r)
      && (not (Stdlib.( = ) l r))
      && Set.is_empty (Formula.filtered_terms_of ~f:T_seq.is_nth q)
  | _ -> false

(** Whether [q] is an equality or a disequality between two whole arrays (an
    array variable, a store chain over one, an array literal), possibly under
    a negation: an atom about arrays as values rather than about their
    elements.  A read [a[i]] has its element sort, so an atom over reads is
    never one of these. *)
let is_whole_array_equality (q : Formula.t) : bool =
  let rec go = function
    | Formula.Atom
        (Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ l; r ], _), _) ->
        Term.is_array_sort (Term.sort_of l)
        && Term.is_array_sort (Term.sort_of r)
    | Formula.UnaryOp (Formula.Not, phi, _) -> go phi
    | _ -> false
  in
  go q

(** Split a placeholder into its kind, the variable it starts at and the
    selectors after it.  [None] for an ordinary variable. *)
let split_placeholder (Ident.Tvar x) =
  let of_body is_idx body =
    match String.split body ~on:'.' with
    | [] -> None
    | base :: sels -> Some (is_idx, Ident.Tvar base, sels)
  in
  match String.chop_prefix x ~prefix:idx_prefix with
  | Some body -> of_body true body
  | None ->
      Option.bind (String.chop_prefix x ~prefix:val_prefix) ~f:(of_body false)

(** Rewrite a placeholder's base variable, keeping its kind and selectors.
    Used where a qualifier written about a clause's variables is re-expressed
    about a predicate's parameters. *)
let rebase_placeholder v ~f =
  match split_placeholder v with
  | None -> None
  | Some (is_idx, base, sels) ->
      Option.map (f base) ~f:(fun base' ->
          let name = path_name base' sels in
          if is_idx then Ident.Tvar (idx_prefix ^ name)
          else Ident.Tvar (val_prefix ^ name))

(** {1 Witness indices observed by the validator}

    A celled candidate is read back as [\ (a,x..). forall i. phi(i, a[i], x..)],
    so the validation query contains [exists i. not phi] and the model that
    refutes the candidate names the index at which it fails.  The example built
    from that model records the predicate's arguments and not the index, so the
    next expansion offers the same fixed candidate cells and the same candidate
    class survives -- measured at 801 counterexamples of which 767 are one.

    This is that index, carried from the phase that computes it to the phase
    that needs it.  It is a channel between two phases and not where the value
    belongs: an index witnesses ONE example, and this holds the union over the
    run, so an index useful to one example is offered to all of them.  That is
    sound -- every offered cell is a cell the expansion is free to use, and both
    sides' soundness arguments quantify over whatever set is offered -- and it
    is the cheap form of the right change, which is for an example to carry its
    own witnesses. *)

(* Keyed by [Z.t]: a witness is a model integer and may exceed a native int.
   Zarith keeps an integer that fits unboxed and a larger one in one canonical
   block, so equal values hash and compare equal in a polymorphic table. *)
let witness_indices : (Z.t, unit) Hashtbl.Poly.t = Hashtbl.Poly.create ()

(* Whether the index a refutation named was among the cells the next round
   offered -- the live route's completeness condition, and the one thing the
   comment on the candidate set says nothing would report.

   The published instantiation heuristic answers the same question about a
   CLAUSE-driven index set and answers it statically, by refusing shapes it
   cannot account for.  Here the set is built by counting off the
   counterexample's array, so there is nothing to refuse and the only honest
   check is after the fact: a refutation names an index, and either the set
   offered when the next candidate was built contained it or it did not.  A miss
   is not a defect -- the offer is a guess and a guess may be wrong -- it is the
   difference between "the space could not say it" and "the space was never
   asked", which no verdict distinguishes.

   Kept here rather than on the offer because a witness outlives the round that
   produced it, exactly as the table above does, and for the same reason: this is
   a channel between two phases and the value belongs on the example. *)
let unoffered_witnesses : (Z.t, unit) Hashtbl.Poly.t = Hashtbl.Poly.create ()

(* Record that [offered] were the candidate indices available, and return the
   witnesses that were not among them and had not already been reported. *)
let note_offer (offered : Z.t list) =
  List.filter (Hashtbl.Poly.keys witness_indices) ~f:(fun w ->
      (not (List.mem offered w ~equal:Z.equal))
      && not (Hashtbl.Poly.mem unoffered_witnesses w))
  |> List.sort ~compare:Z.compare
  |> List.map ~f:(fun w ->
         Hashtbl.Poly.set unoffered_witnesses ~key:w ~data:();
         w)

let unoffered () =
  List.sort ~compare:Z.compare (Hashtbl.Poly.keys unoffered_witnesses)

let record_witness (i : Z.t) = Hashtbl.Poly.set witness_indices ~key:i ~data:()
let witnesses () = List.sort ~compare:Z.compare (Hashtbl.Poly.keys witness_indices)
let clear_witnesses () =
  Hashtbl.Poly.clear witness_indices;
  Hashtbl.Poly.clear unoffered_witnesses

(* The integer index terms [phi] reads the array variable [x] at, keeping
   only those whose variables are all free in [phi]: an index under a binder
   names a bound variable, and a disequality over it outside the binder would
   mention a variable the query does not have.  Deduplicated by printed form.
   The order is the order [Formula.iter_term] visits the reads in, which is a
   function of the formula alone, so the pairs asked for are the same from run
   to run -- and that is the property that matters, because the order of the
   disequalities is the order the solver sees them in.  It is NOT textual order:
   a conjunction built by [and_of] is visited in its own nesting order. *)
let clause_read_indices phi x =
  let fvs = Formula.tvs_of phi in
  let acc = ref [] in
  Formula.iter_term phi ~f:(fun t ->
      match t with
      | Term.FunApp (T_array.ASelect (si, _), [ Term.Var (y, _, _); idx ], _)
        when Ident.tvar_equal x y && Term.is_int_sort si
             && Set.is_subset (Term.tvs_of idx) ~of_:fvs ->
          if not (List.exists !acc ~f:(fun u -> String.equal (Term.str_of u) (Term.str_of idx)))
          then acc := idx :: !acc
      | _ -> ());
  List.rev !acc

(* Does this array value hold more than one thing?  A model returns an array
   as a constant with a chain of stores over it, so "varies" is "has a store
   whose stored value differs from what is underneath" -- approximated here by
   the presence of any store at all, which is what the producer of these
   values does: it writes a store only where the array is constrained to
   differ. *)
let rec array_varies t =
  match t with
  | Term.FunApp (T_array.AStore _, _, _) -> true
  (* a constant array holds ONE thing everywhere -- but for an array of
     arrays that one thing may itself vary, and a cell over the whole
     chain then sees a varying value below a constant level; [const (store
     ...)] read as constant is how a curried trait array was reported
     constant on every head example while it stored values one level down *)
  | Term.FunApp (T_array.AConst _, [ d ], _) -> array_varies d
  | Term.FunApp (T_array.AConst _, _, _) -> false
  | Term.FunApp (T_array.ALambda _, _, _) -> true
  | _ -> (
      match t with
      | Term.FunApp (_, ts, _) -> List.exists ts ~f:array_varies
      | _ -> false)

(** {1 A clause's disjunction about one cell}

    The per-atom lifting above turns each atom about an array's contents into
    one qualifier about a cell, so a goal clause
    [I(a, i, n) /\ 0 <= j /\ j <= n /\ a[j] <> j => bot] contributes the three
    atoms [0 <= #cidx], [#cidx <= n] and [#cval = #cidx] separately, while the
    invariant's body is their DISJUNCTION
    [#cidx < 0 \/ #cidx > n \/ #cval = #cidx] -- a shape the template reaches
    only by spending one disjunct of its own shape per atom.

    [clause_cell_disjunctions ~bvars ~reads phi] reads that disjunction off the
    clause [phi], written as a disjunction of literals (a premise appears
    negated).  For each out-of-scope variable [j] (not in [bvars], the
    variables the clause's unknowns are applied to) that indexes a read in
    [reads] of an array or sequence [a] (as collected by the extraction:
    (array path, index, read term)), the disjuncts [d] kept are those
    - with no binder, no [let] and no application of an unknown,
    - mentioning [j], every other variable of [d] being in [bvars];
    each is lifted by the same renaming as the per-atom lifting (each read of
    [a] at [j] becomes [a]'s value column, [j] becomes its index column), and
    one whose lifted form still reads some array or sequence at the index
    column -- a read of another array at [j] -- is left out.  When at least
    two disjuncts remain their disjunction is returned, paired with [a]: at
    most one formula per (clause, read index, array).

    Contract: the result adds vocabulary only.  Every formula returned is a
    candidate building block for a template and nothing more -- any candidate
    built from one is validated against the clauses -- so what is returned
    cannot bear on soundness, only on which candidates the search can
    express.  The result mentions placeholder columns, which a template that
    generates no cells drops. *)
let clause_cell_disjunctions ~(bvars : Ident.tvar Set.Poly.t)
    ~(reads : (Ident.tvar * Term.t * Term.t) list) (phi : Formula.t) :
    (Ident.tvar * Formula.t) list =
  (* the clause's top-level disjuncts, looking through a negated conjunction
     and an implication, which is how a premise can be written *)
  let rec disjuncts acc phi =
    match phi with
    | Formula.BinaryOp (Formula.Or, p1, p2, _) -> disjuncts (disjuncts acc p2) p1
    | Formula.BinaryOp (Formula.Imply, p1, p2, _) ->
        disjuncts (disjuncts acc p2) (Formula.mk_neg p1)
    | Formula.UnaryOp (Formula.Not, Formula.BinaryOp (Formula.And, p1, p2, _), _)
      ->
        disjuncts (disjuncts acc (Formula.mk_neg p2)) (Formula.mk_neg p1)
    | Formula.UnaryOp (Formula.Not, Formula.UnaryOp (Formula.Not, p, _), _) ->
        disjuncts acc p
    | phi -> phi :: acc
  in
  let ds =
    List.filter (disjuncts [] phi) ~f:(fun d ->
        Formula.is_quantifier_free d && Formula.is_let_free d
        && Set.is_empty (Formula.pvs_of d))
  in
  let index_pairs =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ List.filter_map reads ~f:(fun (a, idx, _) ->
           match idx with
           | Term.Var (j, _, _) when not (Set.mem bvars j) -> Some (j, a)
           | _ -> None)
  in
  List.filter_map index_pairs ~f:(fun (j, a) ->
      let mine =
        List.filter_map ds ~f:(fun d ->
            let fvs = Formula.tvs_of d in
            if
              (not (Set.mem fvs j))
              || Set.exists fvs ~f:(fun v ->
                     (not (Ident.tvar_equal v j)) && not (Set.mem bvars v))
            then None
            else
              let d' =
                Formula.map_term_no_binders d ~f:(fun t ->
                    if
                      List.exists reads ~f:(fun (a', idx, t') ->
                          Ident.tvar_equal a a'
                          && Stdlib.(t = t')
                          &&
                          match idx with
                          | Term.Var (j', _, _) -> Ident.tvar_equal j j'
                          | _ -> false)
                    then val_term a T_int.SInt
                    else t)
              in
              let d' =
                Formula.subst (Map.Poly.singleton j (idx_term a)) d'
              in
              let reads_at_column =
                Set.exists
                  (Formula.filtered_terms_of d' ~f:(fun t ->
                       T_array.is_select t || T_seq.is_nth t))
                  ~f:(function
                    | Term.FunApp (_, [ _; idx ], _) ->
                        Set.mem (Term.tvs_of idx) (idx_of a)
                    | _ -> false)
              in
              if reads_at_column then None else Some d')
      in
      if List.length mine < 2 then None
      else Some (a, Formula.or_of mine))
