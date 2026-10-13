(* Three mechanisms in this subsystem are switched off in every shipped
   configuration -- the index/value cells, the QSAT clause-constraint route
   and the quantifier-prefix synthesis -- and some definitions have no caller
   at all.  Three markers
   say which code is which, and every one of them carries the reason it is
   where it is:

     REACHABLE ON THE DEFAULT PATH -- executes in an ordinary run; the comment
       states what it evaluates to there, which in every case is "no change".
     UNREACHABLE BY DEFAULT (<mechanism>) -- runs only when that mechanism's
       field is set.
     PORTED, UNCALLED -- no caller at all.

   DUBIOUS marks code that is kept without being endorsed: a defect preserved
   deliberately so that unexercised code is not quietly "repaired", a
   heuristic whose constants nothing explains, a printer used as a
   serialiser.  Those are the ones to argue about first. *)

open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open Function
open PCSatCommon

module Config = struct
  type t = {
    verbose : bool; [@default false]
    number_of_disj : int; [@default 1]
    (* "Number of quantifiers per array" is what this was *meant* to be, and
       that feature is still wanted: a template that quantifies over an array's
       indices.  It was never built, and the field came to carry something else
       -- the depth handed to the qualifier term map -- so today the name states
       an intention rather than the field's content.  Both halves are open work:
       implement quantifiers per array, and rename this once it no longer has to
       stand for two things.  Renaming is not free, because the field appears in
       more than a thousand configuration files.

       Since the quantified template below exists, the feature half of that is
       done and lives under [number_of_quantifiers_per_array]; what is left is
       to decide whether the two fields become one, which is a corpus-wide
       rename and a change of meaning for every configuration that sets this
       one, so it is not done in passing. *)
    number_of_qpa : int; [@default 1]
    (* Whether the qualifier term map's depth is the shape parameter that the
       template's growth moves ([increase_qpa] / [decrease_qpa]) rather than
       the fixed [number_of_qpa] above.  Off, the growth action changes the
       recorded parameter and nothing that reads it -- the depth stays at its
       configured value for the whole run -- so a leaf reached through more
       selectors than that never becomes a term, however long the search
       grows the template.  The field above only sets the starting depth when
       this is on. *)
    term_depth_follows_shape : bool; [@default false]
    (* Whether growing the term depth also raises the constant bound to at
       least the new depth.  The constant bound otherwise climbs only when an
       unsat core names it, which it cannot do before terms that can use a
       constant exist, so deeper terms arrive with the bound still at its
       starting value.  Only an increase of the depth raises it; a decrease
       leaves it where it is.  It acts whenever the growth action raises the
       shape parameter, with or without [term_depth_follows_shape]; without
       that field the terms do not deepen, so the raised bound meets no new
       term. *)
    const_bound_follows_depth : bool; [@default false]
    (* How many universally quantified index variables the template gets *per
       array-sorted parameter*.  Zero, the default, is the template this module
       always generated.  Above zero the predicate becomes

         \\ params. forall i_1 .. i_n. <DNF over params and i_1 .. i_n>

       with n = this field times the number of array-sorted parameters, so a
       solution may say something about every index rather than about the
       finitely many a quantifier-free body can name.  The quantified form is
       strictly more expressive and strictly more expensive -- the synthesis
       query grows with the number of bound variables -- which is why it is off
       until an input is measured to need it. *)
    number_of_quantifiers_per_array : int; [@default 0]
    (* Index/value cells per array-sorted parameter.  Where
       [number_of_quantifiers_per_array] lets the predicate *say*
       [forall i. ...], this lets the hypothesis space *see* a read: the
       parameter list gains two integers per cell, an index and the value the
       array holds there, and the example atoms are extended with concrete
       pairs sampled from the array they carry (the constraint generator's
       celled examples).  A qualifier over those columns is then a statement
       about [a[i]], and the learned candidate is read back as one. *)
    number_of_cells_per_array : int; [@default 0]
    (* With cells, is the array parameter itself still part of the template's
       vocabulary?  The point of a cell is that the predicate reasons about
       (index, value) pairs instead of about the array, and the existing
       qualifier term map generates a read at every integer the predicate can
       name -- [a[i]], [a[0]], [a[1]], [a[j]] -- so the two vocabularies are
       present at once and the affine atoms are built over their union.  That
       is not unsound: a celled example still carries its array, so such a term
       has a value.  It is a cost, and it is the one that grows fastest, since
       each extra term is another coefficient in every affine atom of every
       disjunct.  Switching this on drops every term and qualifier mentioning
       an array parameter, leaving the cells to stand for it. *)
    cells_replace_array_terms : bool; [@default false]
    (* Offer, from the parameters alone, the comparisons that bound a cell:
       each column against each of the predicate's own integer parameters and
       against zero.  The clause-driven lifting produces the same shapes where
       a clause happens to write them, and this produces them whether or not it
       does -- the same argument the sequence suffix relation is added on, one
       section below.  It is cheap and bounded: two columns times (integer
       parameters + 1) values times two directions.

       It is not made redundant by the affine atoms the template already
       generates over its extended parameter list, because those carry a bound
       on the constant term -- an atom with no constant cannot say [j >= 0]
       against a bound of zero -- while a qualifier is a formula and carries
       its own. *)
    cell_boundary_quals : bool; [@default false]
    (* The comparisons that relate two cells of one array: their indices, their
       values, and each pairing of the two.  A predicate whose solution needs
       this is one of cell width two -- [a[i] <= a[j]], the shape sortedness is
       written in -- where the boundary family above covers width one.  It is
       vacuous with a single cell per array and quadratic in the cell count, so
       it is the family to switch on for an input whose invariant compares two
       elements and to leave off otherwise. *)
    cell_pair_quals : bool; [@default false]
    (* Keep only the qualifiers that mention a cell column.  With cells, what
       the predicate is supposed to say is a statement about (index, value)
       pairs, and everything else in the space is a statement about the other
       arguments -- true of the abstraction's intent and false of the code,
       which hands the template the whole extracted space on top of the cell
       families.  This is the isolating instrument for the question the search
       keeps failing on: if the intended solution is reachable and the run
       still does not find it, the space is the suspect, and cutting it to the
       columns the answer is written in either finds it or clears the space of
       blame.  It is a measurement switch rather than a shipping default: a
       predicate whose invariant needs one of its scalar arguments outside a
       cell comparison cannot be expressed with this on. *)
    cell_quals_only : bool; [@default false]
    (* Relate the cells of DIFFERENT arrays, with their indices offset by one
       of the predicate's own integer parameters: for each pair of arrays,
       [j_1 = j_2 + p] and [v_1 = v_2] for every integer parameter [p] and for
       zero.

       This is the vocabulary a slice walk needs and the one nothing else here
       produces.  An invariant saying "this array is that one from index i on"
       is [forall k. a[k] = b[i + k]], which as cell qualifiers is
       [j_a = j_b + i] together with [v_a = v_b].  A family generated from the
       parameters compares a column with a parameter; the within-array pair
       family compares two cells of one array; and the clause-driven lifting
       states the relation only at the index the clause happens to be written
       at, because generalising it to every [k] is what the induction is for.

       It is quadratic in the arrays and linear in the integer parameters, so
       it is a switch rather than a default, and with one array it produces
       nothing. *)
    cell_cross_array_quals : bool; [@default false]
    (* Relate an integer index of one array's cell to the integer VALUE of
       another array's cell: [j_1 = v_2 + p] for every pair of distinct arrays
       (both orders), every integer index column [j_1] of the first, every
       cell of the second whose array holds integers, and [p] zero or one of
       the predicate's own integer parameters.  This is the vocabulary of an
       invariant that uses the contents of one array to index another --
       [forall k. 0 <= k < len v => q_produces(x, v[k])] over a sequence [v]
       and a curried universal [q_produces] is, over one cell of each,
       [c /= x \/ j /= w \/ b] with [(k, w)] the sequence's cell and
       [(c, j, b)] the universal's -- which [cell_cross_array_quals] cannot
       state, since it relates indices to indices and values to values only.
       Linear in the pairs of arrays, the cells and the integer parameters;
       changes the hypothesis space only, so it cannot bear on the soundness
       of a verdict.  Nothing is produced with a single array, or when no
       array holds integers. *)
    cell_cross_index_value_quals : bool; [@default false]
    (* Offer, for two cells of ONE array, the equality of their integer
       indices of the same level, [j_1 = j_2].  [cell_pair_quals] offers the
       two orders [j_1 <= j_2] and [j_2 <= j_1] and no equality, so an
       invariant relating an array's contents at two points at the same
       index -- [forall i. q(cur it, i) => q(cur entry, i)], two cells of the
       universal [q] -- needs both orders in one disjunct and their
       negations in two, where a qualifier hole over the equality states the
       disequality in one.  Independent of [cell_pair_quals]; vacuous with a
       single cell per array.  Changes the hypothesis space only. *)
    cell_pair_index_equalities : bool; [@default false]
    (* Two extra disjuncts per integer cell index column [j], on top of the
       [number_of_disj] base disjuncts, each a qualifier hole over only the
       comparisons of [j] with zero and with the predicate's own integer
       parameters, beside the qualifiers that mention no cell column (the
       facts about the scalar arguments, which such an invariant conjoins into
       every disjunct).  The typical quantified invariant is
       [forall j. low <= j /\ j <= high => phi], which over a cell reads
       [j < low \/ j > high \/ phi]: the two guards are meant to take the
       first two disjuncts, so the base shape is left for [phi].  A predicate
       with no integer cell index column gets no guard, so its template is
       the one it gets without this field.  The guards are fixed rather than
       counted into the shape: growing the template grows the base disjuncts
       only.  This changes the hypothesis space and nothing else, so it
       cannot bear on the soundness of a verdict. *)
    cell_guard_disjuncts : bool; [@default false]
    (* With [cell_guard_disjuncts], also let a guard compare its index column
       with the integer-sorted terms of the hypothesis space that mention no
       cell column (a tuple projection, a sequence length), not only with the
       predicate's own integer parameters.  A loop counter carried inside a
       tuple argument is such a term, and without this the guard can state no
       bound on it.  Changes the hypothesis space only. *)
    cell_guard_bound_terms : bool; [@default false]
    (* With [cell_guard_disjuncts], also let a guard compare its index column
       with at most this many integer terms that the predicate's own
       parameters REACH through the selectors of single-constructor datatypes
       (a tuple field, a mutable reference's current value, to depth three),
       taken shallowest first and in printed order within a depth; 0, the
       default, adds none.  These are the terms a counter or a bound carried
       inside a tuple argument is: an invariant [forall k. 0 <= k < t.2 =>
       t.1[k] = 0] over a tuple [t] needs the guard [k >= t.2], and the
       predicate's integer parameters do not include [t.2].  Unlike
       [cell_guard_bound_terms], which offers every term of the hypothesis
       space (affine combinations and sequence lengths among them, so the
       guard grows with the space), the offer is fixed by the predicate's
       signature and bounded, so the guard stays two qualifiers per term.
       Changes the hypothesis space only, so it cannot bear on the soundness
       of a verdict. *)
    cell_guard_reachable_bounds : int; [@default 0]
    (* With [cell_guard_disjuncts], give the guards only to a predicate with at
       most this many integer cell index columns; a predicate with more gets
       the template it gets without guards.  0, the default, sets no bound.
       The guards cost two qualifier holes per column, each over every
       cell-free qualifier of the predicate, and every guard reads its index
       column, so a candidate that selects one is read back with that cell's
       universal kept.  Over three sequence arguments that was measured to be
       the difference: without guards a loop over three slices answered in a
       few seconds on every run, with them it rarely answered in a minute,
       its synthesis rounds growing to seconds and a validation query over
       the candidate's nested universals on sequence indices not returning.
       Only the guards are dropped, so the template left still contains
       every candidate of the cell-free template (the cell coefficients at
       zero), and a predicate at or below the bound keeps exactly the
       template it had.  Like the guards themselves it changes the hypothesis
       space and nothing else, so it cannot bear on the soundness of a
       verdict. *)
    cell_guard_max_index_columns : int; [@default 0]
    (* With [cell_guard_disjuncts], give a predicate its guards only after
       its celled template without guards has been regenerated this many
       times.  The synthesizer regenerates a template when the space it was
       built from no longer serves: a qualifier or term learnt from the
       examples, or a growth of the shape.  A predicate whose first space
       yields its solution is never regenerated and never gets guards.  0,
       the default, gives the guards with the cells.  A growth failure alone
       was tried as the signal and does not fire where the guards are needed:
       a loop zeroing a sequence up to a counter learnt a qualifier every
       round, its template was rebuilt 68 times in a minute, and its shape
       never grew.
       Why: the guards are a second enlargement of the space on top of the
       cells, and every guard a candidate selects is read back with its cell's
       universal, so validating it asks a query with nested universals over
       sequence indices.  A loop over a slice whose remaining part is the
       original shifted by the counter needs no guard; over two sequence
       arguments (a third, equal, one having been dropped as determined by the
       clauses) it answered in under a second with the guards withheld and in
       8 to 17 s with them, most of it validation queries on guarded
       candidates spending their whole 5 s budget undecided.
       The template before the switch is the celled template with every
       guard at zero, so the space only grows, and the switch is never
       undone.  It changes the hypothesis space and its order only, so it
       cannot bear on the soundness of a verdict. *)
    cell_guard_after_failures : int; [@default 0]
    (* Relate a cell's value to its index shifted by an integer term: for
       every cell of an array or sequence indexed by one integer and holding
       integers, the qualifiers [v = j + t] and [v = t], where [t] ranges over
       zero, the predicate's own integer parameters and at most this many
       integer terms the parameters reach through the selectors of
       single-constructor datatypes (the terms [cell_guard_reachable_bounds]
       takes, in the same order); 0, the default, adds none.  This is the
       vocabulary of a range's contents: [forall k. 0 <= k < len v => v[k] =
       r.start + k] over a range [r] carried inside a tuple is, over a cell,
       [v = j + r.start], and the boundary family compares a column with a
       parameter, the lifting states a relation only where a clause writes
       it, and the template's affine atoms cannot reach a term under two
       selectors.  Linear in the cells and in the terms; changes the
       hypothesis space only, so it cannot bear on the soundness of a
       verdict. *)
    cell_affine_value_terms : int; [@default 0]
    (* Compare a cell's integer index with the positions the problem WRITES
       to: for every array write [store A t v] in a clause that also applies
       this predicate to arguments over which [t] can be written -- each
       variable of [t] an argument of the application, so that [t] becomes a
       term over this predicate's parameters by renaming -- the qualifiers
       [j <= t] and [j >= t] for every integer index column [j] of a cell of
       an array of [A]'s sort.  This is the vocabulary of a loop that fills a
       region whose end moves with a counter at a slope other than one: a
       loop writing [3i - 3], [3i - 2] and [3i - 1] at round [i] has the
       invariant [forall j. j < 0 \/ j >= 3i - 3 \/ phi(a[j])], and nothing
       else here offers [j >= 3i - 3] -- the boundary family compares a
       column with one parameter at a time, the lifting states only the atoms
       a clause writes and a write index occurs in no atom, and the
       template's affine atoms start with coefficients bounded by one.  An
       array is matched to a write by its sort alone, so over two arrays of
       one sort both get the qualifiers.  At most
       [cell_store_index_quals_max] distinct index terms are taken per
       predicate, in the order the clauses give them.  It changes the
       hypothesis space only, so it cannot bear on the soundness of a
       verdict; a predicate without an integer-indexed cell gets nothing. *)
    cell_store_index_quals : bool; [@default true]
    cell_store_index_quals_max : int; [@default 8]
    (* Together with [cell_store_index_quals] (alone it does nothing), also
       compare a cell's integer index column with every write index taken at
       the predicate's starting state: for a fact clause of the predicate
       (one applying it positively and no predicate variable negatively) that
       fixes an integer parameter to a ground value, by a ground argument or
       by a premise [y = n], each write index mentioning such a parameter
       with the values substituted and simplified.  A loop writing [kS - i - 1]
       at round [i] from [i = 0] has swept [[kS - i, kS)] so far, and the
       bound [kS - 1] is stated by no atom of any clause, while an invariant
       of the form [forall j. ... \/ (j > kS - 1 /\ j <= (k+1)S - i - 1)]
       needs it and no atom over another direction can replace it.  At most
       [cell_store_index_quals_max] anchors, counted apart from the writes,
       and none equal to a write.  It changes the hypothesis space only, so
       it cannot bear on the soundness of a verdict. *)
    cell_store_index_anchor_quals : bool; [@default true]
    (* Together with [cell_store_index_quals] and [cell_guard_disjuncts]
       (alone it does nothing), also let each guard disjunct compare its
       integer index column with the write indices (and, with
       [cell_store_index_anchor_quals], the anchors) that
       [cell_store_index_quals] computes for the predicate: the guard may then
       select [j >= t] or [j <= t] for a write index [t], not only for zero
       and the predicate's integer parameters.  An invariant [C /\ forall j.
       j < 0 \/ j >= 3i - 3 \/ phi(a[j])] then needs one base disjunct for
       [phi], the two bounds being taken by the two guards; with the write
       indices only among the base-hole qualifiers it needs a second base
       disjunct for [j >= 3i - 3].  Only integer-sorted terms that mention no
       cell column are offered, each once, and no more of them than
       [cell_store_index_quals_max] writes and anchors already allow.  It
       changes the hypothesis space only, so it cannot bear on the soundness
       of a verdict. *)
    cell_guard_store_index_bounds : bool; [@default true]
    (* Remove from a template that has cell columns every qualifier that
       equates (or distinguishes) two whole arrays -- [a = b], [a = store b i
       v], their negations -- so that no hole of that template can select one;
       a cell-free template keeps them.  Why: with cells, an invariant speaks
       of arrays through their cell columns, and a candidate holding a
       whole-array equality turns the step clause's validation question into
       one with that equality under the post-state existential beside a
       universal over two index variables, a formula outside the array
       property fragment that z3 and cvc5 were both seen to leave undecided,
       so the round learns nothing from it.  It narrows the hypothesis space:
       an answer whose invariant needs the atom can be lost.  It changes the
       hypothesis space only, so it cannot bear on the soundness of a
       verdict. *)
    celled_drop_array_equality_quals : bool; [@default false]
    (* Search the template without cells first, and give it its cells (and,
       with [cell_guard_disjuncts], its guards) only after that template has
       failed [plain_template_failures] times.  A failure is a call of
       [update_with_labels] whose labels ask for the template to grow (a shape,
       coefficient or constant label); a label that only reports a timeout or
       a qualifier dependency is not one.  Until then the predicate's template
       binds only its own parameters, so the example expansion, the extended
       truth table and the read-back all treat it as a predicate without
       cells: it is the template the cell-free configuration builds from the
       same hypothesis space.  From the switch on it is the celled template at
       whatever shape the growth has reached, and the switch is never undone,
       not even by a restart of the shape.

       Why: cell columns enter every affine atom and every hole as extra
       parameters, the guards add two holes per index column, and the example
       expansion multiplies every example clause by its candidate cells.  A
       predicate whose invariant needs no cell -- a point fact about a nested
       read such as [a[b[i] + i] = i] -- then searches a larger space for a
       solution the cell-free template states at its first shapes, and was
       measured answering in about a second without cells and in 8 to 74 s, or
       not at all, with them.

       The space only grows: before the switch it is the cell-free template of
       the current shape, after it the celled template of the current shape,
       which contains that one with every cell coefficient and guard at zero.
       It changes the hypothesis space and the order it is searched in and
       nothing else, so it cannot bear on the soundness of a verdict. *)
    declared_atoms_after_failures : int; [@default 0]
    (* With [n > 0], the candidate atoms the input declares for this
       predicate ([(set-info :candidates ...)], [Arg.declared_atoms]) join its
       qualifiers only after [n] growth-asking failures of the template, at the
       next regeneration, and stay from then on.  Meant with the qualifier
       generator's [declared_atoms_houdini_only], which keeps them out of the
       qualifiers it offers: the synthesizer then searches the space extraction
       gives first and the declared atoms widen it only once that space has
       failed, so declaring atoms cannot slow a predicate the plain space
       answers early.  Without that switch the atoms are qualifiers from the
       start and this adds nothing.  [0]: off.  Like [plain_template_first] it
       changes the hypothesis space and the order it is searched in and
       nothing else. *)
    plain_template_first : bool; [@default false]
    plain_template_failures : int; [@default 1]
    (* [plain_template_first] for a predicate that reaches an array indexed by
       a sort variable or an uninterpreted sort, and for no other: such a
       predicate starts from the cell-free template and gets its cells after
       [plain_template_failures] growth failures, while a predicate whose
       arrays are all indexed by integers, enumerations or sequence positions
       gets them at once.  Why the split: a trait or closure contract over a
       quantified sort is an array over that sort, and cells over it gave a
       Rust-derived counting loop that declares no array or sequence cell
       columns on every predicate -- 180 thousand trace lines in a minute and
       no answer, against an answer in 11 s without cells -- while the inputs
       that need cells at once (a bounded prefix over an integer array or a
       sequence) lost their answers when every predicate started without
       them.  Like [plain_template_first] it changes only the hypothesis space
       and its order.

       The enumeration that the finite instantiation of a quantified sort
       substitutes for the sort variable counts as the sort variable here.
       That pass hands each size's instance to a nested constraint solve and
       takes only a refutation from it, so on a satisfiable input the nested
       solve runs until it finds a solution or the whole run's budget is gone.
       With the stand-in read as an ordinary enumeration, every predicate of
       the instance got its cells at once -- the case this switch exists to
       avoid -- and a two-loop Rust program whose run answers in about 13 s
       with the nested solve switched off spent all of 120 s in the nested
       solve at size 1. *)
    plain_template_first_sort_var_only : bool; [@default false]
    (* With [plain_template_first_sort_var_only], also count as a reason to
       defer the cells an array parameter with [Bool] elements that every
       clause passes on unchanged (the same variable at every application of
       the predicate within a clause).  That is the shape a dependency set
       gives: a universally quantified relation the witness may see (a trait
       invariant [Int -> Bool] over a quantified sort, say) is an array-sorted
       free variable of the clauses and is passed to the predicate as an extra
       argument, unchanged, everywhere.  Such an array is a parameter of the
       contract rather than program state, and a Rust-derived generic program
       whose only templated predicate reached an array this way answered in
       about 1.7 s of user CPU without cells and in 10 to 12 s with them.
       Why the criterion is syntactic is at [universal_array_positions].  Like
       the switch it extends, it changes the hypothesis space and its order
       and nothing else. *)
    plain_template_first_universal_arrays : bool; [@default true]
    (* With [plain_template_first], count a growth failure toward
       [plain_template_failures] only when the shape it happened at is not
       contained in a shape at which a failure was already counted.  The
       cell-free space at a shape contains the space at every smaller shape
       (fewer disjuncts, quantifiers, coefficient or constant bounds, a subset
       of the seeds), and the examples only grow, so a failure at a contained
       shape follows from the one already counted and says nothing new about
       whether the cell-free template can succeed.  Such repeats come from a
       restart, which returns the shape to its start while the counter
       stays: a Rust-derived generic loop whose invariant needs two disjuncts
       and no cells failed at one disjunct, grew, restarted after twenty
       rounds without an update, failed again at one disjunct and once at
       two, and so got its cells on its third failure; with cells each round
       took seconds and it never answered within 120 s, where the runs that
       kept the cell-free template answered in 15 to 50 s.  Off: every growth
       failure counts.  Changes the hypothesis space's order only. *)
    plain_template_failures_new_shapes_only : bool; [@default false]
    (* Two alternative growth policies for this template's bounds, from an
       abandoned branch, each off by default so that the default is the policy
       this template has always had.  They were one flag, which made them one
       experiment: a measurement of the pair could say the pair was worse and
       could not say which half was.  They are separate because they are
       separate questions, and because the second is the surprising one.

       [coeff_bound_floor_at_two]: on a failure that raises the coefficient
       bound, raise it to at least two instead of by one, so that the first
       raise from one lands on two rather than crawling.

       [reset_const_bound_on_failure]: on a failure that would raise the
       constant bound, put it back to the value it started at.  This is a
       *decrease* dressed as an increase -- the action is still called
       "increase_const" and still reads as one at the call site -- and it is
       only coherent as a policy if the shapes worth visiting are the small
       ones, revisited, rather than a widening ladder.  Whichever way a
       measurement settles it, the action's name has to say which it does
       before either is adopted. *)
    coeff_bound_floor_at_two : bool; [@default false]
    reset_const_bound_on_failure : bool; [@default false]
    restart_to_configured_shape : bool; [@default false]
    (** Where a restart, and each [init_*] action, puts the shape.  Off: a
        fixed shape of one disjunct, one quantifier per array, coefficient
        bound 1, constant bound 0 and seed 0, whatever the configuration
        says -- so a configuration that starts at two disjuncts is back at
        one after the first restart, and the template can no longer state an
        invariant that needs two, until it has grown again.  On: the shape
        the configuration starts from ([number_of_disj], [number_of_qpa],
        [upper_bound_coeff], [upper_bound_const], [seeds]).  The two agree on
        every configuration whose starting shape is that fixed one. *)
    grow_disj_when_qpa_inert : bool; [@default true]
    (** What a shape-growth step ([DisjQPA] or [Shape] label) raises when the
        quantifier-count parameter [nq] is read by nothing on this
        predicate's path.  The step alternates: it raises the number of
        disjuncts when [nd + nq] is even and [nq] otherwise.  [nq] is read
        only by the qualifier term map under [term_depth_follows_shape], by
        the constant bound under [const_bound_follows_depth], and by the
        depth bound of [in_space] ([upper_bound_depth], or a depth bound the
        problem states for the predicate); with none of these it is inert, so
        every second growth step leaves the shape as it was (the coefficient
        and constant bounds still grow by their own labels).

        On, and only where [nq] is inert in that sense, every growth step
        raises the number of disjuncts: after f steps from nd0 disjuncts the
        template has nd0 + f of them, where off it has about nd0 + f/2 (the
        rounding fixed by the parity of nd0 + nq).  The numbers of disjuncts
        visited are the same ones, reached in half the steps, but each at a
        smaller coefficient bound when the failures also raise the bounds; the
        starting shape, the restart shape and every other parameter are
        unchanged.  Where [nq] is live the step alternates as before. *)
    restart_ladder : bool; [@default true]
    (* Grow the non-ucore template by keeping its built disjuncts.  Off, every
       build draws every hole afresh.  On, a build whose inputs are the last
       build's (the qualifiers, the cell and template parameters, the guard
       inputs) with more disjuncts returns the last template with the new
       disjuncts' holes added beside it: [P := T_old \/ D_new], where [T_old]
       keeps its hole and key names.  A fresh build at the same shape is
       [G \/ D_1 \/ .. \/ D_n] with each [D_i] drawn by the same generator
       independently, so the two templates are equal up to a renaming of hole
       and key names and the order of disjunction: the same hypothesis space
       and the same candidates.  It applies only without quantifier index
       variables and without affine atoms in the base disjuncts (whose bounds
       move with the shape); anything else builds afresh.  What it buys is
       names that survive a growth step, so that a consumer can reuse what it
       computed for the kept disjuncts. *)
    grow_keeping_disjuncts : bool; [@default false]
    (** Where a restart puts the number of disjuncts.  Restarts are kept
        either way, and the first epoch (the run up to the first restart)
        starts at the configured shape either way.

        Off: every restart returns to the restart shape ([init] below).

        On: a restart after an epoch in which the template grew (more
        disjuncts than at the epoch's start, or a larger [nq] where [nq] is
        live) returns to the restart shape exactly as off.  A restart after
        an epoch that ended at its own starting shape -- the growth never
        fired, or fired only on an inert [nq] -- advances a ladder position p
        (1 for the first epoch) and restarts at init.nd + r(p) - 1 disjuncts,
        where r is the ruler sequence 1, 2, 1, 3, 1, 2, 1, 4, ... (r(p) is one
        more than the number of trailing zero bits of p, the Luby schedule's
        repeated-doubling shape on a scale of +1).  Every other field of the
        restart shape is as off; a restart after growth leaves p where it is.
        So a larger disjunct count is entered only after a whole epoch of
        candidate rounds without growth at the previous shape, and every
        count c is revisited with period 2^c in epochs, the small shapes most
        often. *)
    non_ucore_affine_atoms : int; [@default 0]
    (** Affine atoms per disjunct in the arm the trace labels [non-ucore] -- the main synthesis,
        as against the unsat-core arms.  At 0, which is every shipped
        configuration, that arm is a disjunction of the qualifiers it is handed
        and nothing else: no term, no coefficient, no bound, so an array
        predicate's whole expressiveness rests on a vocabulary and the
        coefficient and constant labels that would widen the shape are never
        produced.  A positive value gives each disjunct that many affine atoms
        over the hypothesis space's terms and constants, with the same bounds
        the unsat-core arms use.  It exists to answer whether that arm should
        have affine atoms at all.  Measured: one atom per disjunct answers 18
        of 43 cell-route inputs against 23 at zero, one gained and six lost,
        so the arm stays without them. *)
    upper_bound_coeff : int option; [@default Some 1]
    upper_bound_const : int option; [@default Some 0]
    seeds : int list option; [@default None]
    bound_each_coeff : int option; [@default None]
    threshold_coeff : int option; [@default None]
    threshold_const : int option; [@default Some 3]
    add_mod2_quals : bool; [@default false]
    (* A ceiling on how far the template may be grown before the solution is
       reported to be outside the family (printed as MAYBE) instead of the
       search continuing.  [None], the default, is the behaviour this template
       always had: when the unsat core teaches the synthesizer nothing it
       responds by growing the template, and with nothing to reach it grows
       without bound -- 105 disjuncts over eleven qualifiers in 45 s on one
       input while four CEGIS iterations completed, 141 over 462 rounds on
       another.
       It is off by default deliberately.  A bound set too tight turns a slow
       [sat] into a [MAYBE], which is a lost answer, so which bound to choose
       is a measurement and not a default; what this field buys is that the
       measurement can be made, and that a caller who would rather have an
       answer of "not in this family" than a run that does not end can say so.
       The per-predicate bounds an input may state ([upb_nd], [upb_depth]) are
       respected independently of this and are narrower. *)
    sequence_cells : bool; [@default true]
        (** Whether a sequence parameter gets cells as an array does.  Set by
            the solution template from its own setting of the same name,
            which also decides the example expansion's path list; a value
            written in this file is overwritten, since a template and an
            expansion that disagree on the paths build ill-sorted queries. *)
    sequence_sentinel_cell : bool; [@default true]
        (** Whether a sequence's cells include the sentinel at index -1, so
            that a candidate's instance there is a statement about the other
            arguments that holds on the empty sequence too.  Here it decides
            one thing: under [cell_quals_only], a qualifier that mentions a
            sequence ONLY through its length ([i < seq.len s]) is kept, since
            that is the scalar fact the sentinel instance exists to state.  Set
            by the solution template, like [sequence_cells]. *)
    cell_cut_keeps_seq_store_quals : bool; [@default false]
        (** Under [cell_quals_only], keep a qualifier [x = seq.store s i v]
            between two sequence parameters although it mentions no cell
            column.  It relates two whole sequences by one write, which no cell
            qualifier can state (a cell is one position of one sequence), so
            the cut would otherwise remove every such qualifier from a
            predicate that has cells.  Only such equalities are kept, and only
            where some path is a sequence. *)
    cell_cut_keeps_seq_equalities : bool; [@default true]
        (** Under [cell_quals_only], keep every equality between two
            sequence-sorted terms that reads no position ([x = y],
            [x = seq.extract y i n], [x = seq.store y i v]), where some path is
            a sequence.  The cut removes every qualifier that names no cell
            column, and with sequences as paths that includes the relations
            between whole sequences: a predicate with no cells keeps them, the
            same predicate with its sequences celled loses them, and no cell
            qualifier can say [x = seq.extract y i n] instead -- so turning
            sequence cells on could remove the one fact the plain template
            would have used.  This field subsumes
            [cell_cut_keeps_seq_store_quals]. *)
    upper_bound_disj : int option; [@default None]
    upper_bound_depth : int option; [@default None]
    guarded_partial_selector_quals : bool; [@default true]
        (** Add qualifiers comparing the integer payload of a constructor of a
            multi-constructor datatype, each conjoined with that constructor's
            tester ([HypSpace.qualifiers_of], [QualDT.guarded_payload_quals]).
            Without them a predicate over, say, a [Result] can distinguish its
            argument by constructor only, and two values of one constructor
            with different payloads are the same row of the truth table
            whatever the template's shape. On by default; it enlarges the
            vocabulary of every predicate that reaches such a datatype. *)
    guarded_partial_selector_offsets : bool; [@default true]
        (** With [guarded_partial_selector_quals], also compare the payload
            with each comparand plus or minus [1 .. threshold_const] (1 when
            [threshold_const] is unset), so that payloads differing by a small
            amount from a term of the predicate can be told apart without a
            constant between them.  A separate switch because it multiplies
            those qualifiers by [2 * threshold_const + 1]. *)
    selector_path_quals : bool; [@default true]
        (** Add qualifiers over the integer fields reached through selectors
            of single-constructor datatypes ([QualDT.selector_path_quals]):
            one field compared across two parameters of one sort ([<=], [>=],
            [=]), and every such field compared with the predicate's constants
            and with every integer literal of the problem.  Without them a
            predicate over the value a loop started from and the value it has
            now cannot say that a field is unchanged, and a bound set far from
            the loop is not a constant of the loop predicate at all.  Off by
            default: it enlarges the vocabulary of every predicate over a
            struct. *)
    curried_leaf_reads : bool; [@default false]
        (** Read a curried array argument [x : S1 -> ... -> Sk -> L] ([k >= 2],
            [L] Boolean or integer) to its leaf in one step of the qualifier
            term map: every [x[t1]...[tk]] with each [ti] one of the
            predicate's terms of sort [Si], filed as a Boolean qualifier or an
            integer term, and none of the intermediate arrays.  The term map
            otherwise adds one index level per step, so at depth 1 such an
            argument (a Rust iterator's [produces] relation, for instance) has
            no read of its value in the hypothesis space.  It also stops giving
            a sort-variable or arrow index sort its default instance, which is
            a variable no parameter binds and whose every qualifier the
            template drops.  Off by default: it enlarges the vocabulary of
            every predicate with a curried array argument. *)
    curried_leaf_reads_limit : int; [@default 1000]
        (** With [curried_leaf_reads], the largest number of leaf reads added
            for one array sort (array terms times the product of the
            index-term sets); above it that sort gets none. *)
    seq_length_sum_quals : int; [@default 0]
        (** Relate a sequence parameter's length to an integer parameter and
            an integer term: the qualifiers [len s + x = t] for [s] a
            sequence-sorted parameter, [x] zero or an integer parameter, and
            [t] an integer parameter other than [x] or one of the integer
            terms the parameters reach through the selectors of
            single-constructor datatypes (the terms
            [cell_guard_reachable_bounds] takes, in the same order).  At most
            this many qualifiers are added, taken in that order (sequences,
            then [x] with the parameters before zero, then [t] with the
            parameters before the reached terms); 0, the default, adds none.
            This is the vocabulary of a loop that consumes a sequence while a
            counter moves: [len rest + n = t.1] over a tuple [t] carrying the
            total, which the hypothesis space does not otherwise contain --
            the integer part of the term map offers no qualifier of its own,
            the template without an unsat core has no affine atoms, the
            unsat-core template's affine atoms bound the sum of the absolute
            coefficients by [upper_bound_coeff] (a three-term equation needs
            three), and
            [selector_path_quals] compares a field with one other term at a
            time.  Qualifiers only enlarge the hypothesis space, so this
            cannot bear on the soundness of a verdict. *)
    related_position_quals : bool; [@default false]
        (** Offer the qualifiers the hypothesis space generates over
            combinations of reached terms (equalities and testers over
            datatype, sequence, array and opaque-sort terms, the guarded
            payload and selector-path comparisons, the sequence suffix
            equations) only over sets of parameter positions the problem's
            clauses relate, as [RelatedPositions] defines it: a qualifier
            mentioning parameters [S] is kept when [|S| <= 1] or [S] is
            connected under the related pairs.  The extracted qualifiers and
            the integer part of the template are untouched.  Only narrows the
            hypothesis space, so it bears on which solutions are expressible
            and never on the soundness of a verdict. *)
    related_position_quals_whole_clause : bool; [@default false]
        (** With [related_position_quals], also relate every two variables of
            one clause's pure part (rule (d) of [RelatedPositions]), which
            keeps the relations a pure part states only jointly, through two
            atoms. *)
    opaque_clause_shapes_only : bool; [@default false]
        (** Offer the pairwise equalities over a reached term of an opaque
            sort (the hypothesis space's catch-all case: an uninterpreted
            sort, which a type parameter of the source program becomes) only
            between terms that are parameters or whose shape -- variables
            abstracted, selectors of single-constructor datatypes erased --
            is the shape of some term of that sort the problem's clauses
            write ([OpaqueShapes]).  The term map reads every sequence at
            every integer term in scope, lengths included, and those reads,
            which no clause writes and which are mostly out of range, carry
            most of the pairwise equalities; the reads at the shapes the
            clauses use, a parameter-indexed read [s[i]] or [s[i][j]] and the
            fields of the parameters, are kept.  Only narrows the hypothesis
            space, so it bears on which solutions are expressible and never on
            the soundness of a verdict. *)
    max_quals_per_predicate : int option; [@default None]
        (** At most this many qualifiers in one template of a predicate,
            counted over everything its holes may choose from (the ordinary
            qualifiers, the cell families and the lifted cell qualifiers,
            after [cell_quals_only]'s cut); every hole of the template shares
            that one list.  Above it the smallest qualifiers by [ast_size]
            are kept, ties in the set's own order.  [None], the default,
            keeps them all.  The term map multiplies: a sequence of sequences
            read at every integer term and every suffix gives a hundred
            element terms, and the pairwise equalities over them alone are
            4950 qualifiers, which is where one predicate reached 10,411 and
            a synthesis query exhausted memory.  Fewer qualifiers only narrow
            the hypothesis space, so this cannot bear on the soundness of a
            verdict: a candidate is still validated against the clauses, and
            a synthesis failure is never read as a refutation. *)
    defined_body_quals : int; [@default 0]
        (** Instantiate each non-recursive Bool-valued definition of the
            input ([define-fun]) at the terms the predicate's own parameters
            reach, and add the quantifier-free atoms of the instantiated body
            as qualifiers: at most this many per predicate, 0 (the default)
            adding none ([defined_body_quals] below states the enumeration).
            A contract predicate an input defines -- an iterator's [produces]
            relating a start state, a produced sequence and an end state --
            is inlined by the reader, and where the clauses apply it only at
            variables a binder introduces, qualifier extraction drops every
            atom of it, since none is over the unknown's parameters; this
            puts those atoms back at the unknown's arguments.  Qualifiers only
            enlarge the hypothesis space, so this cannot bear on the
            soundness of a verdict. *)
    loop_rate_terms : int; [@default 8]
    (* With [n > 0] (8 by default), add to the terms the template's affine
       atoms range over at most [n] linear combinations [a * xk + b * xl] of
       two integer parameters that the predicate's self-loop clauses never
       decrease ([loop_rate_terms] below), keeping only those with a
       coefficient of absolute value two or more.  Why: an affine atom's
       coefficients are bounded by the sum of their absolute values, which
       starts at one and grows by one per failure while a restart puts it
       back, so a loop whose counter [i] advances by one while [v] advances by
       at most three, and whose invariant is therefore [v <= x + 3 * i], needs
       a sum of five and the bound never got there; raising the bound for
       every predicate makes every template larger.  As a term, [3 * i - v] is
       one coefficient of one, and only predicates with such a loop get it.
       Over 315 inputs terms appeared in 10, and the questions cost at most a
       quarter of a second per predicate.  [0]: off.  Only enlarges the
       hypothesis space, so it cannot bear on the soundness of a verdict. *)
    rec_fun_app_quals : int; [@default 0]
        (** Apply each recursive definition of the input
            ([define-fun-rec], kept unexpanded in the function environment)
            at the terms the predicate's parameters reach, and add the
            atoms [x = f(t1, ..., tn)] for an integer- or real-valued [f]
            and [x] a parameter of [f]'s result sort not occurring in the
            [ti], and [f(t1, ..., tn)] itself for a Bool-valued one: at most
            this many per predicate, 0 (the default) adding none
            ([rec_fun_app_quals] below states the enumeration).  A loop that
            accumulates what a recursive function computes keeps
            [c = cnt s i] at its head, while the clauses apply [cnt] only at
            the loop's bound, so neither extraction nor any arithmetic family
            puts [cnt] at the loop counter.  Qualifiers only enlarge the
            hypothesis space -- a candidate built from them is validated
            against the clauses like any other, and the synthesis phase
            failing to fit is never read as a refutation -- so this cannot
            bear on the soundness of a verdict. *)
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg = Ok cfg

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "PredicateArray"
    let instantiate = instantiate_ext_files
  end)
end

module type ArgType = sig
  val name : Ident.tvar
  val sorts : Sort.t list
  val fenv : LogicOld.FunEnv.t
  val sol_space : SolSpace.t
  val id : int option

  (* every integer literal of the problem, for [selector_path_quals] *)
  val problem_int_consts : LogicOld.Term.t list Lazy.t

  (* the problem's constraints, for [cell_store_index_quals] *)
  val problem_formulas : LogicOld.Formula.t list Lazy.t

  (* the candidate atoms the input declares for this predicate, over
     [x1 ... xn] in parameter order, for [declared_atoms_after_failures] *)
  val declared_atoms : LogicOld.Formula.t list Lazy.t

  (* the problem's clauses, for [loop_rate_terms] *)
  val problem_clauses : ClauseOld.t list Lazy.t
end

type parameter = {
  nd : int;
  nq : int;
  ubc : Z.t option;
  ubd : Z.t option;
  s : Z.t Set.Poly.t;
}

type parameter_update_type += DisjQPA | Coeff | Const | Qual

(* [parameter_update_type] is extensible and each template module adds its
   own constructors, so a consumer holding a label cannot match it against
   this module's [Coeff] without depending on this module.  Printing the
   label is the only comparison such a consumer has, which is why this is
   here and not a debugging aid. *)
let str_of_param_update_type = function
  | DisjQPA -> "DisjQPA"
  | Coeff -> "Coeff"
  | Const -> "Const"
  | Qual -> "Qual"
  | TimeOut -> "TimeOut"
  | QualDep -> "QualDep"
  | Shape -> "Shape"
  | _ -> "Unknown"

type state =
  int * int * int option * int option * bool * bool * bool * bool * bool
[@@deriving to_yojson]

let state_of param labels : state =
  ( param.nd,
    param.nq,
    (* [Z.to_int] is safe: [ubc] and [ubd] are the template's configured
       coefficient and constant bounds, grown by small steps, never a model
       integer *)
    Option.map ~f:Z.to_int param.ubc,
    Option.map ~f:Z.to_int param.ubd,
    Set.mem labels DisjQPA,
    (* ToDo: this is always true *)
    Set.mem labels Coeff,
    Set.mem labels Const,
    Set.mem labels Qual (* ToDo: this is always true *),
    Set.mem labels TimeOut )

(* The comparisons a guard disjunct for the cell index column [idx] may
   select from: [idx >= v] and [idx <= v] for [v] zero or one of the
   predicate's own integer parameters [int_params].  A hole selects each
   qualifier positively, negatively or not at all, so these state [idx < v],
   [idx <= v], [idx > v] and [idx >= v] -- both ends of a bounded range --
   and nothing about any other column. *)
let cell_guard_quals ?(bound_terms = []) ~int_params idx =
  let values =
    (T_int.zero ()
    :: List.filter_map int_params ~f:(fun (x, s) ->
           if Term.is_int_sort s then Some (Term.mk_var x s) else None))
    @ bound_terms
  in
  List.dedup_and_sort ~compare:Stdlib.compare
  @@ List.concat_map values ~f:(fun v -> [ Formula.geq idx v; Formula.leq idx v ])

(* At most [limit] integer terms reached from [params] through the selectors
   of single-constructor datatypes, the parameters themselves excluded (the
   guard already compares with those): every term at depth one first, then
   depth two, then three, each depth in printed order, so the choice is fixed
   by the predicate's signature.  [limit <= 0] gives none. *)
let reachable_int_bounds ~limit (params : sort_env_list) =
  if limit <= 0 then []
  else
    let args = List.map params ~f:(fun (x, s) -> (Term.mk_var x s, s)) in
    let key t = Term.str_of t in
    let seen = Hash_set.create (module String) in
    List.iter params ~f:(fun (x, s) -> Hash_set.add seen (key (Term.mk_var x s)));
    let by_depth =
      List.concat_map (List.range 1 4) ~f:(fun d ->
          List.filter (CellQual.terms_of_sort ~depth:d T_int.SInt args)
            ~f:(fun t ->
              if Hash_set.mem seen (key t) then false
              else (
                Hash_set.add seen (key t);
                true)))
    in
    List.take by_depth limit

(* The qualifiers [len s + x = t] (written [len s = t] when [x] is zero), at
   most [limit] of them, for [s] a sequence-sorted parameter of [params], [x]
   one of [params]' integer parameters or zero, and [t] an integer parameter
   other than [x] or one of the first [limit] integer terms the parameters
   reach through single-constructor selectors ([reachable_int_bounds]).  The
   order is fixed by the signature: sequences in parameter order, then [x]
   with the parameters before zero, then [t] with the parameters before the
   reached terms, so that a cap keeps the equations over a counter first.
   [limit <= 0], or no sequence parameter, gives none.  A sequence reached
   only through a selector is not taken: the family is sized by the
   parameters.  Only enlarges the hypothesis space. *)
let seq_length_sum_quals ~limit (params : sort_env_list) =
  if limit <= 0 then []
  else
    let lens =
      List.filter_map params ~f:(fun (x, s) ->
          match s with
          | T_seq.SSeq se -> Some (T_seq.mk_len se (Term.mk_var x s))
          | _ -> None)
    in
    if List.is_empty lens then []
    else
      let int_params =
        List.filter_map params ~f:(fun (x, s) ->
            if Term.is_int_sort s then Some (Term.mk_var x s) else None)
      in
      let targets = int_params @ reachable_int_bounds ~limit params in
      let shifts = int_params @ [ T_int.zero () ] in
      let seen = Hash_set.create (module String) in
      let quals =
        List.concat_map lens ~f:(fun len ->
            List.concat_map shifts ~f:(fun x ->
                List.filter_map targets ~f:(fun t ->
                    if String.equal (Term.str_of t) (Term.str_of x) then None
                    else
                      let lhs =
                        if T_int.is_zero x then len else T_int.mk_add len x
                      in
                      let q = Formula.eq lhs t in
                      let key = Formula.str_of q in
                      if Hash_set.mem seen key then None
                      else (
                        Hash_set.add seen key;
                        Some q))))
      in
      List.take quals limit

(* At most [limit] of [quals]: all of them when there are no more, and
   otherwise the [limit] smallest by [Formula.ast_size], ties broken by the
   set's own order, so that the result is a function of the set and not of how
   it was built.  A subset of the input, of exactly [min limit (length quals)]
   elements; [limit <= 0] gives the empty set. *)
let cap_qualifiers ~limit (quals : Formula.t Set.Poly.t) =
  if Set.length quals <= limit then quals
  else
    Set.Poly.of_list
    @@ List.take
         (List.stable_sort (Set.to_list quals) ~compare:(fun a b ->
              Int.compare (Formula.ast_size a) (Formula.ast_size b)))
         (max 0 limit)
(* The atoms of the non-recursive Bool-valued definitions [defs] instantiated
   at the terms [params] reach, at most [limit] of them, each normalised as
   the other qualifiers are.  A definition's formal of sort [s] is filled by
   the terms of sort [s] reachable from [params] through at most two
   single-constructor selectors, the parameters included (in printed order,
   [CellQual.terms_of_sort]); a definition with a formal no such term fills
   is skipped.  Definitions with fewer scalar (Int, Real, Bool) formals come
   first, ties by name, and a definition's argument tuples are taken in
   lexicographic order, at most [limit] of them -- so a definition over the
   structured values an unknown carries, which ties those values together as
   the arithmetic enumeration does not, is not crowded out by one over
   scalars that mostly restates it, and the enumeration is bounded by
   [limit] squared tuples per definition.  An atom is kept when every
   variable in it is a parameter: an atom under a binder of the body
   mentions the bound variable and is dropped, as quantified qualifiers are
   elsewhere.  Literal [true]/[false], duplicates, and an equality with a
   constructor application of a single-constructor datatype (a conjunction of
   field equalities) are dropped.  Only enlarges the hypothesis space. *)
let defined_body_quals ~limit ~(defs : FunEnv.t) (params : sort_env_list) =
  if limit <= 0 || Map.Poly.is_empty defs then []
  else
    let args = List.map params ~f:(fun (x, s) -> (Term.mk_var x s, s)) in
    let pset = Set.Poly.of_list (List.map params ~f:fst) in
    let scalar s =
      Term.is_int_sort s || Term.is_real_sort s || Term.is_bool_sort s
    in
    let defs =
      Map.Poly.to_alist defs
      |> List.filter ~f:(fun (_, (fargs, sret, _, isrec, _)) ->
             (not isrec) && Term.is_bool_sort sret
             && not (List.is_empty fargs))
      |> List.stable_sort ~compare:(fun (_, (a, _, _, _, _)) (_, (b, _, _, _, _)) ->
             Int.compare
               (List.count a ~f:(snd >> scalar))
               (List.count b ~f:(snd >> scalar)))
    in
    (* the first [n] tuples of the product of [cands], lexicographically *)
    let rec tuples n = function
      | [] -> [ [] ]
      | c :: cs ->
          let rest = tuples n cs in
          List.take
            (List.concat_map c ~f:(fun t -> List.map rest ~f:(fun r -> t :: r)))
            n
    in
    let rec atoms acc phi =
      match phi with
      | Formula.Atom ((Atom.True _ | Atom.False _), _) -> acc
      | Formula.Atom (atm, _) -> Formula.mk_atom atm :: acc
      | Formula.UnaryOp (_, phi, _) -> atoms acc phi
      | Formula.BinaryOp (_, phi1, phi2, _) -> atoms (atoms acc phi1) phi2
      | Formula.Bind (_, _, phi, _) -> atoms acc phi
      | _ -> acc
    in
    (* [t = c(u1, ..., un)] for [c] the one constructor of [t]'s sort says
       [t.1 = u1 /\ ... /\ t.n = un], which the reached-term qualifiers state
       field by field; a matcher definition an input carries for every
       datatype would otherwise fill the cap with them *)
    let single_cons_eq q =
      Formula.is_eq q
      &&
      let t1, t2, _ = Formula.let_eq q in
      List.exists [ t1; t2 ] ~f:(fun t ->
          T_dt.is_cons t
          &&
          match Term.sort_of t with
          | T_dt.SDT dt -> List.length (Datatype.conses_of dt) = 1
          | _ -> false)
    in
    let seen = Hash_set.create (module String) in
    let quals =
      List.concat_map defs ~f:(fun (_, (fargs, _, body, _, _)) ->
          let cands =
            List.map fargs ~f:(fun (_, s) -> CellQual.terms_of_sort ~depth:2 s args)
          in
          if List.exists cands ~f:List.is_empty then []
          else
            let body = Formula.of_bool_term body in
            List.concat_map (tuples limit cands) ~f:(fun ts ->
                let sub =
                  Map.Poly.of_alist_exn (List.zip_exn (List.map fargs ~f:fst) ts)
                in
                atoms [] (Evaluator.simplify (Formula.subst sub body))
                |> List.rev
                |> List.filter_map ~f:(fun q ->
                       if not (Set.is_subset (Formula.tvs_of q) ~of_:pset) then
                         None
                       else
                         let q =
                           Evaluator.(simplify >> Normalizer.normalize >> simplify) q
                         in
                         if
                           Formula.is_true q || Formula.is_false q
                           || single_cons_eq q
                         then None
                         else
                           let key = Formula.str_of q in
                           if Hash_set.mem seen key then None
                           else (
                             Hash_set.add seen key;
                             Some q))))
    in
    List.take quals limit

(* The applications of the recursive definitions [fenv] (the [define-fun-rec]
   entries of the function environment, flagged recursive) at the terms
   [params] reach, at most [limit] of them, each normalised as the other
   qualifiers are.  A definition's formal of sort [s] is filled by the terms of
   sort [s] reachable from [params] through at most two single-constructor
   selectors, the parameters included ([CellQual.terms_of_sort]); a definition
   with a formal no such term fills, or with no formal, is skipped.
   Definitions are taken by name and a definition's argument tuples in
   lexicographic order, at most [limit] tuples per definition.  For a tuple
   [t1 ... tn], an integer- or real-valued [f] gives [x = f(t1, ..., tn)] for
   every parameter [x] of [f]'s result sort that occurs in no [ti] (the
   equation [i = f(s, i)] relates a value to itself through the function and
   is never the accumulator equation this family is for), and a Bool-valued
   [f] gives the atom [f(t1, ..., tn)].  Every variable of a result is a
   parameter; the defined function is not a variable, its definition fixing it
   in every model.  Literal [true]/[false] and duplicates are dropped.  Only
   enlarges the hypothesis space. *)
(* The integer combinations a predicate's self-loops never decrease.

   For each clause whose only head atom is [P(t')] and whose body holds one
   application [P(t)] of the same predicate, the per-iteration change
   [d_k = t'_k - t_k] of each integer position [k] is bounded from the
   clause's condition (the negation of its pure part; the other body atoms are
   dropped, which only widens the change) by asking [check] whether
   [cond /\ d_k > c] (resp. [d_k < c]) is satisfiable, for [c] found by
   bisection in [-bound, bound].  A question [check] does not answer [`Unsat]
   to counts as satisfiable, so a bound is only ever claimed where it was
   proved, and a position without a proved bound on both sides is left out.
   The intervals of several self-loops are joined.

   For two bounded positions [k], [l] whose changes lie in the box
   [lo_k, hi_k] x [lo_l, hi_l], a pair [(a, b)] with [a * d_k + b * d_l >= 0]
   at every corner of the box -- an extreme ray of the dual cone, found among
   the perpendiculars of the corners -- makes [a * x_k + b * x_l]
   non-decreasing along every iteration the clause allows, so an affine atom
   [a * x_k + b * x_l + rest >= c] can be inductive with the rest constant.
   Pairs normalised by their gcd; those with both coefficients in [-1, 1] are
   dropped, since the template reaches them with its smallest bound.

   Contract: [params] are the predicate's parameters in position order;
   [check] answers satisfiability of a conjunction; [deadline] is a wall-clock
   time in seconds after which no further question is asked.  The result is
   over [params], has at most [limit] terms, and depends on nothing but
   [clauses] and [check]'s answers. *)
let loop_rate_terms ~limit ~bound ~deadline ~(check : Formula.t list -> bool)
    ~(pvar : Ident.pvar) ~(params : sort_env_list) (clauses : ClauseOld.t list)
    =
  if limit <= 0 then []
  else
    let expired () = Float.(Common.Clock.now_s () > deadline) in
    let unsat phis = (not (expired ())) && not (check phis) in
    let args_of = function
      | Atom.App (Predicate.Var (p, _), ts, _) when Ident.pvar_equal p pvar ->
          Some ts
      | _ -> None
    in
    let loops =
      List.filter_map clauses ~f:(fun (_senv, ps, ns, phi) ->
          match (Set.to_list ps, List.filter_map (Set.to_list ns) ~f:args_of) with
          | [ head ], [ body ] -> (
              match args_of head with
              | Some head when List.length head = List.length params ->
                  Some (Formula.mk_neg phi, body, head)
              | _ -> None)
          | _ -> None)
    in
    let int_positions =
      List.filter_mapi params ~f:(fun k (_, s) ->
          if Term.is_int_sort s then Some k else None)
    in
    (* the largest c in [lo, hi] with [ok c], [ok] true on a prefix of the
       range; [None] when [ok lo] fails *)
    let rec last_ok ok lo hi =
      if lo > hi then None
      else
        let mid = lo + ((hi - lo + 1) / 2) in
        if ok mid then Option.first_some (last_ok ok (mid + 1) hi) (Some mid)
        else last_ok ok lo (mid - 1)
    in
    (* the least c in [lo, hi] with [ok c], [ok] true on a suffix of the
       range; [None] when [ok hi] fails *)
    let first_ok ok lo hi =
      Option.map (last_ok (fun c -> ok (-c)) (-hi) (-lo)) ~f:Int.neg
    in
    let interval_of (cond, body, head) k =
      let d =
        T_int.mk_sub (List.nth_exn head k) (List.nth_exn body k)
      in
      let below c = unsat [ cond; Formula.mk_atom (T_int.mk_lt d (T_int.from_int c)) ] in
      let above c = unsat [ cond; Formula.mk_atom (T_int.mk_gt d (T_int.from_int c)) ] in
      (* lo: the largest c with no d < c; hi: the least c with no d > c *)
      match last_ok below (-bound) bound with
      | None -> None
      | Some lo ->
          Option.map (first_ok above (-bound) bound) ~f:(fun hi -> (lo, hi))
    in
    let join a b =
      match (a, b) with
      | Some (l1, h1), Some (l2, h2) -> Some (min l1 l2, max h1 h2)
      | _ -> None
    in
    let intervals =
      if List.is_empty loops then []
      else
        List.filter_map int_positions ~f:(fun k ->
            match List.map loops ~f:(fun l -> interval_of l k) with
            | [] -> None
            | i :: is -> Option.map (List.fold is ~init:i ~f:join) ~f:(fun i -> (k, i)))
    in
    let rays (lk, hk) (ll, hl) =
      let corners = [ (lk, ll); (lk, hl); (hk, ll); (hk, hl) ] in
      List.concat_map corners ~f:(fun (p, q) ->
          if p = 0 && q = 0 then [] else [ (q, -p); (-q, p) ])
      |> List.filter ~f:(fun (a, b) ->
             List.for_all corners ~f:(fun (p, q) -> (a * p) + (b * q) >= 0))
      |> List.map ~f:(fun (a, b) ->
             let g = Int.max 1 (Z.to_int (Z.gcd (Z.of_int a) (Z.of_int b))) in
             (a / g, b / g))
      |> List.filter ~f:(fun (a, b) -> abs a >= 2 || abs b >= 2)
      |> List.dedup_and_sort ~compare:(Tuple2.compare ~cmp1:Int.compare ~cmp2:Int.compare)
    in
    let var k = Term.mk_var (fst (List.nth_exn params k)) T_int.SInt in
    let rec pairs = function
      | [] -> []
      | x :: xs -> List.map xs ~f:(fun y -> (x, y)) @ pairs xs
    in
    List.concat_map (pairs intervals) ~f:(fun ((k, ik), (l, il)) ->
        List.map (rays ik il) ~f:(fun (a, b) ->
            T_int.mk_add
              (T_int.mk_mul (T_int.from_int a) (var k))
              (T_int.mk_mul (T_int.from_int b) (var l))))
    |> Fn.flip List.take limit

(* [bool_equalities]: for a Bool-valued [f], also [x = f(t1, ..., tn)] for
   every Boolean parameter [x] not among the [ti] -- the shape of a predicate
   that records a Boolean function's result in its last argument. *)
let rec_fun_app_quals ?(bool_equalities = false) ~limit ~(fenv : FunEnv.t)
    (params : sort_env_list) =
  if limit <= 0 || Map.Poly.is_empty fenv then []
  else
    let args = List.map params ~f:(fun (x, s) -> (Term.mk_var x s, s)) in
    let defs =
      Map.Poly.to_alist fenv
      |> List.filter ~f:(fun (_, (fargs, sret, _, isrec, _)) ->
             isrec
             && (not (List.is_empty fargs))
             && (Term.is_int_sort sret || Term.is_real_sort sret
                || Term.is_bool_sort sret))
      |> List.sort ~compare:(fun (a, _) (b, _) ->
             String.compare (Ident.name_of_tvar a) (Ident.name_of_tvar b))
    in
    (* the first [n] tuples of the product of [cands], lexicographically *)
    let rec tuples n = function
      | [] -> [ [] ]
      | c :: cs ->
          let rest = tuples n cs in
          List.take
            (List.concat_map c ~f:(fun t -> List.map rest ~f:(fun r -> t :: r)))
            n
    in
    let seen = Hash_set.create (module String) in
    let keep q =
      let q = Evaluator.(simplify >> Normalizer.normalize >> simplify) q in
      if Formula.is_true q || Formula.is_false q then None
      else
        let key = Formula.str_of q in
        if Hash_set.mem seen key then None
        else (
          Hash_set.add seen key;
          Some q)
    in
    let quals =
      List.concat_map defs ~f:(fun (name, (fargs, sret, _, _, _)) ->
          let sargs = List.map fargs ~f:snd in
          let cands =
            List.map sargs ~f:(fun s -> CellQual.terms_of_sort ~depth:2 s args)
          in
          if List.exists cands ~f:List.is_empty then []
          else
            List.concat_map (tuples limit cands) ~f:(fun ts ->
                let app = Term.mk_fvar_app name sargs sret ts in
                if Term.is_bool_sort sret then
                  let used =
                    Set.Poly.union_list (List.map ts ~f:Term.tvs_of)
                  in
                  Option.to_list (keep (Formula.of_bool_term app))
                  @
                  if not bool_equalities then []
                  else
                    List.filter_map params ~f:(fun (x, s) ->
                        if Term.is_bool_sort s && not (Set.mem used x) then
                          keep (Formula.eq (Term.mk_var x s) app)
                        else None)
                else
                  let used = Set.Poly.union_list (List.map ts ~f:Term.tvs_of) in
                  List.filter_map params ~f:(fun (x, s) ->
                      if
                        String.equal (Term.str_of_sort s) (Term.str_of_sort sret)
                        && not (Set.mem used x)
                      then keep (Formula.eq (Term.mk_var x s) app)
                      else None)))
    in
    List.take quals limit

(* The qualifiers relating a cell's value to its index: [v = j + t] and
   [v = t] for every [t] of [values], for each cell of a path with a single
   integer index and an integer value.  A path of another shape contributes
   nothing: a curried array's cell has several indices and no one shift, and a
   value of another sort has no arithmetic. *)
let cell_affine_value_quals ~values
    (celled_paths :
      (CellQual.array_path * ('a * (Term.t list * Term.t) list)) list) =
  List.dedup_and_sort ~compare:Stdlib.compare
  @@ List.concat_map celled_paths ~f:(fun (path, (_, cells)) ->
         match path.CellQual.index_sorts with
         | [ isort ]
           when Term.is_int_sort isort && Term.is_int_sort path.CellQual.elem_sort
           ->
             List.concat_map cells ~f:(fun (idxs, value) ->
                 match idxs with
                 | [ idx ] ->
                     List.concat_map values ~f:(fun t ->
                         let shifted =
                           if T_int.is_zero t then idx else T_int.mk_add idx t
                         in
                         [ Formula.eq value shifted; Formula.eq value t ])
                 | _ -> [])
         | _ -> [])

(* The positions of [params] that hold a universal relation; the definition
   and its contract are at [CellQual.universal_array_positions], shared with
   the resolver's loop-depth bound. *)
let universal_array_positions = CellQual.universal_array_positions

(* The index terms of the array writes in [phis], each with the write's array
   sort, rewritten over [params]: for every [store A t v] with an integer index
   in a formula that applies [pvar] to [args] (as many as [params]), [t] with
   every variable argument of [args] renamed to the parameter at its position,
   kept when every variable of [t] is so renamed.  Only a variable argument is
   renamed, the first position winning when one variable is passed twice, so
   the result is a term over [params] that equals [t] in the clause wherever
   the application holds.  Distinct terms, first occurrence first, at most
   [limit] of them. *)
let store_index_terms ~limit ~pvar ~(params : sort_env_list)
    (phis : Formula.t list) : (Sort.t * Term.t) list =
  if limit <= 0 then []
  else
    let found =
      List.concat_map phis ~f:(fun phi ->
          let phi = Formula.elim_let phi in
          let pos, neg = Formula.atoms_of phi in
          let apps =
            List.filter_map (Set.to_list (Set.union pos neg)) ~f:(function
              | Atom.App (Predicate.Var (pv, _), args, _)
                when Ident.pvar_equal pv pvar
                     && List.length args = List.length params ->
                  Some args
              | _ -> None)
          in
          if List.is_empty apps then []
          else
            List.concat_map
              (Set.to_list @@ Formula.filtered_terms_of ~f:T_array.is_store phi)
              ~f:(function
                | Term.FunApp (T_array.AStore (si, se), [ _; idx; _ ], _)
                  when Term.is_int_sort si ->
                    List.filter_map apps ~f:(fun args ->
                        let sub =
                          List.fold2_exn args params ~init:Map.Poly.empty
                            ~f:(fun sub arg (x, s) ->
                              match arg with
                              | Term.Var (y, _, _) when not (Map.Poly.mem sub y)
                                ->
                                  Map.Poly.set sub ~key:y ~data:(Term.mk_var x s)
                              | _ -> sub)
                        in
                        if Set.for_all (Term.tvs_of idx) ~f:(Map.Poly.mem sub)
                        then
                          Some
                            ( T_array.mk_array_sort si se,
                              Evaluator.simplify_term (Term.subst sub idx) )
                        else None)
                | _ -> []))
    in
    let seen = Hash_set.create (module String) in
    List.take
      (List.filter found ~f:(fun (s, t) ->
           let k = Term.str_of_sort s ^ "|" ^ Term.str_of t in
           if Hash_set.mem seen k then false
           else (
             Hash_set.add seen k;
             true)))
      limit

(* The values the write indices [writes] take at a predicate's starting
   state, for [cell_store_index_anchor_quals].  A fact clause of [pvar] is a
   formula of [phis] that applies [pvar] positively and applies no predicate
   variable negatively.  From each positive application [pvar(args)] of such
   a clause, an integer parameter [x] at position [k] gets the starting value
   [n] when [args_k] is a ground integer term [n], or a variable [y] for which
   the clause has an equality atom [y = n] or [n = y] in a negative position
   (a premise), [n] ground; the first such atom wins.  For every write
   [(sort, t)] of [writes] (a term over [params], as [store_index_terms] gives
   it) that mentions a parameter with a starting value, the anchor is [t] with
   every such parameter replaced by its value, its constants folded.  It is the other
   end of the region a counter-driven loop has written so far: a write
   [t(i)] with slope one in the counter [i] has swept [t(i) + 1 .. t(i0)] by
   round [i] when [i] starts at [i0], and [t(i0)] is a constant of the loop
   that no atom of any clause states.  Anchors equal (by sort and printed
   term) to a write or to an earlier anchor are dropped; fact clauses in the
   order of [phis], writes in their order; at most [limit] anchors.  A
   predicate without such a fact clause, or whose writes mention no
   parameter with a starting value, gets none.  Read off the clauses only,
   so it changes the hypothesis space and nothing else. *)
let store_index_anchor_terms ~limit ~pvar ~(params : sort_env_list)
    (phis : Formula.t list) (writes : (Sort.t * Term.t) list) :
    (Sort.t * Term.t) list =
  if limit <= 0 || List.is_empty writes then []
  else
    let is_ground_int t = Term.is_int_sort (Term.sort_of t) && Set.is_empty (Term.tvs_of t) in
    let inits_of phi =
      let phi = Formula.elim_let phi in
      let pos, neg = Formula.atoms_of phi in
      if Set.exists neg ~f:Atom.is_pvar_app then []
      else
        let eqs =
          List.filter_map (Set.to_list neg) ~f:(function
            | Atom.App (Predicate.Psym T_bool.Eq, [ Term.Var (y, _, _); n ], _)
              when is_ground_int n ->
                Some (y, n)
            | Atom.App (Predicate.Psym T_bool.Eq, [ n; Term.Var (y, _, _) ], _)
              when is_ground_int n ->
                Some (y, n)
            | _ -> None)
        in
        List.filter_map (Set.to_list pos) ~f:(function
          | Atom.App (Predicate.Var (pv, _), args, _)
            when Ident.pvar_equal pv pvar
                 && List.length args = List.length params ->
              Some
                (List.fold2_exn args params ~init:Map.Poly.empty
                   ~f:(fun sub arg (x, s) ->
                     if not (Term.is_int_sort s) then sub
                     else
                       let v =
                         if is_ground_int arg then Some arg
                         else
                           match arg with
                           | Term.Var (y, _, _) ->
                               List.Assoc.find eqs ~equal:Ident.tvar_equal y
                           | _ -> None
                       in
                       match v with
                       | Some v -> Map.Poly.set sub ~key:x ~data:v
                       | None -> sub))
          | _ -> None)
    in
    (* the simplifier alone leaves [3s - 2 - 1] unfolded; the polynomial
       normal form folds the constants, and a term it does not cover (it
       raises on an operator outside its polynomial fragment) keeps the
       simplifier's form *)
    let fold t =
      let t = Evaluator.simplify_term t in
      try Evaluator.simplify_term (Normalizer.normalize_term t)
      with exn when not (Common.Timer.is_async exn) -> t
    in
    let found =
      List.concat_map phis ~f:(fun phi ->
          List.concat_map (inits_of phi) ~f:(fun sub ->
              List.filter_map writes ~f:(fun (s, t) ->
                  if Set.exists (Term.tvs_of t) ~f:(Map.Poly.mem sub) then
                    Some (s, fold (Term.subst sub t))
                  else None)))
    in
    let key (s, t) = Term.str_of_sort s ^ "|" ^ Term.str_of t in
    let seen = Hash_set.create (module String) in
    List.iter writes ~f:(fun (s, t) ->
        Hash_set.add seen (key (s, t));
        Hash_set.add seen (key (s, fold t)));
    List.take
      (List.filter found ~f:(fun a ->
           let k = key a in
           if Hash_set.mem seen k then false
           else (
             Hash_set.add seen k;
             true)))
      limit

(* [j <= t] and [j >= t] for every write [(sort, t)] of [writes] and every
   integer index column [j] of a cell of a path whose array has that sort and
   a single integer index. *)
let cell_store_index_quals ~writes
    (celled_paths :
      (CellQual.array_path * ('a * (Term.t list * Term.t) list)) list) =
  List.dedup_and_sort ~compare:Stdlib.compare
  @@ List.concat_map celled_paths ~f:(fun (path, (_, cells)) ->
         match path.CellQual.index_sorts with
         | [ isort ] when Term.is_int_sort isort ->
             let psort = Term.str_of_sort (CellQual.curried_sort path) in
             List.concat_map writes ~f:(fun (s, t) ->
                 if not (String.equal psort (Term.str_of_sort s)) then []
                 else
                   List.concat_map cells ~f:(fun (idxs, _) ->
                       match idxs with
                       | [ j ] -> [ Formula.leq j t; Formula.geq j t ]
                       | _ -> []))
         | _ -> [])

(* [j_1 = v_2 + p] for every ordered pair of distinct paths, every integer
   index column [j_1] of a cell of the first, every cell value [v_2] of the
   second when its array holds integers, and every [p] of [offsets] (a zero
   offset is written without the addition).  A path's cells are never related
   to its own. *)
let cell_cross_index_value_quals ~offsets
    (celled_paths :
      (CellQual.array_path * ('a * (Term.t list * Term.t) list)) list) =
  let indexed = List.mapi celled_paths ~f:(fun i c -> (i, c)) in
  List.dedup_and_sort ~compare:Stdlib.compare
  @@ List.concat_map indexed ~f:(fun (i, (p1, (_, cells1))) ->
         List.concat_map indexed ~f:(fun (j, (p2, (_, cells2))) ->
             if i = j || not (Term.is_int_sort p2.CellQual.elem_sort) then []
             else
               List.concat_map cells1 ~f:(fun (idxs1, _) ->
                   List.concat_map
                     (List.zip_exn idxs1 p1.CellQual.index_sorts)
                     ~f:(fun (idx1, s) ->
                       if not (Term.is_int_sort s) then []
                       else
                         List.concat_map cells2 ~f:(fun (_, val2) ->
                             List.map offsets ~f:(fun off ->
                                 Formula.eq idx1
                                   (if T_int.is_zero off then val2
                                    else T_int.mk_add val2 off)))))))

(* [j_1 = j_2] for every two distinct cells of one path and every level whose
   index sort is integer, the first cell's index on the left. *)
let cell_pair_index_equalities
    (celled_paths :
      (CellQual.array_path * ('a * (Term.t list * Term.t) list)) list) =
  List.dedup_and_sort ~compare:Stdlib.compare
  @@ List.concat_map celled_paths ~f:(fun (path, (_, cells)) ->
         let indexed = List.mapi cells ~f:(fun i c -> (i, c)) in
         List.concat_map indexed ~f:(fun (i, (idxs1, _)) ->
             List.concat_map indexed ~f:(fun (j, (idxs2, _)) ->
                 if i >= j then []
                 else
                   List.filter_map
                     (List.zip3_exn idxs1 idxs2 path.CellQual.index_sorts)
                     ~f:(fun (a, b, s) ->
                       if Term.is_int_sort s then Some (Formula.eq a b)
                       else None))))

(* The integer index columns of the cells, in the path-major order the cells
   were generated in.  A column of another sort (a quantified-sort index of a
   curried array) has no order, so a range guard cannot be written for it. *)
let int_cell_index_columns
    (celled_paths :
      (CellQual.array_path * ('a * (Term.t list * Term.t) list)) list) =
  List.concat_map celled_paths ~f:(fun (path, (_, cells)) ->
      List.concat_map cells ~f:(fun (idxs, _) ->
          List.filter_map (List.zip_exn idxs path.CellQual.index_sorts)
            ~f:(fun (c, s) -> if Term.is_int_sort s then Some c else None)))

(* [template] with two guard disjuncts per integer cell index column appended.
   Each guard is a qualifier hole over [gen_params] -- the list every other
   hole of the predicate is built over, since the truth table reads every
   qualifier against one list -- whose qualifiers are [cell_guard_quals] of
   its column together with the qualifiers of [quals] that mention no cell
   column at all.  The latter are there because a quantified invariant is
   [C /\ forall j. (j < low \/ j > high \/ phi)] with [C] a fact about the
   scalar arguments, and over one cell its disjunctive normal form conjoins
   [C] into every disjunct, the guards included: a guard that can state only
   the index bound cannot be a disjunct of such an invariant.  A guard never
   reads a value column.  With no integer index column the template is
   returned unchanged.  The disjunction only grows, so every candidate of the
   original template is still a candidate. *)
let with_cell_guard_disjuncts ?(bound_terms = []) ~print ~int_params
    ~gen_params ~quals celled_paths (template : Templ.templ_pred) =
  let cell_columns =
    Set.Poly.of_list
    @@ List.concat_map celled_paths ~f:(fun (_, (_, cells)) ->
           List.concat_map cells ~f:(fun (idxs, v) ->
               List.concat_map (v :: idxs) ~f:(fun t ->
                   Set.to_list (Term.tvs_of t))))
  in
  let scalar_quals =
    List.filter quals ~f:(fun q ->
        Set.is_empty (Set.inter (Formula.tvs_of q) cell_columns))
  in
  let bound_terms =
    List.filter bound_terms ~f:(fun t ->
        Term.is_int_sort (Term.sort_of t)
        && Set.is_empty (Set.inter (Term.tvs_of t) cell_columns))
  in
  List.fold (int_cell_index_columns celled_paths) ~init:template
    ~f:(fun (acc : Templ.templ_pred) idx ->
      let guard =
        Templ.gen_dnf ~print ~eq_atom:false ~br_bools:false ~only_bools:false
          {
            consts = [];
            terms = [];
            quals =
              List.dedup_and_sort ~compare:Stdlib.compare
                (cell_guard_quals ~bound_terms ~int_params idx @ scalar_quals);
            shp = [ 0; 0 ];
            ubc = None;
            ubd = None;
            s = Set.Poly.empty;
          }
          { bec = None } gen_params
      in
      {
        templ_params = Map.force_merge acc.templ_params guard.templ_params;
        hole_quals_map = acc.hole_quals_map @ guard.hole_quals_map;
        pred = Formula.or_of [ acc.pred; guard.pred ];
        coeffs_bounds = Formula.mk_and acc.coeffs_bounds guard.coeffs_bounds;
        consts_bounds = Formula.mk_and acc.consts_bounds guard.consts_bounds;
        quals_bounds = Formula.mk_and acc.quals_bounds guard.quals_bounds;
      })

(* Whether the cell-free space at shape [p] is contained in the one at shape
   [q]: no more disjuncts, no larger coefficient or constant bound ([None] is
   unbounded), a subset of the seeds, and, unless [nq] is read by nothing on
   this predicate's path ([ignore_nq]), no more quantifiers per array.
   Contract: reflexive and transitive; [true] only when every parameter of [p]
   is within [q]'s. *)
let shape_within ~ignore_nq (p : parameter) (q : parameter) =
  let bound_le a b =
    match (a, b) with
    | _, None -> true
    | None, Some _ -> false
    | Some a, Some b -> Z.leq a b
  in
  p.nd <= q.nd
  && (ignore_nq || p.nq <= q.nq)
  && bound_le p.ubc q.ubc && bound_le p.ubd q.ubd
  && Set.is_subset p.s ~of_:q.s

module Make (Cfg : Config.ConfigType) (Arg : ArgType) : Function.Type = struct
  let config = Cfg.config
  let id = Arg.id

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  let param =
    ref
      {
        nd = config.number_of_disj;
        nq = config.number_of_qpa;
        ubc = Option.map config.upper_bound_coeff ~f:Z.of_int;
        ubd = Option.map config.upper_bound_const ~f:Z.of_int;
        s =
          (match config.seeds with
          | None -> Set.Poly.singleton Z.zero
          | Some s -> Set.Poly.of_list @@ List.map s ~f:Z.of_int);
      }

  (* With [plain_template_first]: how many growth-asking failures the template
     has had, and whether it has been given its cells.  Per predicate, because
     each predicate has its own instance of this module; monotone, because the
     space must only grow. *)
  let plain_failures = ref 0

  (* [loop_rate_terms] over [x1 ... xn]: asked once per predicate, with each
     question bounded by 1 s and all of them by 5 s *)
  let loop_rate_terms_x =
    lazy
      (let check phis =
         match
           Z3Smt.Z3interface.check_sat ~id:Arg.id ~timeout:(Some 1000) Arg.fenv
             phis
         with
         | `Unsat -> false
         | _ -> true
       in
       loop_rate_terms ~limit:config.loop_rate_terms ~bound:16
         ~deadline:(Common.Clock.now_s () +. 5.)
         ~check ~pvar:(Ident.tvar_to_pvar Arg.name)
         ~params:(sort_env_list_of_sorts Arg.sorts)
         (Lazy.force Arg.problem_clauses))
  let cells_enabled = ref (not config.plain_template_first)

  (* [plain_template_first_sort_var_only] is decided once, at the first
     template: until then it is not known which arrays the predicate reaches *)
  let sort_var_scope_decided = ref false

  let decide_sort_var_scope (hspace : HypSpace.hspace) =
    if config.plain_template_first_sort_var_only && not !sort_var_scope_decided
    then (
      sort_var_scope_decided := true;
      let reaches_universal_array () =
        config.plain_template_first_universal_arrays
        && not
             (List.is_empty
                (universal_array_positions
                   ~pvar:(Ident.tvar_to_pvar Arg.name) ~params:hspace.params
                   (Lazy.force Arg.problem_formulas)))
      in
      let reaches_sort_var =
        reaches_universal_array ()
        || List.exists
          (CellQual.array_paths ~sequences:config.sequence_cells
             (List.map ~f:snd hspace.params))
          ~f:(fun path ->
            List.exists path.CellQual.index_sorts ~f:(function
              | Sort.SVar _ | T_dt.SUS _ -> true
              (* the enumeration the finite instantiation of a quantified
                 sort substitutes for the sort variable: the same contract
                 over the same sort, at a fixed size *)
              | s -> CellQual.is_finite_sort_instance s))
      in
      if reaches_sort_var && !cells_enabled && !plain_failures = 0 then (
        cells_enabled := false;
        Debug.print
        @@ lazy
             (sprintf
                "[%s] reaches an array over a sort variable or a universal relation: cells deferred"
                (Ident.name_of_tvar Arg.name))))

  let is_growth_label = function
    | DisjQPA | Shape | Coeff | Const -> true
    | _ -> false

  (* With [cell_guard_after_failures]: how many times the celled template
     without guards has been regenerated, and whether it has its guards.  Per
     predicate and monotone, like the two above. *)
  let guard_failures = ref 0
  let guards_generated_once = ref false
  let guards_enabled = ref (config.cell_guard_after_failures <= 0)

  (* Called once per regeneration, at the template without an unsat core,
     which the synthesizer builds before the unsat-core shapes, so that all
     templates of one regeneration agree on the guards. *)
  let note_regeneration () =
    if !cells_enabled && not !guards_enabled then (
      if !guards_generated_once then incr guard_failures;
      guards_generated_once := true;
      if !guard_failures >= config.cell_guard_after_failures then (
        guards_enabled := true;
        Debug.print
        @@ lazy
             (sprintf
                "[%s] cell guards enabled after %d regenerations without them"
                (Ident.name_of_tvar Arg.name)
                !guard_failures)))

  (* With [declared_atoms_after_failures]: growth-asking failures so far, and
     whether the declared atoms have joined the qualifiers.  Per predicate and
     monotone, like the counters above. *)
  let declared_failures = ref 0
  let declared_enabled = ref false

  (* Whether [nq] is read by nothing that shapes this predicate's template or
     bounds its search: not by the qualifier term map
     ([term_depth_follows_shape]), not by the constant bound
     ([const_bound_follows_depth]), and not by [in_space]'s depth bound (the
     configured [upper_bound_depth], or a depth bound the problem states for
     this predicate).  The reinforcement-learning state printout also shows
     [nq], but only as a report. *)
  let nq_inert =
    lazy
      ((not config.term_depth_follows_shape)
      && (not config.const_bound_follows_depth)
      && Option.is_none config.upper_bound_depth
      &&
      match Map.Poly.find Arg.sol_space Arg.name with
      | None -> true
      | Some space -> (
          match Map.Poly.find space SolSpace.Depth with
          | Some (Some _) -> false
          | _ -> true))

  (* With [plain_template_failures_new_shapes_only]: the shapes at which a
     failure was counted toward the cells.  Per predicate, kept across
     restarts like the counter itself. *)
  let counted_failure_shapes = ref []

  (* Whether a growth failure at the current shape counts toward the cells;
     records the shape when it does. *)
  let counts_toward_cells () =
    if not config.plain_template_failures_new_shapes_only then true
    else
      let ignore_nq = Lazy.force nq_inert in
      if
        List.exists !counted_failure_shapes
          ~f:(shape_within ~ignore_nq !param)
      then (
        Debug.print
        @@ lazy
             (sprintf
                "[%s] failure at a shape within one already counted: not counted toward the cells"
                (Ident.name_of_tvar Arg.name));
        false)
      else (
        counted_failure_shapes := !param :: !counted_failure_shapes;
        true)

  let note_failure labels =
    if
      config.declared_atoms_after_failures > 0
      && (not !declared_enabled)
      && Set.exists labels ~f:is_growth_label
    then (
      incr declared_failures;
      if !declared_failures >= config.declared_atoms_after_failures then (
        declared_enabled := true;
        Debug.print
        @@ lazy
             (sprintf "[%s] declared atoms join the qualifiers after %d failures"
                (Ident.name_of_tvar Arg.name)
                !declared_failures)));
    if
      (not !cells_enabled)
      && Set.exists labels ~f:is_growth_label
      && counts_toward_cells ()
    then (
      incr plain_failures;
      if !plain_failures >= config.plain_template_failures then (
        cells_enabled := true;
        Debug.print
        @@ lazy
             (sprintf "[%s] cells enabled after %d failures of the plain template"
                (Ident.name_of_tvar Arg.name)
                !plain_failures)))

  (* The shape a restart returns to; see [restart_to_configured_shape]. *)
  let init =
    if config.restart_to_configured_shape then
      {
        nd = config.number_of_disj;
        nq = config.number_of_qpa;
        ubc = Option.map config.upper_bound_coeff ~f:Z.of_int;
        ubd = Option.map config.upper_bound_const ~f:Z.of_int;
        s =
          (match config.seeds with
          | None -> Set.Poly.singleton Z.zero
          | Some s -> Set.Poly.of_list @@ List.map s ~f:Z.of_int);
      }
    else
      {
        nd = 1;
        nq = 1;
        ubc = Some Z.one;
        ubd = Some Z.zero;
        s = Set.Poly.singleton Z.zero;
      }

  let name_of () = Arg.name
  let kind_of () = Kind.str_of Kind.Ord
  let kind = Kind.Ord
  let flexible = false
  let sort_of () = Sort.mk_fun @@ Arg.sorts @ [ T_bool.SBool ]
  let params_of () = sort_env_list_of_sorts Arg.sorts

  let show_state ?(config = PCSatCommon.RLConfig.disabled) labels =
    ignore config;
    Debug.print_stdout
    @@ lazy
         (sprintf "state of %s: %s" (Ident.name_of_tvar (name_of ()))
         @@ Yojson.Safe.to_string @@ state_to_yojson @@ state_of !param labels);
    Out_channel.flush Out_channel.stdout

  let str_of () =
    sprintf
      ("number of disjuncts : %d\n" ^^ "number of quantifiers per array : %d\n"
     ^^ "upper bound of the sum of the abs of coefficients : %s\n"
     ^^ "upper bound of the sum of the abs of constant : %s\n" ^^ "seeds : %s")
      !param.nd !param.nq
      (match !param.ubc with None -> "N/A" | Some ubc -> Z.to_string ubc)
      (match !param.ubd with None -> "N/A" | Some ubd -> Z.to_string ubd)
      (String.concat_map_set ~sep:"," !param.s ~f:Z.to_string)

  (* Whether the template is still inside the solution space the PROBLEM
     states for this predicate ([upb_nd], [upb_depth] and the rest, which a
     front end or an input may set per predicate).  Answering [true]
     unconditionally, which this module did, makes the space unbounded whatever
     the input says: when the unsat core teaches the synthesizer nothing it
     responds by growing the template, and with no bound to reach it grows
     forever rather than reporting the solution to be outside the family.
     Measured on one input, 105 disjuncts over eleven qualifiers in 45 s while
     four CEGIS iterations completed, and on another 141 over 462 rounds.  The
     bound is still absent unless the input states one, so nothing changes for
     a problem that states none -- what changes is that a problem CAN state
     one and be believed. *)
  let within = function None -> fun _ -> true | Some c -> fun i -> i <= c

  let in_space () =
    SolSpace.in_space Arg.name SolSpace.ND !param.nd Arg.sol_space
    && SolSpace.in_space Arg.name SolSpace.Depth !param.nq Arg.sol_space
    && within config.upper_bound_disj !param.nd
    && within config.upper_bound_depth !param.nq

  (* REACHABLE ON THE DEFAULT PATH: [None] there, so nothing is filtered.  The
     test [related_position_quals] puts on the generated families, over
     [x1 ... xn], the parameters every hypothesis space of this template has;
     the relation is computed once per clause list for all templates. *)
  let keep_related =
    lazy
      (if not config.related_position_quals then None
       else
         let rel =
           RelatedPositions.compute_cached
             ~whole_clause:config.related_position_quals_whole_clause
             (Lazy.force Arg.problem_clauses)
         in
         let params = sort_env_list_of_sorts Arg.sorts in
         Some
           (RelatedPositions.keep_qual rel (Ident.tvar_to_pvar Arg.name)
              ~params))

  (* The initial qualifier set is what the search uses before it grows the
     template, and it is built from the CLAUSES plus an arithmetic domain -- so
     a relation that belongs to a theory rather than to arithmetic never enters
     it unless the input happens to mention the term.  That is measurable: a
     loop over a slice whose invariant is annotated answers, and the same
     program without the annotation does not, the difference being only that
     the annotation puts the term in a clause.

     For sequence-sorted parameters the relation such an invariant needs is the
     suffix: "what is left to process is the original from this index on".  It
     is added here, from the parameters alone, so that it is present from the
     first round rather than only once the hypothesis space has grown. *)
  let adjust_quals_terms (quals, terms) =
    let params = params_of () in
    let seq_params =
      List.filter_map params ~f:(fun (x, sort) ->
          match sort with
          | T_seq.SSeq se -> Some (Term.mk_var x sort, se)
          | _ -> None)
    in
    if List.is_empty seq_params then (quals, terms)
    else
      let int_params =
        List.filter_map params ~f:(fun (x, sort) ->
            if Term.is_int_sort sort then Some (Term.mk_var x sort) else None)
      in
      let suffixes =
        Set.Poly.of_list
        @@ List.concat_map seq_params ~f:(fun (t, se) ->
            List.map int_params ~f:(fun i ->
                T_seq.mk_extract se t i (T_int.mk_sub (T_seq.mk_len se t) i)))
      in
      let eqs =
        Set.Poly.of_list @@ Formula.eqs @@ Set.to_list @@ Set.union suffixes
        @@ Set.Poly.of_list (List.map seq_params ~f:fst)
      in
      (* [None] by default: the suffix equations are built over every pair of
         terms, so [related_position_quals] filters them as it filters the
         generated families *)
      let eqs =
        match Lazy.force keep_related with
        | None -> eqs
        | Some keep -> Set.filter eqs ~f:keep
      in
      (Set.union quals eqs, Set.union terms suffixes)

  (* REACHABLE ON THE DEFAULT PATH: [None] there, so every reached term of an
     opaque sort enters the pairwise equalities.  The clause shapes are
     computed once per clause list for all templates. *)
  let keep_opaque =
    lazy
      (if not config.opaque_clause_shapes_only then None
       else
         let shapes =
           Common.PhaseTime.with_phase "opaque-shapes" @@ fun () ->
           OpaqueShapes.of_clauses_cached (Lazy.force Arg.problem_clauses)
         in
         Some (OpaqueShapes.keep_term shapes))

  let update_hspace hspace =
    (* the positional argument here is the qualifier term map's depth -- not a
       count of quantifiers: the fixed [number_of_qpa] by default, the shape
       parameter the growth actions move under [term_depth_follows_shape] *)
    let hspace =
      Common.PhaseTime.with_phase "qualifiers-of" @@ fun () ->
      HypSpace.qualifiers_of ?keep_generated:(Lazy.force keep_related)
        ?keep_opaque_term:(Lazy.force keep_opaque)
        ~fenv:Arg.fenv ~add_mod2_quals:config.add_mod2_quals
        ~guarded_partial_selector_quals:config.guarded_partial_selector_quals
        ~guarded_partial_selector_offset:
          (if config.guarded_partial_selector_offsets then
             Option.value config.threshold_const ~default:1
           else 0)
        ~selector_path_quals:config.selector_path_quals
        ?curried_leaf_reads:
          (if config.curried_leaf_reads then
             Some config.curried_leaf_reads_limit
           else None)
        ~selector_path_consts:
          (if config.selector_path_quals then Lazy.force Arg.problem_int_consts
           else [])
        ~add_bv_quals:true
        (if config.term_depth_follows_shape then !param.nq
         else config.number_of_qpa)
        hspace
    in
    (* UNREACHABLE BY DEFAULT (seq_length_sum_quals).  Normalised as the
       qualifiers above are, so that one equation reached both ways is one
       column of the truth table. *)
    let hspace =
    if config.seq_length_sum_quals <= 0 then hspace
    else
      let extra =
        Set.Poly.of_list
        @@ List.map
             (seq_length_sum_quals ~limit:config.seq_length_sum_quals
                hspace.params)
             ~f:Evaluator.(simplify >> Normalizer.normalize >> simplify)
      in
      Debug.print
      @@ lazy
           (sprintf "[%s] sequence-length sum qualifiers (%d): %s"
              (Ident.name_of_tvar Arg.name)
              (Set.length extra)
              (String.concat_map_set ~sep:", " extra ~f:Formula.str_of));
      { hspace with quals = Set.union hspace.quals extra }
    in
    (* UNREACHABLE BY DEFAULT (loop_rate_terms).  Computed once, over
       [x1 ... xn], and renamed onto this template's parameters by position. *)
    let hspace =
      if config.loop_rate_terms <= 0 then hspace
      else
        let sub =
          Map.Poly.of_alist_exn
          @@ List.mapi hspace.params ~f:(fun i (x, s) ->
              (Ident.Tvar (sprintf "x%d" (i + 1)), Term.mk_var x s))
        in
        let extra =
          Set.Poly.of_list
          @@ List.map (Lazy.force loop_rate_terms_x) ~f:(Term.subst sub)
        in
        Debug.print
        @@ lazy
             (sprintf "[%s] loop rate terms (%d): %s"
                (Ident.name_of_tvar Arg.name)
                (Set.length extra)
                (String.concat_map_set ~sep:", " extra ~f:Term.str_of));
        { hspace with terms = Set.union hspace.terms extra }
    in
    (* UNREACHABLE BY DEFAULT (declared_atoms_after_failures).  The atoms are
       over [x1 ... xn]; they are renamed onto this template's parameters by
       position. *)
    let hspace =
      if not !declared_enabled then hspace
      else
        let sub =
          Map.Poly.of_alist_exn
          @@ List.mapi hspace.params ~f:(fun i (x, s) ->
              (Ident.Tvar (sprintf "x%d" (i + 1)), Term.mk_var x s))
        in
        let extra =
          Set.Poly.of_list
          @@ List.map (Lazy.force Arg.declared_atoms) ~f:(Formula.subst sub)
        in
        { hspace with quals = Set.union hspace.quals extra }
    in
    (* UNREACHABLE BY DEFAULT (defined_body_quals). *)
    let hspace =
    if config.defined_body_quals <= 0 then hspace
    else
      let extra =
        Set.Poly.of_list
        @@ defined_body_quals ~limit:config.defined_body_quals
             ~defs:(LogicOld.get_inlined_defs ())
             hspace.params
      in
      Debug.print
      @@ lazy
           (sprintf "[%s] defined-body qualifiers (%d): %s"
              (Ident.name_of_tvar Arg.name)
              (Set.length extra)
              (String.concat_map_set ~sep:", " extra ~f:Formula.str_of));
      { hspace with quals = Set.union hspace.quals extra }
    in
    (* UNREACHABLE BY DEFAULT (the solver's [reconstruct_rec_functions]):
       the applications of the functions a reconstruction pass added, at the
       terms the parameters reach. *)
    let hspace =
      let limit = Atomic.get PCSatCommon.RecFunReconstruct.qual_limit in
      let names = Atomic.get PCSP.Problem.reconstructed_functions in
      if limit <= 0 || Set.is_empty names then hspace
      else
        let extra =
          Set.Poly.of_list
          @@ rec_fun_app_quals ~bool_equalities:true ~limit
               ~fenv:
                 (Map.Poly.filter_keys (LogicOld.get_fenv ()) ~f:(Set.mem names))
               hspace.params
        in
        Debug.print
        @@ lazy
             (sprintf "[%s] reconstructed-function qualifiers (%d): %s"
                (Ident.name_of_tvar Arg.name)
                (Set.length extra)
                (String.concat_map_set ~sep:", " extra ~f:Formula.str_of));
        { hspace with quals = Set.union hspace.quals extra }
    in
    (* UNREACHABLE BY DEFAULT (rec_fun_app_quals). *)
    if config.rec_fun_app_quals <= 0 then hspace
    else
      let extra =
        Set.Poly.of_list
        @@ rec_fun_app_quals ~limit:config.rec_fun_app_quals
             ~fenv:(LogicOld.get_fenv ()) hspace.params
      in
      Debug.print
      @@ lazy
           (sprintf "[%s] recursive-function qualifiers (%d): %s"
              (Ident.name_of_tvar Arg.name)
              (Set.length extra)
              (String.concat_map_set ~sep:", " extra ~f:Formula.str_of));
      { hspace with quals = Set.union hspace.quals extra }

  let kind_cert_template () = None

  (* How many arrays a predicate can REACH, which is not how many of its
     parameters are arrays: an input derived from a Rust program declares its
     unknowns over the tuple a function's arguments arrive in, so the array is
     a field of a parameter and never a parameter.  Counting parameters gives
     such a predicate no quantifiers and no cells, and the whole mechanism then
     runs and produces nothing.  The count is per reachable array, so a
     predicate over two gets twice the index variables of one over one, and one
     over none gets the quantifier-free template however the count is set. *)
  let num_of_arrays params =
    List.length
    @@ CellQual.array_paths ~sequences:config.sequence_cells (List.map ~f:snd params)

  (* The universally quantified index variables.  They are ordinary integer
     parameters while the template is generated -- so the atom templates and
     the qualifier holes are built over them, which is what lets a disjunct say
     something about an arbitrary index -- and are bound by [Formula.forall]
     afterwards, which is what keeps the predicate's own arity unchanged.  The
     names are drawn fresh rather than fixed, because two predicates' templates
     are conjoined in one query and a shared name would identify their
     indices. *)
  (* ------------------------------------------------------------------
     The helpers of an alternative design, kept although nothing calls them.

     That design generates the template over the predicate's own parameters
     and *pads* the holes afterwards; the one in use generates over the
     extended parameter list instead, which is why these have no callers.
     They are the other design, not a worse spelling of this one, so they
     stay until someone decides the question is closed.

     One property to carry with them: they name the extra variables
     [ivar1], [cvar1], … **globally**, so two predicates' templates conjoined
     in one query would identify their indices.  The generating route draws
     fresh names instead. *)

  (* NOT USED BY THE METHOD THIS TEMPLATE IS BEING BUILT FOR, and the three
     below with it: they pad a hole's parameter list after the fact, where
     the template is generated over the extended parameter list and every
     hole is therefore built at the right arity to begin with.  Kept as the
     record of the earlier design rather than as work in progress. *)
  let _expand_senv_list n (senv_list : Logic.sort_env_list) :
      Logic.sort_env_list =
    senv_list
    @ List.init n ~f:(fun i ->
          (Ident.Tvar (sprintf "ivar%d" (i + 1)), Logic.IntTerm.SInt))

  (* NOT USED, with the one above and the one below. *)
  let _adding_index_value_types n (senv_list : Logic.sort_env_list) :
      Logic.sort_env_list =
    senv_list
    @ List.concat
      @@ List.init n ~f:(fun i ->
             let i = i + 1 in
             [
               (Ident.Tvar (sprintf "ivar%d" i), Logic.IntTerm.SInt);
               (Ident.Tvar (sprintf "cvar%d" i), Logic.IntTerm.SInt);
             ])

  (* NOT USED, with the two above. *)
  let _mk_forall_binds n : Logic.sort_env_list =
    List.init n ~f:(fun i ->
        (Ident.Tvar (sprintf "ivar%d" (i + 1)), Logic.IntTerm.SInt))

  (* The padding design also took a disjunction of holes apart and put it
     back together, to rebuild each hole at a wider arity.  Both halves are
     in the tree already -- [Formula.disjuncts_list_of], and [Formula.or_of]
     over [Formula.mk_atom] -- so they are not repeated here. *)

  (* UNREACHABLE BY DEFAULT (cells): [m] is 0 unless configured.  Two
     parameters per cell, an index and the value held there, and their sorts
     are the ARRAY'S -- not [Int].

     Integer columns would be a wall: an array of [(Array Int alpha)] for a
     quantified sort [alpha] has elements that no integer column can hold, and
     the run would end in an ordinary [unknown] saying so.  The sorts are
     carried by the path already, so taking them is the whole of the template
     half.

     The index column takes the path's index sort too, and today that is always
     [Int]: the candidate cells an example offers are built by counting, so an
     array indexed by anything else has no candidate set and is not reported as
     a path at all.  Writing the sort rather than [T_int.SInt] is what keeps
     this honest if that ever changes.

     The order is path-major -- every cell of the first array, then of the
     second -- and every consumer here and in the example expansion slices it
     that way, so it is a shared contract rather than a local choice. *)
  (* The cell columns of this predicate, drawn ONCE and reused by every
     template generated for it -- the plain one and each unsat-core shape, and
     again after every hypothesis-space update.

     They are the parameters of the predicate's extended truth table, and that
     table is shared by all of those templates while holding a SINGLE parameter
     list: a qualifier is evaluated at an atom by substituting the atom's
     arguments for that list.  Drawn fresh per template, each template's
     qualifiers named different columns, the table's list was whichever
     template had been generated last, and every atom added afterwards was
     evaluated with the other templates' cell columns left free -- undecided,
     which the constraint reads as "no constraint" on a body atom and "this
     selector is 0" on a head atom.  The plain template then could not
     separate a negative from a positive example that a single cell qualifier
     separates, and its query came back unsatisfiable.  With one set of
     columns per predicate every template's qualifiers are read against the
     list they were built over, and a qualifier two templates share is one
     column of the table rather than two.

     Keyed by the shape the columns are drawn for, so that a change of paths
     or of [m] draws afresh rather than reusing columns of the wrong count or
     sort. *)
  let cell_binds_memo :
      ((int * int list * string list) * int * sort_env_list) option ref =
    ref None

  let rec cell_binds (paths : CellQual.array_path list) m =
    let key =
      List.map paths ~f:(fun path ->
          ( path.CellQual.param,
            List.map path.CellQual.selectors ~f:snd,
            List.map
              (path.CellQual.index_sorts @ [ path.CellQual.elem_sort ])
              ~f:Term.str_of_sort ))
    in
    let key =
      ( List.length key,
        List.map key ~f:(fun (p, _, _) -> p),
        List.concat_map key ~f:(fun (_, sels, sorts) -> sels @ sorts) )
    in
    match !cell_binds_memo with
    | Some (key', m', binds) when Stdlib.(key = key') && m = m' -> binds
    | _ ->
        let binds = cell_binds_fresh paths m in
        cell_binds_memo := Some (key, m, binds);
        binds

  and cell_binds_fresh (paths : CellQual.array_path list) m =
    List.concat_map paths ~f:(fun path ->
        List.concat
        @@ List.init m ~f:(fun _ ->
               (* one index column per LEVEL of the array -- several for a
                  curried one -- and the value at the end of the chain; the
                  width is [CellQual.cell_width path], which every consumer
                  slices by *)
               List.map path.CellQual.index_sorts ~f:(fun si ->
                   (Ident.mk_fresh_tvar ~prefix:(Some "cell_idx") (), si))
               @ [
                   ( Ident.mk_fresh_tvar ~prefix:(Some "cell_val") (),
                     path.CellQual.elem_sort );
                 ]))

  (* [n] is 0 unless configured.  One integer variable per quantifier, bound
     by [forall] once the DNF has been generated in their scope.

     The method this template is being built for probably has no role for
     these, and that is worth knowing before they are relied on: the
     variables it quantifies are the cells' own index columns -- the read-back
     below closes exactly those and substitutes an array read for each value
     column -- so a *second*, separate set of quantified integers would be
     quantifying nothing the predicate can say anything about.  Kept until
     the lifting is built and settles it, since the two are identical in
     shape and only their role differs.

     Memoised per predicate for the reason the cell columns are: every
     template this module generates -- the plain one and each unsat-core
     shape -- builds its qualifiers over [gen_params], which contains these
     variables, and the extended truth table reads all of them against one
     parameter list.  Drawn fresh per call, the second template's list would
     name different variables from the first, which the table refuses.
     Keyed by the count, so a change of configuration draws afresh. *)
  let index_binds_memo : (int * sort_env_list) option ref = ref None

  let index_binds n =
    match !index_binds_memo with
    | Some (n', binds) when n = n' -> binds
    | _ ->
        let binds =
          List.init n ~f:(fun _ ->
              (Ident.mk_fresh_tvar ~prefix:(Some "qpa_idx") (), T_int.SInt))
        in
        index_binds_memo := Some (n, binds);
        binds

  (* The lifting of the hypothesis space's qualifiers to the cells
     ([CellQual.instantiate] over every qualifier), remembered from the last
     template generated for this predicate.  One rebuild generates the plain
     template and every unsat-core shape from the same hypothesis space, and
     the lifting is the same for all of them, so it is computed once rather
     than once per shape; with a large vocabulary it was a large part of each
     generation.

     Exact: [CellQual.instantiate] is a function of the qualifier and the cells
     alone (it substitutes the cell columns for the placeholders and draws no
     fresh name), so the lifting is a function of the qualifier set and the
     cells.  The key determines both: the qualifier set is the hypothesis
     space's own, compared physically (a hypothesis-space update builds a new
     set, which misses), together with whether the array terms were filtered
     out of it; the cells are determined by the memoised cell columns
     (compared physically: [cell_binds] returns the same list for the same
     shape and draws a new one otherwise), the cells per array, and the
     arrays the cells are named after, which fix the slicing; the parameter
     names are compared too, since the filter of array terms reads which
     parameters are arrays.  A hit returns
     the very set the computation would rebuild. *)
  (* [grow_keeping_disjuncts]: the key, number of disjuncts and template of
     the last non-ucore build. *)
  let retained_template = ref None
  let () = if config.grow_keeping_disjuncts then TemplateLineage.activate ()

  (* the predicate template returned by that build *)
  let retained_tmpl : Logic.term option ref = ref None

  let lifted_memo :
      ((Formula.t Set.Poly.t
       * bool
       * sort_env_list
       * int
       * Ident.tvar list
       * Ident.tvar list)
      * Formula.t Set.Poly.t)
      option
      ref =
    ref None

  let gen_template ~ucore (hspace : HypSpace.hspace) =
    (* REACHABLE ON THE DEFAULT PATH. Both counts are 0 unless configured, so
       [index_binds] and [cell_binds] are empty, [gen_params] is
       [hspace.params], and everything below generates the template this
       module has always generated. *)
    let hspace_quals_in = hspace.quals in
    decide_sort_var_scope hspace;
    if Option.is_none ucore then note_regeneration ();
    let paths =
      (* before [plain_template_first] has switched this predicate's cells on,
         it has no path, and everything below builds the cell-free template *)
      if not !cells_enabled then []
      else
        CellQual.array_paths ~sequences:config.sequence_cells
          (List.map ~f:snd hspace.params)
    in
    (* the same list the count is defined from, so the two cannot drift *)
    let nr_arrays = num_of_arrays hspace.params in
    let index_binds =
      index_binds (config.number_of_quantifiers_per_array * nr_arrays)
    in
    (* The cell parameters go last, because the example expansion appends its
       concrete (index, value) pairs to the end of the atom's argument list
       and reads the count back as (arity - original arity) / 2 / arrays. *)
    let cell_binds = cell_binds paths config.number_of_cells_per_array in
    (* The template is generated over the predicate's parameters extended by the
       index variables, so every hole, every affine atom and every qualifier is
       built in their scope.  [Formula.forall] below closes them again. *)
    let gen_params = hspace.params @ index_binds @ cell_binds in
    (* Which cells belong to which array parameter, and the instantiation of a
       cell qualifier at them.  Extraction cannot name these columns -- they
       are drawn here, and how many there are is this template's decision --
       so it emits a schema naming the array parameter instead, and the schema
       becomes one qualifier per cell.  A qualifier that names no cell passes
       through unchanged; one naming an array with no cells is dropped, as is
       any schema reaching a template that generates none, which the shared
       generator does by the ordinary rule that a qualifier must be about the
       parameters. *)
    let cells =
      (* the binders carry their own sorts; building the terms with
         [T_int.SInt] regardless is how a value column of another
         sort would reach a query as an integer.  Sliced per path by that
         path's cell width, which is what makes a curried array's cell -- its
         index tuple and one value -- one cell rather than several. *)
      let remaining = ref cell_binds in
      let take n =
        let taken, rest = List.split_n !remaining n in
        remaining := rest;
        taken
      in
      let m = config.number_of_cells_per_array in
      (* keyed by the array a path REACHES, so that a predicate over a tuple
         holding an array names the same thing the extraction named *)
      List.map paths ~f:(fun path ->
          let nidx = List.length path.CellQual.index_sorts in
          ( Ident.Tvar
              (CellQual.name_of_path path
                 (fst @@ List.nth_exn hspace.params path.CellQual.param)),
            List.init m ~f:(fun _ ->
                let cols =
                  List.map (take (CellQual.cell_width path)) ~f:(fun (x, s) ->
                      Term.mk_var x s)
                in
                let idxs, value = List.split_n cols nidx in
                (idxs, List.hd_exn value)) ))
    in
    (* the path each cell group was generated for, in the same order *)
    let celled_paths = List.zip_exn paths cells in
    (* The terms of a sort that the predicate's own parameters reach, for the
       equalities a non-integer index or value column can be compared by.  An
       index of a quantified sort has no order and no arithmetic, so the one
       thing a candidate can say about it is which of the terms in scope it is
       equal to -- and that is exactly what a universal over a trait predicate
       needs, [forall b. q_p(cur x, b, v)] being the cell whose first and third
       indices are pinned to [cur x] and [v] and whose second is free. *)
    let reachable_of_sort =
      let args = List.map hspace.params ~f:(fun (x, s) -> (Term.mk_var x s, s)) in
      fun sort -> CellQual.terms_of_sort sort args
    in
    let column_quals col sort =
      if Term.is_int_sort sort then None
      else if Term.is_bool_sort sort then
        (* a boolean column is a qualifier by itself *)
        Some [ Formula.eq col (T_bool.mk_true ()) ]
      else
        Some
          (List.concat_map (reachable_of_sort sort) ~f:(fun t ->
               [ Formula.eq col t; Formula.neq col t ]))
    in
    let array_terms_filtered =
      config.number_of_cells_per_array > 0
      && config.cells_replace_array_terms && !cells_enabled
    in
    let hspace =
      if array_terms_filtered then
        let arrays =
          Set.Poly.of_list @@ List.map ~f:fst
          @@ List.filter hspace.params ~f:(snd >> Term.is_array_sort)
        in
        let mentions vs = Fn.non Set.is_empty @@ Set.inter vs arrays in
        {
          hspace with
          terms = Set.filter hspace.terms ~f:(Term.tvs_of >> mentions >> not);
          quals = Set.filter hspace.quals ~f:(Formula.tvs_of >> mentions >> not);
        }
      else hspace
    in
    let boundary_quals =
      if not config.cell_boundary_quals then Set.Poly.empty
      else
        let values =
          T_int.zero ()
          :: List.filter_map hspace.params ~f:(fun (x, s) ->
                 if Term.is_int_sort s then Some (Term.mk_var x s) else None)
        in
        Set.Poly.of_list
        @@ List.concat_map celled_paths ~f:(fun (path, (_, pairs)) ->
               List.concat_map pairs ~f:(fun (idxs, value) ->
                   (* an integer column takes the order against every integer
                      in scope; a column of another sort takes the equalities
                      of [column_quals] *)
                   let col (c, sort) =
                     match column_quals c sort with
                     | Some qs -> qs
                     | None ->
                         List.concat_map values ~f:(fun v ->
                             [ Formula.geq c v; Formula.leq c v ])
                   in
                   List.concat_map
                     (List.zip_exn idxs path.CellQual.index_sorts
                     @ [ (value, path.CellQual.elem_sort) ])
                     ~f:col))
    in
    (* the relations two columns of ONE sort admit: the order for integers,
       equality for everything else *)
    let same_sort_rel sort a b =
      if Term.is_int_sort sort then [ Formula.leq a b; Formula.leq b a ]
      else [ Formula.eq a b; Formula.neq a b ]
    in
    let pair_quals =
      if not config.cell_pair_quals then Set.Poly.empty
      else
        let per_array (path, (_, pairs)) =
          let indexed = List.mapi pairs ~f:(fun i p -> (i, p)) in
          let sorts = path.CellQual.index_sorts in
          let esort = path.CellQual.elem_sort in
          List.concat_map indexed ~f:(fun (i, (idxs1, val1)) ->
              List.concat_map indexed ~f:(fun (j, (idxs2, val2)) ->
                  if i >= j then []
                  else
                    (* level by level, the two cells' indices of one level
                       have one sort and admit its relation; the values
                       likewise; and an integer index against an integer
                       value, which is the only cross comparison with a
                       meaning *)
                    List.concat
                      (List.map3_exn idxs1 idxs2 sorts ~f:(fun a b s ->
                           same_sort_rel s a b))
                    @ same_sort_rel esort val1 val2
                    @
                    if not (Term.is_int_sort esort) then []
                    else
                      List.concat
                        (List.map2_exn idxs1 sorts ~f:(fun a s ->
                             if Term.is_int_sort s then
                               [ Formula.leq a val2; Formula.leq val2 a ]
                             else []))
                      @ List.concat
                          (List.map2_exn idxs2 sorts ~f:(fun b s ->
                               if Term.is_int_sort s then
                                 [ Formula.leq b val1; Formula.leq val1 b ]
                               else []))))
        in
        Set.Poly.of_list @@ List.concat_map celled_paths ~f:per_array
    in
    let cross_array_quals =
      if not config.cell_cross_array_quals then Set.Poly.empty
      else
        let offsets =
          T_int.zero ()
          :: List.filter_map hspace.params ~f:(fun (x, srt) ->
                 if Term.is_int_sort srt then Some (Term.mk_var x srt) else None)
        in
        let indexed = List.mapi celled_paths ~f:(fun i c -> (i, c)) in
        Set.Poly.of_list
        @@ List.concat_map indexed ~f:(fun (i, (p1, (_, ps1))) ->
               List.concat_map indexed ~f:(fun (j, (p2, (_, ps2))) ->
                   if i >= j then []
                   else
                     (* two value columns are comparable only when their arrays
                        hold the same thing; an offset relates an integer index
                        of one to an integer index of the other, whatever the
                        other levels are *)
                     let same_elem =
                       String.equal
                         (Term.str_of_sort p1.CellQual.elem_sort)
                         (Term.str_of_sort p2.CellQual.elem_sort)
                     in
                     let int_idxs idxs sorts =
                       List.filter_map (List.zip_exn idxs sorts) ~f:(fun (a, s) ->
                           if Term.is_int_sort s then Some a else None)
                     in
                     List.concat_map ps1 ~f:(fun (idxs1, val1) ->
                         List.concat_map ps2 ~f:(fun (idxs2, val2) ->
                             (if same_elem then [ Formula.eq val1 val2 ] else [])
                             @ List.concat_map
                                 (int_idxs idxs1 p1.CellQual.index_sorts)
                                 ~f:(fun idx1 ->
                                   List.concat_map
                                     (int_idxs idxs2 p2.CellQual.index_sorts)
                                     ~f:(fun idx2 ->
                                       List.concat_map offsets ~f:(fun off ->
                                           [
                                             Formula.eq idx1
                                               (T_int.mk_add idx2 off);
                                             Formula.eq idx2
                                               (T_int.mk_add idx1 off);
                                           ])))))))
    in
    let int_params_and_zero () =
      T_int.zero ()
      :: List.filter_map hspace.params ~f:(fun (x, srt) ->
             if Term.is_int_sort srt then Some (Term.mk_var x srt) else None)
    in
    let cross_index_value_quals =
      if not config.cell_cross_index_value_quals then Set.Poly.empty
      else
        Set.Poly.of_list
        @@ cell_cross_index_value_quals ~offsets:(int_params_and_zero ())
             celled_paths
    in
    let pair_index_eqs =
      if not config.cell_pair_index_equalities then Set.Poly.empty
      else Set.Poly.of_list @@ cell_pair_index_equalities celled_paths
    in
    let affine_value_quals =
      if config.cell_affine_value_terms <= 0 then Set.Poly.empty
      else
        let values =
          (T_int.zero ()
          :: List.filter_map hspace.params ~f:(fun (x, srt) ->
                 if Term.is_int_sort srt then Some (Term.mk_var x srt) else None)
          )
          @ reachable_int_bounds ~limit:config.cell_affine_value_terms
              hspace.params
        in
        Set.Poly.of_list @@ cell_affine_value_quals ~values celled_paths
    in
    (* The write indices and anchors over the predicate's parameters; empty
       unless [cell_store_index_quals] is on and the predicate has cells. *)
    let store_index_writes =
      if (not config.cell_store_index_quals) || List.is_empty celled_paths
      then []
      else
        let writes =
          store_index_terms ~limit:config.cell_store_index_quals_max
            ~pvar:(Ident.tvar_to_pvar Arg.name) ~params:hspace.params
            (Lazy.force Arg.problem_formulas)
        in
        let anchors =
          if not config.cell_store_index_anchor_quals then []
          else
            store_index_anchor_terms ~limit:config.cell_store_index_quals_max
              ~pvar:(Ident.tvar_to_pvar Arg.name) ~params:hspace.params
              (Lazy.force Arg.problem_formulas)
              writes
        in
        Debug.print
        @@ lazy
             (sprintf "[%s] write-index anchors (%d): %s"
                (Ident.name_of_tvar Arg.name)
                (List.length anchors)
                (String.concat_map_list ~sep:", " anchors ~f:(fun (_, t) ->
                     Term.str_of t)));
        writes @ anchors
    in
    let store_index_quals =
      if (not config.cell_store_index_quals) || List.is_empty celled_paths
      then Set.Poly.empty
      else
        let quals =
          Set.Poly.of_list
          @@ cell_store_index_quals ~writes:store_index_writes celled_paths
        in
        Debug.print
        @@ lazy
             (sprintf "[%s] write-index cell qualifiers (%d): %s"
                (Ident.name_of_tvar Arg.name)
                (Set.length quals)
                (String.concat_map_list ~sep:", " (Set.to_list quals)
                   ~f:Formula.str_of));
        quals
    in
    let has_celled_sequence = List.exists paths ~f:CellQual.is_sequence in
    let instantiate_cells quals =
      Set.Poly.of_list
      @@ List.concat_map (Set.to_list quals) ~f:(CellQual.instantiate ~cells)
    in
    let cut_to_cells quals =
      if not config.cell_quals_only then quals
      else
        let cols =
          Set.Poly.of_list
          @@ List.concat_map cells ~f:(fun (_, pairs) ->
                 List.concat_map pairs ~f:(fun (idxs, v) ->
                     List.map (idxs @ [ v ]) ~f:(fun c -> fst @@ fst @@ Term.let_var c)))
        in
        if Set.is_empty cols then quals
        else
          Set.filter quals ~f:(fun q ->
              (Fn.non Set.is_empty @@ Set.inter (Formula.tvs_of q) cols)
              || (config.sequence_sentinel_cell && has_celled_sequence
                 && CellQual.speaks_of_sequence_length_only q)
              || (config.cell_cut_keeps_seq_store_quals && has_celled_sequence
                 && CellQual.is_seq_store_equality q)
              || (config.cell_cut_keeps_seq_equalities && has_celled_sequence
                 && CellQual.is_sequence_equality q))
    in
    (* What each cell qualifier family contributed, and what survived the cut.
       A family switched on that contributes nothing is the failure this route
       has met more than once -- the mechanism runs, is called, and produces
       nothing -- and the only thing that separates it from a family that
       contributes and does not help is a count. *)
    let lifted =
      let key =
        ( hspace_quals_in,
          array_terms_filtered,
          cell_binds,
          config.number_of_cells_per_array,
          List.map cells ~f:fst,
          List.map hspace.params ~f:fst )
      in
      let same_key (q, f, cb, m, names, params) =
        let q', f', cb', m', names', params' = key in
        phys_equal q q' && Bool.equal f f' && phys_equal cb cb' && m = m'
        && List.equal Ident.tvar_equal names names'
        && List.equal Ident.tvar_equal params params'
      in
      match !lifted_memo with
      | Some (key', lifted) when same_key key' -> lifted
      | _ ->
          let lifted = instantiate_cells hspace.quals in
          lifted_memo := Some (key, lifted);
          lifted
    in
    let all_cell_quals =
      Set.Poly.union_list
        [
          boundary_quals;
          pair_quals;
          cross_array_quals;
          affine_value_quals;
          cross_index_value_quals;
          pair_index_eqs;
          store_index_quals;
        ]
    in
    let quals = cut_to_cells (Set.union all_cell_quals lifted) in
    let uncapped = Set.length quals in
    let quals =
      match config.max_quals_per_predicate with
      | None -> quals
      | Some limit ->
          let capped = cap_qualifiers ~limit quals in
          if Set.length capped < uncapped then
            Debug.print
            @@ lazy
                 (sprintf "[%s] qualifiers capped: %d of %d kept"
                    (Ident.name_of_tvar Arg.name)
                    (Set.length capped) uncapped);
          capped
    in
    (* A census instrument, read by nothing: with [COAR_QUAL_COUNT] set, one
       line per template built, giving the qualifiers it started from
       ([in], [schema] of them cell schemas), its cell paths and cells per
       path, what the lifting returned ([lifted]: the schemas instantiated
       and every other qualifier passed through unchanged), the cell
       families, the count after the cut and the count kept by
       [max_quals_per_predicate]. *)
    if Option.is_some (Sys.getenv "COAR_QUAL_COUNT") then
      Out_channel.eprintf
        "QUALCOUNT %s in=%d schema=%d paths=%d cells_per_path=%d lifted=%d \
         families=%d after_cut=%d kept=%d\n%!"
        (Ident.name_of_tvar Arg.name)
        (Set.length hspace.quals)
        (Set.count hspace.quals ~f:CellQual.mentions_placeholder)
        (List.length celled_paths) config.number_of_cells_per_array
        (Set.length lifted) (Set.length all_cell_quals) uncapped
        (Set.length quals);
    Debug.print
    @@ lazy
         (sprintf
            "cell qualifiers: boundary %d, pair %d, cross-array %d, lifted %d; \
             %d after the cut"
            (Set.length boundary_quals) (Set.length pair_quals)
            (Set.length cross_array_quals) (Set.length lifted)
            (Set.length quals));
    if
      config.cell_cross_index_value_quals || config.cell_pair_index_equalities
    then
      Debug.print
      @@ lazy
           (sprintf
              "[%s] cross-array index-value cell qualifiers %d, pair index \
               equalities %d"
              (Ident.name_of_tvar Arg.name)
              (Set.length cross_index_value_quals)
              (Set.length pair_index_eqs));
    if config.cell_affine_value_terms > 0 then
      Debug.print
      @@ lazy
           (sprintf "[%s] affine value cell qualifiers (%d): %s"
              (Ident.name_of_tvar Arg.name)
              (Set.length affine_value_quals)
              (String.concat_map_list ~sep:", "
                 (Set.to_list affine_value_quals) ~f:Formula.str_of));
    let quals =
      if
        (not config.celled_drop_array_equality_quals)
        || List.is_empty cell_binds
      then quals
      else
        let kept = Set.filter quals ~f:(Fn.non CellQual.is_whole_array_equality) in
        if Set.length kept < Set.length quals then (
          (* a report only: counts the templates this switch narrowed *)
          Common.PhaseTime.event "synthesis/drop-array-equality-quals";
          Debug.print
          @@ lazy
               (sprintf "[%s] whole-array equality qualifiers dropped: %d"
                  (Ident.name_of_tvar Arg.name)
                  (Set.length quals - Set.length kept)));
        kept
    in
    let hspace = { hspace with quals } in
    (* The template built from nothing at the current shape: the base DNF
       and, where they apply, the cell guards around it. *)
    let fresh_template () =
      let template =
        match ucore with
        | Some (shp, eq_atom, only_bools) ->
            Templ.gen_dnf ~print:Debug.print ~eq_atom ~br_bools:false ~only_bools
              {
                consts = Set.to_list hspace.consts;
                terms = Set.to_list hspace.terms;
                quals =
                  (let quals =
                     Set.filter hspace.quals
                       ~f:
                         (Formula.term_sort_env_of
                         >> Set.for_all ~f:(snd >> Term.is_bool_sort))
                   in
                   (* A hole with no qualifiers cannot say what parameters it
                      takes, and the constraint generator then builds it at the
                      atom's arity -- which is short by the index variables
                      whenever this template binds any.  Keeping one trivial
                      qualifier makes every hole carry its own parameter list,
                      which is where that arity is read from.  It costs nothing
                      where there are no index variables, so it is only done
                      there. *)
                   Set.to_list
                   @@
                   if List.is_empty index_binds && List.is_empty cell_binds then
                     quals
                   else Set.add quals (Formula.mk_false ()));
                shp;
                ubc = !param.ubc;
                ubd = !param.ubd;
                s = !param.s;
              }
              { bec = Option.map config.bound_each_coeff ~f:Z.of_int }
              gen_params
        | None ->
            Templ.gen_dnf ~print:Debug.print ~eq_atom:false ~br_bools:false
              ~only_bools:false
              (if config.non_ucore_affine_atoms <= 0 then
                 {
                   consts = [];
                   terms = [];
                   quals = Set.to_list (Set.add hspace.quals (Formula.mk_false ()));
                   shp = List.init !param.nd ~f:(fun _ -> 0);
                   ubc = None;
                   ubd = None;
                   s = Set.Poly.empty;
                 }
               else
                 {
                   consts = Set.to_list hspace.consts;
                   terms = Set.to_list hspace.terms;
                   quals = Set.to_list (Set.add hspace.quals (Formula.mk_false ()));
                   shp = List.init !param.nd ~f:(fun _ -> config.non_ucore_affine_atoms);
                   ubc = !param.ubc;
                   ubd = !param.ubd;
                   s = !param.s;
                 })
              {
                bec =
                  (if config.non_ucore_affine_atoms <= 0 then None
                   else Option.map config.bound_each_coeff ~f:Z.of_int);
              }
              gen_params
      in
      let template =
        if not config.cell_guard_disjuncts then template
        else if not !guards_enabled then (
          Debug.print
          @@ lazy
               (sprintf "[%s] cell guards withheld: %d of %d failures without them"
                  (Ident.name_of_tvar Arg.name)
                  !guard_failures config.cell_guard_after_failures);
          template)
        else if
          config.cell_guard_max_index_columns > 0
          && List.length (int_cell_index_columns celled_paths)
             > config.cell_guard_max_index_columns
        then (
          Debug.print
          @@ lazy
               (sprintf
                  "[%s] no cell guards: %d integer cell index columns, above \
                   the bound %d"
                  (Ident.name_of_tvar Arg.name)
                  (List.length (int_cell_index_columns celled_paths))
                  config.cell_guard_max_index_columns);
          template)
        else
          let reachable =
            reachable_int_bounds ~limit:config.cell_guard_reachable_bounds
              hspace.params
          in
          if not (List.is_empty reachable) then
            Debug.print
            @@ lazy
                 (sprintf "[%s] cell guard bounds reached from the parameters: %s"
                    (Ident.name_of_tvar Arg.name)
                    (String.concat_map_list ~sep:", " reachable ~f:Term.str_of));
          with_cell_guard_disjuncts
            ~bound_terms:
              ((if config.cell_guard_bound_terms then Set.to_list hspace.terms
                else [])
              @ reachable
              @
              if config.cell_guard_store_index_bounds then
                List.map store_index_writes ~f:snd
              else [])
            ~print:Debug.print ~int_params:hspace.params
            ~gen_params ~quals:(Set.to_list hspace.quals) celled_paths template
      in
      template
    in
    (* the added disjuncts when this build kept the last one's *)
    let kept_delta = ref None in
    let retain_eligible =
      config.grow_keeping_disjuncts && Option.is_none ucore
      && List.is_empty index_binds
      && config.non_ucore_affine_atoms <= 0
    in
    let template =
      if
        (not config.grow_keeping_disjuncts)
        || Option.is_some ucore
        || (not (List.is_empty index_binds))
        || config.non_ucore_affine_atoms > 0
      then fresh_template ()
      else
        (* everything the fresh build reads apart from the number of
           disjuncts, compared structurally; a comparison that meets a
           value it cannot compare counts as a change *)
        let key =
          ( Set.to_list hspace.quals,
            List.map ~f:fst gen_params,
            List.map ~f:snd gen_params,
            ( !guards_enabled,
              List.map store_index_writes ~f:snd,
              Set.to_list hspace.terms,
              List.map ~f:fst hspace.params,
              List.map celled_paths ~f:snd ) )
        in
        let same key' =
          try Stdlib.compare key key' = 0
          with Invalid_argument _ -> false
        in
        match !retained_template with
        | Some (key', nd', (t' : Templ.templ_pred)) when same key' && !param.nd > nd' ->
            Common.PhaseTime.event "synthesis/grow-keeping/kept";
            let (delta : Templ.templ_pred) =
              Templ.gen_dnf ~print:Debug.print ~eq_atom:false
                ~br_bools:false ~only_bools:false
                {
                  consts = [];
                  terms = [];
                  quals =
                    Set.to_list (Set.add hspace.quals (Formula.mk_false ()));
                  shp = List.init (!param.nd - nd') ~f:(fun _ -> 0);
                  ubc = None;
                  ubd = None;
                  s = Set.Poly.empty;
                }
                { bec = None } gen_params
            in
            let (t : Templ.templ_pred) =
                {
                  Templ.templ_params =
                    Map.force_merge t'.templ_params delta.templ_params;
                  hole_quals_map = t'.hole_quals_map @ delta.hole_quals_map;
                  pred = Formula.or_of [ t'.pred; delta.pred ];
                  coeffs_bounds =
                    Formula.mk_and t'.coeffs_bounds delta.coeffs_bounds;
                  consts_bounds =
                    Formula.mk_and t'.consts_bounds delta.consts_bounds;
                  quals_bounds =
                    Formula.mk_and t'.quals_bounds delta.quals_bounds;
                }
            in
            retained_template := Some (key, !param.nd, t);
            kept_delta := Some delta;
            t
        | Some (key', _, _) ->
            Common.PhaseTime.event
              (if same key' then "synthesis/grow-keeping/not-larger"
               else "synthesis/grow-keeping/changed");
            let t = fresh_template () in
            retained_template := Some (key, !param.nd, t);
            t
        | None ->
            let t = fresh_template () in
            retained_template := Some (key, !param.nd, t);
            t
    in
    Debug.print
    @@ lazy
         (sprintf "[%s] predicate template:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.pred));
    Debug.print
    @@ lazy
         (sprintf "[%s] coeffs_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.coeffs_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] consts_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.consts_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] quals_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.quals_bounds));
    if false then
      Debug.print
      @@ lazy
           (sprintf "qdeps:\n%s"
           @@ String.concat_map_list ~sep:"\n" (Map.data hspace.qdeps)
                ~f:QualDep.str_of);
    let qual_qdeps_env = Templ.qual_env_of_hole_map template.hole_quals_map in
    let pred =
      (* Closing the index variables here, and lambda-binding only the
         predicate's own parameters below, is what makes the generated
         predicate a solution for the signature it was asked for: the extra
         parameters exist for the generator's benefit and must not reach the
         predicate's sort. *)
      if List.is_empty index_binds then template.pred
      else Formula.forall index_binds template.pred
    in
    if not (List.is_empty index_binds) then
      Debug.print
      @@ lazy
           (sprintf "[%s] quantified over %d index variable(s): %s"
              (Ident.name_of_tvar Arg.name)
              (List.length index_binds)
              (String.concat_map_list ~sep:", " index_binds
                 ~f:(fst >> Ident.name_of_tvar)));
    let tmpl =
      Logic.(Term.mk_lambda (of_old_sort_env_list (hspace.params @ cell_binds)))
      @@ Logic.ExtTerm.of_old_formula pred
    in
    if retain_eligible then (
      (match (!kept_delta, !retained_tmpl) with
      | Some (delta : Templ.templ_pred), Some old ->
          TemplateLineage.register ~tmpl ~old
            ~delta:
              (Logic.(
                 Term.mk_lambda (of_old_sort_env_list (hspace.params @ cell_binds)))
              @@ Logic.ExtTerm.of_old_formula delta.pred)
            ~delta_holes:(List.map delta.hole_quals_map ~f:fst)
      | _ -> ());
      TemplateLineage.note_base tmpl;
      retained_tmpl := Some tmpl);
    ( (DisjQPA, tmpl),
      (if Formula.is_true template.coeffs_bounds then []
       else
         [ (false, Coeff, Logic.ExtTerm.of_old_formula template.coeffs_bounds) ])
      @ (if Formula.is_true template.consts_bounds then []
         else
           [
             (false, Const, Logic.ExtTerm.of_old_formula template.consts_bounds);
           ])
      @ (if Formula.is_true template.quals_bounds then []
         else
           [
             ( true (*ToDo*),
               Qual,
               Logic.ExtTerm.of_old_formula template.quals_bounds );
           ])
      @ qdep_constr_of_envs hspace.qdeps qual_qdeps_env,
      template.templ_params,
      template.hole_quals_map )

  let restart (_param, actions) =
    Debug.print
    @@ lazy
         ("************* restarting "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    (init, actions @ [ "restart" ])

  let last_non_timeout_param = ref !param

  let revert (_param, actions) =
    Debug.print
    @@ lazy
         ("************* reverting "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    (!last_non_timeout_param, actions @ [ "revert" ])

  let increase_disj (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing number_of_disj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nd = param.nd + 1 }, actions @ [ "increase_disj" ])

  let decrease_disj (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_disj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nd = max (param.nd - 1) 0 }, actions @ [ "decrease_disj" ])

  let init_disj (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing number_of_disj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nd = init.nd }, actions @ [ "init_disj" ])

  let increase_qpa (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing number_of_qpa of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    let nq = param.nq + 1 in
    let ubd =
      if config.const_bound_follows_depth then
        Option.map param.ubd ~f:(fun ubd -> Z.max ubd (Z.of_int nq))
      else param.ubd
    in
    ({ param with nq; ubd }, actions @ [ "increase_qpa" ])

  let decrease_qpa (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_qpa of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nq = max (param.nq - 1) 0 }, actions @ [ "decrease_qpa" ])

  let init_qpa (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing number_of_qpa of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nq = init.nq }, actions @ [ "init_qpa" ])

  let set_inf_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubc = None }, actions @ [ "set_inf_coeff" ])

  let increase_coeff threshold (param, actions) =
    match (param.ubc, threshold) with
    | Some ubc, Some thr when Z.Compare.(ubc >= Z.of_int thr) ->
        set_inf_coeff (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_coeff of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( {
            param with
            ubc =
              (* REACHABLE ON THE DEFAULT PATH, and [ubc + 1] there, which is
                 the policy this template has always had. *)
              Option.map param.ubc ~f:(fun ubc ->
                  if config.coeff_bound_floor_at_two then
                    Z.max (Z.of_int 2) Z.(ubc + one)
                  else Z.(ubc + one));
          },
          actions @ [ "increase_coeff" ] )

  let decrease_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubc = Option.map param.ubc ~f:(fun ubc -> Z.(max (ubc - one) zero));
      },
      actions @ [ "decrease_coeff" ] )

  let init_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubc = init.ubc }, actions @ [ "init_coeff" ])

  let set_inf_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubd = None }, actions @ [ "set_inf_const" ])

  let increase_const threshold (param, actions) =
    match (param.ubd, threshold) with
    | Some ubd, Some thr when Z.Compare.(ubd >= Z.of_int thr) ->
        set_inf_const (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_const of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( {
            param with
            ubd =
              (* REACHABLE ON THE DEFAULT PATH, and [ubd + 1] there. The
                 other arm *resets* the bound, which is the opposite of what
                 this function is called; it is kept behind its own flag
                 rather than adopted, and adopting it means renaming the
                 action. *)
              (if config.reset_const_bound_on_failure then init.ubd
               else Option.map param.ubd ~f:(fun ubd -> Z.(ubd + one)));
          },
          actions @ [ "increase_const" ] )

  let decrease_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubd = Option.map param.ubd ~f:(fun ubd -> Z.(max (ubd - one) zero));
      },
      actions @ [ "decrease_const" ] )

  let init_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubd = init.ubd }, actions @ [ "init_const" ])

  let increase_disj_qpa (param, actions) =
    if (param.nd + param.nq) mod 2 = 0 then increase_disj (param, actions)
    else increase_qpa (param, actions)

  (* One shape-growth step.  Contract: with [grow_disj_when_qpa_inert] off,
     or where [nq] is live, exactly [increase_disj_qpa]; with it on and [nq]
     inert, [increase_disj], so that every step changes the template rather
     than every second one.  With [account] (the step really applied, not the
     preview [actions_of] prints) it counts the step in the phase-time report
     when that is on: [synthesis/widen/nd=N] for a step to N disjuncts,
     [synthesis/widen/nq=N] for a step of a live [nq], and
     [synthesis/widen-inert] for a step that changed only an inert [nq]. *)
  let grow_shape ~account (param, actions) =
    let inert = Lazy.force nq_inert in
    let ((param', _) as res) =
      if config.grow_disj_when_qpa_inert && inert then
        increase_disj (param, actions)
      else increase_disj_qpa (param, actions)
    in
    (if account then
       if param'.nd <> param.nd then
         Common.PhaseTime.event (sprintf "synthesis/widen/nd=%d" param'.nd)
       else if inert then Common.PhaseTime.event "synthesis/widen-inert"
       else Common.PhaseTime.event (sprintf "synthesis/widen/nq=%d" param'.nq));
    res

  (* with [account] and the phase-time report on, every label a growth step
     reads is counted as [synthesis/label/<name>], so a run says what its
     failed rounds blamed (a label that moves nothing, [Qual] or [TimeOut],
     included); the step itself is unchanged *)
  let count_label ~account name =
    if account then Common.PhaseTime.event ("synthesis/label/" ^ name)

  let rec inner ~account param_actions = function
    | [] -> param_actions
    | (DisjQPA | Shape) :: labels ->
        count_label ~account "shape";
        inner ~account (grow_shape ~account param_actions) labels
    | Coeff :: labels ->
        count_label ~account "coeff";
        inner ~account
          (increase_coeff config.threshold_coeff param_actions)
          labels
    | Const :: labels ->
        count_label ~account "const";
        inner ~account
          (increase_const config.threshold_const param_actions)
          labels
    | Qual :: labels ->
        count_label ~account "qual";
        inner ~account param_actions (*ToDo*) labels
    | QualDep :: labels ->
        count_label ~account "qualdep";
        inner ~account param_actions labels
    | TimeOut :: _labels ->
        count_label ~account "timeout";
        param_actions (* z3 may unexpectedly time out*)
    | _ -> assert false

  let actions_of labels =
    (snd @@ inner ~account:false (!param, []) @@ Set.to_list labels) @ [ "end" ]

  let update_with_labels labels =
    note_failure labels;
    param := fst @@ inner ~account:true (!param, []) @@ Set.to_list labels

  (* called on failure, ignore config.fix_shape *)
  let rl_action labels =
    if not @@ Set.mem labels TimeOut then last_non_timeout_param := !param;
    let rec action param_actions =
      match In_channel.input_line_exn In_channel.stdin with
      | "increase_disj" -> action (increase_disj param_actions)
      | "decrease_disj" -> action (decrease_disj param_actions)
      | "init_disj" -> action (init_disj param_actions)
      | "increase_qpa" -> action (increase_qpa param_actions)
      | "decrease_qpa" -> action (decrease_qpa param_actions)
      | "init_qpa" -> action (init_qpa param_actions)
      | "set_inf_coeff" -> action (set_inf_coeff param_actions)
      | "increase_coeff" -> action (increase_coeff None param_actions)
      | "decrease_coeff" -> action (decrease_coeff param_actions)
      | "init_coeff" -> action (init_coeff param_actions)
      | "set_inf_const" -> action (set_inf_const param_actions)
      | "increase_const" -> action (increase_const None param_actions)
      | "decrease_const" -> action (decrease_const param_actions)
      | "init_const" -> action (init_const param_actions)
      | "restart" -> action (restart param_actions)
      | "revert" -> action (revert param_actions)
      | "end" -> fst param_actions
      | s -> failwith ("Unknown action: " ^ s)
    in
    param := action (!param, [])

  (* The ruler sequence: one more than the number of trailing zero bits of
     [p], for p >= 1 -- 1, 2, 1, 3, 1, 2, 1, 4, ... *)
  let ruler p =
    let rec tz p n = if p land 1 = 1 then n else tz (p lsr 1) (n + 1) in
    1 + tz p 0

  (* With [restart_ladder]: the ladder position and the shape the current
     epoch started from (the configured shape for the first epoch). *)
  let ladder_pos = ref 1
  let epoch_start = ref !param

  (* Whether the template grew since the epoch started: more disjuncts, or a
     larger [nq] where something reads it. *)
  let grew_in_epoch () =
    !param.nd > !epoch_start.nd
    || ((not (Lazy.force nq_inert)) && !param.nq > !epoch_start.nq)

  (* Contract: with [restart_ladder] off, exactly the restart action (the
     shape becomes [init]).  On, see [restart_ladder]: [init] after an epoch
     that grew, [init] with init.nd + ruler p - 1 disjuncts (p advanced) after
     one that did not.  With the phase-time report on it counts
     [synthesis/restart/nd=K] for a restart to K disjuncts and
     [synthesis/restart-undo/nd=K] when the restart takes away disjuncts the
     epoch had grown to K. *)
  let restart () =
    let grew = grew_in_epoch () in
    if grew && !param.nd > !epoch_start.nd then
      Common.PhaseTime.event (sprintf "synthesis/restart-undo/nd=%d" !param.nd);
    let p, _ = restart (!param, []) in
    let p =
      if config.restart_ladder && not grew then (
        incr ladder_pos;
        let nd = init.nd + ruler !ladder_pos - 1 in
        Debug.print
        @@ lazy
             (sprintf "************* restart ladder: %s at %d disjuncts"
                (Ident.name_of_tvar Arg.name) nd);
        { p with nd })
      else p
    in
    Common.PhaseTime.event (sprintf "synthesis/restart/nd=%d" p.nd);
    param := p;
    epoch_start := p
  let update_with_solution _ = failwith "not implemented"
  let sync _thre = assert false

  let _ =
    Debug.print
    @@ lazy
         (sprintf "************* initializing %s ***************"
            (Ident.name_of_tvar Arg.name));
    Debug.print @@ lazy (str_of ())
end
