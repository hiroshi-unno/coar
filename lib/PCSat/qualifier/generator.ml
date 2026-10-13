(* The qualifier generator: the atomic formulas a predicate's candidate
   solutions are built from.

   Two sources.  Extraction ([extract_pcsp]) reads atoms off the problem
   itself -- each clause, normalised so that every argument of an unknown is
   a fresh variable, gives the atoms of its pure part that mention one
   application's variables only, lifted to that unknown's parameters -- plus
   the candidate atoms the input declares; with [propagate_quals] the
   qualifiers of one unknown are carried to another along the clauses that
   pass arguments between them.  This is done once, when the functor is
   applied ([extracted_qualifiers]).  Generation reads the labelled examples
   through a list of abstract domains (interval, octagon, octahedron,
   polyhedron, SVM, ...), one domain per call: [generate pvar params labeled
   examples n] uses domain [n], of [num_of_domains], and returns the union of
   the extracted, the generated and the configured derived qualifiers
   (negations, argument permutations, homogeneous forms, reflections), all
   normalised and over [params].

   Contract: every qualifier returned is a formula over [params], save that
   a qualifier lifted to an array's cell may also mention the cell-column
   placeholders the templates bind; the flags derive variants and never drop an extracted atom except where
   [elim_neg] or a [filter_out_*] flag says so.  The derived families are a
   choice of hypothesis space, not a soundness matter: a candidate is always
   checked against the clauses. *)
open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open PCSP
open PCSatCommon

type qualifier = sort_env_list * Formula.t

module type QualifierType = sig
  val qualifiers_of :
    Ident.pvar ->
    Sort.t list ->
    (ExAtom.t * int) Set.Poly.t ->
    sort_env_map * VersionSpace.examples ->
    qualifier Set.Poly.t

  val str_of_domain : string
end

module type GeneratorType = sig
  val generate :
    Ident.pvar ->
    sort_env_list ->
    (ExAtom.t * int) Set.Poly.t ->
    sort_env_map * VersionSpace.examples ->
    int ->
    qualifier Set.Poly.t

  val elim_neg : qualifier Set.Poly.t -> qualifier Set.Poly.t
  val str_of_domain : int -> string
  val num_of_domains : int

  val normalized_problem : PCSP.Problem.t
  (** the problem qualifiers are extracted from: the input normalised when
      [normalize_pcsp] is set, the input otherwise *)

  val extracted_qualifiers :
    (Ident.pvar, (int Set.Poly.t * Formula.t) Set.Poly.t) Map.Poly.t
  (** the qualifiers read off [normalized_problem] (and the declared atoms),
      propagated when [propagate_quals] is set, per unknown, each with the
      positions of the parameters it mentions *)
end

module Config = struct
  type domain =
    | Null
    | Interval
    | Octagon
    | Octahedron
    | Polyhedron of int
    | Polynomial
    | SVM of int (* approx_level *) * float (* csvm *)
    | NN of
        int (* dummy parameter for neural network guided qualifier generation *)
    | Union of domain list
  [@@deriving yojson]

  type t = {
    verbose : bool; [@default false]
    domains : domain list; [@default [ Null ]]
    extract_pcsp : bool; [@default true]  (** extract qualifiers from pfwCSP *)
    normalize_pcsp : bool; [@default true]  (** normalize pfwCSP to enhance extraction *)
    share_normalize_of_clauses : bool; [@default false]
        (** the normalisation of the clauses for extraction runs inside one
            scope of each node-address memo: the term conversions'
            ([Logic.ExtTerm.with_shared_term_conversion]), the simplifier's
            ([Evaluator.with_shared_simplify]), the normaliser's and the let
            passes' ([LogicOld.with_shared_let_passes]).  Each memo acts only
            when its own switch is on ([share_rebuilt_formulas],
            [share_let_passes]); each stores a result only when computing it
            drew no fresh name, so the clauses are the same values with the
            same draws, but shared where the input was.  Why: a clause's pure
            part reached this normalisation shared, and every conversion and
            rebuild here made it a tree, once per clause and once more per
            atom *)
    normalize_per_atom_relevant_only : bool; [@default false]
        (** with [normalize_per_atom_by_disjunct], an atom's copy of the pure
            part keeps only the disjuncts its substitution changes and that
            then mention a variable the atom binds.  The clause stays
            equivalent; the disjuncts, hence the qualifiers extracted from
            them, change *)
    normalize_per_atom_extractable_only : bool; [@default false]
        (** in the normalisation of a clause with several atoms, an atom's
            copy of a disjunct of the pure part is kept only when the
            extraction can read a qualifier from it
            ([image_may_give_a_qualifier]): every atom of the simplified copy
            that mentions the variables of two or more applications gives none,
            since each application's arguments are fresh variables of its own.
            The clause stays equivalent (it keeps the pure part and every
            disequality between variables of one class) and the qualifiers
            extracted from it are meant to be the same.  Why: in a clause of
            some 70 functional applications, each argument's class holds a copy
            per application, an atom's copy of a disjunct names the other
            applications' copies for every class the atom does not bind, and
            nine in ten atoms of the normalised clause spanned several
            applications *)
    normalize_per_atom_by_disjunct : bool; [@default false]
        (** in the normalisation of a clause with several atoms, the copy of
            the pure part rewritten for each atom's bound variables is built
            disjunct by disjunct, once for each distinct restriction of the
            atom's substitution to the disjunct's free variables, instead of
            substituting into the whole pure part once per atom
            ([per_atom_disjuncts_by_disjunct]).  The disjunct set is the same
            up to the names of bound variables: copies that differ only in
            those names are built once *)
    dedup_alpha_equivalent_disjuncts : bool; [@default true]
        (** after that normalization, drop disjuncts of a clause that differ
            only in the names of their bound variables; the normalization
            distributes, so one premise can leave it as several alpha-variants
            of itself *)
    propagate_quals : bool; [@default true]  (** propagate qualifiers *)
    propagate_declared_atoms : bool; [@default false]
        (** let the candidate atoms the input declares for an unknown
            ([(set-info :candidates ...)]) take part in [propagate_quals] like
            extracted qualifiers.  Off: a declared atom is a qualifier of the
            unknown it was declared for and of no other, so which declared atom
            matters can be measured one unknown at a time. *)
    declared_atoms_houdini_only : bool; [@default false]
        (** keep the declared candidate atoms out of the qualifiers this
            generator offers, so the hypothesis space the synthesizer searches
            is the one extraction gives without the declarations; the atoms are
            then read only by the validator's Houdini-style pre-pass, which
            takes them from the problem's parameters and not from here.  A
            declared atom widens the space every template hole searches, and
            on a Rust-derived loop that answers [sat] without its declarations
            (3 of 3 runs) the widened space was measured to lose the answer (0
            of 3 at 60 s, sixteen atoms declared for the loop head, none of
            them the invariant); with this on, what the declarations add is
            the pre-pass's attempt.  Off: the
            declared atoms are qualifiers of their unknown ([declared_qualifiers]
            below). *)
    add_bool : bool; [@default true]  (** add qualifiers for boolean variables *)
    offset_parity_quals : bool; [@default false]
        (** add [x mod 2 = 0] for an integer argument position of an unknown
            that some clause reads at two constant offsets: two applications
            of the unknown in one clause's premise whose arguments there
            differ by a nonzero constant ([I i /\ I (i + 1) => false]), or a
            premise application and a conclusion application that differ there
            by a nonzero even constant ([I i => I (i + 2)]).  Such a clause
            separates values of that argument by their parity, which no linear
            atom states, while an ordinary step by one relates no two values
            of the same parity.  The same atom for every integer argument of
            every unknown ([add_mod2_quals] of the templates) was measured to
            answer the inputs that need it and to slow the rest down by a third;
            this adds it only where a clause asks for it. *)
    add_homogeneous : bool; [@default false]  (** add homogeneous qualifiers *)
    add_reflections : bool; [@default true]
        (** also offer each halfspace approached from the other side: a space
            that holds [-t >= 0] and not [t >= 0] cannot put a boundary on the
            other piece of a partition, because the negation of [t <= 0] is the
            strict [t > 0] and excludes it *)
    add_arg_equalities : bool; [@default false]
        (** also offer, for each pair of the predicate's parameters that have
            the same non-array sort, the qualifier saying the two are equal --
            which no extraction reaches unless a clause already wrote it, and no
            numeric domain reaches at all for a datatype or an uninterpreted
            sort *)
    add_arg_transpositions : bool; [@default false]
        (** also add, for each qualifier, the forms obtained by swapping a
            pair of the predicate's parameters that have the same sort *)
    transpositions_keep_words : bool; [@default true]
        (** with [add_arg_transpositions], drop a form the swaps produced (the
            extracted qualifier itself is kept) that puts under
            [(_ int_to_bv n)] a parameter the problem never reads as a word,
            when the predicate has a parameter it does.  A parameter position
            is read as a word when some clause applies the predicate there to
            a variable that occurs directly under [int_to_bv] in the same
            clause.  On a loop counting the set bits of a 64-bit word
            ([inv w b k n1 n2], the counts [n1], [n2] never converted), the
            swaps of the one bit atom [bit_b(w) = 0] over five [Int]
            parameters put the counts under [int_to_bv] as well; each
            candidate carrying one then made the validation question split
            the count into an unbounded quotient and a word, and one such
            question was not answered in 30 s while the loop's other
            questions took well under a second. *)
    add_neg : bool; [@default false]  (** add negation of qualifiers *)
    add_func_qual_disj : bool; [@default true]
        (** add disjoined qualifiers involving function variables *)
    filter_out_neg : bool; [@default true]
    filter_out_non_div_mod : bool; [@default false]
    filter_out_quantified : bool; [@default false]
    sat_point_instances : bool; [@default false]
        (** ground a parametric example at a point its own CONDITION admits,
            rather than at the dummy point, before the numeric domains read it.
            Those domains build their half-spaces out of the instantiated
            argument tuples, and the dummy point does not look at the condition
            at all -- an integer parameter becomes 0 -- so every parametric
            example whose condition that point misses contributes the same
            tuple, and a vocabulary learned from a set of identical points
            separates none of them.  Any point is a consequence of the example,
            so the choice is sound either way; what it decides is whether the
            points differ.  Off by default: it costs one satisfiability query
            per parametric atom, and where the conditions are ones the dummy
            point already satisfies it buys nothing. *)
    instantiate_quantified_quals : bool; [@default true]
        (** offer an atom that sits under a quantifier inside a clause as a
            qualifier, instantiated at the unknown's own arguments *)
    ground_open_term_quals : bool; [@default true]
        (** offer a GROUND atom as a qualifier to every unknown applied in the
            clause, when the background theory does not fix its value. The
            ordinary rule keeps an atom only when one of its variables is an
            argument of an unknown, which a ground atom fails vacuously; that
            is right for an atom the theory decides, whose value is the same at
            every example and so separates nothing, and wrong for one whose
            value the theory leaves open -- a selector on the wrong
            constructor, a division by zero, an uninterpreted symbol. A
            solution may have to name such a fact as a guard, as in
            [P(x) := (tl nil = nil) /\ 0 <= x], and no atom over the unknown's
            own parameters can express it. *)
    nested_selector_subst : bool; [@default false]
        (** when a clause binds an argument of an unknown by an equation
            [u = c(..)] with [c] the only constructor of its datatype, also
            recover the variables that sit inside NESTED constructors of
            single-constructor datatypes -- [u = mut (tuple (tuple x3 x2)) x0]
            gives [x2 = tuple_1 (tuple_0 (mut_current u))] -- rather than only
            the variables that are direct arguments of [c].  Every selector
            introduced is total, since each constructor on the path is the
            only one of its datatype; a constructor of a datatype with several
            constructors stops the descent, because its selectors are partial.
            Off, only one level is looked at, which is what drops every atom
            over the integer leaves of a value that a Rust-derived problem
            wraps in a reference and a tuple. *)
    instantiate_quals_memo : bool; [@default false]
        (** in [instantiate_quantified_quals], instantiate an atom at an
            application of an unknown only when no atom equal to it up to a
            renaming of its bound variables has been instantiated at that
            application in the same clause.  The instances are the same,
            since each bound variable ranges independently over the
            application's arguments of its sort.  Why: a Rust-derived clause
            of 2,000 atoms whose premises restate one quantified fact per
            obligation, each copy with its own bound names, was instantiated
            copy by copy at a dozen applications of thirty arguments, 90 s of
            the generator's 100 s. *)
    parity_pvar_apps_only : bool; [@default false]
        (** in [offset_parity_quals]'s reading of the problem, simplify only
            the atoms that mention an unknown ([Formula.pvar_apps_of]) rather
            than every atom of every clause, of which it uses only the
            applications of unknowns.  The applications found are the same
            (an atom that mentions no unknown cannot simplify into an
            application of one).  Why: on a Rust-derived input of 119 clauses
            with about 22,000 atoms and 570 applications, the reading took
            about 30 s of the qualifier generator's 60 s, every one of it
            spent simplifying atoms it then discarded. *)
    extract_atom_quals_once : bool; [@default false]
        (** in the qualifier extraction, build the quantified qualifier of a
            clause's atom (and decide whether its private variables occur in
            a division) once per atom rather than once per unknown
            application of the clause it is offered to.  Both are functions
            of the atom and of the variables it does not share with the
            applications, so the qualifiers are the same; the simplifier is
            run fewer times, which can change how many fresh names it draws.
            Why: a clause of a Rust-derived input holds hundreds of atoms and
            up to a dozen applications of unknowns with thirty arguments
            each, and the extraction rebuilt the same qualifier for each
            application. *)
    lift_index_quals : bool; [@default false]
        (** offer an atom about an ARRAY ARGUMENT'S CONTENTS as a qualifier
            about that array's cell columns.

            The ordinary rule keeps an atom only when every variable it
            mentions is an argument of some unknown applied in the clause, so
            the atoms that say what an array holds are exactly the ones it
            drops: [a[j] > bound] and its guards [0 <= j], [j <= i] mention the
            loop index [j], which the invariant does not take.  A predicate
            whose parameters have been extended by (index, value) cells CAN say
            those things -- about the cell rather than about [j] -- so an atom
            whose out-of-scope variables occur in this clause only as the index
            of a read of an in-scope array is kept, with the index variable
            rewritten to the array's index column and the read to its value
            column.  No equation between the two is needed: the column IS that
            variable renamed, and the guards travel with it, which is what
            makes the three atoms above into the three the solution uses.

            Instantiating is safe in the usual sense -- a qualifier is a
            candidate building block and every candidate is validated -- so the
            cost is a larger hypothesis space.  The result mentions placeholder
            columns and is therefore useless to any template that generates no
            cells, which drops it. *)
    lift_read_quals : bool; [@default false]
        (** also lift an atom that reads an in-scope array at a term the
            predicate already takes -- [a[i] = 0], say -- into the guarded form
            [#cidx = i => a[#cidx] = 0].  The unguarded lifting above does not
            apply to it, because it has no out-of-scope variable, and the atom
            itself is already a qualifier; what this adds is the same fact
            stated about the cell, which is the only form a celled example can
            evaluate. *)
    lift_seq_nth_quals : bool; [@default true]
        (** also collect the reads [seq.nth s j] of a sequence of integers, not
            only the array reads, for the two liftings above, so that an atom
            about a sequence's elements becomes one about that sequence's cell
            columns.  It matters only where the template gives sequences cells;
            elsewhere a schema naming a sequence's columns instantiates
            nothing.  A lifted result that still contains a [seq.nth] is
            dropped whenever this is on, because such a read has no range
            premise and its value outside [0 <= j < seq.len s] is one the
            theory leaves open; the cell columns themselves carry the range,
            since a sequence cell exists only inside it (or at the sentinel,
            whose value is a constant). *)
    seq_store_equality_quals : bool; [@default false]
        (** offer [x = seq.store s i v] to an unknown for each sequence write
            [seq.store s i v] in a clause whose variables are all arguments of
            that unknown, [x] ranging over the unknown's other arguments of the
            write's sort.  The relation a write step needs between an old and a
            new sequence is otherwise offered only when the clause states it as
            an atom over one unknown's arguments.  The writes come from the
            problem, so the vocabulary is bounded by the writes it contains
            times the unknown's sequence arguments. *)
    lift_index_quals_max_vars : int; [@default 1]
    lift_clause_cell_disjunctions : bool; [@default true]
        (** offer, per clause, read index [j] and array [a] it indexes, the
            DISJUNCTION of the clause's disjuncts about [a]'s cell at [j] as one
            qualifier ([CellQual.clause_cell_disjunctions]): the disjuncts with
            no binder that mention [j] and otherwise only variables the
            clause's unknowns are applied to, lifted by the renaming
            [lift_index_quals] uses, when there are at least two.  A goal
            [I(a, i, n) /\ 0 <= j /\ j <= n /\ a[j] <> j => bot] then offers
            [#cidx < 0 \/ #cidx > n \/ #cval = #cidx], which is the body of
            the invariant's universal: with the atoms alone the template needs
            one disjunct of its own shape per atom.  At most one qualifier per
            (clause, read index, array), read off the problem.  It adds
            vocabulary only, so it cannot bear on soundness; such a qualifier
            is kept whole rather than split into its atoms after extraction. *)
        (** how many out-of-scope variables an atom may mention and still be
            lifted.  Two variables both rewritten to the same index column say
            something the atom did not (they were distinct indices), which is a
            legal but wilder guess, so one is the default. *)
    reduce : bool; [@default false]  (** reduce redundant qualifiers *)
  }
  [@@deriving yojson]

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Generator"

    (* a leaf: no nested config to load *)
    let instantiate = Or_error.return
  end)

  module type ConfigType = sig
    val config : t
  end
end

(* The substitution that rewrites a clause's pure part for one atom, whose
   free variables are [bounds_atm], and the disequalities that go with it.
   [eqcs] are the clause's classes of variables known equal, each with its
   sort.  In a class, a variable the atom does not bind is replaced by one the
   atom binds when there is one, and by the class's first variable otherwise;
   two variables of a class that the atom both binds stay, and the
   disequality of the extra ones with the first is returned as a disjunct.
   The substitution maps variables to variables. *)
let atom_sub_and_neqs eqcs bounds_atm =
  let sub, phis =
    Set.Poly.map eqcs ~f:(fun (eqc, ty) ->
        let bvs, fvs = Set.partition_tf ~f:(Set.mem bounds_atm) eqc in
        match (Set.to_list bvs, Set.to_list fvs) with
        | [], fv :: fvs' ->
            let tt = Logic.Term.mk_var fv in
            (List.map fvs' ~f:(fun x -> (x, tt)), [])
        | bv :: bvs', fvs ->
            let tt = Logic.Term.mk_var bv in
            ( List.map fvs ~f:(fun x -> (x, tt)),
              List.map bvs' ~f:(fun x ->
                  Logic.BoolTerm.neq_of ty tt (Logic.Term.mk_var x)) )
        | [], [] -> assert false)
    |> Set.to_list |> List.unzip
    |> Tuple2.map_both ~f1:List.concat ~f2:List.concat
  in
  (Map.Poly.of_alist_exn sub, phis)

(* The disjuncts, in the old representation, of the pure part [phi]
   rewritten for each atom of [atms] whose free variables meet [fvs_phi]
   (the free variables of [phi]): [phi] under the atom's substitution, with
   the atom's disequalities beside it, converted and its let binders renamed
   apart.  Every atom costs a substitution into the whole of [phi], which
   renames every binder of it, so a disjunct with a binder that no
   substitution touches enters the result once per atom, each copy under
   other bound names. *)
let per_atom_disjuncts_whole exi_senv uni_senv atms fvs_phi phi eqcs =
  Set.concat_map (Set.Poly.map atms ~f:Logic.Term.fvs_of) ~f:(fun bounds_atm ->
      if Set.are_disjoint fvs_phi bounds_atm then Set.Poly.empty
      else
        let sub, phis = atom_sub_and_neqs eqcs bounds_atm in
        LogicOld.Formula.disjuncts_of @@ LogicOld.Formula.alpha_rename_let
        @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv
        @@ Logic.BoolTerm.or_of (Logic.Term.subst sub phi :: phis))

(* [per_atom_disjuncts_whole] up to the names of bound variables, in time
   proportional to what the atoms change.

   Contract: for a [phi] whose free variables are [fvs_phi], the result and
   [per_atom_disjuncts_whole]'s have the same elements up to the names of
   bound variables: each element of one is alpha-equivalent to an element of
   the other.  The result is smaller where the other holds alpha-variants of
   one formula.

   Why it holds: [Logic.Term.subst] and the conversion to the old
   representation send an application of [Or] to two arguments to the
   disjunction of their images, the let renaming and [disjuncts_of]
   distribute over a disjunction, and the substitution leaves no constant
   at the top where [phi] is not one, so the whole disjunction's disjuncts
   are the union of those of its disjuncts' images (the constant case is
   handed to [per_atom_disjuncts_whole]).  A disjunct's image under a
   substitution of variables for variables depends, up to the names of the
   binders the substitution renames, only on the substitution restricted to
   the disjunct's free variables, so it is built once for each restriction
   met and reused for every atom that restricts to it.  [restrict:false]
   keys a disjunct's image on the disjunct alone, ignoring the substitution;
   it is wrong, and exists so that a test can show it is told apart.

   [relevant_only:true] builds, for an atom, only the images of the
   disjuncts the atom's substitution changes and whose image mentions a
   variable the atom binds; the result is then a subset of the one above.
   The clause it is put in stays equivalent: that clause also holds [phi]
   and the disequalities of every class of equal variables, and an image
   of a disjunct differs from the disjunct only by identifying variables of
   one class, so the two agree wherever no disequality holds, and any
   subset of the images can be dropped.  What changes is the qualifiers
   extraction reads off the clause: an image that mentions none of the
   atom's variables offers it none, but may offer another atom some. *)
let per_atom_disjuncts_by_disjunct ?(restrict = true) ?(relevant_only = false)
    exi_senv uni_senv atms fvs_phi phi eqcs =
  match phi with
  | Logic.Con _ ->
      per_atom_disjuncts_whole exi_senv uni_senv atms fvs_phi phi eqcs
  | _ ->
      let leaves =
        Array.of_list
        @@ List.map (Logic.BoolTerm.disjuncts_of phi) ~f:(fun d ->
            (d, Logic.Term.fvs_of d))
      in
      let conv t =
        LogicOld.Formula.disjuncts_of @@ LogicOld.Formula.alpha_rename_let
        @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv t
      in
      let census = Option.is_some (Sys.getenv "COAR_NPA_CENSUS") in
      let census_built_size = ref 0 in
      let census_dropped = ref 0 in
      let built = Hashtbl.PolyDeep.create () in
      let images = ref [] in
      Set.iter (Set.Poly.map atms ~f:Logic.Term.fvs_of) ~f:(fun bounds_atm ->
          if not (Set.are_disjoint fvs_phi bounds_atm) then (
            let sub, phis = atom_sub_and_neqs eqcs bounds_atm in
            Array.iteri leaves ~f:(fun i (d, fvs_d) ->
                let sub_d = Map.Poly.filter_keys sub ~f:(Set.mem fvs_d) in
                (* the image's free variables, read off the substitution of
                   variables for variables without building the image *)
                let relevant () =
                  (not (Map.Poly.is_empty sub_d))
                  && Set.exists fvs_d ~f:(fun v ->
                      Set.mem bounds_atm
                        (match Map.Poly.find sub_d v with
                        | Some (Logic.Var (w, _)) -> w
                        | Some _ | None -> v))
                in
                if relevant_only && not (relevant ()) then incr census_dropped
                else
                let key =
                  (i, if restrict then Map.Poly.to_alist sub_d else [])
                in
                if not (Hashtbl.mem built key) then (
                  Hashtbl.set built ~key ~data:();
                  let img = Logic.Term.subst sub_d d in
                  if census then
                    census_built_size :=
                      !census_built_size
                      + Logic.Term.ast_size_up_to 100_000_000 img;
                  images := conv img :: !images));
            List.iter phis ~f:(fun neq -> images := conv neq :: !images)));
      if census then
        eprintf
          "[npa-census] atoms=%d leaves=%d leaf_size=%d images=%d \
           image_size=%d dropped=%d\n\
           %!"
          (Set.length atms) (Array.length leaves)
          (Array.sum (module Int) leaves ~f:(fun (d, _) ->
               Logic.Term.ast_size_up_to 100_000_000 d))
          (Hashtbl.length built) !census_built_size !census_dropped;
      Set.Poly.union_list !images

(* Whether the qualifier extraction can read anything from [phi], one disjunct
   of a clause's normalised pure part, in a clause whose applications of
   unknowns have the variable sets [apps_vars] (pairwise disjoint: the
   normalisation gives every argument of every application a fresh variable)
   and whose unknowns [is_unknown] names.

   Contract: [false] only when every atom the extraction reads off [phi] gives
   no qualifier and adds nothing to what the clause's other atoms give.  The
   extraction reads an atom [a] of a clause as [Evaluator.simplify] of [a]
   back as an atom, and with the variables [vs] of [a] that some application
   binds:
   - by the ordinary rule it offers [a] to an application [p] only when [vs]
     is within [p]'s variables, and to quantified instances only when the
     variables free in the clause are within them too;
   - an atom whose [vs] is empty may be recovered through selectors or offered
     as a ground fact, so it is kept;
   - an atom that mentions an unknown is read differently, so it is kept;
   - a read of an array or a sequence anywhere in the clause decides which
     variables are cell indices, and a write which sequence equalities are
     offered, so a disjunct with a read or a write is kept;
   - an equation or disequation between a variable and a constructor
     application feeds the clause's selector substitution, so it is kept;
   - a disjunct with a [let] is kept, since the extraction reads its atoms
     with the definitions substituted.
   An atom whose [vs] meets two applications is offered to none by the rules
   above: a lifted cell qualifier made from it still names a variable of an
   application other than the one it is offered to, and is dropped where the
   qualifier is mapped onto the parameters.  So the remaining atoms give
   nothing. *)
let image_may_give_a_qualifier ~is_unknown apps_vars phi =
  let open LogicOld in
  (not (Formula.is_let_free phi))
  || (not
        (Set.is_empty
           (Formula.filtered_terms_of phi ~f:(fun t ->
                T_array.is_select t || T_seq.is_nth t || T_seq.is_store t))))
  ||
  let pos, neg = Formula.atoms_of phi in
  Set.exists (Set.union pos neg) ~f:(fun atm ->
      match Formula.to_atom (Evaluator.simplify (Formula.mk_atom atm)) with
      | exception exn_ when not (Common.Timer.is_async exn_) -> false
      | atm -> (
          match atm with
          | Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ t1; t2 ], _)
            when (Term.is_var t1 && T_dt.is_cons t2)
                 || (T_dt.is_cons t1 && Term.is_var t2) ->
              true
          | _ ->
              let tvs = Atom.tvs_of atm in
              Set.exists tvs ~f:is_unknown
              ||
              let vs =
                List.filter apps_vars ~f:(fun app ->
                    not (Set.are_disjoint app tvs))
              in
              List.length vs <= 1))

module Make (Cfg : Config.ConfigType) (APCSP : Problem.ProblemType) :
  GeneratorType = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id
  let print_log = false

  (* a census stamp, read by nothing: with [COAR_EXTRACT_CENSUS] set, the
     time at which the generator's construction passes [label] *)
  let stamp label =
    if Option.is_some (Sys.getenv "COAR_EXTRACT_CENSUS") then
      eprintf "[extract-census] %s at=%.3f\n%!" label (Common.Clock.now_s ())

  let pcsp =
    if config.normalize_pcsp then (
      stamp "normalize-start";
      Debug.print @@ lazy "normalizing pfwCSP for qualifiers extraction";
      let exi_senv = Problem.senv_of APCSP.problem in
      let cls =
        Set.Poly.map
          (Problem.clauses_of APCSP.problem)
          ~f:(Clause.refresh_pvar_args exi_senv)
      in
      stamp "normalize-refreshed";
      (* normalization is essential for qualifiers extraction *)
      let count = ref 0 in
      (* a census line per clause, read by nothing: with [COAR_NPA_CENSUS]
         set, the clause's normalisation time and the major heap after it *)
      let census_clause n f =
        let t0 = Common.Clock.now_s () in
        Exn.protect ~f ~finally:(fun () ->
            if Option.is_some (Sys.getenv "COAR_NPA_CENSUS") then (
              eprintf "[npa-census] clause %d of %d done in %.3f s heap=%d MB\n%!"
                n (Set.length cls)
                (Common.Clock.now_s () -. t0)
                ((Gc.quick_stat ()).heap_words * 8 / 1_000_000);
              (* the live heap, which walks the heap: every 25 clauses *)
              if n mod 25 = 0 then
                eprintf "[npa-census] clause %d live=%d MB\n%!" n
                  ((Gc.stat ()).live_words * 8 / 1_000_000)))
      in
      (* a census of the clauses whose normalisation takes more than
         [COAR_NPA_HEAVY_S] seconds (default 0.5), read by nothing: their
         unknowns, the shape of their pure part and the size of the
         normalised clause; with [COAR_NPA_DUMP] a directory, the clause before
         and after is written there *)
      let census_heavy n secs (ps, ns, phi) (uni_senv', _, _, phi') =
        if Option.is_some (Sys.getenv "COAR_NPA_CENSUS") then
          let bound =
            Option.value_map (Sys.getenv "COAR_NPA_HEAVY_S") ~default:0.5
              ~f:Float.of_string
          in
          if Float.(secs > bound) then (
            let name t =
              match Logic.Term.let_apps t with
              | Logic.Var (Ident.Tvar x, _), args ->
                  sprintf "%s/%d" x (List.length args)
              | _ -> "?"
            in
            let names s =
              String.concat ~sep:" "
              @@ List.map ~f:(fun (x, k) -> sprintf "%s*%d" x k)
              @@ List.map ~f:(fun l -> (List.hd_exn l, List.length l))
              @@ List.group ~break:String.( <> )
              @@ List.sort ~compare:String.compare
              @@ List.map ~f:name @@ Set.to_list s
            in
            let size t = Logic.Term.ast_size_up_to 1_000_000_000 t in
            let phi = Lazy.force phi in
            (* each output atom against the unknowns' variables: an atom whose
               variables bound by the applications lie within ONE
               application's arguments can give that application a qualifier
               by the ordinary rule; one whose variables span two or more
               applications gives none by it *)
            let apps_vars =
              List.map ~f:Logic.Term.fvs_of @@ Set.to_list (Set.union ps ns)
            in
            let bvs = Set.Poly.union_list apps_vars in
            let phi_old =
              Logic.ExtTerm.to_old_fml
                (Problem.senv_of APCSP.problem)
                uni_senv' phi'
            in
            let pos, neg = LogicOld.Formula.atoms_of phi_old in
            let atoms = Set.union pos neg in
            let one = ref 0 and none = ref 0 and many = ref 0 in
            let one_size = ref 0 and many_size = ref 0 in
            Set.iter atoms ~f:(fun atm ->
                let tvs = Set.inter bvs (LogicOld.Atom.tvs_of atm) in
                let sz = LogicOld.Atom.ast_size atm in
                if Set.is_empty tvs then incr none
                else if
                  List.exists apps_vars ~f:(fun vs -> Set.is_subset tvs ~of_:vs)
                then (
                  incr one;
                  one_size := !one_size + sz)
                else (
                  incr many;
                  many_size := !many_size + sz))
            ;
            eprintf
              "[npa-heavy] clause %d out_atoms=%d no_app_var=%d one_app=%d \
               (size %d) several_apps=%d (size %d)\n%!"
              n (Set.length atoms) !none !one !one_size !many !many_size;
            eprintf
              "[npa-heavy] clause %d secs=%.3f ps=%d ns=%d pure_disjuncts=%d \
               pure_size=%d out_disjuncts=%d out_size=%d live=%d MB\n\
               [npa-heavy] clause %d heads: %s\n\
               [npa-heavy] clause %d body: %s\n\
               %!"
              n secs (Set.length ps) (Set.length ns)
              (List.length (Logic.BoolTerm.disjuncts_of phi))
              (size phi)
              (List.length (Logic.BoolTerm.disjuncts_of phi'))
              (size phi')
              ((Gc.stat ()).live_words * 8 / 1_000_000)
              n (names ps) n (names ns);
            match Sys.getenv "COAR_NPA_DUMP" with
            | Some dir ->
                let atoms =
                  String.concat ~sep:"\n"
                  @@ List.map ~f:Logic.ExtTerm.str_of
                  @@ Set.to_list (Set.union ps ns)
                in
                Out_channel.write_all (sprintf "%s/heavy_%d_in.txt" dir n)
                  ~data:(atoms ^ "\n----\n" ^ Logic.ExtTerm.str_of phi);
                Out_channel.write_all (sprintf "%s/heavy_%d_out.txt" dir n)
                  ~data:(Logic.ExtTerm.str_of phi')
            | None -> ())
      in
      let shared f =
        if config.share_normalize_of_clauses then
          Logic.ExtTerm.with_shared_term_conversion @@ fun () ->
          Evaluator.with_shared_simplify @@ fun () ->
          Normalizer.with_shared_normalize @@ fun () ->
          LogicOld.with_shared_let_passes f
        else f ()
      in
      let pcsp =
        Common.PhaseTime.with_phase "normalize-of-clauses" @@ fun () ->
        shared @@ fun () ->
        Problem.of_clauses ~params:(Problem.params_of APCSP.problem)
        @@ Set.Poly.map cls ~f:(fun (uni_senv, ps, ns, phi) ->
            count := !count + 1;
            Debug.print
            @@ lazy
                 (sprintf "normalizing %s clause (out of %d)"
                    (Ordinal.string_of @@ Ordinal.make !count)
                    (Set.length cls)
                    (*(Clause.str_of exi_senv (uni_senv, ps, ns, phi))*));
            (* assume that [phi] is alpha-renamed *)
            if print_log then (
              print_endline "begin";
              Out_channel.flush stdout);
            Common.PhaseTime.with_phase "normalize-clause" @@ fun () ->
            census_clause !count @@ fun () ->
            let phi =
              Common.PhaseTime.with_phase "let" @@ fun () ->
              Normalizer.normalize_let
              @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi
            in
            let uni_senv =
              (* Map.force_merge (Logic.Term.let_sort_env_of @@ Logic.ExtTerm.of_old_formula phi) *)
              uni_senv
            in
            if print_log then print_endline "let-normalized";
            let census_t0 = Common.Clock.now_s () in
            let res =
              let senv = Map.force_merge exi_senv uni_senv in
              let atms = Set.union ps ns in
              let phi0, uni_senv, phi, eqcs =
                let bounds =
                  let fvs = Set.concat_map ~f:Logic.Term.fvs_of atms in
                  Map.Poly.filter_keys senv ~f:(Set.mem fvs)
                in
                let uni_senv_phi, _, phi =
                  if
                    false
                    (*Map.Poly.exists ~f:Logic.Sort.is_arrow
                    @@ Logic.Term.let_sort_env_of
                    @@ Logic.ExtTerm.of_old_formula phi*)
                  then (uni_senv, [], Logic.ExtTerm.of_old_formula phi)
                  else
                    Common.PhaseTime.with_phase "free-univ" @@ fun () ->
                    Qelim.elim_free_univ_vars ~simplify:false bounds exi_senv
                      (uni_senv, [], Logic.ExtTerm.of_old_formula phi)
                in
                let eqcs, phis =
                  Common.PhaseTime.with_phase "eqcs" @@ fun () ->
                  Qelim.eqcs_of
                    phi (*~only_bvs:(Some (Map.Poly.key_set bounds))*)
                in
                if print_log then print_endline "formula QEed";
                ( phi,
                  Map.force_merge bounds uni_senv_phi,
                  Logic.ExtTerm.or_of phis,
                  eqcs )
              in
              let phi =
                if Set.length ps + Set.length ns = 1 then
                  Evaluator.simplify
                  @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi0
                else
                  Common.PhaseTime.with_phase "per-atom" @@ fun () ->
                  let fvs_phi = Logic.Term.fvs_of phi in
                  (* the copies are built before the pure part and the
                     disequalities are converted; keep this order, since the
                     conversions can draw fresh names and a run's later names
                     depend on the order of the draws *)
                  let images =
                    if config.normalize_per_atom_by_disjunct then
                      Common.PhaseTime.with_phase "by-disjunct" @@ fun () ->
                      per_atom_disjuncts_by_disjunct
                        ~relevant_only:config.normalize_per_atom_relevant_only
                        exi_senv uni_senv atms fvs_phi phi eqcs
                    else
                      per_atom_disjuncts_whole exi_senv uni_senv atms fvs_phi
                        phi eqcs
                  in
                  let phi_old = Logic.ExtTerm.to_old_fml exi_senv uni_senv phi in
                  let neqs =
                    Set.concat_map eqcs ~f:(fun (eqc, ty) ->
                        match Set.to_list eqc with
                        | [] -> assert false
                        | v :: vs ->
                            let s = Logic.ExtTerm.to_old_sort ty in
                            Set.Poly.of_list
                            @@ List.map vs ~f:(fun v' ->
                                LogicOld.(
                                  Formula.neq (Term.mk_var v s)
                                    (Term.mk_var v' s))))
                  in
                  let base = Set.add neqs phi_old in
                  if print_log then print_endline "qelimed";
                  let disjs =
                    Common.PhaseTime.with_phase "simplify" @@ fun () ->
                    if not config.normalize_per_atom_extractable_only then
                      Set.Poly.map (Set.union base images) ~f:Evaluator.simplify
                      (*Z3Smt.Z3interface.simplify (Problem.fenv_of APCSP.problem)*)
                    else
                      (* the same set as above with the copies the extraction
                         reads nothing from left out: the simplified base is
                         kept whole, and a copy is tested as simplified *)
                      let apps_vars =
                        List.map ~f:Logic.Term.fvs_of @@ Set.to_list atms
                      in
                      let is_unknown = Map.Poly.mem exi_senv in
                      let dropped = ref 0 in
                      let kept =
                        Set.Poly.filter_map (Set.diff images base) ~f:(fun d ->
                            let d = Evaluator.simplify d in
                            if
                              image_may_give_a_qualifier ~is_unknown apps_vars d
                            then Some d
                            else (
                              incr dropped;
                              None))
                      in
                      if Option.is_some (Sys.getenv "COAR_NPA_CENSUS") then
                        eprintf "[npa-census] extractable-only kept=%d dropped=%d\n%!"
                          (Set.length kept) !dropped;
                      Set.union (Set.Poly.map base ~f:Evaluator.simplify) kept
                  in
                  (* Formula.elim_ite @@ Formula.elim_let_equivalid @@ Formula.elim_let @@ *)
                  Normalizer.normalize_let @@ LogicOld.Formula.or_of
                  @@ Set.to_list disjs
              in
              if print_log then
                print_endline
                  (if true then "simplified"
                   else sprintf "simplified: %s" (Formula.str_of phi));
              if print_log then print_endline "end";
              Clause.reduce_sort_map
                (uni_senv, ps, ns, Logic.ExtTerm.of_old_formula phi)
            in
            census_heavy !count (Common.Clock.now_s () -. census_t0)
              (ps, ns, lazy (Logic.ExtTerm.of_old_formula phi)) res;
            res)
      in
      (*Debug.print @@ lazy (Problem.str_of pcsp);*)
      (* the normalization above distributes, so a premise that reached it as one
         disjunct can leave it as several alpha-variants of one another; they
         would each be walked for every qualifier of every atom *)
      stamp "normalize-built";
      if Option.is_some (Sys.getenv "COAR_NPA_CENSUS") then
        eprintf "[npa-census] built live=%d MB\n%!"
          ((Gc.stat ()).live_words * 8 / 1_000_000);
      let pcsp =
        if config.dedup_alpha_equivalent_disjuncts then
          Common.PhaseTime.with_phase "normalize-dedup" @@ fun () ->
          Problem.dedup_alpha_equivalent_disjuncts ~print:(Debug.print ~id) pcsp
        else pcsp
      in
      if Option.is_some (Sys.getenv "COAR_NPA_CENSUS") then
        eprintf "[npa-census] deduped live=%d MB\n%!"
          ((Gc.stat ()).live_words * 8 / 1_000_000);
      pcsp)
    else APCSP.problem

  let normalized_problem = pcsp

  let rec module_of_domain = function
    | Config.Null -> (module Null : QualifierType)
    | Interval -> (module Interval : QualifierType)
    | Octagon -> (module Octagon : QualifierType)
    | Octahedron -> (module Octahedron : QualifierType)
    | Polyhedron ub ->
        (module Polyhedron.Make (struct
          let upper_bound = ub
        end) : QualifierType)
    | Polynomial -> (module Polynomial : QualifierType)
    | SVM (approx_level, csvm) ->
        (module SVM.Make (struct
          let approx_level = approx_level
          let csvm = csvm
        end) : QualifierType)
    | NN dummy_param ->
        (module NN.Make (struct
          let dummy_param = dummy_param
        end) : QualifierType)
    | Union ds ->
        (module Union.Make (struct
          let domains = List.map ds ~f:module_of_domain
        end) : QualifierType)

  let domains = List.map config.domains ~f:module_of_domain

  let elim_neg =
    if config.filter_out_neg then
      Set.fold ~init:Set.Poly.empty ~f:(fun quals q ->
          if Set.mem quals (Qual.neg q) then quals else Set.add quals q)
    else Fn.id

  (* whether [phi] is a clause's disjunction about a cell
     ([lift_clause_cell_disjunctions]): no other extracted qualifier is a
     quantifier-free cell schema that is not an atom, since the per-atom
     liftings return atoms *)
  let is_clause_cell_disjunction phi =
    config.lift_clause_cell_disjunctions
    && (not (Formula.is_atom phi))
    && Formula.is_quantifier_free phi
    && CellQual.mentions_placeholder phi

  let qelim_quals =
    List.map ~f:(fun (pa, quals) ->
        Debug.print
        @@ lazy
             (sprintf "eliminating quantifiers in qualifiers for %s"
                (Ident.name_of_pvar pa));
        ( pa,
          Set.fold quals ~init:Set.Poly.empty ~f:(fun acc (ids, phi) ->
              (* a quantifier-free cell schema that is not an atom can only be a
                 clause's disjunction about a cell
                 ([lift_clause_cell_disjunctions]); the qualifier is the whole
                 disjunction, so it is not split into its atoms below, and it
                 has no quantifier to eliminate *)
              if is_clause_cell_disjunction phi then Set.add acc (ids, phi)
              else (
              if print_log then
                Debug.print
                @@ lazy ("qualifier before qelim: " ^ Formula.str_of phi);
              let fenv = Problem.fenv_of pcsp in
              let phi' =
                if
                  (* What the eliminator would be asked to remove is what the
                     formula QUANTIFIES, and [sort_env_of] cannot say: it is
                     built on the free environment, whose binder case subtracts
                     exactly these.  So this test used to look at the free
                     variables and let a quantified one of the same sort
                     through.  A sequence-sorted one is what matters: the
                     tactic neither eliminates it nor gives up, and the call
                     does not return at all -- a ten-line satisfiable problem
                     whose only quantifier is over a sequence is not answered
                     at 180 s, and the whole of it is spent here. *)
                  (* whether a query can come back at all is one question
                     and is answered beside the solver entry points, so that
                     the ten callers that ask it cannot drift apart again.
                     It has two arms and only one of them is about binders:
                     over regular expressions the hazard is an OCCURRENCE,
                     free or bound, because no budget and no cancellation
                     call holds there and only killing the process ends such
                     a query *)
                  Z3Smt.Z3interface.may_not_return phi
                  (* and one this caller alone has: an arrow-sorted variable
                     left FREE is not something a quantifier binds, so the
                     shared test does not look for it, while [qelim] over one
                     is still useless here *)
                  || Set.exists ~f:(snd >> Sort.is_arrow)
                       (Formula.sort_env_of phi)
                then phi
                else
                  (*Normalizer.normalize @@ Evaluator.simplify @@*)
                  try
                    Common.PhaseTime.with_phase "qelim" (fun () ->
                        Z3Smt.Z3interface.qelim ~timeout:(Some 1000)
                          ~id:(Problem.id_of pcsp) ~fenv phi)
                  with
                  | exn_ when not (Common.Timer.is_async exn_) ->
                      (* The tactic accepts theories it cannot eliminate over
                         and does not report that: for a sequence it returns a
                         goal that still mentions one, which the reader of the
                         result cannot convert and raises on, ending the whole
                         run with an exception instead of a verdict.  Keeping
                         the qualifier unchanged is what the arrow-sort test
                         above already does, and the quantified-qualifier check
                         below is what decides whether it is usable, so this
                         adds no case downstream.  Caught here rather than
                         inside the elimination because that function's other
                         callers read its result as quantifier-free, and a
                         fourth silent identity return would widen that.  An
                         entry test cannot replace it: the sort that cannot be
                         read may occur only under a binder or inside a
                         datatype's instantiation -- a qualifier
                         [forall (q1 q2 : seq(int)). x <> mut<Seq<Int>> q1 q2]
                         has no free variable of sequence sort and no sequence
                         function symbol at all. *)
                      Debug.print
                      @@ lazy
                           (sprintf
                              "qelim could not be read back (%s); keeping the \
                               qualifier unchanged"
                              (Exn.to_string exn_));
                      phi
              in
              if print_log then
                Debug.print
                @@ lazy ("qualifier after qelim: " ^ Formula.str_of phi');
              if config.filter_out_quantified && Formula.is_bind (*ToDo*) phi'
              then acc
              else
                (* [atoms_of] also returns atoms that sit under a binder --
                   inside a [T_array.ALambda] body, or under a quantifier that
                   [qelim] could not remove.  Taking such an atom as a
                   standalone qualifier frees the variable it bound, and the
                   qualifier then escapes the parameters of whatever hole it is
                   attached to.  Keep only the atoms whose variables are free in
                   the formula they came from. *)
                let fvs = Formula.tvs_of phi' in
                Set.union acc
                @@ Set.Poly.filter_map ~f:(fun atm ->
                    if Set.is_subset (Atom.tvs_of atm) ~of_:fvs then
                      Some (ids (*ToDo*), Formula.mk_atom atm)
                    else None)
                @@ Tuple2.uncurry Set.union @@ Formula.atoms_of phi')) ))

  (* Putting a clause in Horn form replaces an argument of an unknown that is
     not a variable by a fresh variable and adds an equation binding it, so a
     clause about [p (mut c f)] reads [u != mut c f \/ ... \/ p u ...].  Every
     candidate qualifier built from that clause then mentions [c] and [f], which
     are not arguments of the unknown, and the extraction below drops it -- so a
     loop invariant that has to speak about the parts of such an argument has no
     qualifier to build from at all.  On a Rust-derived problem, where a mutable
     reference is encoded as a two-field value carrying its current and its final
     contents, that is every interesting qualifier: one such clause set dropped
     296 candidates, among them the equation between the two field lengths that
     the invariant needs.

     The clause's own equation says what the parts are.  When the constructor
     belongs to a datatype with exactly one constructor, its selectors are total
     and fixed by the theory, so the equation [u = mut c f] gives [c = mut_current u]
     and [f = mut_final u], and rewriting a candidate that way turns it into an
     atom about the argument.  This must not be done for a datatype with several
     constructors: there a selector is partial, [sel u] for a [u] built by
     another constructor denotes a value the theory leaves open, and an atom
     about it says less than it appears to.  By default only the direct
     variable arguments of the constructor are recovered; [nested_selector_subst]
     also follows arguments built by further single-constructor constructors. *)
  let selector_subst_of_clause atomics bvars =
    List.fold atomics ~init:Map.Poly.empty ~f:(fun sub atomic ->
        match atomic with
        | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) -> (
            (* the clause is a disjunction, so a premise equality appears
               negated; an equality among the disjuncts is a conclusion and says
               nothing about the arguments *)
            let arg_and_cons =
              match (t1, t2) with
              | Term.Var (u, _, _), (Term.FunApp (T_dt.DTCons _, _, _) as c)
              | (Term.FunApp (T_dt.DTCons _, _, _) as c), Term.Var (u, _, _) ->
                  Some (u, c)
              | _ -> None
            in
            match arg_and_cons with
            | Some (u, Term.FunApp (T_dt.DTCons (cname, _, dt), args, _))
              when Set.mem bvars u
                   && List.length (Datatype.conses_of dt) = 1
                   && List.length args
                      = List.length (T_dt.sels_of_cons (T_dt.DTCons (cname, [], dt)))
              ->
                let usort = T_dt.SDT dt in
                if not config.nested_selector_subst then
                  List.foldi args ~init:sub ~f:(fun i sub arg ->
                      match arg with
                      | Term.Var (y, _, _) when not (Set.mem bvars y) ->
                          Map.Poly.set sub ~key:y
                            ~data:
                              (T_dt.mk_sel_by_cons dt cname i
                              @@ Term.mk_var u usort)
                      | _ -> sub)
                else
                  (* [base] is a term denoting the value built by
                     [cons(args)]; each argument is then the corresponding
                     total selector applied to [base].  A variable argument is
                     recorded, and an argument that is itself built by the only
                     constructor of its datatype is descended into.  Anything
                     else -- a constructor of a datatype with several
                     constructors, whose selectors are partial, or a term that
                     is not a constructor -- contributes nothing. *)
                  let rec descend sub base dt cname args =
                    List.foldi args ~init:sub ~f:(fun i sub arg ->
                        let sel = T_dt.mk_sel_by_cons dt cname i base in
                        match arg with
                        | Term.Var (y, _, _) when not (Set.mem bvars y) ->
                            Map.Poly.set sub ~key:y ~data:sel
                        | Term.FunApp (T_dt.DTCons (cname', _, dt'), args', _)
                          when List.length (Datatype.conses_of dt') = 1
                               && List.length args'
                                  = List.length
                                      (T_dt.sels_of_cons
                                         (T_dt.DTCons (cname', [], dt'))) ->
                            descend sub sel dt' cname' args'
                        | _ -> sub)
                  in
                  descend sub (Term.mk_var u usort) dt cname args
            | _ -> sub)
        | _ -> sub)

  (* A census of the extraction, read by nothing: with [COAR_EXTRACT_CENSUS]
     set, one line on stderr per clause (its size, the atoms
     [psym_pvar_apps_of] splits it into, the candidate pairs it added and the
     time it took), one line with the pairs collected before they are grouped
     by unknown, and per unknown the qualifier count before and after the
     quantifier elimination.  Without the variable each hook is the identity
     apart from the clause's phase, which the phase report counts. *)
  module ExtractCensus = struct
    (* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
    let on = Lazy.from_val (Option.is_some (Sys.getenv "COAR_EXTRACT_CENSUS"))
    let n = ref 0

    let clause phi acc k =
      Common.PhaseTime.with_phase "clause" @@ fun () ->
      if not (Lazy.force on) then k acc
      else (
        incr n;
        if !n = 1 then
          eprintf "[extract-census] first-clause at=%.3f\n%!"
            (Common.Clock.now_s ());
        let t0 = Common.Clock.now_s () in
        let before = Set.length acc in
        let acc' = k acc in
        let atomics, pos, neg =
          Formula.psym_pvar_apps_of ~simplifier:Fn.id phi
        in
        eprintf
          "[extract-census] clause=%d size=%d atomics=%d pos=%d neg=%d \
           added=%d secs=%.3f\n%!"
          !n (Formula.ast_size phi) (List.length atomics) (List.length pos)
          (List.length neg)
          (Set.length acc' - before)
          (Common.Clock.now_s () -. t0);
        acc')

    (* [first_instance tbl key]: whether [key] is new to [tbl] (and records
       it); with the census on, the hits and misses are counted *)
    let hits = ref 0
    let misses = ref 0

    let first_instance tbl key =
      match Hashtbl.add tbl ~key ~data:() with
      | `Ok ->
          incr misses;
          true
      | `Duplicate ->
          incr hits;
          false

    (* quantified qualifiers built, over the run *)
    let nbuilt = ref 0
    let built () = if Lazy.force on then incr nbuilt

    let pairs acc =
      if Lazy.force on then
        eprintf
          "[extract-census] pairs=%d built=%d inst_hits=%d inst_misses=%d at=%.3f\n%!"
          (Set.length acc) !nbuilt !hits !misses (Common.Clock.now_s ());
      acc

    let quals label groups =
      if Lazy.force on then
        eprintf "[extract-census] %s at=%.3f\n%!" label (Common.Clock.now_s ());
      if Lazy.force on then
        List.iter groups ~f:(fun (pv, qs) ->
            eprintf "[extract-census] %s pvar=%s quals=%d\n%!" label
              (Ident.name_of_pvar pv) (Set.length qs));
      groups
  end

  let add_ineqs_for_eqs = false

  let extract pcsp =
    stamp "extract-start";
    (* whether any qualifier here can mention a cell column *)
    let lifts =
      config.lift_index_quals || config.lift_read_quals
      || config.lift_clause_cell_disjunctions
    in
    let cls =
      Common.PhaseTime.with_phase "formulas" @@ fun () ->
      Set.Poly.map (Problem.formulas_of pcsp)
        ~f:(Tuple2.uncurry @@ Logic.ExtTerm.to_old_fml (Problem.senv_of pcsp))
    in
    stamp "extract-formulas";
    (* the (unknown, argument position) pairs [offset_parity_quals] asks for *)
    let parity_positions =
      if not config.offset_parity_quals then Set.Poly.empty
      else
        let const_offset t1 t2 =
          if not (Term.is_int_sort (Term.sort_of t1)) then None
          else
            (* the difference as a linear sum: an offset when only the
               constant monomial is left, kept in [Z] since it is a term's
               constant of any size *)
            match
              Normalizer.linear_int_monomials_of (Value.Int Z.one)
                (T_int.mk_sub t1 t2)
            with
            | monos
              when Map.Poly.for_alli monos ~f:(fun ~key ~data:_ ->
                       Option.is_none key) -> (
                match Map.Poly.find monos None with
                | Some (Value.Int c) when not (Z.equal c Z.zero) -> Some c
                | _ -> None)
            | _ -> None
            | exception exn_ when not (Common.Timer.is_async exn_) -> None
        in
        let apps_of atoms =
          List.filter_map atoms ~f:(function
            | Atom.App (Predicate.Var (pv, _), args, _) -> Some (pv, args)
            | _ -> None)
        in
        (* read from the problem as given, not from its normalised copy
           [cls]: the normalisation replaces every argument of an unknown by a
           fresh variable and an equation, which hides the offsets *)
        let cls0 =
          Set.Poly.map (Problem.formulas_of APCSP.problem)
            ~f:
              (Tuple2.uncurry
              @@ Logic.ExtTerm.to_old_fml (Problem.senv_of APCSP.problem))
        in
        Set.fold cls0 ~init:Set.Poly.empty ~f:(fun acc phi ->
            let pos_papps, neg_papps =
              if config.parity_pvar_apps_only then
                Formula.pvar_apps_of ~simplifier:Evaluator.simplify phi
              else
                let _, pos, neg =
                  Formula.psym_pvar_apps_of ~simplifier:Evaluator.simplify phi
                in
                (pos, neg)
            in
            let heads = apps_of pos_papps and bodies = apps_of neg_papps in
            let pairs ~ok xs ys =
              List.concat_map xs ~f:(fun (p1, a1) ->
                  List.concat_map ys ~f:(fun (p2, a2) ->
                      if
                        (not (Ident.pvar_equal p1 p2))
                        || List.length a1 <> List.length a2
                      then []
                      else
                        List.filter_mapi (List.zip_exn a1 a2)
                          ~f:(fun i (t1, t2) ->
                            match const_offset t1 t2 with
                            | Some c when ok c -> Some (p1, i)
                            | _ -> None)))
            in
            let within_premise =
              let rec go = function
                | [] -> []
                | x :: rest -> pairs ~ok:(fun _ -> true) [ x ] rest @ go rest
              in
              go bodies
            in
            let step = pairs ~ok:Z.is_even heads bodies in
            Debug.print
            @@ lazy
                 (sprintf "[parity] clause %s: %d premise pair(s), %d step(s)"
                    (Formula.str_of phi) (List.length within_premise)
                    (List.length step));
            Set.union acc (Set.Poly.of_list (within_premise @ step)))
    in
    let count = ref 0 in
    Set.fold cls ~init:Set.Poly.empty ~f:(fun acc phi ->
        ExtractCensus.clause phi acc @@ fun acc ->
        count := !count + 1;
        Debug.print
        @@ lazy
             (sprintf "extracting from %s clause (out of %d): %s"
                (Ordinal.string_of @@ Ordinal.make !count)
                (Set.length cls) (Formula.str_of phi));
        if print_log then
          print_endline @@ sprintf "extract phi: %s" @@ Formula.str_of phi;
        let atomics, pos_papps, neg_papps =
          Common.PhaseTime.with_phase "apps" @@ fun () ->
          Formula.psym_pvar_apps_of ~simplifier:Evaluator.simplify phi
        in
        (* a variable of an atom that is not free in the clause is bound by a
           quantifier inside it *)
        let clause_fvs = Formula.tvs_of phi in
        let pos_papp_tvs =
          List.map pos_papps ~f:(fun a -> (a, Atom.term_sort_env_of (*ToDo*) a))
        in
        let neg_papp_tvs =
          List.map neg_papps ~f:(fun a -> (a, Atom.term_sort_env_of (*ToDo*) a))
        in
        let bvs =
          Set.Poly.union_list @@ List.map ~f:snd @@ pos_papp_tvs @ neg_papp_tvs
        in
        if print_log then
          print_endline @@ sprintf "bvs: %s"
          @@ String.concat_map_set ~sep:", " bvs ~f:(fst >> Ident.name_of_tvar);
        let sel_sub =
          selector_subst_of_clause atomics (Set.Poly.map bvs ~f:fst)
        in
        (* the (application, canonical atom) pairs instantiated so far in
           this clause ([instantiate_quals_memo]) *)
        let inst_seen = Hashtbl.PolyDeep.create () in
        (* Which clause variables index a read of an array that an unknown of
           this clause is applied to, and where those reads are.  This is a
           property of the CLAUSE and not of the atom being lifted: [0 <= j]
           says nothing about an array by itself, and what makes it a statement
           about a cell is that [j] indexes [a] somewhere in the same clause.
           Only integer indices and integer elements are collected, because
           that is the shape of the cell columns a template generates today. *)
        let bvars = Set.Poly.map bvs ~f:fst in
        (* The array a read is of need not be a variable: a clause derived
           from a program with structured values writes [select (proj x) i],
           where the array is a field of an argument.  The read is kept when
           that access path starts at a variable the unknowns are applied to,
           and the columns are then named for the path -- the same name the
           template gives them, which is the only thing making the two halves
           of this mechanism talk about the same array. *)
        let rec access_path t =
          match t with
          | Term.Var (a, _, _) -> if Set.mem bvars a then Some (a, []) else None
          | Term.FunApp (T_dt.DTSel (name, _, _), [ arg ], _) ->
              Option.map (access_path arg) ~f:(fun (a, sels) -> (a, sels @ [ name ]))
          | _ -> None
        in
        let cell_reads =
          if not lifts then Set.Poly.empty
          else
            Set.Poly.filter_map
              (Formula.filtered_terms_of ~f:T_array.is_select phi)
              ~f:(function
                | Term.FunApp (T_array.ASelect (si, se), [ arr; idx ], _) as t
                  when Term.is_int_sort si && Term.is_int_sort se -> (
                    match access_path arr with
                    | Some (a, sels) ->
                        Some (Ident.Tvar (CellQual.path_name a sels), idx, t)
                    | None -> None)
                | _ -> None)
        in
        (* the sequence reads of this clause, collected the same way; see
           [CellQual.seq_nth_read] for what makes a read eligible *)
        let seq_reads =
          if not (lifts && config.lift_seq_nth_quals) then Set.Poly.empty
          else
            Set.Poly.filter_map
              (Formula.filtered_terms_of ~f:T_seq.is_nth phi)
              ~f:(CellQual.seq_nth_read ~access_path)
        in
        let cell_reads = Set.union cell_reads seq_reads in
        (* a lifted qualifier may not keep a sequence read, which would be one
           without the range premise; only checked with the switch on, so that
           the array liftings are unchanged without it *)
        let keeps_seq_read_atom atm =
          config.lift_seq_nth_quals && CellQual.mentions_seq_read_atom atm
        in
        let keeps_seq_read_atom_formula q =
          config.lift_seq_nth_quals && CellQual.mentions_seq_read q
        in
        (* The equalities relating an unknown's sequence arguments by a write
           this clause performs; see [CellQual.seq_store_equalities]. *)
        let acc =
          if not config.seq_store_equality_quals then acc
          else
            let stores =
              Set.to_list @@ Formula.filtered_terms_of ~f:T_seq.is_store phi
            in
            if List.is_empty stores then acc
            else
              List.fold (pos_papp_tvs @ neg_papp_tvs) ~init:acc
                ~f:(fun acc (pa, pftv) ->
                  List.fold
                    (CellQual.seq_store_equalities ~args:(Set.to_list pftv)
                       stores)
                    ~init:acc
                    ~f:(fun acc q ->
                      Debug.print
                      @@ lazy
                           (sprintf "sequence write qualifier of %s: %s"
                              (Atom.str_of pa) (Formula.str_of q));
                      Set.add acc (pa, q)))
        in
        (* the out-of-scope variables that a cell's index column can stand for,
           each with the arrays it indexes *)
        let cell_index_vars =
          Set.fold cell_reads ~init:Map.Poly.empty ~f:(fun acc (a, idx, _) ->
              match idx with
              | Term.Var (j, _, _) when not (Set.mem bvars j) ->
                  Map.Poly.update acc j ~f:(function
                    | None -> Set.Poly.singleton a
                    | Some s -> Set.add s a)
              | _ -> acc)
        in
        (* the clause's disjunction about one cell, offered whole to the
           unknowns applied to the array (see [CellQual.clause_cell_disjunctions]) *)
        let acc =
          if not config.lift_clause_cell_disjunctions then acc
          else
            List.fold
              (CellQual.clause_cell_disjunctions ~bvars
                 ~reads:(Set.to_list cell_reads) phi)
              ~init:acc
              ~f:(fun acc (a, q) ->
                if keeps_seq_read_atom_formula q then acc
                else
                  let base =
                    Ident.Tvar
                      (List.hd_exn @@ String.split ~on:'.' (Ident.name_of_tvar a))
                  in
                  List.fold (pos_papp_tvs @ neg_papp_tvs) ~init:acc
                    ~f:(fun acc (pa, pftv) ->
                      if not (Set.mem (Set.Poly.map pftv ~f:fst) base) then acc
                      else (
                        Debug.print
                        @@ lazy
                             (sprintf
                                "clause cell disjunction of %s: %s"
                                (Atom.str_of pa) (Formula.str_of q));
                        Set.add acc (pa, q))))
        in
        (* (* assume that [phi] is alpha-renamed *)
           let lenv = Formula.let_env_of phi in *)
        Common.PhaseTime.with_phase "atoms" @@ fun () ->
        List.fold atomics ~init:acc ~f:(fun acc atomic ->
            let tvs = Atom.sort_env_of atomic in
            if print_log then (
              print_endline @@ sprintf "extract atom: %s" @@ Atom.str_of atomic;
              print_endline @@ sprintf "tvs: %s"
              @@ String.concat_map_set ~sep:", " tvs
                   ~f:(fst >> Ident.name_of_tvar));
            let fvs = Set.diff tvs bvs in
            (* An atom under a quantifier *inside* the clause -- the premise
               [forall c. p(c) \/ p(c + 1)] of a specification, say -- mentions
               the bound variable and nothing the unknown is applied to, so the
               test below drops it and the hypothesis space never contains a
               qualifier about that predicate.  The obligation it supports is at
               the clause's own index, so the atom instantiated at the unknown's
               arguments is exactly the qualifier that is missing: from
               [p(c)] and [p(c + 1)] with [c := x1] come [x2[x1]] and
               [x2[x1 + 1]].  Instantiating is always safe -- a qualifier is a
               candidate building block, and every candidate is validated -- so
               the only cost is a larger hypothesis space, which is why the
               atom's other variables must already be the unknown's arguments
               and why the number of bound variables is capped. *)
            let acc =
              Common.PhaseTime.with_phase "instantiate" @@ fun () ->
              if (not config.instantiate_quantified_quals) || Set.is_empty tvs
              then acc
              else
                let qvs =
                  Set.filter tvs ~f:(fst >> Set.mem clause_fvs >> not)
                in
                if Set.is_empty qvs then acc
                else if Set.length qvs > 2 then (
                  Debug.print
                  @@ lazy
                       (sprintf
                          "dropping %s: %d variables bound inside the clause, \
                           more than the two this instantiates"
                          (Atom.str_of atomic) (Set.length qvs));
                  acc)
                else
                  (* [instantiate_quals_memo]: the instances of [atomic] at
                     [pa] depend on [atomic] only up to a renaming of [qvs],
                     since each bound variable ranges independently over the
                     arguments of its sort; so an atom equal to one already
                     instantiated at [pa] once its bound variables are named
                     canonically (in the order of [qvs]) adds nothing *)
                  let canon =
                    lazy
                      (Atom.subst
                         (Map.Poly.of_alist_exn
                         @@ List.mapi (Set.to_list qvs) ~f:(fun i (v, sort) ->
                                ( v,
                                  Term.mk_var
                                    (Ident.Tvar (sprintf "#iq%d" i))
                                    sort )))
                         atomic)
                  in
                  List.fold (pos_papp_tvs @ neg_papp_tvs) ~init:acc
                    ~f:(fun acc (pa, pftv) ->
                      let args = Set.Poly.map pftv ~f:fst in
                      if
                        config.instantiate_quals_memo
                        && not
                             (ExtractCensus.first_instance inst_seen
                                (pa, Lazy.force canon))
                      then acc
                      else if
                        (* everything but the bound variables must already be an
                           argument of this unknown *)
                        Fn.non
                          (Set.is_subset
                             ~of_:(Set.union args @@ Set.Poly.map qvs ~f:fst))
                          (Set.Poly.map tvs ~f:fst)
                      then acc
                      else
                        let subs =
                          Set.fold qvs ~init:[ Map.Poly.empty ]
                            ~f:(fun subs (v, sort) ->
                              List.concat_map subs ~f:(fun sub ->
                                  List.filter_map (Set.to_list pftv)
                                    ~f:(fun (a, asort) ->
                                      if Stdlib.(sort = asort) then
                                        Some
                                          (Map.Poly.set sub ~key:v
                                             ~data:(Term.mk_var a sort))
                                      else None)))
                        in
                        List.fold subs ~init:acc ~f:(fun acc sub ->
                            if Map.Poly.is_empty sub then acc
                            else
                              let atm = Atom.subst sub atomic in
                              if
                                Set.is_subset (Atom.tvs_of atm) ~of_:args
                                && Set.is_empty
                                   @@ Set.inter args
                                        (Set.concat_map (Atom.div_rem_of atm)
                                           ~f:(fun (t1, t2) ->
                                             Set.union (Term.fvs_of t1)
                                               (Term.fvs_of t2)))
                              then Set.add acc (pa, Evaluator.simplify_atom atm)
                              else acc))
            in
            (* Lift an atom about an array's CONTENTS to one about that
               array's cell columns.  The ordinary rule below keeps an atom
               only when every variable it mentions is an argument of an
               unknown here, so the atoms that say what an array holds are
               exactly the ones it drops: in
               [0 <= j /\ j <= i /\ I(a, i, bound) /\ a[j] > bound => bot]
               the invariant takes [a], [i] and [bound] and the three atoms
               that state the obligation all mention [j].  A predicate whose
               parameters carry (index, value) cells can state them about a
               cell, and the rewriting is a renaming: [j] IS the cell's index,
               so [0 <= #cidx], [#cidx <= i] and [#cval > bound] come out
               without any equation relating the two. *)
            let acc =
              Common.PhaseTime.with_phase "lift" @@ fun () ->
              if not lifts then acc
              else
                (* [a] names an access path, so the unknown to offer the
                   qualifier to is the one applied to the variable that path
                   starts at *)
                let unknowns_with a =
                  let base =
                    Ident.Tvar
                      (List.hd_exn
                      @@ String.split ~on:'.' (Ident.name_of_tvar a))
                  in
                  List.filter (pos_papp_tvs @ neg_papp_tvs) ~f:(fun (_, pftv) ->
                      Set.mem (Set.Poly.map pftv ~f:fst) base)
                in
                let emit acc a lifted =
                  List.fold (unknowns_with a) ~init:acc ~f:(fun acc (pa, _) ->
                      Debug.print
                      @@ lazy
                           (sprintf "lifted %s to a cell qualifier of %s: %s"
                              (Atom.str_of atomic) (Atom.str_of pa)
                              (Formula.str_of lifted));
                      Set.add acc (pa, lifted))
                in
                let acc =
                  if
                    (not config.lift_index_quals)
                    || Set.is_empty fvs
                    || Set.length fvs > config.lift_index_quals_max_vars
                  then acc
                  else
                    (* every out-of-scope variable of the atom must be a read
                       index, and of one array in common *)
                    match
                      Set.fold fvs ~init:None ~f:(fun acc (v, _) ->
                          let here =
                            Option.value ~default:Set.Poly.empty
                            @@ Map.Poly.find cell_index_vars v
                          in
                          match acc with
                          | None -> Some here
                          | Some s -> Some (Set.inter s here))
                    with
                    | None -> acc
                    | Some arrays ->
                        Set.fold arrays ~init:acc ~f:(fun acc a ->
                            let atm =
                              Atom.map_term_no_binders atomic ~f:(function
                                | Term.FunApp
                                    ( T_array.ASelect _,
                                      [ Term.Var (a', _, _); Term.Var (j, _, _) ],
                                      _ )
                                  when Ident.tvar_equal a a'
                                       && Set.exists fvs
                                            ~f:(fst >> Ident.tvar_equal j) ->
                                    CellQual.val_term a T_int.SInt
                                | t -> t)
                            in
                            (* the sequence reads of [a] at an out-of-scope
                               index become the value column too, and the
                               out-of-scope variables become the index column;
                               with no sequence read collected this is the
                               renaming alone *)
                            let atm =
                              CellQual.lift_seq_index_atom
                                ~reads:(Set.to_list seq_reads)
                                ~out_of_scope:
                                  (List.map (Set.to_list fvs) ~f:fst)
                                a atm
                            in
                            (* a read at a term this predicate cannot name, or
                               a second out-of-scope variable that is not an
                               index, leaves a variable behind; such an atom
                               says nothing the template could evaluate.  A
                               sequence read left behind would be one without
                               its range premise. *)
                            if
                              Set.exists (Atom.tvs_of atm) ~f:(fun v ->
                                  (not (Set.mem bvars v))
                                  && not (CellQual.is_placeholder v))
                              || keeps_seq_read_atom atm
                            then acc
                            else emit acc a @@ Evaluator.simplify_atom atm)
                in
                (* The guarded form: an atom that reads an in-scope array at a
                   term the predicate already takes is a qualifier as it
                   stands, but a celled example carries no array to read, so
                   the same fact has to be available about a cell. *)
                if (not config.lift_read_quals) || not (Set.is_empty fvs) then
                  acc
                else
                  let here =
                    Atom.filtered_terms_of
                      ~f:(fun t ->
                        T_array.is_select t
                        || (config.lift_seq_nth_quals && T_seq.is_nth t))
                      atomic
                  in
                  (* Every read in the atom is replaced at once, one per
                     array, and the guards are conjoined.  Replacing them one
                     at a time leaves the other arrays' reads standing in the
                     result, which a celled row cannot evaluate -- and it loses
                     the only shape that relates two arrays.  An invariant that
                     says "this slice is that one from index i on" is exactly
                     [s[0] = slice[i]] generalised, and as a cell qualifier
                     that is
                     [#cidx@s = 0 /\ #cidx@slice = i => #cval@s = #cval@slice]:
                     a statement about two arrays' columns together, which no
                     family generated from the parameters alone produces. *)
                  let mine =
                    Set.filter cell_reads ~f:(fun (_, _, t) -> Set.mem here t)
                  in
                  if Set.is_empty mine then acc
                  else
                    let atm =
                      Atom.map_term_no_binders atomic ~f:(fun t' ->
                          match
                            Set.find mine ~f:(fun (_, _, t) -> Stdlib.(t' = t))
                          with
                          | Some (a, _, _) -> CellQual.val_term a T_int.SInt
                          | None -> t')
                    in
                    let guard =
                      Formula.and_of @@ List.map (Set.to_list mine)
                        ~f:(fun (a, idx, _) ->
                          Formula.eq (CellQual.idx_term a) idx)
                    in
                    let lifted =
                      Formula.mk_imply guard (Formula.mk_atom atm)
                    in
                    (* a sequence read that was not collected -- one of a
                       sequence no unknown here reaches, or of non-integer
                       elements -- would stay in the result without its range
                       premise *)
                    if keeps_seq_read_atom atm then acc
                    else
                      (* offered to every array it mentions, since it is about
                         all of them together *)
                      Set.fold mine ~init:acc ~f:(fun acc (a, _, _) ->
                          emit acc a lifted)
            in
            (* let tvs, fvs, cond =
                 mk_let_to_cond Set.Poly.empty bvs fvs tvs lenv
               in
               print_endline @@ "fvs: "
               ^ String.concat_map_set ~sep:", " fvs ~f:(fst >> Ident.name_of_tvar);
               print_endline @@ "cond: " ^ Formula.str_of cond; *)
            let mentions_an_unknown =
              Fn.non Set.is_empty
              @@ Set.inter (Set.Poly.map ~f:fst tvs)
                   (Map.key_set @@ Problem.senv_of pcsp)
            in
            (* [fvs] is what this atom does not share with any unknown
               application, so [tvs = fvs] means the atom and the unknowns have
               no variable in common and no qualifier can be built from it.
               Silently dropping such an atom is how a premise stated only under
               a quantifier came to contribute nothing at all, so say it. *)
            let unrelated_to_every_unknown = Set.is_subset tvs ~of_:fvs in
            if mentions_an_unknown || unrelated_to_every_unknown then (
              (* the atom may still be about an argument, written in terms of
                 that argument's parts; see [selector_subst_of_clause] *)
              let recovered =
                if mentions_an_unknown || Map.Poly.is_empty sel_sub then []
                else
                  let atm = Atom.subst sel_sub atomic in
                  let atvs = Atom.tvs_of atm in
                  if Set.is_empty atvs then []
                  else
                    List.filter_map (pos_papp_tvs @ neg_papp_tvs)
                      ~f:(fun (pa, pftv) ->
                        if
                          Set.is_subset atvs ~of_:(Set.Poly.map pftv ~f:fst)
                        then Some (pa, Evaluator.simplify_atom atm)
                        else None)
              in
              (* A ground atom belongs to no particular argument, so when the
                 theory leaves its value open it is offered to every unknown
                 applied in this clause rather than to one of them. *)
              let recovered_ground =
                if
                  (not config.ground_open_term_quals)
                  || mentions_an_unknown
                  || (not @@ Set.is_empty tvs)
                  || (not
                      @@ ClauseOld.interpretation_dependent
                           (Formula.mk_atom atomic))
                then []
                else
                  List.map (pos_papp_tvs @ neg_papp_tvs) ~f:(fun (pa, _) ->
                      (pa, Evaluator.simplify_atom atomic))
              in
              if unrelated_to_every_unknown && not mentions_an_unknown then
                Debug.print
                @@ lazy
                     (match (recovered, recovered_ground) with
                     | (_, phi) :: _, _ ->
                         sprintf
                           "qualifier from %s through the parts of an \
                            argument: %s"
                           (Atom.str_of atomic) (Formula.str_of phi)
                     | [], (_, phi) :: _ ->
                         sprintf
                           "qualifier from %s as a ground fact the theory \
                            leaves open, offered to every unknown here: %s"
                           (Atom.str_of atomic) (Formula.str_of phi)
                     | [], [] ->
                         sprintf
                           "no qualifier from %s: %s"
                           (Atom.str_of atomic)
                           (if Set.is_empty tvs then
                              "it is ground, and the theory fixes its value, \
                               so it separates no two examples"
                            else
                              sprintf
                                "none of its variables (%s) is an argument \
                                 of an unknown here"
                                (String.concat_map_set ~sep:", " tvs
                                   ~f:(fst >> Ident.name_of_tvar))));
              Set.union acc @@ Set.Poly.of_list (recovered @ recovered_ground))
            else
              (* what follows depends on the atom alone and not on the
                 application [pa] it is offered to: whether no variable it
                 does not share with the unknowns occurs in a division, and
                 the quantified qualifier built from it.  With
                 [extract_atom_quals_once] each is computed once per atom
                 rather than once per application; the values are the same,
                 since both are functions of [atomic] and [fvs] *)
              let once f =
                if config.extract_atom_quals_once then
                  let v = lazy (f ()) in
                  fun () -> Lazy.force v
                else f
              in
              let div_free =
                once (fun () ->
                    Set.is_empty
                    @@ Set.inter (Set.Poly.map ~f:fst fvs)
                         (Set.concat_map (Atom.div_rem_of atomic)
                            ~f:(fun (t1, t2) ->
                              Set.union (Term.fvs_of t1) (Term.fvs_of t2))))
              in
              let exi_atm =
                once (fun () ->
                    ExtractCensus.built ();
                    let cnt = ref 0 in
                    Formula.aconv_tvar_norm (fun () ->
                        cnt := !cnt + 1;
                        Ident.Tvar ("#q" ^ string_of_int !cnt))
                    @@ Formula.exists (Set.to_list fvs)
                    @@ Evaluator.simplify (*Formula.mk_and cond @@*)
                    @@ Formula.mk_atom
                    @@
                    match Atom.negate atomic with
                    | None -> failwith "[extract]"
                    | Some neg_atom -> neg_atom)
              in
              let uni_atm =
                once (fun () ->
                    ExtractCensus.built ();
                    let cnt = ref 0 in
                    Formula.aconv_tvar_norm (fun () ->
                        cnt := !cnt + 1;
                        Ident.Tvar ("#q" ^ string_of_int !cnt))
                    @@ Formula.forall (Set.to_list fvs)
                    @@ Evaluator.simplify
                    @@
                    (*Formula.mk_imply cond @@*)
                    Formula.mk_atom atomic)
              in
              let acc =
                List.fold pos_papp_tvs ~init:acc ~f:(fun acc (pa, pftv) ->
                    if
                      Set.is_subset tvs ~of_:(Set.union pftv fvs)
                      && div_free ()
                    then (
                      if print_log then
                        print_endline
                        @@ sprintf "pos atom (%d): %s" (Atom.ast_size atomic)
                        @@ Atom.str_of atomic;
                      let atm = exi_atm () in
                      if print_log then
                        Debug.print
                        @@ lazy (sprintf "exi atomic: %s" @@ Formula.str_of atm);
                      Set.add acc (pa, atm))
                    else acc)
              in
              List.fold neg_papp_tvs ~init:acc ~f:(fun acc (pa, pftv) ->
                  if
                    Set.is_subset tvs ~of_:(Set.union pftv fvs)
                    && div_free ()
                  then (
                    if print_log then
                      print_endline
                      @@ sprintf "neg atom (%d): %s" (Atom.ast_size atomic)
                      @@ Atom.str_of atomic;
                    let atm = uni_atm () in
                    if print_log then
                      Debug.print
                      @@ lazy (sprintf "uni atomic: %s" @@ Formula.str_of atm);
                    Set.add acc (pa, atm))
                  else acc)))
    |> ExtractCensus.pairs
    |> (fun pairs ->
    Common.PhaseTime.with_phase "group" (fun () ->
        Set.group_by pairs ~equiv:(fun (pa1, _) (pa2, _) ->
            Ident.pvar_equal (Atom.pvar_of pa1) (Atom.pvar_of pa2))))
    |> List.map ~f:(fun lst ->
        let pvar, sorts =
          match Set.choose lst with
          | None -> failwith "each group must contains at least one term"
          | Some (Atom.App (Predicate.Var (pv, ss), _, _), _) -> (pv, ss)
          | Some (_, _) -> assert false
        in
        let params = sort_env_list_of_sorts sorts in
        let extracted_quals =
          Set.Poly.filter_map lst ~f:(function
            | Atom.App (_, args, _), atomic -> (
                (* args are assumed to be distinct variables
                      ohterwise no qualifier is extracted *)
                try
                  let tvars =
                    List.map args ~f:(function
                      | Term.Var (x, _, _) -> x
                      | term ->
                          failwith
                          @@ sprintf "[Generator.extract] invalid term: %s"
                               (Term.str_of term))
                  in
                  let base_index =
                    Map.Poly.of_alist_exn @@ List.mapi tvars ~f:(fun i x -> (x, i))
                  in
                  (* a cell column belongs to the argument its access path
                     starts at, whatever selectors follow *)
                  let index_of_var v =
                    match Map.Poly.find base_index v with
                    | Some i -> Some i
                    | None ->
                        Option.bind (CellQual.split_placeholder v)
                          ~f:(fun (_, base, _) -> Map.Poly.find base_index base)
                  in
                  let ids =
                    Set.Poly.map (Formula.tvs_of atomic) ~f:(fun v ->
                        match index_of_var v with
                        | Some i -> i
                        | None ->
                            failwith
                            @@ sprintf
                                 "[Generator.extract] %s is neither an \
                                  argument nor a column of one"
                                 (Ident.name_of_tvar v))
                  in
                  if print_log then
                    Debug.print
                    @@ lazy
                         (sprintf "qualifier before sub: %s"
                         @@ Formula.str_of atomic);
                  let phi =
                    let tsub =
                      (* the arguments, plus every column this qualifier
                         mentions rebased from the argument its path starts at
                         onto the predicate's parameter *)
                      let arg_to_param =
                        Map.Poly.of_alist_exn
                        @@ List.map2_exn tvars params ~f:(fun x (p, _) -> (x, p))
                      in
                      Map.Poly.of_alist_exn
                      @@ List.zip_exn tvars (Term.of_sort_env params)
                      @ List.filter_map (Set.to_list (Formula.tvs_of atomic))
                          ~f:(fun v ->
                            Option.map
                              (CellQual.rebase_placeholder v ~f:(fun b ->
                                   Map.Poly.find arg_to_param b))
                              ~f:(fun v' ->
                                (v, Term.mk_var v' T_int.SInt)))
                    in
                    Normalizer.normalize @@ Evaluator.simplify
                    @@ Formula.subst tsub atomic
                  in
                  if print_log then
                    Debug.print
                    @@ lazy
                         (sprintf "qualifier after sub: %s"
                         @@ Formula.str_of phi);
                  (* A ground qualifier has the same truth value at every
                     example and so separates none of them -- unless the
                     background theory does not fix that value, in which case
                     it is the one ground fact a solution can need to name as a
                     guard.  This is the same distinction the extraction above
                     makes, and it has to be made twice because a ground atom
                     that survives extraction is discarded again here. *)
                  if
                    Formula.is_ground phi
                    && not
                         (config.ground_open_term_quals
                         && ClauseOld.interpretation_dependent phi)
                  then None
                  else Some (ids, phi)
                with exn_ when not (Common.Timer.is_async exn_) -> None)
            | atom, _ ->
                failwith
                @@ sprintf "[Generator.extract] fail with %s"
                     (Atom.str_of ~priority:20 atom))
        in
        ( pvar,
          Set.Poly.union_list
            [
              extracted_quals;
              (if add_ineqs_for_eqs then
                 Set.concat_map extracted_quals ~f:(fun (ids, phi) ->
                     if Formula.is_eq phi then
                       let t1, t2, _ = Formula.let_eq phi in
                       if T_int.is_sint t1 || T_real.is_sreal t1 then
                         Set.Poly.of_list
                           [
                             (ids, Normalizer.normalize @@ Formula.leq t1 t2);
                             (ids, Normalizer.normalize @@ Formula.geq t1 t2);
                           ]
                       else Set.Poly.empty
                     else Set.Poly.empty)
               else Set.Poly.empty);
              (if config.add_bool then
                 Set.Poly.filter_map (Set.Poly.of_list params) ~f:(fun (x, s) ->
                     if Term.is_bool_sort s then
                       Some (Set.Poly.empty, Formula.of_bool_var x)
                     else None)
               else Set.Poly.empty);
              Set.Poly.of_list
              @@ List.filter_mapi params ~f:(fun i (x, s) ->
                  if
                    Term.is_int_sort s
                    && Set.mem parity_positions (pvar, i)
                  then
                    Some
                      ( Set.Poly.empty,
                        Formula.eq
                          (T_int.mk_rem Value.Euclidean (Term.mk_var x s)
                             (T_int.from_int 2))
                          (T_int.zero ()) )
                  else None);
            ] ))
    |> ExtractCensus.quals "before-qelim"
    |> (fun groups ->
    Common.PhaseTime.with_phase "qelim-quals" (fun () -> qelim_quals groups))
    |> ExtractCensus.quals "after-qelim"

  let qualifier_propagation ~ignore_wf kind_map
      (quals_map :
        (Ident.pvar, (int Set.Poly.t * Formula.t) Set.Poly.t) Map.Poly.t) =
    let open Ast.Logic in
    (* find ids in args1 and args2 of same args between args1 and args2 *)
    let rec same_args_id_of args1 args2 id1 =
      match args1 with
      | [] -> ([], [])
      | arg1 :: args1' -> (
          let ids1, ids2 = same_args_id_of args1' args2 (id1 + 1) in
          match
            List.find_mapi args2 ~f:(fun i arg2 ->
                if Stdlib.(arg1 = arg2) then Some i else None)
          with
          | Some id2 -> (id1 :: ids1, id2 :: ids2)
          | None -> (ids1, ids2))
    in
    let x_i = QualPropagation.x_i in
    let pairs =
      let cls = Problem.clauses_of APCSP.problem in
      let count = ref 0 in
      Set.fold cls ~init:Set.Poly.empty ~f:(fun acc (uni_senv, ps, ns, _) ->
          count := !count + 1;
          let atms = Set.union ps ns in
          Debug.print
          @@ lazy
               (sprintf
                  "propagating qualifiers across %s clause (out of %d) with %d \
                   atoms"
                  (Ordinal.string_of @@ Ordinal.make !count)
                  (Set.length cls) (Set.length atms));
          Set.fold_distinct_pairs atms ~init:acc ~f:(fun acc atm1 atm2 ->
              if print_log then
                Debug.print
                @@ lazy
                     (sprintf "comparing %s and %s"
                        (Atom.str_of
                        @@ ExtTerm.to_old_atm
                             (Problem.senv_of APCSP.problem)
                             uni_senv atm1)
                        (Atom.str_of
                        @@ ExtTerm.to_old_atm
                             (Problem.senv_of APCSP.problem)
                             uni_senv atm2));
              let pvar1, args1 = ExtTerm.let_var_app atm1 in
              let pvar2, args2 = ExtTerm.let_var_app atm2 in
              if
                Stdlib.(pvar1 = pvar2)
                || ignore_wf
                   &&
                   match
                     (Map.Poly.find kind_map pvar1, Map.Poly.find kind_map pvar2)
                   with
                   | Some Kind.WF, _
                   | _, Some Kind.WF
                   | Some Kind.DWF, _
                   | _, Some Kind.DWF
                   | Some (Kind.NWF _), _
                   | _, Some (Kind.NWF _)
                   | Some (Kind.Parity _), _
                   | _, Some (Kind.Parity _) ->
                       true
                   | _ -> false
              then acc
              else
                let ids1, ids2 = same_args_id_of args1 args2 0 in
                let sub =
                  List.fold2_exn ids1 ids2 ~init:Map.Poly.empty
                    ~f:(fun acc id1 id2 ->
                      let x1, x2 = (x_i id1, x_i id2) in
                      Map.Poly.update acc x2
                        ~f:
                          Set.(
                            function
                            | None -> Poly.singleton x1
                            | Some xs -> add xs x1))
                in
                Set.add acc
                  ( Ident.tvar_to_pvar pvar1,
                    Ident.tvar_to_pvar pvar2,
                    sub,
                    Set.Poly.of_list ids1,
                    Set.Poly.of_list ids2 )))
    in
    if Lazy.force QualPropagation.census then (
      (* per unknown: its occurrences, and how many of its argument positions
         hold the same argument as an earlier position at every occurrence
         (always) or at some but not all (sometimes); a qualifier of another
         unknown is copied onto every such position *)
      let occ = Hashtbl.Poly.create () in
      Set.iter (Problem.clauses_of APCSP.problem) ~f:(fun (_, ps, ns, _) ->
          Set.iter (Set.union ps ns) ~f:(fun atm ->
              let pvar, args = ExtTerm.let_var_app atm in
              Hashtbl.add_multi occ ~key:pvar ~data:(Array.of_list args)));
      Hashtbl.iteri occ ~f:(fun ~key ~data ->
          let n = Array.length (List.hd_exn data) in
          let same i j =
            List.for_all data ~f:(fun a -> Stdlib.(a.(i) = a.(j)))
          in
          let some i j =
            List.exists data ~f:(fun a -> Stdlib.(a.(i) = a.(j)))
          in
          let always = ref 0 and sometimes = ref 0 in
          for i = 0 to n - 1 do
            if List.exists (List.init i ~f:Fn.id) ~f:(fun j -> same i j) then
              incr always
            else if List.exists (List.init i ~f:Fn.id) ~f:(fun j -> some i j)
            then incr sometimes
          done;
          eprintf
            "[propagate-census] unknown=%s arity=%d occurrences=%d \
             positions_equal_to_an_earlier_always=%d sometimes=%d\n%!"
            (Ident.name_of_tvar key) n (List.length data) !always !sometimes);
      eprintf "[propagate-census] clauses=%d at=%.3f\n%!"
        (Set.length (Problem.clauses_of APCSP.problem))
        (Common.Clock.now_s ()));
    QualPropagation.fixpoint ~fast:true
      ~print:(fun s -> Debug.print s)
      pairs quals_map

  (* The candidate atoms the input declared, as qualifiers of the unknown each
     was declared for: over [x1 ... xn], the names every qualifier of an
     unknown is written over here, with the argument positions each mentions.
     Read through [PCSP.Params.candidate_atoms_at], so an argument the
     preprocessor dropped takes the atoms mentioning it with it, and an unknown
     it eliminated has none.  They are offered whether or not qualifiers are
     extracted from the clauses: the input asked for them. *)
  let declared_qualifiers =
    let params = PCSP.Problem.params_of APCSP.problem in
    Map.Poly.fold (PCSP.Problem.senv_of APCSP.problem) ~init:Map.Poly.empty
      ~f:(fun ~key ~data acc ->
        let sorts =
          List.map (Logic.Sort.args_of data) ~f:Logic.ExtTerm.to_old_sort
        in
        match PCSP.Params.candidate_atoms_at params key sorts with
        | None -> acc
        | Some (xs, atoms) ->
            let ys = sort_env_list_of_sorts sorts in
            let index =
              Map.Poly.of_alist_exn @@ List.mapi xs ~f:(fun i (x, _) -> (x, i))
            in
            let sub =
              Map.Poly.of_alist_exn
              @@ List.map2_exn xs ys ~f:(fun (x, _) (y, s) ->
                  (x, Term.mk_var y s))
            in
            let quals =
              Set.Poly.of_list
              @@ List.filter_map atoms ~f:(fun phi ->
                  let ids =
                    Set.Poly.filter_map (Formula.tvs_of phi)
                      ~f:(Map.Poly.find index)
                  in
                  let phi =
                    Normalizer.normalize @@ Evaluator.simplify
                    @@ Formula.subst sub phi
                  in
                  if Formula.is_true phi || Formula.is_false phi then None
                  else Some (ids, phi))
            in
            Debug.print
            @@ lazy
                 (sprintf "declared candidate atoms of %s (%d of %d kept): %s"
                    (Ident.name_of_tvar key) (Set.length quals)
                    (List.length atoms)
                    (String.concat_map_set ~sep:"; " quals ~f:(fun (_, phi) ->
                         Formula.str_of phi)));
            if Set.is_empty quals then acc
            else Map.Poly.set acc ~key:(Ident.tvar_to_pvar key) ~data:quals)

  let union_quals m1 m2 =
    Map.Poly.merge m1 m2 ~f:(fun ~key:_ -> function
      | `Left d | `Right d -> Some d
      | `Both (d1, d2) -> Some (Set.union d1 d2))

  (* the declared atoms as the hypothesis space sees them: none when they are
     for the Houdini pre-pass only *)
  let declared_qualifiers =
    if config.declared_atoms_houdini_only then Map.Poly.empty
    else declared_qualifiers

  (* [transpositions_keep_words]: the parameter positions of each unknown the
     problem reads as words *)
  let int_to_bv_vars = Qual.int_to_bv_vars

  let word_positions =
    lazy
      (let exi_senv = Problem.senv_of APCSP.problem in
       Set.fold (Problem.clauses_of APCSP.problem) ~init:Map.Poly.empty
         ~f:(fun acc c ->
           let _, ps, ns, phi = Clause.to_old_clause exi_senv c in
           let atoms = Set.to_list (Set.union ps ns) in
           let words =
             Set.Poly.union_list
               (int_to_bv_vars phi
               :: List.map atoms ~f:(fun a -> int_to_bv_vars (Formula.mk_atom a)))
           in
           List.fold atoms ~init:acc ~f:(fun acc -> function
             | Atom.App (Predicate.Var (p, _), ts, _) ->
                 List.foldi ts ~init:acc ~f:(fun i acc -> function
                   | Term.Var (x, _, _) when Set.mem words x ->
                       Map.Poly.update acc p ~f:(function
                         | None -> Set.Poly.singleton i
                         | Some is -> Set.add is i)
                   | _ -> acc)
             | _ -> acc)))

  let keep_word_forms pvar params extracted permuted =
    match Map.Poly.find (Lazy.force word_positions) pvar with
    | None -> permuted
    | Some is ->
        let words =
          Set.Poly.of_list
          @@ List.filter_mapi params ~f:(fun i (x, _) ->
                 if Set.mem is i then Some x else None)
        in
        Qual.drop_non_word_forms ~words
          ~params:(Set.Poly.of_list (List.map params ~f:fst))
          ~extracted permuted

  let extracted_qualifiers =
    let declared_first = config.propagate_declared_atoms in
    (if (not declared_first) || not config.extract_pcsp then
       union_quals declared_qualifiers
     else Fn.id)
    @@
    if config.extract_pcsp then (
      Debug.print @@ lazy "*** extracting qualifiers";
      let extracted =
        List.fold
          (Common.PhaseTime.with_phase "extract" (fun () -> extract pcsp))
          ~init:Map.Poly.empty ~f:(fun map (key, d) ->
            Map.Poly.update map key ~f:(function
              | None -> d
              | Some d' -> Set.union d d'))
      in
      let extracted =
        if declared_first then union_quals declared_qualifiers extracted
        else extracted
      in
      if config.propagate_quals then (
        Debug.print @@ lazy "*** propagating qualifiers";
        let propagated =
          Common.PhaseTime.with_phase "propagate" @@ fun () ->
          Map.Poly.map ~f:elim_neg
          @@ qualifier_propagation ~ignore_wf:false (*ToDo*)
               (PCSP.Problem.kind_map_of APCSP.problem)
               extracted
        in
        Debug.print @@ lazy "done";
        propagated)
      else extracted)
    else Map.Poly.empty

  let generate pvar params labeled_atoms examples n =
    match List.nth domains n with
    | None -> failwith "generate"
    | Some (module Q) ->
        (* done here rather than in each domain because every one of them
           begins by instantiating, and an atom already ground passes through
           that step unchanged -- so one site covers all of them and the
           domains keep their signatures *)
        let labeled_atoms =
          if not config.sat_point_instances then labeled_atoms
          else
            let sat_point =
              ExampleInstance.chooser
                ~id:(PCSP.Problem.id_of APCSP.problem)
                (PCSP.Problem.fenv_of APCSP.problem)
            in
            let atoms =
              Set.Poly.map labeled_atoms ~f:(fun (atom, label) ->
                  (ExAtom.instantiate_gen ~sat_point atom, label))
            in
            (* also what says the flag was read at all, a defaulted field being
               invisible in every config that does not mention it *)
            Debug.print
            @@ lazy
                 (sprintf "sat-point instances for %s: %s"
                    (Ident.name_of_pvar pvar)
                    (ExampleInstance.str_of_counts ()));
            atoms
        in
        (* printed whether or not the flag is on, because the cheapest question
           about it -- is there an exposure at all -- is answered by an ORDINARY
           run: a count of how many parametric atoms were grounded at a point
           their own condition rejects.  A counter visible only once the feature
           is enabled cannot say whether enabling it could help. *)
        (let grounded, vacuous = ExAtom.instantiation_counts () in
         if grounded > 0 then
           Debug.print
           @@ lazy
                (sprintf
                   "parametric atoms grounded so far: %d, of which %d at a \
                    point their condition rejects"
                   grounded vacuous));
        (* a clause's disjunction about a cell ([lift_clause_cell_disjunctions])
           is offered as read off its clause: the families below rewrite an
           atom (swap arguments, drop a constant, reflect a halfspace), and
           applied to every atom of a disjunction at once they make a variant
           per family that no clause states *)
        let clause_disjs, extracted_raw =
          Map.Poly.find extracted_qualifiers pvar
          |> Option.value ~default:Set.Poly.empty
          |> Set.partition_tf ~f:(snd >> is_clause_cell_disjunction)
        in
        let clause_disjs =
          Set.Poly.map clause_disjs ~f:(fun (_, phi) ->
              ( params,
                Normalizer.canon_eq_signs @@ Normalizer.normalize phi ))
        in
        let extracted =
          extracted_raw
          (* |> Set.filter ~f:(fun phi ->
             not @@ Set.exists (Formula.fvs_of phi) ~f:(fun tvar ->
                not @@ List.exists params ~f:(fun (tvar1, _) -> Stdlib.(tvar = tvar1)))) *)
          |> Set.Poly.map ~f:(fun (_, phi) -> (params, phi))
          |> (if config.add_arg_transpositions then fun extracted ->
                let permuted =
                  Common.PhaseTime.with_phase "gen-permutations" (fun () ->
                      Qual.add_arg_permutations ?limit:None extracted)
                in
                if config.transpositions_keep_words then
                  keep_word_forms pvar params extracted permuted
                else permuted
              else Fn.id)
          (* An extracted qualifier carries whatever constant the clause it came
             from compared against, so a slice whose contract says its first
             element is 10 contributes only "that element is not 10" and the
             hypothesis space can never say what it *is*.  The homogeneous form
             compares the same quantity to zero, which with the negation below
             is the atom a loop invariant over a mutable reference needs -- the
             element written through it is 0, a fact the clauses state about the
             final side and never about the current one.  This was applied to
             the generated qualifiers only, and the domain a template-based run
             selects generates none, so it had no effect on the qualifiers that
             exist. *)
          |> (if config.add_homogeneous then fun qs ->
                Common.PhaseTime.with_phase "gen-homogeneous" (fun () ->
                    Qual.add_homogeneous qs)
              else Fn.id)
          |>
          if config.add_neg then fun qs ->
            Common.PhaseTime.with_phase "gen-neg" (fun () -> Qual.add_neg qs)
          else Fn.id
        in
        let generated =
          Q.qualifiers_of pvar (List.map ~f:snd params) labeled_atoms examples
          |> if config.add_homogeneous then Qual.add_homogeneous else Fn.id
        in
        (* built from the parameters rather than from a qualifier, so it is
           unioned in rather than mapped over either set above *)
        let equalities =
          if not config.add_arg_equalities then Set.Poly.empty
          else
            Qual.arg_equalities params
            |> if config.add_neg then Qual.add_neg else Fn.id
        in
        let interm = Set.union equalities @@ Set.union extracted generated in

        let interm =
          Set.union interm
            (if config.add_func_qual_disj then
               let qs = Set.Poly.map ~f:snd @@ Qual.add_neg interm in
               (* The pairs are built only to be filtered by "does a free
                  variable of ARROW sort occur", and a disjunction has one
                  exactly when one of its two disjuncts does.  So the qualifiers
                  that can contribute are known BEFORE the product: pairing an
                  arrow-free qualifier with another arrow-free one can only
                  produce an arrow-free disjunction, and every such pair was
                  built, normalised into a formula and then discarded.

                  On a dependency-quantified benchmark, for instance: 346
                  qualifiers become 692 with their negations, the product is
                  478,864 pairs, 239,778 disjunctions are constructed and
                  **none** survives the filter, because not one of the 692
                  mentions an arrow sort at all.  That is 14.1 s of a 20.5 s
                  qualifier-generation block, against 0.01 s for every other
                  stage of [generate] put together.

                  Splitting the set first keeps the result identical -- a pair
                  with at least one arrow-sorted side is still built, and it is
                  the only kind that could be kept -- while a predicate with no
                  arrow-sorted qualifier at all now costs one pass instead of a
                  square. *)
               let has_arrow q =
                 Set.exists (Formula.term_sort_env_of q)
                   ~f:(snd >> Sort.is_arrow)
               in
               let arrowed = Set.filter qs ~f:has_arrow in
               if Set.is_empty arrowed then Set.Poly.empty
               else
                 let qqs =
                   Set.union
                     (Set.cartesian_map
                        ~f:(fun q1 q2 -> Set.Poly.of_list [ q1; q2 ])
                        arrowed qs)
                     (Set.cartesian_map
                        ~f:(fun q1 q2 -> Set.Poly.of_list [ q1; q2 ])
                        qs arrowed)
                 in
                 Set.Poly.map ~f:(fun q -> (params, q))
                 @@ Set.filter
                      ~f:
                        (Formula.term_sort_env_of
                        >> Set.exists ~f:(snd >> Sort.is_arrow))
                 @@ Set.Poly.map qqs ~f:(Set.to_list >> Formula.or_of)
             else Set.Poly.empty)
        in
        (if config.filter_out_non_div_mod then
           Set.filter interm ~f:Qual.div_mod_filter
         else interm)
        |> Set.Poly.map ~f:(fun (params, phi) ->
            (* [canon_eq_signs] merges the two spellings of one equation -- an equation's
               sign is free, so [x1 - x2 = 0] and [x2 - x1 = 0] are one qualifier and used
               to be two.  It is applied HERE, to a finished qualifier, rather than inside
               [normalize]: see the comment on the function for what doing it globally
               costs. *)
            ( params,
              Normalizer.canon_eq_signs
              @@ Normalizer.normalize (*@@ Evaluator.simplify_neg*) phi ))
        (* reflected AFTER normalization, because before it a halfspace may
           still be written as [0 <= -t] rather than [-t >= 0] and the
           reflection would not see it *)
        |> (if config.add_reflections then Qual.add_reflections else Fn.id)
        |> Set.union
             (if config.filter_out_non_div_mod then
                Set.filter clause_disjs ~f:Qual.div_mod_filter
              else clause_disjs)
        |> elim_neg
  (*|> (fun quals -> if config.reduce then Q.reduce_qualifiers quals neg_ex pos_ex else quals)*)

  let str_of_domain n =
    match List.nth domains n with
    | None -> failwith "str_of_domain"
    | Some (module Q) -> Q.str_of_domain

  let num_of_domains = List.length domains
end
