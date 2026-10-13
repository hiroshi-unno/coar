open Core
open Common.Ext
open LogicOld

(* The shapes at which a problem's clauses handle values of an OPAQUE sort --
   a sort with no operation but equality, which the hypothesis space treats by
   its catch-all case: not Bool, Int, Real, a bit-vector, an array, a
   sequence, a tuple, a datatype or a function sort; in practice an
   uninterpreted sort standing for a type parameter of the source program --
   and the filter that offers a reached term of such a sort only at a shape
   the clauses use.

   The SHAPE of a term is the term with every variable replaced by one
   placeholder and every selector of a single-constructor datatype erased (a
   field of a record, a tuple or a reference is the same value whether the
   clause reads it through the selector or binds it by destructuring, and
   preprocessing turns one into the other), every other function symbol, an
   integer literal included, kept with the shapes of its arguments.  The
   CLAUSE SHAPES of a problem are the pairs (sort, shape) of the subterms of
   an opaque sort anywhere in its clauses: in the pure part and in the
   arguments of the unknowns' applications, under binders, lets, embedded
   formulas and array lambdas alike.

   The filter: a term of an opaque sort reached from the parameters is
   offered when its shape is a variable's (a parameter, or a field of one
   through selectors of single-constructor datatypes) or when its (sort,
   shape) is a clause shape.  What it removes is a read the program never
   writes: the term map reads every sequence at every integer term in scope,
   lengths and counters included, so [s[len t]], [s[i][len u]] and the like,
   which no clause reads and which are mostly out of range, carry most of the
   pairwise equalities an opaque sort contributes (on one Rust-derived input,
   438,516 of one unknown's 461,255 generated qualifiers).

   Why a solution loses little: an opaque value has no operation but
   equality, so the only facts about it a clause can establish or consume are
   about the terms the clause writes; an invariant's equality between two
   opaque values carries such a fact from one clause to another.  Reads at
   variable indices and fields of parameters keep their shapes under this
   abstraction, so the equality of a yielded element with the read at the
   iterator's position, [x = s[i]] or [fst e = s[i][j]], survives whenever the
   clauses read at that shape.  This is an argument, not a theorem: a fact the
   clauses establish only through a chain of steps whose terms have other
   shapes can need a qualifier the filter removes.  Fewer qualifiers only
   narrow the hypothesis space, so the filter bears on which solutions are
   expressible and never on the soundness of a verdict. *)

(* the sorts [HypSpace.qualifiers_of] gives its catch-all case *)
let is_opaque_sort = function
  | Sort.SArrow _ | T_bool.SBool | T_int.SInt | T_real.SReal | T_bv.SBV _
  | T_array.SArray _ | T_seq.SSeq _ | T_tuple.STuple _ | T_dt.SDT _ ->
      false
  | _ -> true

let single_constructor dt = List.length (Datatype.conses_of dt) = 1

let rec shape_of = function
  | Term.Var _ -> "_"
  | Term.FunApp (T_dt.DTSel (_, dt, _), [ t ], _) when single_constructor dt ->
      shape_of t
  | Term.FunApp (f, [], _) -> Term.str_of_funsym f
  | Term.FunApp (f, args, _) ->
      Term.str_of_funsym f ^ "("
      ^ String.concat ~sep:"," (List.map args ~f:shape_of)
      ^ ")"
  | Term.LetTerm (_, _, _, body, _) -> shape_of body

type t = (Sort.t * string) Set.Poly.t

(* the clause shapes of a formula, added to [acc]; every subterm is visited *)
let rec of_formula acc = function
  | Formula.Atom (atom, _) -> of_atom acc atom
  | Formula.UnaryOp (_, phi, _) -> of_formula acc phi
  | Formula.BinaryOp (_, phi1, phi2, _) -> of_formula (of_formula acc phi1) phi2
  | Formula.Bind (_, _, phi, _) -> of_formula acc phi
  | Formula.LetRec (defs, phi, _) ->
      List.fold defs ~init:(of_formula acc phi) ~f:(fun acc def ->
          of_formula acc def.body)
  | Formula.LetFormula (_, _, def, body, _) -> of_formula (of_term acc def) body

and of_atom acc = function
  | Atom.True _ | Atom.False _ -> acc
  | Atom.App (_, args, _) -> List.fold args ~init:acc ~f:of_term

and of_term acc t =
  match t with
  | Term.Var _ -> acc
  | Term.FunApp (T_bool.Formula phi, args, _) ->
      List.fold args ~init:(of_formula acc phi) ~f:of_term
  | Term.FunApp (f, args, _) ->
      let acc = List.fold args ~init:acc ~f:of_term in
      let acc = of_cons_fields acc f args in
      let sort = Term.sort_of t in
      if is_opaque_sort sort then Set.add acc (sort, shape_of t) else acc
  | Term.LetTerm (_, _, def, body, _) -> of_term (of_term acc def) body

(* a constructor application [C(t1, ..., tn)] of a datatype with several
   constructors makes the selector of each opaque field equal its argument
   ([sel_k (C(t1, ..., tn)) = t_k]), so the selector read [sel_k(_)] is a shape
   the clause handles even though it writes the constructor instead: an
   [Option] built from a read gives its payload the read's value *)
and of_cons_fields acc f args =
  match f with
  | T_dt.DTCons (name, _, dt) when not (single_constructor dt) -> (
      match Datatype.look_up_cons dt name with
      | None -> acc
      | Some cons -> (
          match List.zip (Datatype.sels_of_cons cons) args with
          | Unequal_lengths -> acc
          | Ok pairs ->
              List.fold pairs ~init:acc ~f:(fun acc (sel, arg) ->
                  let sort = Term.sort_of arg in
                  if is_opaque_sort sort then
                    Set.add acc
                      (sort, Datatype.name_of_sel sel ^ "(" ^ "_" ^ ")")
                  else acc)))
  | _ -> acc

let of_clauses (clauses : ClauseOld.t list) : t =
  List.fold clauses ~init:Set.Poly.empty ~f:(fun acc (_, ps, ns, phi) ->
      let acc = Set.fold ps ~init:acc ~f:of_atom in
      let acc = Set.fold ns ~init:acc ~f:of_atom in
      of_formula acc phi)

(* the clause shapes of the last clause list asked about, kept while the
   caller passes the same (physically equal) list: every template of every
   unknown asks about the problem's one clause list *)
let cache : (ClauseOld.t list * t) option Atomic.t = Atomic.make None

let of_clauses_cached clauses =
  match Atomic.get cache with
  | Some (cs, shapes) when phys_equal cs clauses -> shapes
  | _ ->
      let shapes = of_clauses clauses in
      Atomic.set cache (Some (clauses, shapes));
      shapes

(* the filter of the header: [t] is a term of an opaque sort.  A term of the
   variable shape -- a parameter, or a field of one reached through selectors
   of single-constructor datatypes, which destructuring makes a variable -- is
   always kept. *)
let keep_term (shapes : t) t =
  Term.is_var t
  ||
  let shape = shape_of t in
  String.equal shape "_" || Set.mem shapes (Term.sort_of t, shape)
