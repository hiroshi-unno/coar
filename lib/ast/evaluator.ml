open Core
open Common.Ext
open Common.Util
open Common.Combinator
open LogicOld

let simplify_theory_atoms = true
let simplify_ite_case = true
let elim_case = true

(* [simplify_term] and [simplify_atom] lift a conditional out of an application,
   [f (ite c a b)] to [ite c (f a) (f b)] (and likewise for [Case] and for a
   predicate's arguments), and then simplify the rebuilt term as a whole.  The
   condition, the branches and the other arguments are already outputs of
   [simplify_term], so that second pass re-simplifies them, and since every
   lift inside it does the same, nested lifts multiply: one simplification of a
   51,219-node formula holding two-level conditionals over sequence reads made
   48.7 million [simplify_term] calls for 315,269 lifts and spent 22-67 s.

   With this switch on, a lift simplifies only the nodes it built and takes the
   parts it was handed as they are ([simplify_known]).  The result is the one
   the switch-off path gives whenever [simplify_term] maps each such part to
   itself, and it does not always: some rules return a term they do not
   simplify again, which a second pass then rewrites -- an [iff] or [xor] of
   two Boolean constants (left by [simplify], folded by the evaluator once the
   embedding term is simplified again), a negated literal product built by the
   multiplication rules for a negated factor, and the constant array of a
   finitely expanded array literal whose default is a conditional.  Every
   rewrite here preserves meaning, so the result is equivalent to the
   switch-off result in every model; what can differ is its shape, a part left
   one rewrite short of the form a second pass would give.  Off by default:
   whether a different shape helps or hurts the consumers downstream (the
   predicate eliminator and the zero-unknown verdict's piece splitting depend
   on a formula's shape) is decided by measuring answers, not assumed. *)
let simplify_skip_simplified = Atomic.make false

(* Normal-form outputs.  Some rules of [simplify_term] and [simplify] build
   their result from simplified parts without applying the rules to the node
   they build, so the result is one rewrite short of the form a second pass
   gives: an [iff]/[xor] of two Boolean constants left unfolded; the negation
   of a product rebuilt as [-(n * x)] where the negation rule gives
   [(-n) * x], or as the negation of a conditional the negation rule lifts;
   the constant array of a finitely expanded array literal whose default is a
   conditional (the constant-array rule lifts it), and a [store] of the
   default value into it; the negated condition of an [ite(c, false, true)]
   (a negated quantifier not pushed inward); a tester of a nullary
   constructor rewritten into an equation whose other side is a conditional;
   the two-sided bounds of an absolute value conjoined without the grouping a
   conjunction gets; and the orientation of an (dis)equation, which the
   grouping of a conjunction or disjunction turns around while a lifted
   comparison left alone comes out as [t = true], and which the grouping
   turns from [x = -y] into [-y = x] for the atom rules to turn into
   [y = -x].  With this switch on, each of those rules applies the rules for
   the node it builds, a lifted comparison is oriented as the grouping would
   orient it, and the grouping leaves an equation with a negation on its
   right as it is, so the output is a fixed point of a second pass.
   Contract: every such change replaces a term or formula by one equal to it
   in every model, since each is a rule [simplify] already applies on the
   next pass or an equation read the other way round.  Off by default: it
   changes the simplifier's output on those shapes, and consumers that depend
   on a formula's shape are judged by measuring answers. *)
let simplify_normal_forms = Atomic.make false

(* A memo for [simplify] and [simplify_neg] that lives for one scope of
   [with_shared_simplify], keyed by node address.

   Contract of [with_shared_simplify f]: when [share_simplify] is set, [f ()]
   runs with this domain's [simplify] and [simplify_neg] remembering, for
   every formula node they simplify, the result -- but only when computing it
   drew no fresh name ([Ident.fresh_stamp] unchanged) -- and a node met again
   in the scope, physically the same value, gets the remembered result; the
   tables are dropped when [f] returns or raises, and a scope inside a scope
   uses the outer one.  Unset, it only runs [f].

   Why it is exact: [simplify] of a node is a function of the node and of
   state no simplification changes (the function and datatype environments,
   the switches above), so a recomputation would return a structurally equal
   value; and a remembered computation drew no name, so skipping it leaves
   every later draw as it was.  So the results are the ones without the
   scope, value for value and draw for draw; they are only more shared.  The
   instrument [skip_simplified_probe] counts fewer parts on a hit.

   Why: a clause set whose clauses share large pure parts physically (the
   product a clausal form multiplies) was simplified clause by clause, and
   each clause got its own copy of every shared part. *)
let share_simplify = Atomic.make false

module PhysFml = Stdlib.Hashtbl.Make (struct
  type t = Formula.t

  let equal = phys_equal
  let hash = Common.Ext.Hashtbl.phys_hash
end)

type simplify_tables = { pos : Formula.t PhysFml.t; neg : Formula.t PhysFml.t }

let simplify_scope : simplify_tables option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_shared_simplify f =
  if not (Atomic.get share_simplify) then f ()
  else
    match Stdlib.Domain.DLS.get simplify_scope with
    | Some _ -> f ()
    | None ->
        Stdlib.Domain.DLS.set simplify_scope
          (Some { pos = PhysFml.create 1024; neg = PhysFml.create 1024 });
        Exn.protect ~f ~finally:(fun () ->
            Stdlib.Domain.DLS.set simplify_scope None)

(* Whether the simplifier decides a [let]'s inlining by the size the inlining
   would give the body as a tree, rather than admitting any small definition at
   any number of uses (see [inline_let]).  Off by default: on, a chain of small
   definitions each used more than once is kept as [let]s past the point where
   inlining would add more than a few nodes, which changes the simplifier's
   output (and, at the solver boundary, a kept [let] is asked as an existential
   with its equation).  Process-wide once on. *)
let inline_by_expanded_size = Atomic.make false

(* The tree size a term or formula has once every [let] in it is inlined,
   computed without inlining: a [let]-bound variable counts as its definition's
   expanded size, and the [let] node itself counts nothing.  Elsewhere the node
   counts are those of [Term.ast_size] and [Formula.ast_size], which agree with
   this on a let-free value but do not carry a binding's size into a formula
   embedded in a term (an [ite]'s condition) or into a [let] formula's body, and
   so undercount a chain whose bound variables occur there.  Assumes the value
   is alpha-renamed, as the simplifier's input is: a binder never shadows a
   [let]-bound name. *)
let rec expanded_size_term ex = function
  | Term.Var (x, _, _) -> Option.value ~default:1 (Map.Poly.find ex x)
  | Term.FunApp (T_bool.Formula phi, args, _) ->
      expanded_size_fml ex phi
      + List.sum (module Int) args ~f:(expanded_size_term ex)
  | Term.FunApp (_, args, _) ->
      1 + List.sum (module Int) args ~f:(expanded_size_term ex)
  | Term.LetTerm (x, _, def, body, _) ->
      expanded_size_term
        (Map.Poly.set ex ~key:x ~data:(expanded_size_term ex def))
        body

and expanded_size_atom ex = function
  | Atom.True _ | Atom.False _ -> 1
  | Atom.App (Predicate.Fixpoint def, args, _) ->
      1 + Formula.ast_size def.body
      + List.sum (module Int) args ~f:(expanded_size_term ex)
  | Atom.App (_, args, _) ->
      1 + List.sum (module Int) args ~f:(expanded_size_term ex)

and expanded_size_fml ex = function
  | Formula.Atom (atom, _) -> expanded_size_atom ex atom
  | Formula.UnaryOp (_, phi, _) | Formula.Bind (_, _, phi, _) ->
      1 + expanded_size_fml ex phi
  | Formula.BinaryOp (_, phi1, phi2, _) ->
      1 + expanded_size_fml ex phi1 + expanded_size_fml ex phi2
  | Formula.LetRec _ as phi -> Formula.ast_size phi
  | Formula.LetFormula (x, _, def, body, _) ->
      expanded_size_fml
        (Map.Poly.set ex ~key:x ~data:(expanded_size_term ex def))
        body

let expanded_size_of_term = expanded_size_term Map.Poly.empty
let expanded_size_of_formula = expanded_size_fml Map.Poly.empty

(* The tree size of [body] with [def] substituted for every free occurrence of
   [x], both read as their expansions, computed without substituting: every
   occurrence replaces one leaf by [def]'s expanded tree.  [Term.occur_times]
   already counts occurrences through a [let] as its expansion. *)
let let_inlined_size x ~def ~body =
  expanded_size_of_term body
  + (Term.occur_times x body * (expanded_size_of_term def - 1))

(* A measurement instrument for the premise above: with this on (and the switch
   above off), every lift also re-simplifies each part it hands over and counts
   the parts that do not come back structurally equal.  It costs a second
   simplification of every part, and a probe inside a probe is not taken. *)
let skip_simplified_probe = Atomic.make false
let probe_parts_checked = Atomic.make 0
let probe_parts_changed = Atomic.make 0

(* the first parts that did not come back equal, as (part, re-simplified part) *)
let probe_examples : (Term.t * Term.t) list ref = ref []
let probe_max_examples = 200
let probing = Stdlib.Domain.DLS.new_key (fun () -> ref false)

(*val eval_term: Term.t -> Value.t*)
(* structural equality modulo the bound variables of Z3-style array lambdas
   ([T_array.ALambda]); every other node is compared structurally *)
let rec alpha_equiv t1 t2 =
  match (t1, t2) with
  | ( Term.FunApp (T_array.ALambda ((x1, s1), se1), [ b1 ], _),
      Term.FunApp (T_array.ALambda ((x2, s2), se2), [ b2 ], _) ) ->
      Stdlib.(s1 = s2 && se1 = se2)
      && alpha_equiv b1 (Term.rename (Map.Poly.singleton x2 x1) b2)
  | Term.FunApp (f1, ts1, _), Term.FunApp (f2, ts2, _) ->
      Stdlib.(f1 = f2)
      && List.length ts1 = List.length ts2
      && List.for_all2_exn ts1 ts2 ~f:alpha_equiv
  | _ -> Stdlib.(t1 = t2)

(* bound on nested unfoldings of defined functions in [eval_term]: a
   definition that does not terminate on its argument ([f n = f n]) would
   otherwise make constant folding run forever.  Per domain, because
   folding runs in every solver domain. *)
let max_unfold_depth = 1000
let unfold_depth = Stdlib.Domain.DLS.new_key (fun () -> ref 0)

(* [Evaluator.simplify_term] applies [eval_term] speculatively to every
   application node and discards the failure, so a failure message must not
   serialize the offending term: doing so made [PCSP.Problem.normalize]
   quadratic in the term size (and, on wide bit-vectors, dominated the whole
   run).  These helpers name the head of the term instead. *)
(* Rewriting [a = store(b, i, v)] into [v = … /\ a = b] states equality at EVERY
   index, where the original only asks for it away from [i].  The two agree
   exactly when some index lies outside the stores, and that needs the index
   sort to have more elements than they cover.  [T_array.non_stored] does not
   say this: it says [i] was not written, a syntactic fact about one term.  A
   Bool-indexed array with both indices stored is the smallest case where the
   difference shows -- the two arrays are then equal at every index, and the
   rewrite goes on to compare defaults that nothing can observe and reports them
   different, which is a wrong [unsat] (and a wrong [sat] through the
   disequality rules beside it).  So the room is required explicitly, and
   answered conservatively: only sorts that are certainly infinite qualify, and
   a finite or unknown index sort keeps the equality unrewritten.  A datatype is
   refused even when it is recursive and so infinite, because deciding that
   needs an analysis this predicate does not do. *)
let index_sort_has_room = function
  | T_int.SInt | T_real.SReal | T_string.SString -> true
  | T_seq.SSeq _ -> true
  | _ -> false

let non_stored_roomy arr i =
  index_sort_has_room (Term.sort_of i) && T_array.non_stored arr i

(* Is the divisor known to be nonzero?  The theory says what division and
   remainder mean at a nonzero divisor and says nothing at zero, which is not
   permission to pick a value there: folding [0 / d] to [0] without knowing [d]
   decides an unspecified case, and a query that merely observes the choice --
   [(not (= (div 0 0) 0))] -- then comes back unsat where z3 and cvc5 answer
   sat.  A symbolic divisor is not known nonzero, so it declines; the literal
   fold further down already carried this condition, and only the shortcut above
   it did not. *)
let divisor_is_nonzero = function
  | Term.FunApp (T_int.Int n, [], _) -> Z.Compare.(n <> Z.zero)
  | Term.FunApp (T_real.Real r, [], _) -> Q.(r <> Q.zero)
  | _ -> false

(* Is the exponent known to be strictly positive?  [0 ^ e] is [0] only then:
   at [e = 0] this tool's own ground fold gives [1], and a negative exponent of
   zero is not a value at all.  "Not syntactically the literal zero" is not the
   same question -- a variable that happens to be zero passes it -- and reading
   it as one made [0 ^ x] fold to [0] while [0 ^ 0] folded to [1], so
   substituting [x = 0] and simplifying disagreed with simplifying and then
   substituting: [(assert (= x 0)) (assert (distinct (^ 0 x) (^ 0 0)))] came
   back sat where z3 answers unsat, which congruence alone decides. *)
let exponent_is_positive = function
  | Term.FunApp (T_int.Int n, [], _) -> Z.Compare.(n > Z.zero)
  | Term.FunApp (T_real.Real r, [], _) -> Q.(r > Q.zero)
  | _ -> false

(* The length of a sequence when its own STRUCTURE gives one: a literal empty or
   unit sequence, a concatenation of two such, or a store, which keeps the
   length whether or not the write lands inside.  [None] for anything else --
   notably a variable -- because the alternative is to consult a hypothesis, and
   the callers below are term rewrites with no premise in hand. *)
let rec seq_len_of = function
  | Term.FunApp (T_seq.SqEmpty _, [], _) -> Some Z.zero
  | Term.FunApp (T_seq.SqUnit _, [ _ ], _) -> Some Z.one
  | Term.FunApp (T_seq.SqConcat _, [ s1; s2 ], _) -> (
      match (seq_len_of s1, seq_len_of s2) with
      | Some n1, Some n2 -> Some Z.(n1 + n2)
      | _ -> None)
  | Term.FunApp (T_seq.SqStore _, [ s; _; _ ], _) ->
      (* a store keeps the length whether or not the write lands inside *)
      seq_len_of s
  | _ -> None

(* Is this read index known to be inside the sequence?  [Some ()] only when the
   length is available as above and the index is a literal within it; a symbolic
   index or a sequence whose length is not syntactically available gives [None],
   because a read outside the sequence is underspecified and rules that rewrite
   one such read into another are then claiming an agreement the theory does not
   give. *)
let seq_index_in_range sq j =
  match (seq_len_of sq, j) with
  | Some n, Term.FunApp (T_int.Int m, [], _) ->
      if Z.Compare.(Z.zero <= m) && Z.Compare.(m < n) then Some () else None
  | _ -> None

(* The element at literal index [k] of a sequence whose structure fixes it, or
   [None].

   Contract: [Some v] only when, in every model of the sequence theory, [k] is
   a position of [sq] (so the read is not the open out-of-range term) and
   [seq.nth sq k = v].  The proof is by induction on [sq]:
   - [unit e] at 0 is [e]; any other index is out of range, [None];
   - [a ++ b] with [len a] syntactic: below [len a] the read is [a]'s read at
     the same index, which by induction is in range of [a], hence of [a ++ b];
     at or past it, [b]'s read at [k - len a], which by induction is in range
     of [b], so [k] is in range of [a ++ b].  [b] need not have a syntactic
     length for the first branch, which is why [nth (unit x ++ s) 0] folds;
   - [store s i e]: by induction [k] is in range of [s], and a store keeps the
     length, so [k] is in range of the store; the position holds [e] where it
     is the written one and [s]'s element otherwise.  With [i] a literal that
     is decided here; with [i] symbolic it becomes an [ite] on [i = k], whose
     then-branch needs no range guard on [i] because [i = k] puts it in range.
   Everything else -- a variable, an empty sequence, a negative index -- gives
   [None].  In particular an out-of-range literal read is never folded: it is
   a term the theory leaves open, and the element next to it is not its value. *)
let rec seq_nth_of_literal sq k =
  if Z.(lt k zero) then None
  else
    match sq with
    | Term.FunApp (T_seq.SqUnit _, [ e ], _) ->
        if Z.(equal k zero) then Some e else None
    | Term.FunApp (T_seq.SqConcat _, [ a; b ], _) -> (
        match seq_len_of a with
        | Some la when Z.(lt k la) -> seq_nth_of_literal a k
        | Some la -> seq_nth_of_literal b Z.(k - la)
        | None -> None)
    | Term.FunApp (T_seq.SqStore _, [ s; i; e ], _) -> (
        match seq_nth_of_literal s k with
        | None -> None
        | Some v -> (
            match i with
            | Term.FunApp (T_int.Int m, [], _) ->
                Some (if Z.equal m k then e else v)
            | _ ->
                Some
                  (T_bool.mk_if_then_else
                     (T_bool.of_formula @@ Formula.eq i (T_int.mk_int k))
                     e v)))
    | _ -> None

(* The elements of a sequence built from [seq.empty], [seq.unit] and [seq.++]
   alone, in order; [None] for anything else.  Such a term is a sequence
   literal: its length and every element are fixed by the theory. *)
let rec seq_elems_of = function
  | Term.FunApp (T_seq.SqEmpty _, [], _) -> Some []
  | Term.FunApp (T_seq.SqUnit _, [ e ], _) -> Some [ e ]
  | Term.FunApp (T_seq.SqConcat _, [ a; b ], _) ->
      Option.map2 (seq_elems_of a) (seq_elems_of b) ~f:( @ )
  | _ -> None

(* The literal whose elements are [es], right-nested. *)
let seq_of_elems se es =
  match List.rev es with
  | [] -> T_seq.mk_empty se
  | last :: rest ->
      List.fold rest ~init:(T_seq.mk_unit se last) ~f:(fun acc e ->
          T_seq.mk_concat se (T_seq.mk_unit se e) acc)

(* A store at literal index [k] pushed into the sequence literal part that
   holds position [k]; [None] when no part of [sq]'s structure decides where
   [k] falls.  The exactness argument is the store-normalisation comment in
   [simplify_term]. *)
let rec push_literal_store se sq k e =
  if Z.(lt k zero) then Some sq
  else
    match sq with
    | Term.FunApp (T_seq.SqEmpty _, [], _) -> Some sq
    | Term.FunApp (T_seq.SqUnit _, [ _ ], _) ->
        Some (if Z.(equal k zero) then T_seq.mk_unit se e else sq)
    | Term.FunApp (T_seq.SqConcat _, [ a; b ], _) -> (
        let store_in s k =
          match push_literal_store se s k e with
          | Some t -> t
          | None -> T_seq.mk_store se s (T_int.mk_int k) e
        in
        match seq_len_of a with
        | Some la when Z.(lt k la) -> Some (T_seq.mk_concat se (store_in a k) b)
        | Some la -> Some (T_seq.mk_concat se a (store_in b Z.(k - la)))
        | None -> None)
    | _ -> None

(* Read over write for sequences, applied where the hypothesis it needs is
   available.

   The law [nth (store sq i e) j = if i = j then e else nth sq j] is sound only
   where the READ index [j] is inside the sequence: outside it both sides are
   underspecified and need not agree, so rewriting one into the other would
   claim an agreement the theory does not give.  That fact is almost always
   stated -- but in the CLAUSE and not in the term, which is why the term-level
   simplifier cannot apply this rule and fires only where the length can be
   computed from the sequence's own syntax, i.e. almost never on a corpus whose
   sequences are variables.

   A clause is a disjunction, so while rewriting one disjunct every other
   disjunct may be assumed false; [entails] is asked whether those assumptions
   give [0 <= j < seq.len sq].  [entails] may answer false whenever it likes --
   the reads it declines are simply left alone -- but an answer of true must be
   sound.

   Terms and subformulas under a BINDER are left alone, which is what
   [Formula.map_term_no_binders] is for: a quantifier, a [let], an array lambda
   and an embedded formula all bind, and an assumption gathered outside one of
   them is about another variable that happens to share a name. *)
(* The one rewrite step: [seq.nth (seq.store sq i e) j] where the assumptions
   put [j] inside [sq].  Everything about WHERE it may be applied is the
   traversal's business, not this function's. *)
let rec rewrite_nth_over_store_at ~in_range t =
  match t with
  | Term.FunApp
      (T_seq.SqNth _, [ Term.FunApp (T_seq.SqStore se, [ sq; i; e ], _); j ], _)
    when in_range ~sq ~j ->
      T_bool.mk_if_then_else
        (T_bool.of_formula
        @@ Formula.and_of
             [
               Formula.eq i j;
               Formula.leq (T_int.zero ()) i;
               Formula.lt i (T_seq.mk_len se sq);
             ])
        e
        (* the inner read can be a redex of its own, and the traversal that
           called us has already finished with [sq], so step again here; [sq] is
           one store shallower than what we consumed, so this terminates *)
        (rewrite_nth_over_store_at ~in_range @@ T_seq.mk_nth se sq j)
  | _ -> t

(* One clause.  [entails assumptions goal] decides whether the goal follows; it
   is given by the caller because deciding it wants a solver and this module is
   below one. *)
let rewrite_seq_read_over_write ~entails phi =
  let disjuncts = Set.to_list @@ Formula.disjuncts_of phi in
  match disjuncts with
  | [] -> phi
  | disjuncts ->
      let rewritten =
        List.mapi disjuncts ~f:(fun m d ->
            let assumptions =
              Formula.and_of
              @@ List.filter_mapi disjuncts ~f:(fun k d' ->
                  if k = m then None else Some (Formula.mk_neg d'))
            in
            let in_range ~sq ~j =
              entails assumptions
              @@ Formula.and_of
                   [
                     Formula.leq (T_int.zero ()) j;
                     Formula.lt j
                       (T_seq.mk_len (T_seq.elem_sort_of @@ Term.sort_of sq) sq);
                   ]
            in
            Formula.map_term_no_binders
              ~f:(rewrite_nth_over_store_at ~in_range)
              d)
      in
      if List.equal Stdlib.( == ) rewritten disjuncts then phi
      else Formula.or_of rewritten

(* Read over concatenation, as an EXACT identity and without any hypothesis:

     nth (a ++ b) j  =  if 0 <= j < len a then nth a j
                        else if len a <= j < len a + len b then nth b (j - len a)
                        else nth (a ++ b) j

   Each branch is justified where it is taken.  Inside [a] the concatenation
   holds [a]'s element at [j] and [j] is inside [a], so the right-hand read is
   specified too; inside [b] likewise at [j - len a].  Outside both the value is
   the one the theory leaves open, and the third branch is the SAME term, so the
   two sides agree in every model whatever it assigns there.  The unguarded
   two-branch form [if j < len a then nth a j else nth b (j - len a)] is not an
   identity: an out-of-range read is underspecified per sequence (z3 and cvc5
   both give it the value of a function of the sequence and the index), and
   [nth (a ++ b) (-1)] and [nth a (-1)] are applications to different sequences
   that a model may separate.

   A branch read of a unit sequence is its element: the branch's guard confines
   the index to [0, 1).  A branch read of a concatenation is expanded again, and
   the recursion is on a strict subterm.  The kept third-branch read is NOT
   expanded again, so one application terminates; applying the rewrite a second
   time to its own output nests one more layer, which is why the caller applies
   it once, to a query, and never inside a fixpoint of simplification.

   Why it is worth having: a solver asked about a read of a concatenation under
   a quantified hypothesis over the parts ([forall i. 0 <= i < len a =>
   nth a i = ...]) was observed to answer neither way, z3 and cvc5 alike, while
   the same question with the read split by index was decided by both at once. *)
let rec seq_read_over_concat se a b j =
  let len s =
    match seq_len_of s with
    | Some n -> T_int.mk_int n
    | None -> T_seq.mk_len se s
  in
  let branch_read s i =
    match s with
    | Term.FunApp (T_seq.SqUnit _, [ e ], _) -> e
    | Term.FunApp (T_seq.SqConcat _, [ s1; s2 ], _) ->
        seq_read_over_concat se s1 s2 i
    | _ -> T_seq.mk_nth se s i
  in
  let la = len a in
  T_bool.mk_if_then_else
    (T_bool.of_formula
    @@ Formula.and_of [ Formula.leq (T_int.zero ()) j; Formula.lt j la ])
    (branch_read a j)
    (T_bool.mk_if_then_else
       (T_bool.of_formula
       @@ Formula.and_of
            [ Formula.leq la j; Formula.lt j (T_int.mk_add la (len b)) ])
       (branch_read b (T_int.mk_sub j la))
       (T_seq.mk_nth se (T_seq.mk_concat se a b) j))

(* Apply the identity above once to every read of a concatenation, under
   binders too: it needs no hypothesis, so a binder cannot invalidate it.  The
   traversal is bottom-up and does not revisit what [f] returns, which is what
   keeps the kept third-branch read from being expanded again. *)
let rewrite_seq_read_over_concat_rebuilt phi =
  Formula.map_term phi ~f:(function
    | Term.FunApp
        (T_seq.SqNth se, [ Term.FunApp (T_seq.SqConcat _, [ a; b ], _); j ], _)
      ->
        seq_read_over_concat se a b j
    | t -> t)

(* Whether [rewrite_seq_read_over_concat] keeps the subterms it does not change
   physically ([rewrite_seq_read_over_concat_sharing]) instead of rebuilding
   the whole formula ([rewrite_seq_read_over_concat_rebuilt]).  The two results
   are equal wherever the input's nodes carry the default info, which every
   formula built in the tree does; the switch exists so a test can compare them.
   Why: the zero-unknown check rewrites every piece's deep form, 100,000-270,000
   nodes on a Rust-derived loop-body clause, of which a few hundred reads are
   rewritten; rebuilding the rest was 4-6 s of a 120 s budget under load, and
   the fresh copy made every later comparison of the form with its neighbours'
   structural. *)
let seq_read_over_concat_sharing = ref true

(* [rewrite_seq_read_over_concat_rebuilt phi] with every unchanged node the
   input's own: the same bottom-up traversal (entering embedded formulas, array
   lambdas, lets and binders), the same rewrite at each read, and a node rebuilt
   only when a child changed. *)
let rewrite_seq_read_over_concat_sharing phi =
  let same xs ys = List.for_all2_exn xs ys ~f:phys_equal in
  let rewrite = function
    | Term.FunApp
        (T_seq.SqNth se, [ Term.FunApp (T_seq.SqConcat _, [ a; b ], _); j ], _)
      ->
        seq_read_over_concat se a b j
    | t -> t
  in
  let rec term t =
    match t with
    | Term.Var _ -> rewrite t
    | Term.FunApp (T_bool.Formula p, [], info) ->
        let p' = formula p in
        rewrite
          (if phys_equal p p' then t
           else Term.mk_fsym_app ~info (T_bool.Formula p') [])
    | Term.FunApp (sym, args, info) ->
        let args' = List.map args ~f:term in
        rewrite (if same args args' then t else Term.mk_fsym_app ~info sym args')
    | Term.LetTerm (x, s, d, b, info) ->
        let d' = term d and b' = term b in
        rewrite
          (if phys_equal d d' && phys_equal b b' then t
           else Term.mk_let_term ~info x s d' b')
  and formula phi =
    match phi with
    | Formula.Atom (Atom.App (pred, args, ai), info) ->
        let args' = List.map args ~f:term in
        if same args args' then phi
        else Formula.mk_atom ~info (Atom.mk_app ~info:ai pred args')
    | Formula.Atom _ -> phi
    | Formula.UnaryOp (op, p, info) ->
        let p' = formula p in
        if phys_equal p p' then phi else Formula.mk_unop ~info op p'
    | Formula.BinaryOp (op, p, q, info) ->
        let p' = formula p and q' = formula q in
        if phys_equal p p' && phys_equal q q' then phi
        else Formula.mk_binop ~info op p' q'
    | Formula.Bind (b, senv, p, info) ->
        let p' = formula p in
        if phys_equal p p' then phi else Formula.mk_bind ~info b senv p'
    | Formula.LetRec (funcs, p, info) ->
        let funcs' = Formula.map_funcs ~f:formula funcs and p' = formula p in
        if
          phys_equal p p'
          && List.for_all2_exn funcs funcs' ~f:(fun d d' ->
                 phys_equal d.body d'.body)
        then phi
        else Formula.mk_letrec ~info funcs' p'
    | Formula.LetFormula (x, s, d, b, info) ->
        let d' = term d and b' = formula b in
        if phys_equal d d' && phys_equal b b' then phi
        else Formula.mk_let_formula ~info x s d' b'
  in
  formula phi

let rewrite_seq_read_over_concat phi =
  if !seq_read_over_concat_sharing then rewrite_seq_read_over_concat_sharing phi
  else rewrite_seq_read_over_concat_rebuilt phi

(* Prefix over concatenation, as an EXACT identity and without any hypothesis:

     extract (a ++ b) 0 k  =  if k <= len a then extract a 0 k
                              else a ++ extract b 0 (k - len a)

   SMT-LIB's [seq.extract s 0 k] is the prefix of [s] of length
   [max 0 (min k (len s))] (empty when [k <= 0], the whole of [s] when
   [k >= len s]).  When [k <= len a] the prefix of [a ++ b] lies inside [a],
   and it is [a]'s prefix of the same length, [k < 0] included (empty on both
   sides).  When [k > len a] the prefix is all of [a] followed by [b]'s prefix
   of length [min (k - len a) (len b)], and [k - len a > 0], so the right-hand
   side is that; [k > len (a ++ b)] gives [a ++ b] on both sides.  So the two
   sides are equal in every model, and the rewrite may be applied to any
   formula that is asked for validity or satisfiability.

   The offset must be the literal [0]; a length written [k - 0] (the form an
   encoding that states an extraction by its end and start produces) is read as
   [k].  A branch whose sequence is again a concatenation is rewritten again,
   which handles a chain nested either way; the recursion is on a strict
   subterm, so it terminates.  Returns [phi] itself when nothing applies. *)
let rec seq_prefix_over_concat se a b k =
  let len s =
    match seq_len_of s with
    | Some n -> T_int.mk_int n
    | None -> T_seq.mk_len se s
  in
  let prefix s k =
    match s with
    | Term.FunApp (T_seq.SqConcat _, [ s1; s2 ], _) ->
        seq_prefix_over_concat se s1 s2 k
    | _ -> T_seq.mk_extract se s (T_int.zero ()) k
  in
  let la = len a in
  T_bool.mk_if_then_else
    (T_bool.of_formula @@ Formula.leq k la)
    (prefix a k)
    (T_seq.mk_concat se a (prefix b (T_int.mk_sub k la)))

let rewrite_seq_prefix_over_concat phi =
  let changed = ref false in
  let phi' =
    Formula.map_term phi ~f:(function
      | Term.FunApp
          ( T_seq.SqExtract se,
            [ Term.FunApp (T_seq.SqConcat _, [ a; b ], _); off; k ],
            _ )
        when T_int.is_zero off ->
          changed := true;
          let k =
            match k with
            | Term.FunApp (T_int.Sub, [ k'; z ], _) when T_int.is_zero z -> k'
            | _ -> k
          in
          seq_prefix_over_concat se a b k
      | t -> t)
  in
  if !changed then phi' else phi

(* Substitute a clause's DEFINITION of a sequence variable by a sequence
   constructor, so that a read of the variable becomes a read of the
   constructor and the identity above can act on it.

   [phi] is ONE clause, read as valid when it holds for every value of its free
   variables.  The law is [forall x. (x != t \/ R(x))  <=>  R(t)] for [x] not
   occurring in [t]: the only value of [x] at which the disjunction says
   anything is [t].  A clause is not always a flat disjunction -- a clause head
   that is a conjunction leaves the definition inside one conjunct -- so the law
   is applied at any disjunction reached from the root through conjunctions and
   disjunctions alone, PROVIDED [x] occurs free nowhere outside that
   disjunction.  Then the universal over [x] can be pushed down to it, since
   [forall x. (A /\ B(x))] is [A /\ forall x. B(x)] and [forall x. (A \/
   B(x))] is [A \/ forall x. B(x)] when [x] is not in [A]; nothing is pushed
   past a negation, a binder or any other connective, which the traversal does
   not enter.  So the rewrite is exact.  It is exact only per clause: two
   clauses of one conjunction may use one name for different variables, which
   is harmless to validity but means a definition must not be carried across.

   Restricted to a sequence-sorted [x] and a [t] whose head is a sequence
   constructor (empty, unit, concatenation), because that is the case the
   identity above needs and substituting every equation would change queries
   this has no reason to touch.  Returns [phi] itself when nothing applies. *)
let rec subst_seq_definitions phi =
  let is_cons = function
    | Term.FunApp ((T_seq.SqEmpty _ | T_seq.SqUnit _ | T_seq.SqConcat _), _, _)
      ->
        true
    | _ -> false
  in
  subst_clause_definitions
    ~accept:(fun sort t ->
      match sort with T_seq.SSeq _ -> is_cons t | _ -> false)
    phi

(* [subst_seq_definitions] for a variable of any sort defined as any term:
   the same law, [forall x. (x != t \/ R(x)) <=> R(t)] for [x] not in [t].
   For a caller that asks [phi] for VALIDITY and wants the equations between
   its variables gone before it is split and instantiated, as a preprocessor
   would have removed them.  Only validity is preserved, not the meaning in
   each model, and for that the variables free in a sibling CONJUNCT do not
   count as occurring outside a disjunction: [forall x. (A /\ B)] is
   [(forall x. A) /\ (forall x. B)], so each conjunct is valid or not on its
   own, and [A \/ (C /\ D)] is valid exactly when [A \/ C] and [A \/ D]
   are.  Only disjunction siblings do. *)
and subst_var_definitions phi =
  subst_clause_definitions ~conjunct_siblings:false ~accept:(fun _ _ -> true)
    phi

(* the law above for the definitions [accept sort t] admits; with
   [conjunct_siblings] (the default), a variable free in a sibling conjunct
   is not substituted either *)
and subst_clause_definitions ?(conjunct_siblings = true) ~accept phi =
  let def_of x sort t =
    if accept sort t && not (Set.mem (Term.tvs_of t) x) then Some (x, t)
    else None
  in
  let definition = function
    | Formula.UnaryOp
        ( Formula.Not,
          Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
          _ )
    | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _) -> (
        match (t1, t2) with
        | Term.Var (x, sort, _), t when Option.is_some (def_of x sort t) ->
            def_of x sort t
        | t, Term.Var (x, sort, _) -> def_of x sort t
        | _ -> None)
    | _ -> None
  in
  let changed = ref false in
  (* [ctx x] holds when [x] is free somewhere outside the current subformula.
     It is a predicate rather than a set so that [with_siblings] can answer it
     from occurrence counts: building, for each of n siblings, the union of the
     other n - 1 siblings' free variables took time quadratic in n, and a pure
     clause of a thousand disjuncts made that the largest cost of asking it for
     validity. *)
  let rec go ctx phi =
    match phi with
    | Formula.BinaryOp (Formula.And, _, _, _) ->
        Formula.and_of
        @@
        if conjunct_siblings then
          with_siblings ctx @@ Formula.conjuncts_list_of phi
        else List.map ~f:(go ctx) @@ Formula.conjuncts_list_of phi
    | Formula.BinaryOp (Formula.Or, _, _, _) ->
        let rec elim ds =
          match
            List.find_mapi ds ~f:(fun k d ->
                match definition d with
                | Some (x, t) when not (ctx x) -> Some (k, x, t)
                | _ -> None)
          with
          | None -> ds
          | Some (k, x, t) ->
              changed := true;
              let sub = Map.Poly.singleton x t in
              elim
              @@ List.filter_mapi ds ~f:(fun k' d ->
                  if k = k' then None else Some (Formula.subst sub d))
        in
        Formula.or_of @@ with_siblings ctx @@ elim
        @@ Formula.disjuncts_list_of phi
    | _ -> phi
  (* sibling [k] is visited with [ctx] extended by the variables free in some
     other sibling: those occurring in more siblings than [k] itself
     accounts for *)
  and with_siblings ctx fs =
    let tvss = List.map fs ~f:Formula.tvs_of in
    let count = Hashtbl.Poly.create () in
    List.iter tvss ~f:(Set.iter ~f:(fun x -> Hashtbl.incr count x));
    List.map2_exn fs tvss ~f:(fun f tvs ->
        go
          (fun x ->
            ctx x
            ||
            let n = Option.value ~default:0 (Hashtbl.find count x) in
            n > if Set.mem tvs x then 1 else 0)
          f)
  in
  let phi' = go (fun _ -> false) (Formula.nnf_of phi) in
  if !changed then phi' else phi

(* Substitute a clause's DEFINITION of a sequence-valued PROJECTION of a clause
   variable -- a selector [sel] applied to a variable [x], as in a tuple's third
   component -- by the constructor term it is defined as, the companion of
   [subst_seq_definitions] for a defined side that is not itself a variable.

   [phi] is one clause.  At a disjunction reached from the root through
   conjunctions and disjunctions alone, a disjunct [sel(x) != t] (or [t !=
   sel(x)]) defines [sel(x)] when
   - [x] is a variable (it is free in the clause: nothing between the root and
     the disjunction binds),
   - [sel(x)] is sequence-sorted and [t] is headed by a sequence constructor
     (empty, unit, concatenation), and [sel(x)] does not occur in [t].
   Which side is rewritten is therefore not a choice: it is the projection, and
   the other side must be a constructor term, which a projection never is.
   Every occurrence of [sel(x)] in the OTHER disjuncts of that disjunction is
   replaced by [t]; the defining disjunct is kept as it is.

   The argument, in every model and for every assignment: where [sel(x) != t]
   holds, the disjunction holds before and after; where it fails, [sel(x)] and
   [t] denote the same value, and replacing one by the other preserves the
   truth of each disjunct by congruence -- provided every replaced occurrence
   denotes what it denotes at the disjunction.  So the replacement does not
   enter a binder (a quantifier, a [let], an array [lambda]) that binds [x] or a
   variable of [t], and does not enter a fixpoint predicate or a recursive
   definition at all; at such a node the subformula is left as it is, which is
   trivially exact.  The rewritten clause is thus EQUIVALENT to the clause in
   every model, not only valid when it is: the equation is kept, and the
   replacement is used only where it holds.  Nothing is renamed, so no capture
   can arise.

   Definitions are taken one at a time, in disjunct order, each re-read in the
   current form of its disjunct (an earlier replacement may have rewritten it,
   and one that no longer defines anything is skipped).  Returns [phi] itself
   when nothing applies. *)
let subst_seq_projection_definitions phi =
  let is_cons = function
    | Term.FunApp ((T_seq.SqEmpty _ | T_seq.SqUnit _ | T_seq.SqConcat _), _, _)
      ->
        true
    | _ -> false
  in
  let proj_var = function
    | Term.FunApp
        ((T_dt.DTSel _ | T_tuple.TupleSel _), [ Term.Var (x, _, _) ], _) as s
      -> (
        match Term.sort_of s with T_seq.SSeq _ -> Some x | _ -> None)
    | _ -> None
  in
  let rec occurs s t =
    Stdlib.(s = t)
    ||
    match t with
    | Term.FunApp (_, args, _) -> List.exists args ~f:(occurs s)
    | Term.LetTerm (_, _, d, b, _) -> occurs s d || occurs s b
    | Term.Var _ -> false
  in
  let def_of s t =
    match proj_var s with
    | Some x when is_cons t && not (occurs s t) -> Some (s, x, t)
    | _ -> None
  in
  let definition = function
    | Formula.UnaryOp
        ( Formula.Not,
          Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
          _ )
    | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _) -> (
        match def_of t1 t2 with Some d -> Some d | None -> def_of t2 t1)
    | _ -> None
  in
  let replace (s, x, t) =
    let fvt = Term.tvs_of t in
    let blocked y = Stdlib.(y = x) || Set.mem fvt y in
    let rec rt u =
      if Stdlib.(u = s) then t
      else
        match u with
        | Term.Var _ -> u
        | Term.FunApp (T_bool.Formula f, [], info) ->
            Term.mk_fsym_app ~info (T_bool.Formula (rf f)) []
        | Term.FunApp (T_array.ALambda ((y, _), _), _, _) when blocked y -> u
        | Term.FunApp (fsym, args, info) ->
            Term.mk_fsym_app ~info fsym (List.map args ~f:rt)
        | Term.LetTerm (y, sort, d, b, info) ->
            Term.mk_let_term ~info y sort (rt d)
              (if blocked y then b else rt b)
    and rf f =
      match f with
      | Formula.Atom (Atom.App (pred, args, ainfo), info)
        when not (Predicate.is_fix pred) ->
          Formula.mk_atom ~info
            (Atom.mk_app ~info:ainfo pred (List.map args ~f:rt))
      | Formula.Atom _ -> f
      | Formula.UnaryOp (op, f1, info) -> Formula.mk_unop ~info op (rf f1)
      | Formula.BinaryOp (op, f1, f2, info) ->
          Formula.mk_binop ~info op (rf f1) (rf f2)
      | Formula.Bind (binder, bound, body, info) ->
          if List.exists bound ~f:(fun (y, _) -> blocked y) then f
          else Formula.mk_bind ~info binder bound (rf body)
      | Formula.LetRec _ -> f
      | Formula.LetFormula (y, sort, d, body, info) ->
          Formula.mk_let_formula ~info y sort (rt d)
            (if blocked y then body else rf body)
    in
    rf
  in
  let changed = ref false in
  let rec go phi =
    match phi with
    | Formula.BinaryOp (Formula.And, _, _, _) ->
        Formula.and_of @@ List.map ~f:go @@ Formula.conjuncts_list_of phi
    | Formula.BinaryOp (Formula.Or, _, _, _) ->
        let ds = Array.of_list @@ Formula.disjuncts_list_of phi in
        for k = 0 to Array.length ds - 1 do
          match definition ds.(k) with
          | None -> ()
          | Some def ->
              let rep = replace def in
              Array.iteri ds ~f:(fun k' d ->
                  if k <> k' then (
                    let d' = rep d in
                    if not (Stdlib.( = ) d d') then changed := true;
                    ds.(k') <- d'))
        done;
        Formula.or_of @@ List.map ~f:go @@ Array.to_list ds
    | _ -> phi
  in
  let phi' = go (Formula.nnf_of phi) in
  if !changed then phi' else phi

(* The two rewrites above, for a formula that is about to be asked for
   VALIDITY: the definitions first, so that a read of a defined variable becomes
   a read of the constructor, then every read of a concatenation split by index.
   Both preserve validity (the first per clause, the second in every model), so
   the question asked is the same one; a formula that reads no sequence is
   returned as it is.  One application only, for the reason given at
   [seq_read_over_concat]: this belongs on a query, never inside a fixpoint of
   simplification. *)
let split_seq_reads_for_validity phi =
  if
    Set.exists (Formula.funsyms_of phi) ~f:(function
      | T_seq.SqNth _ -> true
      | _ -> false)
  then rewrite_seq_read_over_concat @@ subst_seq_definitions phi
  else phi

(* An existential over a sequence that the body reads only through its LENGTH
   is an arithmetic condition, and eliminating it is what makes such a clause
   decidable at all.

   The law: for a non-empty element sort, every non-negative length is realised
   by some sequence, so [exists v. phi(seq.len v)] is [exists n >= 0. phi(n)].
   Both directions were checked against z3 and cvc5 rather than recalled --
   a sequence's length is never negative (asserting one is `unsat` in both), and
   lengths 0, 1 and 7 are all realised (`sat` in both).  The equivalence at a
   SYMBOLIC length neither solver decides, which is precisely why the clause it
   appears in is not answered and why this rewrite exists.

   A read at the last position is admitted with it -- [seq.nth v (seq.len v - 1)]
   -- because a sequence of a given length with a given last element exists
   whenever the length is positive, so it constrains nothing beyond the length.
   Any OTHER occurrence of the bound variable disqualifies the rewrite: a read
   at an arbitrary index, a concatenation, an equality between sequences all say
   something the length does not, and the elimination would then be a claim the
   theory does not make. *)
let seq_existential_is_length_only x body =
  let rec ok_term t =
    match t with
    | Term.Var (y, _, _) -> Stdlib.(y <> x)
    | Term.FunApp (T_seq.SqLen _, [ Term.Var (y, _, _) ], _) when Stdlib.(y = x)
      ->
        true
    | Term.FunApp (T_seq.SqNth _, [ Term.Var (y, _, _); i ], _)
      when Stdlib.(y = x) -> (
        (* only the last position, written as [len - 1] *)
        match i with
        | Term.FunApp
            ( T_int.Add,
              [
                Term.FunApp (T_seq.SqLen _, [ Term.Var (z, _, _) ], _);
                Term.FunApp (T_int.Int n, [], _);
              ],
              _ )
          when Stdlib.(z = x) && Z.Compare.(n = Z.minus_one) ->
            true
        | Term.FunApp
            ( T_int.Sub,
              [
                Term.FunApp (T_seq.SqLen _, [ Term.Var (z, _, _) ], _);
                Term.FunApp (T_int.Int n, [], _);
              ],
              _ )
          when Stdlib.(z = x) && Z.Compare.(n = Z.one) ->
            true
        | _ -> false)
    | Term.FunApp (_, args, _) -> List.for_all args ~f:ok_term
    | Term.LetTerm (_, _, def, b, _) -> ok_term def && ok_term b
  in
  let rec ok_formula phi =
    match phi with
    | Formula.Atom (atom, _) -> Set.for_all (Atom.terms_of atom) ~f:ok_term
    | Formula.UnaryOp (_, phi1, _) -> ok_formula phi1
    | Formula.BinaryOp (_, phi1, phi2, _) -> ok_formula phi1 && ok_formula phi2
    | Formula.Bind (_, _, phi1, _) -> ok_formula phi1
    | Formula.LetRec (_, phi1, _) -> ok_formula phi1
    | Formula.LetFormula (_, _, def, phi1, _) -> ok_term def && ok_formula phi1
  in
  ok_formula body

(* Replace such an existential by one over the length.  The bound sequence
   variable becomes a bound integer, [seq.len x] becomes that integer, and a
   read at the last position becomes a fresh variable of the ELEMENT sort --
   which is what "some sequence with this length and this last element" says
   when the length is positive.  At length 0 the only sequence is the empty
   one and the read at [len - 1 = -1] is the open term [seq.nth seq.empty (-1)],
   one fixed value in each model, not a free choice: treating it as free made
   [exists w. len w = 0 /\ nth w (len w - 1) = y] true for every [y], where z3
   finds a [y] for which it is false.  So the read becomes
   [if n >= 1 then last else seq.nth seq.empty (-1)], which is exact in every
   model.  The non-negativity the sequence carried implicitly is stated
   explicitly, because an integer does not carry it. *)
let eliminate_seq_existential (x, sort) body =
  let se = T_seq.elem_sort_of sort in
  let n = Ident.mk_fresh_tvar () in
  let nt = Term.mk_var n T_int.SInt in
  let last = Ident.mk_fresh_tvar () in
  let lastt =
    T_bool.mk_if_then_else
      (T_bool.of_formula @@ Formula.geq nt (T_int.one ()))
      (Term.mk_var last se)
      (T_seq.mk_nth se (T_seq.mk_empty se) (T_int.mk_int Z.minus_one))
  in
  let rec on_term t =
    match t with
    | Term.FunApp (T_seq.SqLen _, [ Term.Var (y, _, _) ], _) when Stdlib.(y = x)
      ->
        nt
    | Term.FunApp (T_seq.SqNth _, [ Term.Var (y, _, _); _ ], _)
      when Stdlib.(y = x) ->
        lastt
    | Term.FunApp (fsym, args, info) ->
        Term.mk_fsym_app ~info fsym (List.map args ~f:on_term)
    | Term.LetTerm (y, sort, def, b, info) ->
        Term.mk_let_term ~info y sort (on_term def) (on_term b)
    | Term.Var _ -> t
  in
  Formula.exists
    [ (n, T_int.SInt); (last, se) ]
    (Formula.and_of
       [
         Formula.leq (T_int.zero ()) nt;
         Formula.map_term_no_binders ~f:on_term body;
       ])

(* One formula: every existential over a sequence whose body reads it only
   through its length is replaced.  Nothing else is touched. *)
let rec elim_seq_existentials phi =
  match phi with
  | Formula.Atom _ -> phi
  | Formula.UnaryOp (op, phi1, info) ->
      Formula.mk_unop ~info op (elim_seq_existentials phi1)
  | Formula.BinaryOp (op, phi1, phi2, info) ->
      Formula.mk_binop ~info op
        (elim_seq_existentials phi1)
        (elim_seq_existentials phi2)
  | Formula.Bind (Formula.Exists, [ ((x, sort) as b) ], phi1, info)
    when (match sort with T_seq.SSeq _ -> true | _ -> false)
         && seq_existential_is_length_only x phi1 ->
      ignore info;
      eliminate_seq_existential b (elim_seq_existentials phi1)
  | Formula.Bind (binder, senv, phi1, info) ->
      Formula.mk_bind ~info binder senv (elim_seq_existentials phi1)
  | Formula.LetRec _ | Formula.LetFormula _ -> phi

(* The ONE-POINT RULE, the SINGLE-CONSTRUCTOR SPLIT and the SEQUENCE-LENGTH
   SPLIT, iterated to a fixpoint over the quantifiers of a formula's
   propositional spine.

   Contract: the result is equivalent to the input in every model of the
   background theory (every sort non-empty, as SMT-LIB requires), and its free
   variables are a subset of the input's -- a free variable can disappear, when
   the only thing said about it was an equation a bound variable absorbed, but
   none is introduced.  Three rewrites, each an equivalence:

   (1) one-point.  [exists x. x = t /\ phi] is [phi[t/x]], and dually
       [forall x. x <> t \/ phi] is [phi[t/x]], provided [x] does not occur in
       [t].  The equation may be written either way round, may be [not (x <> t)]
       under an existential or [not (x = t)] under a universal, and may be
       [x + a = b], [a - x = b], [-x = b] over the integers or the reals, which
       is solved for [x] exactly because its coefficient is one: no division is
       introduced.  The equation must be a TOP-LEVEL conjunct (existential) or
       disjunct (universal; the premise of an implication counts, negated) of
       the binder's body, which is what makes the body at [x := t] equal to
       the quantified formula.  Variables bound in the same block may occur in
       [t]; they stay bound.  [x] may have any sort, a sequence included.

   (2) single-constructor split.  A bound variable whose sort is an inductive
       datatype with exactly ONE constructor [c(s1 .. sn)] -- a tuple, a
       record, a reference wrapper -- is replaced by [c(y1 .. yn)] over fresh
       bound [yi : si].  Every value of such a sort is [c] applied to its
       fields, so the two quantifications range over the same values.  A
       selector applied to a constructor application is then folded to the
       field, which is what lets (1) fire on [0 = sel_2 x] once [x] is
       [c(y1, y2)].  A datatype whose constructor takes a field of its own sort
       is not split (it would unfold for ever), nor is a codatatype.

   (3) sequence-length split.  A bound sequence variable [s] whose length a
       top-level literal fixes at a literal [n] (0 <= n <= 4), read as (1)
       reads an equation -- [seq.len s = n] solved for [seq.len s] under an
       existential, its negation under a universal -- is replaced by
       [seq.unit e1 ++ .. ++ seq.unit en] over fresh bound elements (the empty
       sequence when [n = 0]).  The sequences of length [n] are exactly those
       terms, so the literal becomes [n = n] and the quantification ranges over
       the same values.  A length, and a read at a literal index inside the
       sequence, of such a term is then folded; a read outside it is left as it
       is, since the theory does not fix its value.

   Unused bound variables are dropped ([exists y. phi] is [phi] when [y] does
   not occur in [phi], the sort being non-empty).

   Why it exists: a solver instantiates a quantifier with the ground terms the
   query already contains, and a quantifier over a pair that only a selector
   ever reads, or a bound variable standing for a term the query spells out,
   gives it nothing to instantiate with -- Z3 answers "incomplete (theory
   array)" on such a validity question and decides the rewritten one.

   Scope: only [Forall]/[Exists] nodes of the formula itself are rewritten.  A
   quantifier inside a TERM -- an embedded formula, an array lambda -- is left
   alone, and nothing is lifted out through such a binder; the selector and
   sequence folding does reach inside terms, which is harmless because each
   folded identity holds wherever it is written.  [let] and [letrec] nodes and
   probabilistic binders are left untouched. *)

(* [lhs = rhs] rewritten as [target = t] with no target in [t], where that is
   exact: the target occurs once, under [+], [-] and unary [-] only (integer or
   real), so its coefficient is one and no division is introduced.  [target] is
   a bound variable for the one-point rule and [seq.len s] for the
   sequence-length split. *)
let isolate_target ~is_target ~occurs lhs rhs =
  let rec go lhs rhs =
    if is_target lhs then Some rhs
    else
      match lhs with
      | Term.FunApp (T_int.Add, [ a; b ], _) ->
          if occurs a && not (occurs b) then go a (T_int.mk_sub rhs b)
          else if occurs b && not (occurs a) then go b (T_int.mk_sub rhs a)
          else None
      | Term.FunApp (T_int.Sub, [ a; b ], _) ->
          if occurs a && not (occurs b) then go a (T_int.mk_add rhs b)
          else if occurs b && not (occurs a) then go b (T_int.mk_sub a rhs)
          else None
      | Term.FunApp (T_int.Neg, [ a ], _) -> go a (T_int.mk_neg rhs)
      | Term.FunApp (T_real.RAdd, [ a; b ], _) ->
          if occurs a && not (occurs b) then go a (T_real.mk_rsub rhs b)
          else if occurs b && not (occurs a) then go b (T_real.mk_rsub rhs a)
          else None
      | Term.FunApp (T_real.RSub, [ a; b ], _) ->
          if occurs a && not (occurs b) then go a (T_real.mk_radd rhs b)
          else if occurs b && not (occurs a) then go b (T_real.mk_rsub a rhs)
          else None
      | Term.FunApp (T_real.RNeg, [ a ], _) -> go a (T_real.mk_rneg rhs)
      | _ -> None
  in
  match (occurs lhs, occurs rhs) with
  | true, false -> go lhs rhs
  | false, true -> go rhs lhs
  | _ -> None

(* the two sides of the equation a literal states when read under [binder]:
   an equality under an existential, a disequality under a universal *)
let equation_of_literal binder lit =
  match (binder, lit) with
  | ( Formula.Exists,
      Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _) )
  | ( Formula.Exists,
      Formula.UnaryOp
        ( Formula.Not,
          Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _),
          _ ) )
  | ( Formula.Forall,
      Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _) )
  | ( Formula.Forall,
      Formula.UnaryOp
        ( Formula.Not,
          Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
          _ ) ) ->
      Some (t1, t2)
  | _ -> None

(* the top-level literals of a binder's body: its conjuncts under an
   existential, its disjuncts under a universal (where the premise of an
   implication contributes its conjuncts negated) *)
let spine_literals binder body =
  match binder with
  | Formula.Exists -> Formula.conjuncts_list_of body
  | _ ->
      let rec disj = function
        | Formula.BinaryOp (Formula.Or, p1, p2, _) -> disj p1 @ disj p2
        | Formula.BinaryOp (Formula.Imply, p1, p2, _) ->
            List.map (Formula.conjuncts_list_of p1) ~f:Formula.mk_neg @ disj p2
        | p -> [ p ]
      in
      disj body

(* [x] as a one-point variable of [lit]: the term the equation defines it as *)
let point_of_literal binder x lit =
  Option.bind (equation_of_literal binder lit) ~f:(fun (t1, t2) ->
      let occurs t = Set.mem (Term.tvs_of t) x in
      let is_target = function
        | Term.Var (y, _, _) -> Ident.tvar_equal x y
        | _ -> false
      in
      isolate_target ~is_target ~occurs t1 t2)

(* the largest length the sequence-length split writes out as units *)
let max_seq_length_split = 4

(* [s] as a sequence whose length [lit] fixes: that length *)
let seq_length_of_literal binder s lit =
  Option.bind (equation_of_literal binder lit) ~f:(fun (t1, t2) ->
      let is_target = function
        | Term.FunApp (T_seq.SqLen _, [ Term.Var (y, _, _) ], _) ->
            Ident.tvar_equal s y
        | _ -> false
      in
      (* the target must be the ONLY occurrence of [s] in the equation *)
      let occurs t = Set.mem (Term.tvs_of t) s in
      (* the isolated side is ground arithmetic over literals, [2 - 0] say *)
      let rec value_of = function
        | Term.FunApp (T_int.Int n, [], _) -> Some n
        | Term.FunApp (T_int.Add, [ a; b ], _) ->
            Option.map2 (value_of a) (value_of b) ~f:Z.( + )
        | Term.FunApp (T_int.Sub, [ a; b ], _) ->
            Option.map2 (value_of a) (value_of b) ~f:Z.( - )
        | Term.FunApp (T_int.Neg, [ a ], _) -> Option.map (value_of a) ~f:Z.neg
        | _ -> None
      in
      match Option.bind (isolate_target ~is_target ~occurs t1 t2) ~f:value_of with
      | Some n when Z.(leq zero n && leq n (of_int max_seq_length_split)) ->
          Some (Z.to_int n)
      | _ -> None)

(* identities over constructor applications, valid wherever they are written:
   a selector of a constructor application is its field (when the constructor
   is the selector's), the length of a sequence built from units is its count,
   and a read at a literal index inside such a sequence is the element there *)
let fold_constructor_reads =
  Formula.map_term ~f:(function
    | Term.FunApp (T_dt.DTSel (sel, dt, _), [ t ], _) as t0 -> (
        match T_dt.eval_select sel dt t with Some t' -> t' | None -> t0)
    | Term.FunApp (T_seq.SqLen _, [ sq ], _) as t0 -> (
        match seq_len_of sq with Some n -> T_int.mk_int n | None -> t0)
    | Term.FunApp (T_seq.SqNth _, [ sq; Term.FunApp (T_int.Int k, [], _) ], _)
      as t0 -> (
        match seq_nth_of_literal sq k with Some e -> e | None -> t0)
    | t -> t)

let splittable_sort = function
  | T_dt.SDT dt when Datatype.is_dt dt -> (
      match Datatype.conses_of dt with
      | [ cons ] ->
          let fields = Datatype.sorts_of_cons dt cons in
          if
            List.exists fields ~f:(function
              | T_dt.SDT dt' ->
                  String.(Datatype.name_of dt' = Datatype.name_of dt)
              | _ -> false)
          then None
          else Some (dt, cons, fields)
      | _ -> None)
  | _ -> None

(* at most this many rounds of splitting per binder: a mutually recursive pair
   of single-constructor datatypes would otherwise unfold for ever *)
let max_split_rounds = 8

(* The variables [x] of [phi] that occur as the argument of a selector,
   [sel(x)].  Collected over every term of [phi], binders' bodies included, so
   a bound variable that shares a free one's name also counts; that can only
   admit a split, and every split is exact. *)
let selected_vars phi =
  let acc = ref Set.Poly.empty in
  ignore
  @@ Formula.map_term phi ~f:(function
    | Term.FunApp (T_dt.DTSel _, [ Term.Var (x, _, _) ], _) as t ->
        acc := Set.add !acc x;
        t
    | t -> t);
  !acc

let rec split_single_cons_binders ?(selected_only = false) changed senv body
    round =
  if round >= max_split_rounds then (senv, body)
  else
    let selected = if selected_only then selected_vars body else Set.Poly.empty in
    let senv', sub =
      List.fold_right senv ~init:([], Map.Poly.empty)
        ~f:(fun (x, sort) (acc, sub) ->
          match splittable_sort sort with
          | Some _ when selected_only && not (Set.mem selected x) ->
              ((x, sort) :: acc, sub)
          | Some (dt, cons, sorts) ->
              let fields =
                List.map sorts ~f:(fun s -> (Ident.mk_fresh_tvar (), s))
              in
              let t =
                T_dt.mk_cons dt (Datatype.name_of_cons cons)
                @@ List.map fields ~f:(fun (f, s) -> Term.mk_var f s)
              in
              (fields @ acc, Map.Poly.add_exn sub ~key:x ~data:t)
          | None -> ((x, sort) :: acc, sub))
    in
    if Map.Poly.is_empty sub then (senv, body)
    else (
      changed := true;
      split_single_cons_binders ~selected_only changed senv'
        (fold_constructor_reads @@ Formula.subst sub body)
        (round + 1))

(* The single-constructor split applied to a clause's own universally
   quantified variables, which a clause set leaves implicit: [senv] is the
   clause's variable environment and [phi] its body.

   Contract: for every variable [x] of [senv] that is free in [phi] and whose
   sort is an inductive datatype with exactly one constructor [c(s1 .. sn)]
   none of whose fields has the datatype's own sort, [x] is replaced by
   [c(y1 .. yn)] over fresh [yi : si], and the fields that are themselves of
   such a sort are split in turn, at most [max_split_rounds] levels deep (the
   bound only matters for a mutually recursive pair of single-constructor
   datatypes, which would otherwise unfold for ever).  Selectors applied to the
   new constructor applications are then folded to the fields.  The returned
   environment is [senv] without the split variables and with the fresh ones;
   the result is EQUIVALENT to the input under the universal closure over its
   environment, in every model of the theory, because every value of such a
   datatype equals its constructor applied to its selectors (the fields range
   over all values of their sorts, as the variable ranged over all values of
   its own).  The third component is the number of variables split at the top
   level; 0 means the input came back untouched.

   Left alone: a sort with several constructors (there [x = c(..)] would also
   say WHICH constructor [x] is, a restriction rather than an identity), a
   datatype whose constructor takes a field of its own sort, a codatatype, a
   variable of [senv] that does not occur free, and the whole clause when it
   contains a [let] or [letrec] node, since the substitution below is not
   promised to respect those binders.  Quantifiers of the formula and binders
   inside terms need no special care: the substitution is capture-avoiding
   (a binder that shadows [x] keeps its own [x], and the fresh [yi] cannot be
   captured by anything already in the formula).

   With [~selected_only:true] a variable is split only when it occurs as the
   argument of a selector somewhere in the clause, and a field variable the
   split creates only when it is itself read through a selector (a nested
   projection [sel2 (sel1 x)] becomes [sel2 y1] once [x] is split).  A
   variable that the clause only passes whole -- to an unknown, to a function,
   to an equation with another variable -- is left as it is: splitting it adds
   variables and turns its occurrences into constructor applications without
   freeing any projection.  Every split made is the same identity, so the
   result is still equivalent to the input. *)
let split_single_cons_free_vars ?(selected_only = false) (senv : sort_env_map)
    phi =
  if not (Formula.is_let_free phi) then (senv, phi, 0)
  else
    let fvs = Formula.tvs_of phi in
    let selected = if selected_only then selected_vars phi else fvs in
    let cands =
      Map.Poly.to_alist
      @@ Map.Poly.filteri senv ~f:(fun ~key ~data ->
          Set.mem fvs key && Set.mem selected key
          && Option.is_some (splittable_sort data))
    in
    if List.is_empty cands then (senv, phi, 0)
    else
      let split_names = Set.Poly.of_list (List.map cands ~f:fst) in
      let senv', phi' =
        split_single_cons_binders ~selected_only (ref false) cands phi 0
      in
      let rest = Map.Poly.filter_keys senv ~f:(Fn.non (Set.mem split_names)) in
      ( Map.force_merge rest (Map.Poly.of_alist_exn senv'),
        phi',
        List.length cands )

(* Is an equation between two applications of one constructor split into
   the equations of their fields, inside [elim_onepoint_and_split_binders]?
   Switched per process by the caller, off unless set. *)
let split_constructor_equations = ref false

(* Constructor injectivity: [C(a1..an) = C(b1..bn)] holds exactly when every
   [ai = bi] does, and [C(a1..an) != C(b1..bn)] exactly when some [ai != bi],
   in every model of an (inductive) datatype theory, since its constructors
   are injective.  Applied to nested applications too.  An equation between
   two different constructors is left as it is.  What it buys: after the
   single-constructor split replaces a bound tuple by an application of its
   constructor to fresh variables, an equation of that application with a
   literal tuple becomes one equation per field, which the one-point rule
   then eliminates -- and a sequence whose length such a field fixed can
   then be written out as units. *)
let split_cons_equations changed phi =
  let same_cons t1 t2 =
    match (t1, t2) with
    | ( Term.FunApp (T_dt.DTCons (n1, _, dt), as1, _),
        Term.FunApp (T_dt.DTCons (n2, _, _), as2, _) )
      when String.(n1 = n2)
           && Datatype.is_dt dt
           && List.length as1 = List.length as2 ->
        Some (as1, as2)
    | _ -> None
  in
  let rec split atom =
    match atom with
    | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) -> (
        match same_cons t1 t2 with
        | Some (as1, as2) ->
            changed := true;
            Formula.and_of
              (List.map2_exn as1 as2 ~f:(fun a b -> split (T_bool.mk_eq a b)))
        | None -> Formula.mk_atom atom)
    | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) -> (
        match same_cons t1 t2 with
        | Some (as1, as2) ->
            changed := true;
            Formula.or_of
              (List.map2_exn as1 as2 ~f:(fun a b -> split (T_bool.mk_neq a b)))
        | None -> Formula.mk_atom atom)
    | _ -> Formula.mk_atom atom
  in
  Formula.map_atom ~f:split phi

(* Exact cancellation of a common prefix and suffix across a sequence
   equation: an atom [s = t] or [s != t] whose sides are sequences is read as
   two lists of concatenation operands (associativity, empty sequences
   dropped), the longest common prefix of syntactically equal operands is
   removed, then the longest common suffix of what is left, and the atom is
   rebuilt over the remainders.  Exact in every model because sequences under
   concatenation form a free monoid, which is cancellative on both sides:
   [a ++ x = a ++ y] iff [x = y], and [x ++ a = y ++ a] iff [x = y].  When
   both remainders are empty the equation is [true] (its negation [false]).

   What it is for: once a clause's projections of a tuple are plain variables,
   the predicate elimination substitutes the premises that define one of them,
   [v1 = v0 ++ v3], into the others, and an equation such as
   [v10 ++ w = (v10 ++ v4) ++ v3] appears where the input had
   [p.2 x2 ++ w = p.2 x1]; Z3's sequence solver and the zero-unknown check's
   sequence instantiation both decide the cancelled form [w = v4 ++ v3] far
   more easily, and the one-point rule can then eliminate [w].

   Returns the formula physically unchanged when no atom changes. *)
let cancel_seq_concat_equations phi =
  let flatten t =
    let rec go t acc =
      match t with
      | Term.FunApp (T_seq.SqConcat _, [ t1; t2 ], _) -> go t1 (go t2 acc)
      | Term.FunApp (T_seq.SqEmpty _, [], _) -> acc
      | _ -> t :: acc
    in
    go t []
  in
  let concat_of se = function
    | [] -> T_seq.mk_empty se
    | t :: ts -> List.fold ts ~init:t ~f:(T_seq.mk_concat se)
  in
  let rec drop_common = function
    | a :: xs, b :: ys when Stdlib.(a = b) -> drop_common (xs, ys)
    | p -> p
  in
  let elem_sort t1 t2 =
    match (Term.sort_of t1, Term.sort_of t2) with
    | T_seq.SSeq se, _ | _, T_seq.SSeq se -> Some se
    | _ -> None
  in
  let rewrite eq t1 t2 =
    match elem_sort t1 t2 with
    | None -> None
    | Some se ->
        let l1 = flatten t1 and l2 = flatten t2 in
        let r1, r2 = drop_common (l1, l2) in
        let r1, r2 =
          let s1, s2 = drop_common (List.rev r1, List.rev r2) in
          (List.rev s1, List.rev s2)
        in
        if List.length r1 = List.length l1 && List.length r2 = List.length l2
        then None
        else if List.is_empty r1 && List.is_empty r2 then
          Some (if eq then Formula.mk_true () else Formula.mk_false ())
        else
          let u1 = concat_of se r1 and u2 = concat_of se r2 in
          Some (if eq then Formula.eq u1 u2 else Formula.neq u1 u2)
  in
  let changed = ref false in
  let phi' =
    Formula.map_atom phi ~f:(fun atom ->
        let res =
          match atom with
          | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) ->
              rewrite true t1 t2
          | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) ->
              rewrite false t1 t2
          | _ -> None
        in
        match res with
        | Some f ->
            changed := true;
            f
        | None -> Formula.mk_atom atom)
  in
  if !changed then phi' else phi

(* Is a read of a bound array fixed by a top-level literal eliminated,
   inside [elim_onepoint_and_split_binders]?  Switched per process by the
   caller, off unless set.

   The rule (array-read one-point): for a bound array [s] and a top-level
   literal stating [select s k = t] (under an existential; its negation under
   a universal) where neither [k] nor [t] mentions [s],
     [exists s. L(s) /\ select s k = t]  is  [exists s. L(store s k t)]
     [forall s. select s k != t \/ R(s)] is  [forall s. R(store s k t)]
   with [s] still bound.  Exact under extensionality (the SMT-LIB theory
   ArraysEx): an [s] with [select s k = t] IS [store s k t], and every
   [store s' k t] reads [t] at [k].  What it buys: a validity question whose
   disjunct [exists s. not P(s) /\ select s 0 = x] needs a witness array
   reading [x] at [0], a term the question does not contain, so Z3 answers
   "incomplete quantifiers"; after the rewrite the witness shape is spelled
   out and the question is decided. *)
let onepoint_array_reads = ref false

(* [simplify], defined further down, for the pointwise rule: it beta-reduces
   a read of the substituted lambda and folds the ground part of its guard *)
let simplify_hook : (Formula.t -> Formula.t) ref = ref Fn.id

(* [s] as a bound array whose read [lit] fixes: the index and the value *)
(* [t1 = t2] solved for a read [select s k] of the array variable [s]:
   the read and the term it equals, when [s] occurs nowhere else in the
   equation and the read is isolated with coefficient one (as the one-point
   rule isolates a variable), so [0 = s[i] - (x + i)] gives [s[i], x + i] *)
let isolate_array_read s t1 t2 =
  let occurs t = Set.mem (Term.tvs_of t) s in
  let reads =
    Set.to_list
    @@ Formula.filtered_terms_of (Formula.eq t1 t2) ~f:(function
      | Term.FunApp (T_array.ASelect _, [ Term.Var (y, _, _); k ], _) ->
          Ident.tvar_equal s y && not (occurs k)
      | _ -> false)
  in
  match reads with
  | [ r ] ->
      Option.map
        (isolate_target ~is_target:(Stdlib.( = ) r) ~occurs t1 t2)
        ~f:(fun u -> (r, u))
  | _ -> None

let array_read_of_literal binder s lit =
  Option.bind (equation_of_literal binder lit) ~f:(fun (t1, t2) ->
      Option.bind (isolate_array_read s t1 t2) ~f:(function
        | Term.FunApp (T_array.ASelect _, [ _; k ], _), u -> Some (k, u)
        | _ -> None))

(* [s] as a bound array whose reads over an integer range [lit] fixes
   pointwise: [lit] is [forall i. R(i) \/ select s (i + c) = u(i)] (the
   disjunction also as an implication), [R] and [u] not mentioning [s], and
   the result is the array [lam j. ite (not R(j - c)) u(j - c) (select s j)].
   Under an existential,
     [exists s. L(s) /\ lit]  is  [exists s. L(lam j. ...)]
   and dually [forall s. not lit \/ R(s)] is [forall s. R(lam j. ...)],
   with [s] still bound, exact under extensionality: an [s] satisfying [lit]
   IS that array, pointwise, and the array satisfies [lit] ([i |-> i + c] is
   a bijection of the integers).  The shape is how a sequence shifted by
   [c] positions is stated in the array encoding of sequences, e.g. the
   tail of a witness that prepends one element.

   The rule fires only when [not R(i)] confines [i] to an interval bounded
   on both sides, so that the lambda differs from [s] at finitely many
   indices and is [s] under finitely many [store]s.  That is what makes it
   exact over every model of the array theory and not only over the full
   function space: the theory's axioms (read over write, extensionality)
   also have models whose arrays are, say, exactly the functions differing
   from a constant function at finitely many indices, and those models are
   closed under [store] but contain no array for an unbounded pointwise
   definition.  Over such a model [exists s. forall i. select s i = i] is
   false while its rewrite, [exists s. true], is true, so an unbounded
   rewrite turned an invalid clause into a valid one. *)
let int_interval_bounded x phi =
  (* the coefficient of [x] in [t] when [t] is affine in [x] (its other
     part may be any term [x] does not occur in) *)
  let rec coeff t =
    if not (Set.mem (Term.tvs_of t) x) then Some Z.zero
    else
      match t with
      | Term.Var (y, _, _) when Ident.tvar_equal x y -> Some Z.one
      | Term.FunApp (T_int.Add, [ a; b ], _) ->
          Option.map2 (coeff a) (coeff b) ~f:Z.add
      | Term.FunApp (T_int.Sub, [ a; b ], _) ->
          Option.map2 (coeff a) (coeff b) ~f:Z.sub
      | Term.FunApp (T_int.Neg, [ a ], _) -> Option.map (coeff a) ~f:Z.neg
      | Term.FunApp (T_int.Mul, [ Term.FunApp (T_int.Int n, [], _); a ], _)
      | Term.FunApp (T_int.Mul, [ a; Term.FunApp (T_int.Int n, [], _) ], _) ->
          Option.map (coeff a) ~f:(Z.mul n)
      | _ -> None
  in
  (* (gives a lower bound, gives an upper bound) for [t1 psym t2], with
     [neg] when the atom occurs negated *)
  let bounds neg psym t1 t2 =
    match (coeff t1, coeff t2) with
    | Some a1, Some a2 when not (Z.equal a1 a2) -> (
        let pos = Z.gt (Z.sub a1 a2) Z.zero in
        (* [a * x <= r] bounds [x] above when [a > 0], below otherwise *)
        let le = (not pos, pos) and ge = (pos, not pos) in
        match (psym, neg) with
        | (T_int.Leq | T_int.Lt), false | (T_int.Geq | T_int.Gt), true -> le
        | (T_int.Geq | T_int.Gt), false | (T_int.Leq | T_int.Lt), true -> ge
        | T_bool.Eq, false | T_bool.Neq, true -> (true, true)
        | _ -> (false, false))
    | _ -> (false, false)
  in
  let lo, hi =
    List.fold
      (Formula.conjuncts_list_of (Formula.nnf_of phi))
      ~init:(false, false)
      ~f:(fun (lo, hi) c ->
        let l, h =
          match c with
          | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) ->
              bounds false psym t1 t2
          | Formula.UnaryOp
              ( Formula.Not,
                Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _),
                _ ) ->
              bounds true psym t1 t2
          | _ -> (false, false)
        in
        (lo || l, hi || h))
  in
  lo && hi

let array_pointwise_of_literal ~outer s sort lit =
  match (sort, lit) with
  | ( T_array.SArray ((T_int.SInt as si), se),
      Formula.Bind (Formula.Forall, [ (i, T_int.SInt) ], body, _) ) -> (
      let occurs_s phi = Set.mem (Formula.tvs_of phi) s in
      let rec disj = function
        | Formula.BinaryOp (Formula.Or, p1, p2, _) -> disj p1 @ disj p2
        | Formula.BinaryOp (Formula.Imply, p1, p2, _) ->
            List.map (Formula.conjuncts_list_of p1) ~f:Formula.mk_neg @ disj p2
        | p -> [ p ]
      in
      (* [t] as [a * i + c] over literals, when it is such a term *)
      let rec lin t =
        match t with
        | Term.Var (y, _, _) when Ident.tvar_equal i y -> Some (Z.one, Z.zero)
        | Term.FunApp (T_int.Int c, [], _) -> Some (Z.zero, c)
        | Term.FunApp (T_int.Add, [ a; b ], _) ->
            Option.map2 (lin a) (lin b) ~f:(fun (a1, c1) (a2, c2) ->
                (Z.(a1 + a2), Z.(c1 + c2)))
        | Term.FunApp (T_int.Sub, [ a; b ], _) ->
            Option.map2 (lin a) (lin b) ~f:(fun (a1, c1) (a2, c2) ->
                (Z.(a1 - a2), Z.(c1 - c2)))
        | Term.FunApp (T_int.Neg, [ a ], _) ->
            Option.map (lin a) ~f:(fun (a1, c1) -> (Z.neg a1, Z.neg c1))
        | Term.FunApp (T_int.Mul, [ a; b ], _) -> (
            match (lin a, lin b) with
            | Some (a1, c1), Some (a2, c2) when Z.(equal a1 zero) ->
                Some (Z.(c1 * a2), Z.(c1 * c2))
            | Some (a1, c1), Some (a2, c2) when Z.(equal a2 zero) ->
                Some (Z.(a1 * c2), Z.(c1 * c2))
            | _ -> None)
        | _ -> None
      in
      (* [c] when [t] is [i + c] *)
      let offset_of t =
        match lin t with
        | Some (a, c) when Z.(equal a one) -> Some c
        | _ -> None
      in
      let pointwise = function
        | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _)
          -> (
            (* [s[i] = a[i + c]] with [c] nonzero and [a] mentioning a
               variable bound further out -- the array of a tuple the
               enclosing block has not split yet, say -- is left for the
               enclosing block, which takes the shifted array instead (see
               the preference at the call) *)
            let shifted_outer = function
              | Term.FunApp (T_array.ASelect _, [ a; k ], _) -> (
                  (not (Set.is_empty (Set.inter (Term.tvs_of a) outer)))
                  &&
                  match offset_of k with
                  | Some c -> not (Z.equal c Z.zero)
                  | None -> false)
              | _ -> false
            in
            match isolate_array_read s t1 t2 with
            | Some (Term.FunApp (T_array.ASelect _, [ _; k ], _), u) -> (
                match offset_of k with
                | Some c when Z.equal c Z.zero && shifted_outer u -> None
                | Some c -> Some (c, u)
                | None -> None)
            | _ -> None)
        | _ -> None
      in
      let ds = disj body in
      match
        List.filter_mapi ds ~f:(fun k d ->
            Option.map (pointwise d) ~f:(fun cu -> (k, cu)))
      with
      | [ (k, (c, u)) ] ->
          let rest = List.filteri ds ~f:(fun k' _ -> k' <> k) in
          if List.exists rest ~f:occurs_s then None
          else if
            not (int_interval_bounded i (Formula.mk_neg (Formula.or_of rest)))
          then None
          else
            let nonzero = not (Z.equal c Z.zero) in
            let j = Ident.mk_fresh_tvar () in
            let back =
              Map.Poly.singleton i
                (T_int.mk_sub (Term.mk_var j T_int.SInt) (T_int.mk_int c))
            in
            let guard =
              Formula.mk_neg (Formula.subst back (Formula.or_of rest))
            in
            Some
              ( nonzero,
                T_array.mk_lambda (j, si) se
                  (T_bool.ifte guard (Term.subst back u)
                     (T_array.mk_select si se (Term.mk_var s sort)
                        (Term.mk_var j T_int.SInt))) )
      | _ -> None)
  | _ -> None

(* Is an equation between a term and a constructor application of a
   single-constructor type split into the equations of the fields, inside
   [elim_onepoint_and_split_binders]?  Switched per process by the caller, off
   unless set.

   The rule (surjective pairing): for a datatype or tuple with ONE
   constructor [C], every value [u] is [C(sel_1 u, .., sel_n u)], and [C] is
   injective, so
     [u = C(a_1, .., a_n)]  is  [sel_1 u = a_1 /\ .. /\ sel_n u = a_n]
   in every model, and dually [u != C(..)] is the disjunction of the fields'
   disequations.  It is applied to a top-level literal of a binder's body
   when some [a_i] is a variable of that binder not occurring in [u], so the
   one-point rule then eliminates it as [sel_i u]:
   [exists v1 v2. t.0 = tuple(v1, v2) /\ phi] becomes [phi[t.0.0/v1, t.0.1/v2]]
   where the projection [t.0] is no constructor application and the plain
   rule does not fire.  Not for a type with several constructors, where
   [u = C(..)] also states which constructor [u] is built with. *)
let surjective_pairing = ref false

(* Does [surjective_pairing] also split an equation whose constructor side has
   an argument that MENTIONS a variable of the binder (not occurring in the
   other side) without being one?  Switched per process by the caller, off
   unless set.  The split is the same identity, so exact; what changes is
   only when it fires.  What it buys: [exists c. u = TM (mut c d) /\ ..]
   ([TM] and [mut] single-constructor types) becomes, in two steps,
   [sel (sel u) = c /\ ..], and the one-point rule removes [c]; with the
   variable two constructors deep the plain rule leaves [c] bound, and a
   piece whose goal names a closure state as such a nested constructor
   application could then only be instantiated at a state the piece writes,
   not at the field of the state its premises fix. *)
let surjective_pairing_nested = ref false

(* [lit] as the field literals of a single-constructor equation whose
   constructor side has an argument bound in [senv] and not in the other
   side: conjuncts under an existential, disjuncts under a universal *)
let pairing_of_literal binder senv lit =
  Option.bind (equation_of_literal binder lit) ~f:(fun (t1, t2) ->
      let fields = function
        | Term.FunApp (T_dt.DTCons (name, _, dt), args, _)
          when Datatype.is_dt dt -> (
            match Datatype.conses_of dt with
            | [ cons ] when String.(Datatype.name_of_cons cons = name) ->
                let sels = Datatype.sels_of_cons cons in
                if List.length sels = List.length args then
                  Some
                    ( args,
                      fun u ->
                        List.map sels ~f:(fun sel ->
                            T_dt.mk_sel dt (Datatype.name_of_sel sel) u) )
                else None
            | _ -> None)
        | Term.FunApp (T_tuple.TupleCons sorts, args, _)
          when List.length sorts = List.length args ->
            Some
              ( args,
                fun u -> List.mapi args ~f:(fun i _ -> T_tuple.mk_tuple_sel sorts u i) )
        | _ -> None
      in
      let is_cons = function
        | Term.FunApp ((T_dt.DTCons _ | T_tuple.TupleCons _), _, _) -> true
        | _ -> false
      in
      let try_side c u =
        if is_cons u then None
        else
          Option.bind (fields c) ~f:(fun (args, sels_of) ->
              let fv_u = Term.tvs_of u in
              if
                List.exists args ~f:(function
                  | Term.Var (x, _, _) ->
                      (not (Set.mem fv_u x))
                      && List.exists senv ~f:(fun (y, _) -> Ident.tvar_equal x y)
                  | a ->
                      !surjective_pairing_nested
                      && Set.exists (Term.tvs_of a) ~f:(fun x ->
                             (not (Set.mem fv_u x))
                             && List.exists senv ~f:(fun (y, _) ->
                                    Ident.tvar_equal x y)))
              then
                Some
                  (List.map2_exn (sels_of u) args ~f:(fun sel a ->
                       match binder with
                       | Formula.Exists -> Formula.eq sel a
                       | _ -> Formula.neq sel a))
              else None)
      in
      match try_side t1 t2 with Some ls -> Some ls | None -> try_side t2 t1)

(* what one step at a binder does: remove [x] and substitute [t] for it
   (one-point), replace the sequence [x] by [t] over the fresh [bound]
   (sequence-length split), or substitute [t] for the array [x], which stays
   bound, dropping the literal that fixed one of its reads (array-read
   one-point) *)
type binder_step =
  | Point of Ident.tvar * Term.t * Formula.t list
  | SeqShape of Ident.tvar * Term.t * sort_env_list
  | ArrayRead of Ident.tvar * Term.t * Formula.t list * bool
  | Pairing of Formula.t list

let rec onepoint_binders ~outer changed binder senv body =
  let lits = spine_literals binder body in
  let point =
    List.find_map senv ~f:(fun (x, _) ->
        List.find_mapi lits ~f:(fun i lit ->
            Option.map (point_of_literal binder x lit) ~f:(fun t ->
                Point (x, t, List.filteri lits ~f:(fun j _ -> j <> i)))))
  in
  let point =
    match point with
    | None when !surjective_pairing ->
        List.find_mapi lits ~f:(fun i lit ->
            Option.map (pairing_of_literal binder senv lit) ~f:(fun ls ->
                Pairing
                  (List.concat
                  @@ List.mapi lits ~f:(fun j l -> if i = j then ls else [ l ]))))
    | _ -> point
  in
  let step =
    match point with
    | Some _ -> point
    | None ->
        List.find_map senv ~f:(fun (s, sort) ->
            match sort with
            | T_seq.SSeq se ->
                List.find_map lits ~f:(fun lit ->
                    Option.map (seq_length_of_literal binder s lit) ~f:(fun n ->
                        let elems =
                          List.init n ~f:(fun _ -> (Ident.mk_fresh_tvar (), se))
                        in
                        let t =
                          match
                            List.map elems ~f:(fun (e, _) ->
                                T_seq.mk_unit se (Term.mk_var e se))
                          with
                          | [] -> T_seq.mk_empty se
                          | u :: us ->
                              List.fold us ~init:u ~f:(T_seq.mk_concat se)
                        in
                        SeqShape (s, t, elems)))
            | _ -> None)
  in
  let step =
    match step with
    | Some _ -> step
    | None when !onepoint_array_reads ->
        (* tried before the single-read rule, whose [store] would leave the
           pointwise literal reading a [store] of [s] rather than [s], which
           this rule does not recognise; the single reads are taken after,
           once the substituted body is simplified and a read of the lambda
           at an index outside the range has become a read of [s] *)
        let found =
          List.concat_map senv ~f:(fun (s, sort) ->
              List.filter_mapi lits ~f:(fun i lit ->
                  (* under a universal the literal is a disjunct, and it is
                     its negation that constrains [s]:
                     [forall s. not lit \/ R(s)] is [forall s. R(lam j. ...)] *)
                  let lit =
                    match binder with
                    | Formula.Exists -> lit
                    | _ -> Formula.nnf_of (Formula.mk_neg lit)
                  in
                  Option.map (array_pointwise_of_literal ~outer s sort lit)
                    ~f:(fun (nonzero, t) ->
                      ( nonzero,
                        ArrayRead
                          (s, t, List.filteri lits ~f:(fun j _ -> j <> i), true)
                      ))))
        in
        (* a literal [s1[i + 1] = s2[i]] over two bound arrays defines
           either by the other; the shifted one is taken, so the array left
           bound is read at the plain index, where a solver can match it
           against a read of the same shape (either choice is exact) *)
        Option.map ~f:snd
          (match List.find found ~f:fst with
          | Some x -> Some x
          | None -> List.hd found)
    | _ -> step
  in
  let step =
    match step with
    | Some _ -> step
    | None when !onepoint_array_reads ->
        List.find_map senv ~f:(fun (s, sort) ->
            match sort with
            | T_array.SArray (si, se) ->
                List.find_mapi lits ~f:(fun i lit ->
                    Option.map (array_read_of_literal binder s lit)
                      ~f:(fun (k, t) ->
                        ArrayRead
                          ( s,
                            T_array.mk_store si se (Term.mk_var s sort) k t,
                            List.filteri lits ~f:(fun j _ -> j <> i),
                            false )))
            | _ -> None)
    | None -> None
  in
  match step with
  | None -> (senv, body)
  | Some (ArrayRead (s, t, rest, simp)) ->
      changed := true;
      let sub = Map.Poly.singleton s t in
      let rest = List.map rest ~f:(Formula.subst sub) in
      let body =
        match binder with
        | Formula.Exists -> Formula.and_of rest
        | _ -> Formula.or_of rest
      in
      let body = if simp then !simplify_hook body else body in
      onepoint_binders ~outer changed binder senv body
  | Some (Pairing lits) ->
      changed := true;
      let body =
        match binder with
        | Formula.Exists -> Formula.and_of lits
        | _ -> Formula.or_of lits
      in
      onepoint_binders ~outer changed binder senv body
  | Some (Point (x, t, rest)) ->
      changed := true;
      let sub = Map.Poly.singleton x t in
      let rest = List.map rest ~f:(Formula.subst sub) in
      let body =
        fold_constructor_reads
        @@
        match binder with
        | Formula.Exists -> Formula.and_of rest
        | _ -> Formula.or_of rest
      in
      onepoint_binders ~outer changed binder
        (List.filter senv ~f:(fun (y, _) -> not (Ident.tvar_equal x y)))
        body
  | Some (SeqShape (s, t, elems)) ->
      changed := true;
      let body =
        fold_constructor_reads @@ Formula.subst (Map.Poly.singleton s t) body
      in
      onepoint_binders ~outer changed binder
        (List.filter senv ~f:(fun (y, _) -> not (Ident.tvar_equal s y)) @ elems)
        body

(* Is a block of the same quantifier that is a conjunct of an existential's
   body (a disjunct of a universal's) merged into the enclosing block, inside
   [elim_onepoint_and_split_binders]?  Switched per process by the caller,
   off unless set.  The plain merge above takes a block only when it is the
   whole body.

   The rule: [exists xs. A /\ exists ys. B] is [exists xs ys. A /\ B] when no
   [y] of [ys] is bound in [xs] or occurs free in [A] (dually
   [forall xs. A \/ forall ys. B]); an equivalence in every model.  What it
   buys: a goal [exists c w. P(c) /\ exists s. w = t ++ s /\ Q(s)] names its
   outer witness [w] only through the inner binder [s]; once the blocks are
   one, the one-point rule removes [w] as [t ++ s], whereas left apart [w] has
   no pattern of its own and the matched-instance form, which instantiates a
   block only at a substitution of all its sequence binders, drops the goal. *)
let lift_spine_blocks = ref false

(* [senv] and [body] of a [binder] block with the same-quantifier blocks among
   [body]'s spine parts (conjuncts under [Exists], disjuncts under [Forall])
   merged in, as [lift_spine_blocks] states; any other binder is returned as
   it is *)
let lift_spine_blocks_of changed binder senv body =
  let parts, join =
    match binder with
    | Formula.Exists -> (Formula.conjuncts_list_of body, Formula.and_of)
    | Formula.Forall -> (Formula.disjuncts_list_of body, Formula.or_of)
    | _ -> ([ body ], fun ps -> List.hd_exn ps)
  in
  if List.length parts < 2 then (senv, body)
  else
    let senv, parts, lifted =
      List.foldi parts ~init:(senv, [], false) ~f:(fun i (senv, acc, lifted) p ->
          match p with
          | Formula.Bind (b', senv', body', _)
            when Stdlib.( = ) b' binder
                 && (not
                       (List.exists senv' ~f:(fun (y, _) ->
                            List.exists senv ~f:(fun (x, _) ->
                                Ident.tvar_equal x y))))
                 &&
                 let others = List.filteri parts ~f:(fun j _ -> j <> i) in
                 not
                   (List.exists others ~f:(fun q ->
                        let fv = Formula.tvs_of q in
                        List.exists senv' ~f:(fun (y, _) -> Set.mem fv y))) ->
              (senv @ senv', body' :: acc, true)
          | _ -> (senv, p :: acc, lifted))
    in
    if lifted then (
      changed := true;
      (senv, join (List.rev parts)))
    else (senv, body)

let rec onepoint_split_pass ?(outer = Set.Poly.empty) changed phi =
  match phi with
  | Formula.Atom _ -> phi
  | Formula.UnaryOp (op, phi1, info) ->
      Formula.mk_unop ~info op (onepoint_split_pass ~outer changed phi1)
  | Formula.BinaryOp (op, phi1, phi2, info) ->
      Formula.mk_binop ~info op
        (onepoint_split_pass ~outer changed phi1)
        (onepoint_split_pass ~outer changed phi2)
  | Formula.Bind
      (((Formula.Forall | Formula.Exists) as binder), senv, body, info) ->
      let body =
        onepoint_split_pass
          ~outer:(Set.union outer (Set.Poly.of_list (List.map senv ~f:fst)))
          changed body
      in
      (* a nested block of the same quantifier is merged into this one, so an
         equation between variables of the two blocks is seen; only when no
         name is bound twice, since the inner binding would shadow the outer *)
      let senv, body =
        match (binder, body) with
        | Formula.Forall, Formula.Bind (Formula.Forall, senv', body', _)
        | Formula.Exists, Formula.Bind (Formula.Exists, senv', body', _)
          when not
                 (List.exists senv' ~f:(fun (y, _) ->
                      List.exists senv ~f:(fun (x, _) -> Ident.tvar_equal x y)))
          ->
            (senv @ senv', body')
        | _ -> (senv, body)
      in
      let senv, body =
        if !lift_spine_blocks then lift_spine_blocks_of changed binder senv body
        else (senv, body)
      in
      let senv, body = split_single_cons_binders changed senv body 0 in
      let body =
        if !split_constructor_equations then split_cons_equations changed body
        else body
      in
      let senv, body = onepoint_binders ~outer changed binder senv body in
      let used = Formula.fvs_of body in
      let senv' = List.filter senv ~f:(fun (x, _) -> Set.mem used x) in
      if List.length senv' <> List.length senv then changed := true;
      Formula.mk_bind_if_bounded ~info binder senv' body
  | Formula.Bind _ | Formula.LetRec _ | Formula.LetFormula _ -> phi

(* Is an [ite] whose guard the surrounding formula decides replaced by the
   branch it selects, inside [elim_onepoint_and_split_binders]?  Switched per
   process by the caller, off unless set.

   The rule (contextual [ite]): a subterm [ite c a b] is replaced by [a] where
   its context entails [c], and by [b] where it entails [not c].  The context
   of a subformula is what must hold wherever its value can matter: a sibling
   conjunct of a conjunction, the negation of a sibling disjunct of a
   disjunction (of the conclusion, for an implication's premise; the premise
   itself, for its conclusion), and inside the branches of an [ite], its guard
   (resp. its negation).  So [phi] and its rewrite are equivalent in every
   model, not only under a strengthening: [R /\ phi] and [R /\ phi'] agree
   wherever [R] entails [phi <=> phi'], and dually for [not R \/ phi].  Only
   literals free of [ite] enter a context, so a literal that justifies one
   rewrite is never itself rewritten (two conjuncts cannot justify each
   other's rewrite), and under a binder the literals mentioning a bound name
   are dropped, since they are about another variable of that name.
   Entailment is decided syntactically: structural equality, or over the
   integers a single context literal [L >= 0] (an equation, or a pair of an
   inequation and a disequation of the same linear form) implying the
   guard's [L' >= 0] with [L' = k L + c], [k > 0], [c >= 0]; a guard the test
   cannot show is left as it is.  What it buys: the array-read one-point rule
   defines a bound array [s] as [lam j. ite (not R(j)) u(j) s[j]], and a read
   of it where the disjunction around the read already states [R] leaves [s]
   bound in the else branch only; after the rewrite [s] no longer occurs and
   the binder is dropped. *)
let contextual_ite = ref false

(* an integer term as a linear form: opaque subterms (compared structurally,
   so a mismatch only loses a match) with coefficients, and a constant *)
let rec ctx_linear_of t =
  let add (m1, c1) (m2, c2) =
    let m =
      List.fold m2 ~init:m1 ~f:(fun acc (x, a) ->
          match List.Assoc.find acc x ~equal:Stdlib.( = ) with
          | Some b -> List.Assoc.add acc x (Q.add a b) ~equal:Stdlib.( = )
          | None -> (x, a) :: acc)
    in
    (List.filter m ~f:(fun (_, a) -> not (Q.equal a Q.zero)), Q.add c1 c2)
  in
  let scale k (m, c) = (List.map m ~f:(fun (x, a) -> (x, Q.mul k a)), Q.mul k c) in
  match t with
  | Term.FunApp (T_int.Int n, [], _) -> ([], Q.of_bigint n)
  | Term.FunApp (T_int.Add, [ t1; t2 ], _) ->
      add (ctx_linear_of t1) (ctx_linear_of t2)
  | Term.FunApp (T_int.Sub, [ t1; t2 ], _) ->
      add (ctx_linear_of t1) (scale Q.minus_one @@ ctx_linear_of t2)
  | Term.FunApp (T_int.Neg, [ t1 ], _) -> scale Q.minus_one @@ ctx_linear_of t1
  | Term.FunApp (T_int.Mul, [ Term.FunApp (T_int.Int n, [], _); t1 ], _)
  | Term.FunApp (T_int.Mul, [ t1; Term.FunApp (T_int.Int n, [], _) ], _) ->
      scale (Q.of_bigint n) @@ ctx_linear_of t1
  | t -> ([ (t, Q.one) ], Q.zero)

(* a literal as [`Ge l] ([l >= 0]), [`Eq l] ([l = 0]) or [`Ne l]
   ([l != 0]) over the integers; strict comparisons become non-strict by the
   integer step, which is exact *)
let ctx_lin_lit phi =
  let diff a b =
    let m1, c1 = ctx_linear_of a and m2, c2 = ctx_linear_of b in
    let m2 = List.map m2 ~f:(fun (x, q) -> (x, Q.neg q)) in
    let m =
      List.fold m2 ~init:m1 ~f:(fun acc (x, a) ->
          match List.Assoc.find acc x ~equal:Stdlib.( = ) with
          | Some b -> List.Assoc.add acc x (Q.add a b) ~equal:Stdlib.( = )
          | None -> (x, a) :: acc)
    in
    (List.filter m ~f:(fun (_, a) -> not (Q.equal a Q.zero)), Q.sub c1 c2)
  in
  let dec (m, c) = (m, Q.sub c Q.one) in
  let is_int t =
    try Stdlib.( = ) (Term.sort_of t) T_int.SInt with _ -> false
  in
  let of_psym neg psym t1 t2 =
    match (neg, psym) with
    | false, T_int.Leq | true, T_int.Gt -> Some (`Ge (diff t2 t1))
    | false, T_int.Geq | true, T_int.Lt -> Some (`Ge (diff t1 t2))
    | false, T_int.Lt | true, T_int.Geq -> Some (`Ge (dec @@ diff t2 t1))
    | false, T_int.Gt | true, T_int.Leq -> Some (`Ge (dec @@ diff t1 t2))
    | false, T_bool.Eq | true, T_bool.Neq ->
        if is_int t1 then Some (`Eq (diff t1 t2)) else None
    | false, T_bool.Neq | true, T_bool.Eq ->
        if is_int t1 then Some (`Ne (diff t1 t2)) else None
    | _ -> None
  in
  match phi with
  | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) ->
      of_psym false psym t1 t2
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _),
        _ ) ->
      of_psym true psym t1 t2
  | _ -> None

(* [d = k * t + c] for some [k > 0] and [c >= 0]: then [t >= 0] implies
   [d >= 0]; [false] may be wrong, [true] may not *)
let ctx_lin_implies (mt, ct) (md, cd) =
  match mt with
  | [] -> Q.(lt ct zero) || (List.is_empty md && Q.(geq cd zero))
  | (x, a) :: _ -> (
      match List.Assoc.find md x ~equal:Stdlib.( = ) with
      | None -> false
      | Some b ->
          let k = Q.div b a in
          Q.(gt k zero)
          && List.length md = List.length mt
          && List.for_all mt ~f:(fun (y, a') ->
              match List.Assoc.find md y ~equal:Stdlib.( = ) with
              | Some b' -> Q.equal b' (Q.mul k a')
              | None -> false)
          && Q.(geq (sub cd (mul k ct)) zero))

let ctx_lin_neg (m, c) = (List.map m ~f:(fun (x, q) -> (x, Q.neg q)), Q.neg c)

(* the facts [l >= 0] a context gives: its inequations, both halves of its
   equations, and [l - 1 >= 0] for an inequation [l >= 0] beside the
   disequation [l != 0] *)
let ctx_ge_facts ctx =
  let lins = List.filter_map ctx ~f:ctx_lin_lit in
  let ges =
    List.concat_map lins ~f:(function
      | `Ge l -> [ l ]
      | `Eq l -> [ l; ctx_lin_neg l ]
      | `Ne _ -> [])
  in
  let nes = List.filter_map lins ~f:(function `Ne l -> Some l | _ -> None) in
  let same l e = ctx_lin_implies l e && ctx_lin_implies e l in
  ges
  @ List.filter_map ges ~f:(fun ((m, c) as l) ->
      if
        List.exists nes ~f:(fun e -> same l e || same l (ctx_lin_neg e))
      then Some (m, Q.sub c Q.one)
      else None)

let rec ctx_entails ctx ges g =
  let structural =
    List.exists ctx ~f:(fun l -> try Stdlib.( = ) l g with _ -> false)
  in
  structural
  || Formula.is_true g
  ||
  match g with
  | Formula.BinaryOp (Formula.And, g1, g2, _) ->
      ctx_entails ctx ges g1 && ctx_entails ctx ges g2
  | Formula.BinaryOp (Formula.Or, g1, g2, _) ->
      ctx_entails ctx ges g1 || ctx_entails ctx ges g2
  | _ -> (
      let implied d = List.exists ges ~f:(fun t -> ctx_lin_implies t d) in
      match ctx_lin_lit g with
      | Some (`Ge d) -> implied d
      | Some (`Eq d) -> implied d && implied (ctx_lin_neg d)
      | Some (`Ne d) ->
          let m, c = d in
          implied (m, Q.sub c Q.one)
          || implied (let m, c = ctx_lin_neg d in (m, Q.sub c Q.one))
          || List.exists ctx ~f:(fun l ->
                 match ctx_lin_lit l with
                 | Some (`Ne e) ->
                     let same a b = ctx_lin_implies a b && ctx_lin_implies b a in
                     same d e || same d (ctx_lin_neg e)
                 | _ -> false)
      | None -> false)

let rec ctx_term_has_ite = function
  | Term.Var _ -> false
  | Term.FunApp (T_bool.IfThenElse, _, _) -> true
  | Term.FunApp (T_bool.Formula phi, ts, _) ->
      ctx_formula_has_ite phi || List.exists ts ~f:ctx_term_has_ite
  | Term.FunApp (_, ts, _) -> List.exists ts ~f:ctx_term_has_ite
  | Term.LetTerm _ -> true

and ctx_formula_has_ite = function
  | Formula.Atom (Atom.App (_, ts, _), _) -> List.exists ts ~f:ctx_term_has_ite
  | Formula.Atom _ -> false
  | Formula.UnaryOp (_, p, _) -> ctx_formula_has_ite p
  | Formula.BinaryOp (_, p, q, _) -> ctx_formula_has_ite p || ctx_formula_has_ite q
  | Formula.Bind (_, _, p, _) -> ctx_formula_has_ite p
  | Formula.LetRec _ | Formula.LetFormula _ -> true

(* a literal that may enter a context: an atom or a negated atom, free of
   [ite] (so the rewrite leaves it as it is) *)
let ctx_literal = function
  | (Formula.Atom (Atom.App _, _) | Formula.UnaryOp (Formula.Not, Formula.Atom (Atom.App _, _), _))
    as l ->
      not (ctx_formula_has_ite l)
  | _ -> false

let ctx_negate l = Formula.nnf_of (Formula.mk_neg l)

let ctx_without ctx bound =
  if Set.is_empty bound then ctx
  else
    List.filter ctx ~f:(fun l ->
        Set.is_empty (Set.inter (Formula.tvs_of l) bound))

let rec ctx_formula changed ctx phi =
  match phi with
  | Formula.Atom (Atom.App (pred, ts, ainfo), info) ->
      let ts' = List.map ts ~f:(ctx_term changed ctx) in
      if List.for_all2_exn ts ts' ~f:phys_equal then phi
      else Formula.mk_atom ~info (Atom.mk_app ~info:ainfo pred ts')
  | Formula.Atom _ -> phi
  | Formula.UnaryOp (op, p, info) ->
      let p' = ctx_formula changed ctx p in
      if phys_equal p p' then phi else Formula.mk_unop ~info op p'
  | Formula.BinaryOp (((Formula.And | Formula.Or) as op), _, _, info) ->
      let rec flat = function
        | Formula.BinaryOp (op', p, q, _) when Stdlib.( = ) op op' ->
            flat p @ flat q
        | p -> [ p ]
      in
      let parts = flat phi in
      let lits = List.filter parts ~f:ctx_literal in
      let facts =
        match op with
        | Formula.And -> lits
        | _ -> List.map lits ~f:ctx_negate
      in
      let ctx' = facts @ ctx in
      let parts' =
        List.map parts ~f:(fun p ->
            if ctx_literal p then p else ctx_formula changed ctx' p)
      in
      if List.for_all2_exn parts parts' ~f:phys_equal then phi
      else
        List.reduce_exn parts' ~f:(fun p q -> Formula.mk_binop ~info op p q)
  | Formula.BinaryOp (Formula.Imply, p1, p2, info) ->
      let prem = List.filter (Formula.conjuncts_list_of p1) ~f:ctx_literal in
      let concl =
        List.map ~f:ctx_negate
        @@ List.filter (Formula.disjuncts_list_of p2) ~f:ctx_literal
      in
      let p1' = if ctx_literal p1 then p1 else ctx_formula changed (concl @ ctx) p1 in
      let p2' = if ctx_literal p2 then p2 else ctx_formula changed (prem @ ctx) p2 in
      if phys_equal p1 p1' && phys_equal p2 p2' then phi
      else Formula.mk_binop ~info Formula.Imply p1' p2'
  | Formula.BinaryOp (op, p1, p2, info) ->
      let p1' = ctx_formula changed ctx p1 and p2' = ctx_formula changed ctx p2 in
      if phys_equal p1 p1' && phys_equal p2 p2' then phi
      else Formula.mk_binop ~info op p1' p2'
  | Formula.Bind (binder, senv, body, info) ->
      let ctx = ctx_without ctx (Set.Poly.of_list (List.map senv ~f:fst)) in
      let body' = ctx_formula changed ctx body in
      if phys_equal body body' then phi
      else Formula.mk_bind ~info binder senv body'
  | Formula.LetRec _ | Formula.LetFormula _ -> phi

and ctx_term changed ctx t =
  match t with
  | Term.Var _ -> t
  | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], info) ->
      let c' = ctx_term changed ctx c in
      let g = Formula.of_bool_term c' in
      let ges = ctx_ge_facts ctx in
      if ctx_entails ctx ges g then (
        changed := true;
        ctx_term changed ctx a)
      else if ctx_entails ctx ges (ctx_negate g) then (
        changed := true;
        ctx_term changed ctx b)
      else
        let then_facts =
          List.filter (Formula.conjuncts_list_of g) ~f:ctx_literal
        in
        let else_facts =
          List.map ~f:ctx_negate
          @@ List.filter (Formula.disjuncts_list_of g) ~f:ctx_literal
        in
        let a' = ctx_term changed (then_facts @ ctx) a in
        let b' = ctx_term changed (else_facts @ ctx) b in
        if phys_equal c c' && phys_equal a a' && phys_equal b b' then t
        else Term.mk_fsym_app ~info T_bool.IfThenElse [ c'; a'; b' ]
  | Term.FunApp (T_bool.Formula phi, [], info) ->
      let phi' = ctx_formula changed ctx phi in
      if phys_equal phi phi' then t
      else Term.mk_fsym_app ~info (T_bool.Formula phi') []
  | Term.FunApp (fsym, ts, info) ->
      let ctx =
        match fsym with
        | T_array.ALambda ((x, _), _) -> ctx_without ctx (Set.Poly.singleton x)
        | _ -> ctx
      in
      let ts' = List.map ts ~f:(ctx_term changed ctx) in
      if List.for_all2_exn ts ts' ~f:phys_equal then t
      else Term.mk_fsym_app ~info fsym ts'
  | Term.LetTerm _ -> t

(* rounds of the whole pass: an elimination at an inner binder can expose an
   equation to an outer one *)
let max_onepoint_split_rounds = 8

(* [contextual] says whether the contextual [ite] rule runs in each round;
   [elim_onepoint_and_split_binders] reads it from the process-wide
   [contextual_ite], and [elim_onepoint_and_split_binders_contextual] runs it
   on one formula only, without switching it on for every other rewrite in the
   process.  Either way the result is equivalent to [phi] in every model. *)
let elim_onepoint_and_split_binders_with ~contextual phi =
  let rec loop phi round =
    if round >= max_onepoint_split_rounds then phi
    else
      let changed = ref false in
      let phi' = onepoint_split_pass changed phi in
      let phi' =
        if contextual then ctx_formula changed [] phi' else phi'
      in
      if !changed then loop phi' (round + 1) else phi'
  in
  loop phi 0

let elim_onepoint_and_split_binders phi =
  elim_onepoint_and_split_binders_with ~contextual:!contextual_ite phi

(* every [ite] whose guard its context decides replaced by the branch it
   selects (the contextual rule above, exact in every model), whatever the
   [contextual_ite] switch *)
let decide_contextual_ites phi = ctx_formula (ref false) [] phi

let elim_onepoint_and_split_binders_contextual phi =
  elim_onepoint_and_split_binders_with ~contextual:true phi

let head_str_of_term = function
  | Term.Var (tvar, _, _) -> Ident.name_of_tvar tvar
  | FunApp (T_bool.Formula _, _, _) -> "Formula(..)"
  | FunApp (fsym, _, _) -> Term.str_of_funsym fsym
  | LetTerm (tvar, _, _, _, _) -> "let " ^ Ident.name_of_tvar tvar

(* Does [eval_term] evaluate the sequence operators on ground values?  Off by
   default and switched per process, because [eval_term] is also what
   [simplify_term] tries on every application node: turning this on folds a
   ground sequence term into its literal wherever the simplifier runs, not only
   where a truth-table cell is decided, so it can move a trajectory even though
   every value it gives is the one the theory fixes.  Anything that reads the
   switch reads it at each call, so a solver that turns it on at the start of a
   run affects everything evaluated after that point in the process. *)
let evaluate_sequences = Atomic.make false

(* The value of a sequence term, or a raise where the theory does not fix one.
   The operators and their meaning are SMT-LIB's (Z3's sequence theory):
   [seq.extract s i n] is the empty sequence unless [0 <= i < len s] and
   [n > 0], and is otherwise the elements from [i] up to [min (i + n) (len s)];
   [seq.store] is this tool's own symbol and means what its expansion at the
   solver boundary says, the sequence with index [i] replaced when [i] is inside
   it and the sequence unchanged otherwise.  [seq.nth] outside [0, len s)
   RAISES: that read is a term whose value is fixed within one model and differs
   across models, so any value given here would be a choice the theory does not
   make, and a caller deciding a verdict from it would be deciding for one model
   what must hold in all of them. *)
let seq_values_of = function
  | Value.Seq (dummy, vs) -> (dummy, vs)
  | v -> failwith @@ "[eval_term] not a sequence value: " ^ Value.str_of v

let seq_index_of = function
  | Value.Int i -> i
  | v -> failwith @@ "[eval_term] not an integer index: " ^ Value.str_of v

let head_str_of_atom = function
  | Atom.True _ -> "true"
  | False _ -> "false"
  | App (pred, _, _) -> Predicate.str_of pred

let rec eval_term ?(env = Map.Poly.empty) =
  let open Term in
  function
  | Var (tvar, _, _) -> (
      match Map.Poly.find env tvar with
      | Some v -> v
      | None -> failwith @@ Ident.name_of_tvar tvar ^ " is not bound")
  | FunApp (FVar (fvar, _, _), ts, _) as term ->
      if false then print_endline @@ "eval rec fun: " ^ Term.str_of term;
      let params, _, def, _, _ = Map.Poly.find_exn (get_fenv ()) fvar in
      let env =
        Map.update_with env @@ Map.Poly.of_alist_exn
        @@ List.zip_exn (List.map ~f:fst params)
        @@ List.map ts ~f:(eval_term ~env)
      in
      let depth = Stdlib.Domain.DLS.get unfold_depth in
      if !depth >= max_unfold_depth then
        failwith
          (sprintf "[eval_term] %s: %d nested unfoldings, giving up"
             (Ident.name_of_tvar fvar) max_unfold_depth)
      else (
        incr depth;
        match eval_term ~env def with
        | v ->
            decr depth;
            v
        | exception exn_ ->
            decr depth;
            raise exn_)
  | FunApp (T_bool.Formula phi, [], _) -> Value.Bool (eval ~env phi)
  (* the condition is evaluated first and only the chosen branch after it:
     evaluating both branches eagerly made every recursive function definition
     -- whose body is an [ite] whose one branch recurses -- unfold forever.
     When the condition itself cannot be
     evaluated (e.g. a division by zero in it), the old behaviour is kept: the
     value if both branches agree, the condition's failure otherwise. *)
  | FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], _) -> (
      match eval_term ~env t1 with
      | Value.Bool true -> eval_term ~env t2
      | Value.Bool false -> eval_term ~env t3
      | _ ->
          failwith
            "a conditional expression must be evaluated to a boolean value"
      | exception exn_ when not (Common.Timer.is_async exn_) ->
          let t2', t3' = (eval_term ~env t2, eval_term ~env t3) in
          if Stdlib.(t2' = t3') then t2' else raise exn_)
  | FunApp (T_int.Case n, t1 :: branches, _) -> (
      match eval_term ~env t1 with
      (* compared in [Z]: the selector is a term's value and can be any
         integer, and an exception raised in a guard is not caught by the
         [exception] arm below; [Z.to_int] is applied only once [m < n] *)
      | Value.Int m when Z.(leq zero m && lt m (of_int n)) ->
          eval_term ~env (List.nth_exn branches (Z.to_int m))
      | exception exn_ when not (Common.Timer.is_async exn_) ->
          let t2, ts = List.hd_tl @@ List.map ~f:(eval_term ~env) branches in
          if List.for_all ts ~f:(fun t -> Stdlib.(t2 = t)) then t2
          else raise exn_
      | _ ->
          failwith
            "a conditional expression must be evaluated to an integer value")
  | FunApp (T_int.Int i, [], _) -> Value.Int i
  | FunApp (T_real.Real r, [], _) -> Value.Real r
  | FunApp (T_bv.BVNum (size, i), [], _) -> Value.BV (size, i)
  | FunApp (T_array.AConst (si, _), [ t ], _) ->
      Value.Arr
        (eval_term ~env @@ Term.mk_dummy si, eval_term ~env t, Map.Poly.empty)
  | FunApp (T_array.AStore _, [ t1; t2; t3 ], _) -> (
      match eval_term ~env t1 with
      | Value.Arr (dummy, v, m) ->
          let v2 = eval_term ~env t2 in
          let v3 = eval_term ~env t3 in
          if Value.eq v v3 then Value.Arr (dummy, v, Map.Poly.remove m v2)
          else Value.Arr (dummy, v, Map.Poly.set m ~key:v2 ~data:v3)
      | _ ->
          failwith @@ "Array store: first term must be an array: "
          ^ head_str_of_term t1)
  | FunApp (T_array.ASelect _, [ t1; t2 ], _) -> (
      match eval_term ~env t1 with
      | Value.Arr (_dummy, v, m) -> (
          match Map.Poly.find m (eval_term ~env t2) with
          | Some v' -> v'
          | None -> v)
      | _ ->
          failwith @@ "Array select: first term must be an array: "
          ^ head_str_of_term t1)
  | FunApp (T_tuple.TupleCons sorts, ts, _) ->
      let ts' = List.map ~f:(eval_term ~env) ts in
      if List.length ts' <> List.length sorts then
        failwith "Tuple constructor: number of terms does not match sorts";
      Value.TupleCons ts'
  | FunApp (T_dt.DTSel (sel_name, dt, _), [ t1 ], _) -> (
      match eval_term ~env t1 with
      | Value.DTCons (cons_name, _pvs, vs) -> (
          match Datatype.look_up_cons dt cons_name with
          | Some cons -> (
              match
                List.fold2_exn (Datatype.sels_of_cons cons) vs ~init:None
                  ~f:(fun ret sel v ->
                    match ret with
                    | Some _ -> ret
                    | None ->
                        if String.(Datatype.name_of_sel sel = sel_name) then
                          Some v
                        else None)
              with
              | Some v -> v
              | None ->
                  failwith
                    (sprintf "Selector %s is not found in the constructor %s"
                       sel_name cons_name))
          | None -> failwith @@ cons_name ^ " not found")
      | _ ->
          failwith @@ head_str_of_term t1
          ^ " must be evaluated to a datatype constructor application")
  | FunApp (T_dt.DTCons (name, sorts, dt), ts, _) ->
      let vs = List.map ~f:(eval_term ~env) ts in
      if List.length vs <> List.length sorts then
        failwith "Datatype constructor: number of terms does not match sorts";
      Value.DTCons
        ( name,
          List.map (Datatype.params_of dt) ~f:(Term.mk_dummy >> eval_term ~env),
          vs )
  | FunApp (T_irb.RealToInt, [ FunApp (T_real.Real r, [], _) ], _) ->
      Value.Int (Z.fdiv (Q.num r) (Q.den r)) (* SMT-LIB to_int is floor *)
  | FunApp (T_irb.IntToReal, [ FunApp (T_int.Int i, [], _) ], _) ->
      Value.Real (Q.of_bigint i)
  | FunApp ((T_int.Neg | T_real.RNeg), [ t1 ], _) ->
      Value.neg (eval_term ~env t1)
  | FunApp (T_int.Nop, [ t1 ], _) -> eval_term ~env t1
  | FunApp ((T_int.Abs | T_real.RAbs), [ t1 ], _) ->
      Value.abs (eval_term ~env t1)
  | FunApp (T_int.Add, [ t1; t2 ], _) ->
      Value.add (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_int.Sub, [ t1; t2 ], _) ->
      Value.sub (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_int.Mul, [ t1; t2 ], _) ->
      Value.mul (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_int.Div m, [ t1; t2 ], _) ->
      Value.div m (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_int.Rem m, [ t1; t2 ], _) ->
      Value.rem m (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_int.Power, [ t1; t2 ], _) ->
      Value.pow (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_real.RAdd, [ t1; t2 ], _) ->
      Value.radd (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_real.RSub, [ t1; t2 ], _) ->
      Value.rsub (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_real.RMul, [ t1; t2 ], _) ->
      Value.rmul (eval_term ~env t1) (eval_term ~env t2)
  | FunApp (T_real.RDiv, [ t1; t2 ], _) ->
      Value.rdiv (eval_term ~env t1) (eval_term ~env t2)
  (*| FunApp (T_real.RPower, [ t1; t2 ], _) ->
      Value.rpow (eval_term ~env t1) (eval_term ~env t2)*)
  | FunApp
      (T_bv.BVNot _ (*ToDo*), [ FunApp (T_bv.BVNum (Some size, i), [], _) ], _)
    ->
      Value.BV (Some size, bvnot size i)
  | FunApp
      ( T_bv.BVAnd _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvand (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVOr _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvor (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVXor _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvxor (T_bv.bits_of size) i1 i2)
  | FunApp (T_bv.BVNeg _ (*ToDo*), [ FunApp (T_bv.BVNum (size1, i1), [], _) ], _)
    ->
      Value.BV (size1, bvneg (T_bv.bits_of size1) i1)
  | FunApp
      ( T_bv.BVAdd _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvadd (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVSub _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvsub (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVMul _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvmul (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVDiv (_ (*ToDo*), signed),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV
        ( size,
          (if T_bv.is_signed signed then bvsdiv else bvudiv)
            (T_bv.bits_of size) i1 i2 )
  | FunApp
      ( T_bv.BVRem (_ (*ToDo*), signed),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV
        ( size,
          (if T_bv.is_signed signed then bvsrem else bvurem)
            (T_bv.bits_of size) i1 i2 )
  (* The three shifts take the shift amount as a [Z.t] of any size:
     [Common.Util.bvshl], [bvlshr] and [bvashr] answer a shift of the width or
     more without narrowing it to a native int. *)
  | FunApp
      ( T_bv.BVSHL _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvshl (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVLSHR _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvlshr i1 i2)
  | FunApp
      ( T_bv.BVASHR _ (*ToDo*),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ )
    when T_bv.eq_size size1 size2 ->
      let size = T_bv.merge_size size1 size2 in
      Value.BV (size, bvashr (T_bv.bits_of size) i1 i2)
  | FunApp
      ( T_bv.BVEXTRACT (_ (*ToDo*), h, l),
        [ FunApp (T_bv.BVNum (size, i), [], _) ],
        _ ) ->
      let bvextract size h l i =
        let size' = h - l + 1 in
        if size' <= 0 then
          failwith
            "getbit_range: the range is not valid (h must be greater than or \
             equal to l)"
        else if size' > size then
          failwith "getbit_range: the range is larger than the bitvector size"
        else
          let mask = Z.(shift_left (of_int 1) size' - one) in
          let i' = Z.(shift_right i l land mask) in
          Value.BV (Some size', i')
      in
      bvextract (T_bv.bits_of size) h l i
  | FunApp
      ( T_bv.BVZEXT (_, ext) (*ToDo*),
        [ FunApp (T_bv.BVNum (Some bits, i), [], _) ],
        _ ) ->
      Value.BV (Some (bits + ext), i)
  | FunApp
      (T_bv.BVSEXT (_, ext), [ FunApp (T_bv.BVNum (Some bits, i), [], _) ], _)
    ->
      let bits' = bits + ext in
      let i' =
        if Z.testbit i (bits - 1) then
          Z.(logor i (shift_left (shift_left one ext - one) bits))
        else i
      in
      Value.BV (Some bits', i')
  | FunApp
      ( T_bv.BVCONCAT (_ (*ToDo*), _ (*ToDo*)),
        [
          FunApp (T_bv.BVNum (size1, i1), [], _);
          FunApp (T_bv.BVNum (size2, i2), [], _);
        ],
        _ ) ->
      let i = Z.(shift_left i1 (T_bv.bits_of size2) + i2) in
      Value.BV (T_bv.add_size size1 size2, i)
  | FunApp (fsym, ts, info)
    when T_bv.is_bv_fsym fsym && List.exists ts ~f:(Fn.non T_bv.is_bvnum) ->
      (* the bit-vector cases above match their arguments as numerals
         syntactically rather than evaluating them, so a nested operation such
         as bvlshr (bvand a b) c reaches the catch-all and fails *)
      eval_term ~env
      @@ Term.mk_fsym_app ~info fsym
           (List.map ts ~f:(fun t ->
                Term.of_value (get_dtenv ()) @@ eval_term ~env t))
  | LetTerm (var, _, def, body, _) ->
      let subst =
        Map.Poly.singleton var
        @@ Term.of_value (get_dtenv ())
        @@ eval_term ~env def
      in
      eval_term ~env @@ Term.subst subst body
  | FunApp (T_seq.SqEmpty se, [], _) when Atomic.get evaluate_sequences ->
      Value.Seq (eval_term ~env @@ Term.mk_dummy se, [])
  | FunApp (T_seq.SqUnit se, [ t ], _) when Atomic.get evaluate_sequences ->
      Value.Seq (eval_term ~env @@ Term.mk_dummy se, [ eval_term ~env t ])
  | FunApp (T_seq.SqConcat _, [ t1; t2 ], _) when Atomic.get evaluate_sequences
    ->
      let dummy, vs1 = seq_values_of @@ eval_term ~env t1 in
      let _, vs2 = seq_values_of @@ eval_term ~env t2 in
      Value.Seq (dummy, vs1 @ vs2)
  | FunApp (T_seq.SqLen _, [ t ], _) when Atomic.get evaluate_sequences ->
      Value.Int
        (Z.of_int @@ List.length @@ snd @@ seq_values_of @@ eval_term ~env t)
  | FunApp (T_seq.SqNth _, [ t; i ], _) when Atomic.get evaluate_sequences -> (
      let _, vs = seq_values_of @@ eval_term ~env t in
      let k = seq_index_of @@ eval_term ~env i in
      match
        if Z.Compare.(k >= Z.zero && k < Z.of_int (List.length vs)) then
          List.nth vs (Z.to_int k)
        else None
      with
      | Some v -> v
      | None ->
          failwith
            "[eval_term] seq.nth outside the sequence: the theory leaves this \
             read open")
  | FunApp (T_seq.SqExtract _, [ t; i; n ], _)
    when Atomic.get evaluate_sequences ->
      let dummy, vs = seq_values_of @@ eval_term ~env t in
      let i = seq_index_of @@ eval_term ~env i in
      let n = seq_index_of @@ eval_term ~env n in
      let len = Z.of_int (List.length vs) in
      if Z.Compare.(i < Z.zero || i >= len || n <= Z.zero) then
        Value.Seq (dummy, [])
      else
        let stop = Z.min Z.(i + n) len in
        Value.Seq
          (dummy, List.sub vs ~pos:(Z.to_int i) ~len:(Z.to_int Z.(stop - i)))
  | FunApp (T_seq.SqStore _, [ t; i; e ], _) when Atomic.get evaluate_sequences
    ->
      let dummy, vs = seq_values_of @@ eval_term ~env t in
      let k = seq_index_of @@ eval_term ~env i in
      let v = eval_term ~env e in
      if Z.Compare.(k >= Z.zero && k < Z.of_int (List.length vs)) then
        let k = Z.to_int k in
        Value.Seq (dummy, List.mapi vs ~f:(fun j x -> if j = k then v else x))
      else Value.Seq (dummy, vs)
  | t -> failwith (sprintf "[eval_term] not supported: %s" (head_str_of_term t))

(*val eval_pred: pred_sym -> Term.t list -> bool*)
and eval_pred ?(env = Map.Poly.empty) psym terms =
  match (psym, terms) with
  | T_tuple.IsTuple _, [ Term.FunApp (T_tuple.TupleCons _, _, _) ] -> true
  | T_tuple.NotIsTuple _, [ Term.FunApp (T_tuple.TupleCons _, _, _) ] -> false
  | T_dt.IsCons (n1, _), [ Term.FunApp (T_dt.DTCons (n2, _, _), _, _) ] ->
      String.(n1 = n2)
  | T_dt.NotIsCons (n1, _), [ Term.FunApp (T_dt.DTCons (n2, _, _), _, _) ] ->
      String.(n1 <> n2)
  | _ -> (
      match (psym, List.map ~f:(eval_term ~env) terms) with
      | T_bool.Eq, [ BV (size1, i1); BV (size2, i2) ]
        when T_bv.eq_size size1 size2 ->
          Z.Compare.(i1 = i2)
      | T_bool.Neq, [ BV (size1, i1); BV (size2, i2) ]
        when T_bv.eq_size size1 size2 ->
          Z.Compare.(i1 <> i2)
      | ( T_bv.BVLeq (_ (*Some s*), Some true),
          [ Value.BV (s1, i1); Value.BV (s2, i2) ] )
        when (*s = s1 &&*) T_bv.eq_size s1 s2 -> (
          match
            ( Z.testbit i1 (T_bv.bits_of s1 - 1),
              Z.testbit i2 (T_bv.bits_of s2 - 1) )
          with
          | false, true -> false
          | true, false -> true
          | _ -> Z.Compare.(i1 <= i2))
      | ( T_bv.BVLt (_ (*Some s*), Some true),
          [ Value.BV (s1, i1); Value.BV (s2, i2) ] )
        when (*s = s1 &&*) T_bv.eq_size s1 s2 -> (
          match
            ( Z.testbit i1 (T_bv.bits_of s1 - 1),
              Z.testbit i2 (T_bv.bits_of s2 - 1) )
          with
          | false, true -> false
          | true, false -> true
          | _ -> Z.Compare.(i1 < i2))
      | ( T_bv.BVGeq (_ (*Some s*), Some true),
          [ Value.BV (s1, i1); Value.BV (s2, i2) ] )
        when (*s = s1 &&*) T_bv.eq_size s1 s2 -> (
          match
            ( Z.testbit i1 (T_bv.bits_of s1 - 1),
              Z.testbit i2 (T_bv.bits_of s2 - 1) )
          with
          | false, true -> true
          | true, false -> false
          | _ -> Z.Compare.(i1 >= i2))
      | ( T_bv.BVGt (_ (*Some s*), Some true),
          [ Value.BV (s1, i1); Value.BV (s2, i2) ] )
        when (*s = s1 &&*) T_bv.eq_size s1 s2 -> (
          match
            ( Z.testbit i1 (T_bv.bits_of s1 - 1),
              Z.testbit i2 (T_bv.bits_of s2 - 1) )
          with
          | false, true -> true
          | true, false -> false
          | _ -> Z.Compare.(i1 > i2))
      | T_bool.Eq, [ t1; t2 ] -> Value.eq t1 t2
      | T_bool.Neq, [ t1; t2 ] -> Value.neq t1 t2
      | (T_int.Leq | T_real.RLeq | T_bv.BVLeq (_, Some false)), [ t1; t2 ] ->
          Value.leq t1 t2
      | (T_int.Geq | T_real.RGeq | T_bv.BVGeq (_, Some false)), [ t1; t2 ] ->
          Value.geq t1 t2
      | (T_int.Lt | T_real.RLt | T_bv.BVLt (_, Some false)), [ t1; t2 ] ->
          Value.lt t1 t2
      | (T_int.Gt | T_real.RGt | T_bv.BVGt (_, Some false)), [ t1; t2 ] ->
          Value.gt t1 t2
      | T_int.PDiv, [ t1; t2 ] ->
          Value.eq (Value.rem Euclidean t2 t1) (Value.Int Z.zero)
      | T_int.NotPDiv, [ t1; t2 ] ->
          Value.neq (Value.rem Euclidean t2 t1) (Value.Int Z.zero)
      | _ -> failwith "[eval_pred] not supported")

(*val eval_atom: Atom.t -> bool*)
and eval_atom ?(env = Map.Poly.empty) = function
  | Atom.True _ -> true
  | False _ -> false
  | App (Predicate.Psym psym, terms, _) -> eval_pred ~env psym terms
  | App (Predicate.(Var (_, _) | Fixpoint _), _, _) as atm ->
      failwith
        (sprintf
           "Predicate variables and fixpoints applications not supported: %s"
           (head_str_of_atom atm))

(*val eval: Formula.t -> bool*)
and eval ?(env = Map.Poly.empty) =
  let open Formula in
  function
  | Atom (atom, _) -> eval_atom ~env atom
  | UnaryOp (Not, phi, _) -> Fn.non (eval ~env) phi
  | BinaryOp (And, phi1, phi2, _) -> eval ~env phi1 && eval ~env phi2
  | BinaryOp (Or, phi1, phi2, _) -> eval ~env phi1 || eval ~env phi2
  | BinaryOp (Imply, phi1, phi2, _) -> Fn.non (eval ~env) phi1 || eval ~env phi2
  | BinaryOp (Iff, phi1, phi2, _) -> Stdlib.(eval ~env phi1 = eval ~env phi2)
  | BinaryOp (Xor, phi1, phi2, _) -> Stdlib.(eval ~env phi1 <> eval ~env phi2)
  | LetRec (_, _, _) -> failwith "[eval] LetRec not supported"
  | Bind (_, _, _, _) -> failwith "[eval] Bind not supported"
  | LetFormula (tvar, _, def, body, _) ->
      let env = Map.Poly.set env ~key:tvar ~data:(eval_term ~env def) in
      eval ~env body

and size_threshold = 3
and count_threshold = 1
and prod_threshold = 16

(* Whether a [let] whose simplified definition has tree size [size] and occurs
   [count] times in its simplified body is inlined.  Both numbers are read
   after the body's own lets were decided, and with the switch on both count
   through a kept [let] as if it were inlined ([expanded_size_of_term],
   [occur_times]), so they are the sizes of the expansion, and inlining turns a tree of size [b] into one of size
   [b + count * (size - 1)] -- [let_inlined_size] below, without performing the
   substitution.  The default rule inlines any definition of at most
   [size_threshold] nodes whatever its use count, so on a chain
   [let x1 = f x0 x0 in let x2 = f x1 x1 in ...] every link is inlined and the
   result, physically shared but walked as a tree by every consumer, doubles
   per link.  With [inline_by_expanded_size] on, such a small definition is
   inlined only while the nodes the inlining adds, [(size - 1) * (count - 1)]
   beyond what keeping the [let] costs, stay within [prod_threshold]; a leaf
   ([size <= 1]) and a single use still always are.  Either way the result is
   equivalent: a [let] and its inlining denote the same value. *)
(* the size [inline_let] reads of a [let]'s simplified definition: with the
   switch on, its expanded size; off, [Term.ast_size] as before *)
and let_def_size def =
  if Atomic.get inline_by_expanded_size then expanded_size_of_term def
  else Term.ast_size def (*ToDo*)

and inline_let ~size ~count =
  (* two rows of the phase report, deciding nothing: every decision taken,
     and every [let] the switch keeps that the default rule would inline *)
  Common.PhaseTime.event_here ~in_copy:false "let-inline-decision";
  count <= count_threshold
  || size * count <= prod_threshold
  || size <= size_threshold
     && ((not (Atomic.get inline_by_expanded_size))
        || size <= 1
        || (size - 1) * (count - 1) <= prod_threshold
        || (Common.PhaseTime.event_here ~in_copy:false
              "let-kept-by-expanded-size";
            false))

(* the most elements an array literal is expanded into.  One [store] node per
   element, so this is a size bound and not a semantic one; the inputs that
   motivated the rewrite need one and two. *)
and max_finite_array_size = 32

(* [t] as [a * x + rest] with an integer literal coefficient and a remainder
   that does not mention [x], or [None] when it is not of that shape.
   Structural rather than sampled: sampled points agreeing on a line do not make
   a term affine, and a wrong coefficient here would produce a wrong array. *)
and affine_part_in x t =
  let combine f g t1 t2 =
    match (affine_part_in x t1, affine_part_in x t2) with
    | Some (a1, r1), Some (a2, r2) -> Some (f a1 a2, simplify_term (g r1 r2))
    | _ -> None
  in
  match t with
  (* first, so that a term the binder does not occur in is a remainder whatever
     its shape -- the arithmetic cases below only have to handle the ones it
     does occur in *)
  | _ when not (Set.mem (Term.tvs_of t) x) -> Some (Z.zero, t)
  | Term.Var (y, _, _) when Stdlib.(y = x) -> Some (Z.one, T_int.zero ())
  | Term.FunApp (T_int.Add, [ t1; t2 ], _) -> combine Z.add T_int.mk_add t1 t2
  | Term.FunApp (T_int.Sub, [ t1; t2 ], _) -> combine Z.sub T_int.mk_sub t1 t2
  | Term.FunApp (T_int.Neg, [ t1 ], _) ->
      Option.map (affine_part_in x t1) ~f:(fun (a, r) ->
          (Z.neg a, simplify_term (T_int.mk_neg r)))
  | Term.FunApp (T_int.Mul, [ t1; t2 ], _) -> (
      let scaled n a r =
        Some (Z.mul n a, simplify_term (T_int.mk_mul (T_int.mk_int n) r))
      in
      match (affine_part_in x t1, affine_part_in x t2) with
      | Some (a1, Term.FunApp (T_int.Int n, [], _)), Some (a2, r2)
        when Z.equal a1 Z.zero ->
          scaled n a2 r2
      | Some (a1, r1), Some (a2, Term.FunApp (T_int.Int n, [], _))
        when Z.equal a2 Z.zero ->
          scaled n a1 r1
      | _ -> None)
  | _ -> None

(* the same with the remainder required to be a literal, which is what a
   concrete range needs *)
and affine_in x t =
  match affine_part_in x t with
  | Some (a, Term.FunApp (T_int.Int b, [], _)) -> Some (a, b)
  | _ -> None

(* [a * x <= c] narrowed into the interval accumulated so far *)
and narrow_le a c (lo, hi) =
  if Z.(gt a zero) then
    let h = Z.fdiv c a in
    (lo, Some (match hi with None -> h | Some h' -> Z.min h h'))
  else if Z.(lt a zero) then
    let l = Z.cdiv c a in
    (Some (match lo with None -> l | Some l' -> Z.max l l'), hi)
  else (lo, hi)

(* the interval the guard forces on the array literal's binder, as far as its
   conjuncts of the form [a * x + b <compare> 0] say.  Every bound is a
   necessary condition of the guard, so the guard is false outside the
   interval, which is what makes the expansion exact. *)
and int_range_of_guard x phi =
  Set.fold (Formula.conjuncts_of phi) ~init:(None, None) ~f:(fun acc -> function
    | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) -> (
        match (affine_in x t1, affine_in x t2) with
        | Some (a1, b1), Some (a2, b2) -> (
            let a = Z.sub a1 a2 and b = Z.sub b1 b2 in
            match psym with
            | T_int.Leq -> narrow_le a (Z.neg b) acc
            | T_int.Lt -> narrow_le a Z.(neg b - one) acc
            | T_int.Geq -> narrow_le (Z.neg a) b acc
            | T_int.Gt -> narrow_le (Z.neg a) Z.(b - one) acc
            | T_bool.Eq -> narrow_le (Z.neg a) b (narrow_le a (Z.neg b) acc)
            | _ -> acc)
        | _ -> acc)
    | _ -> acc)

(* [fun (x : int) -> if guard then body else d], with [d] free of [x] and the
   guard confining [x] to a small concrete interval, as the chain of [store]s
   over the constant array [d] that it denotes *)
and finite_array_of_lambda (x, si) se body =
  match (si, body) with
  | T_int.SInt, Term.FunApp (T_bool.IfThenElse, [ cond; _; els ], _)
    when not (Set.mem (Term.tvs_of els) x) -> (
      match cond with
      | Term.FunApp (T_bool.Formula phi, [], _) -> (
          match int_range_of_guard x phi with
          | Some lo, Some hi when Z.gt lo hi ->
              (* the guard is unsatisfiable, so the literal is the constant
                 array of its own default *)
              Some (nf_app (T_array.mk_const_array si se els))
          | Some lo, Some hi
            when Z.leq lo hi
                 && Z.(leq (hi - lo + one) (Z.of_int max_finite_array_size)) ->
              let rec elements k acc =
                if Z.gt k hi then acc
                else
                  let e =
                    simplify_term
                    @@ Term.subst (Map.Poly.singleton x (T_int.mk_int k)) body
                  in
                  elements (Z.succ k)
                    (nf_app (T_array.mk_store si se acc (T_int.mk_int k) e))
              in
              Some (elements lo (nf_app (T_array.mk_const_array si se els)))
          | _ -> None)
      | _ -> None)
  | _ -> None

(* The terms that bound the index of an array literal in [t] and are not already
   concrete.  An array literal is what puts a goal outside the fragment an SMT
   solver decides -- it answers "incomplete (theory array)" and settles nothing
   -- while a literal confined to a concrete range is expanded into a chain of
   [store]s above and is no longer a literal at all.  So these terms are exactly
   what stands between such a goal and a decidable one, and a caller that may
   strengthen its question (one asking for a model rather than for validity) can
   fix them and get an answer. *)
and array_literal_range_bounds_of_term t =
  Set.fold (Term.filtered_terms_of ~f:T_array.is_lambda t) ~init:Set.Poly.empty
    ~f:(fun acc lam -> Set.union acc (range_bounds_of_lambda lam))

and array_literal_range_bounds phi =
  Set.fold (Formula.filtered_terms_of ~f:T_array.is_lambda phi)
    ~init:Set.Poly.empty ~f:(fun acc lam ->
      Set.union acc (range_bounds_of_lambda lam))

and range_bounds_of_lambda = function
  | Term.FunApp (T_array.ALambda ((x, si), _), [ body ], _) ->
      let nested = array_literal_range_bounds_of_term body in
      let here =
        match (si, body) with
        | ( T_int.SInt,
            Term.FunApp
              ( T_bool.IfThenElse,
                [ Term.FunApp (T_bool.Formula guard, [], _); _; _ ],
                _ ) ) ->
            (* a comparison in which the binder occurs linearly bounds it by
               the rest of the comparison; that remainder is the term to fix,
               unless it is a literal already, in which case the range is
               concrete and the expansion above has taken care of it *)
            Set.fold (Formula.conjuncts_of guard) ~init:Set.Poly.empty
              ~f:(fun acc -> function
              | Formula.Atom
                  ( Atom.App
                      (Predicate.Psym T_int.(Leq | Lt | Geq | Gt), [ t1; t2 ], _),
                    _ ) -> (
                  match (affine_part_in x t1, affine_part_in x t2) with
                  | Some (a1, r1), Some (a2, r2)
                    when not (Z.equal (Z.sub a1 a2) Z.zero) -> (
                      match simplify_term (T_int.mk_sub r1 r2) with
                      | Term.FunApp (T_int.Int _, [], _) -> acc
                      | r -> Set.add acc r)
                  | _ -> acc)
              | _ -> acc)
        | _ -> Set.Poly.empty
      in
      Set.union nested here
  | _ -> Set.Poly.empty

(*val simplify_term: Term.t -> Term.t*)
and simplify_term = function
  | Term.Var (_, sort, _) when Datatype.is_unit_sort sort -> Datatype.mk_unit ()
  | Var (tvar, sort, info) -> Term.mk_var ~info tvar sort
  | FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], info) ->
      let t1' = simplify_term t1 in
      let t2' = simplify_term t2 in
      let t3' = simplify_term t3 in
      simplify_ite_parts t1' t2' t3' info
  | FunApp (T_int.Case n, t1 :: branches, info) ->
      let t1' = simplify_term t1 in
      simplify_case_parts n t1' (List.map ~f:simplify_term branches) info
  | LetTerm (tvar, sort, def, body, info) ->
      let def' = simplify_term def in
      let body' = simplify_term body in
      let size = let_def_size def' in
      let count = Term.occur_times tvar body' in
      if inline_let ~size ~count then
        simplify_term @@ Term.subst (Map.Poly.singleton tvar def') body'
      else Term.mk_let_term ~info tvar sort def' body'
  | FunApp (fsym, ts, info) ->
      simplify_app fsym (List.map ~f:simplify_term ts) info

(* the [ite] rules of [simplify_term], on a condition and branches that are
   already simplified *)
and simplify_ite_parts t1' t2' t3' info =
  if T_bool.is_true t1' then t2'
  else if T_bool.is_false t1' then t3'
  else if Stdlib.(t2' = t3') then t2'
  else if T_bool.is_true t2' && T_bool.is_false t3' then t1'
  else if T_bool.is_false t2' && T_bool.is_true t3' then
    (* with [simplify_normal_forms] on, the negated condition is simplified
       (a negated quantifier pushed inward), as the next pass would; as a
       whole, since negating a conditional negates its branches, which are
       then no longer simplified parts *)
    if Atomic.get simplify_normal_forms then simplify_term (T_bool.negate t1')
    else T_bool.negate t1'
  else Term.mk_fsym_app ~info T_bool.IfThenElse [ t1'; t2'; t3' ]

(* the [Case] rules of [simplify_term], on a selector and branches that are
   already simplified *)
and simplify_case_parts n t1' branches' info =
      let t2, ts = List.hd_tl branches' in
      if
        T_int.is_int t1'
        &&
        let m = T_int.let_int t1' in
        Z.Compare.(m >= Z.zero && m < Z.of_int (List.length branches'))
      then List.nth_exn (t2 :: ts) (Z.to_int @@ T_int.let_int t1')
      else if List.for_all ts ~f:(fun t -> Stdlib.(t2 = t)) then t2
      else Term.mk_fsym_app ~info (T_int.Case n) (t1' :: t2 :: ts)

(* [t], an application a rule has just built over arguments that are already
   simplified, with the rules for its own node applied when
   [simplify_normal_forms] is on (and [t] itself when it is off).  The result
   equals [t] in every model; with the switch on it is what [simplify_term t]
   gives, without simplifying the arguments again. *)
and nf_app t =
  if not (Atomic.get simplify_normal_forms) then t
  else
    match t with
    | Term.FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], info) ->
        simplify_ite_parts t1 t2 t3 info
    | FunApp (T_int.Case n, t1 :: branches, info) ->
        simplify_case_parts n t1 branches info
    | FunApp (fsym, ts, info) -> simplify_app fsym ts info
    | Var _ | LetTerm _ -> t

(* the rules of [simplify_term] for an application other than [ite] and [Case],
   on arguments that are already simplified.  [known], when given, is the list
   of parts [simplify_known] takes as already simplified, and only an embedded
   formula ([T_bool.Formula]) uses it. *)
and simplify_app ?known fsym ts' info =
      try
        Term.of_value (get_dtenv ())
        @@ eval_term
        @@ Term.mk_fsym_app ~info fsym ts'
      with exn_ when not (Common.Timer.is_async exn_) -> (
        match (fsym, ts') with
        | T_bool.Formula phi, [] -> (
            match known with
            | None -> T_bool.of_formula (simplify phi) ~info
            | Some parts -> T_bool.of_formula (simplify_formula_known ~parts phi) ~info)
        | T_array.ALambda ((x, si), se), [ t ] -> (
            (* [ALambda] binds a variable in its argument, so the [ite]- and
               [Case]-lifting rules below must not apply to it: they would move
               a condition mentioning the binder out of its scope.  The body is
               already simplified, being one of [ts'].

               An array literal whose index the body confines to a finite,
               concrete range is a finite object, and writing it as one matters
               for more than size: a literal takes an SMT solver outside the
               array fragment it decides, while a chain of [store]s over a
               constant array stays inside it.  On the inputs this was written
               for, Z3 answered "incomplete (theory array)" on a goal that was
               otherwise ground -- it could not even decide that two such
               literals one [store] apart were equal -- and decided the same
               goal immediately once they were expanded.  The rewrite is exact,
               so it cannot move a verdict. *)
            match finite_array_of_lambda (x, si) se t with
            | Some arr -> arr
            | None -> Term.mk_fsym_app ~info fsym [ t ])
        | fsym, [ FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], _) ]
          when simplify_ite_case ->
            (* the following could make z3 much slower *)
            resimplify ~parts:[ t1; t2; t3 ]
            @@ T_bool.mk_if_then_else t1
                 (Term.mk_fsym_app fsym [ t2 ])
                 (Term.mk_fsym_app fsym [ t3 ])
        | fsym, [ t1; FunApp (T_bool.IfThenElse, [ t21; t22; t23 ], _) ]
          when simplify_ite_case && (not @@ T_bv.is_sbv t1) ->
            (* the following could make z3 much slower *)
            resimplify ~parts:[ t1; t21; t22; t23 ]
            @@ T_bool.mk_if_then_else t21
                 (Term.mk_fsym_app fsym [ t1; t22 ])
                 (Term.mk_fsym_app fsym [ t1; t23 ])
        | fsym, [ FunApp (T_bool.IfThenElse, [ t21; t22; t23 ], _); t1 ]
          when simplify_ite_case && (not @@ T_bv.is_sbv t1) ->
            (* the following could make z3 much slower *)
            resimplify ~parts:[ t1; t21; t22; t23 ]
            @@ T_bool.mk_if_then_else t21
                 (Term.mk_fsym_app fsym [ t22; t1 ])
                 (Term.mk_fsym_app fsym [ t23; t1 ])
        | fsym, [ FunApp (T_int.Case n, t1 :: branches, _) ]
          when simplify_ite_case ->
            resimplify ~parts:(t1 :: branches)
            @@ T_int.mk_case n t1
                 (List.map branches ~f:(fun t -> Term.mk_fsym_app fsym [ t ]))
        | fsym, [ t1; FunApp (T_int.Case n, t2 :: branches, _) ]
          when simplify_ite_case ->
            resimplify ~parts:(t1 :: t2 :: branches)
            @@ T_int.mk_case n t2
                 (List.map branches ~f:(fun t ->
                      Term.mk_fsym_app fsym [ t1; t ]))
        | fsym, [ FunApp (T_int.Case n, t2 :: branches, _); t1 ]
          when simplify_ite_case ->
            resimplify ~parts:(t1 :: t2 :: branches)
            @@ T_int.mk_case n t2
                 (List.map branches ~f:(fun t ->
                      Term.mk_fsym_app fsym [ t; t1 ]))
        | T_int.Neg, [ t ] -> (
            match t with
            | FunApp (T_int.Int n, [], _) ->
                Term.mk_fsym_app ~info (T_int.Int Z.(-n)) []
            | FunApp (T_int.Neg, [ t1 ], _) -> t1
            | FunApp (T_int.Mul, [ FunApp (T_int.Int n, [], _); t1 ], _)
            | FunApp (T_int.Mul, [ t1; FunApp (T_int.Int n, [], _) ], _) ->
                (* n is not 0, 1, -1 *)
                T_int.mk_mul (T_int.mk_int Z.(-n)) t1
            | _ -> Term.mk_fsym_app ~info T_int.Neg [ t ])
        | T_int.Nop, [ t ] -> t
        | T_int.Abs, [ t ] -> (
            match t with
            | FunApp (T_int.Int n, [], _) ->
                Term.mk_fsym_app ~info (T_int.Int Z.(abs n)) []
            | FunApp (T_int.Neg, [ t1 ], _) ->
                simplify_term (Term.mk_fsym_app ~info T_int.Abs [ t1 ])
            | FunApp (T_int.Mul, [ FunApp (T_int.Int n, [], _); t1 ], _)
            | FunApp (T_int.Mul, [ t1; FunApp (T_int.Int n, [], _) ], _) ->
                T_int.mk_mul
                  (T_int.mk_int Z.(abs n))
                  (simplify_term (Term.mk_fsym_app ~info T_int.Abs [ t1 ]))
            | _ -> Term.mk_fsym_app ~info T_int.Abs [ t ])
        | ( T_int.Add,
            [ FunApp (T_int.Neg, [ t1 ], _); FunApp (T_int.Neg, [ t2 ], _) ] )
          ->
            nf_app @@ T_int.mk_neg @@ simplify_term (T_int.mk_add t1 t2)
        | T_int.Add, [ FunApp (T_int.Neg, [ t1 ], _); t2 ] ->
            simplify_term (T_int.mk_sub t2 t1)
        | T_int.Add, [ t1; FunApp (T_int.Neg, [ t2 ], _) ] ->
            simplify_term (T_int.mk_sub t1 t2)
        | T_int.Add, [ t1; t2 ] -> (
            if T_int.is_zero t2 then t1
            else if T_int.is_zero t1 then t2
            else
              match (t1, t2) with
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) ->
                  Term.mk_fsym_app ~info (T_int.Int Z.(n1 + n2)) []
              | _, _ -> Term.mk_fsym_app ~info T_int.Add [ t1; t2 ])
        | ( T_int.Sub,
            [ FunApp (T_int.Neg, [ t1 ], _); FunApp (T_int.Neg, [ t2 ], _) ] )
          ->
            simplify_term (T_int.mk_sub t2 t1)
        | T_int.Sub, [ FunApp (T_int.Neg, [ t1 ], _); t2 ] ->
            nf_app @@ T_int.mk_neg @@ simplify_term (T_int.mk_add t1 t2)
        | T_int.Sub, [ t1; FunApp (T_int.Neg, [ t2 ], _) ] ->
            simplify_term (T_int.mk_add t1 t2)
        | T_int.Sub, [ t1; t2 ] -> (
            if T_int.is_zero t2 then t1
            else if T_int.is_zero t1 then nf_app (T_int.mk_neg t2)
            else if Stdlib.(t1 = t2) then T_int.zero ()
            else
              match (t1, t2) with
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) ->
                  Term.mk_fsym_app ~info (T_int.Int Z.(n1 - n2)) []
              | _, _ -> Term.mk_fsym_app ~info T_int.Sub [ t1; t2 ])
        | ( T_int.Mul,
            [ FunApp (T_int.Neg, [ t1 ], _); FunApp (T_int.Neg, [ t2 ], _) ] )
          ->
            simplify_term (T_int.mk_mul t1 t2)
        | T_int.Mul, [ FunApp (T_int.Neg, [ t1 ], _); t2 ]
        | T_int.Mul, [ t1; FunApp (T_int.Neg, [ t2 ], _) ] ->
            nf_app @@ T_int.mk_neg @@ simplify_term (T_int.mk_mul t1 t2)
        | T_int.Mul, [ t1; t2 ] -> (
            if T_int.is_zero t1 || T_int.is_zero t2 then T_int.zero ()
            else if T_int.is_unit t1 then t2
            else if T_int.is_unit t2 then t1
            else if T_int.is_minus_one t1 then nf_app (T_int.mk_neg t2)
            else if T_int.is_minus_one t2 then nf_app (T_int.mk_neg t1)
            else
              match (t1, t2) with
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) ->
                  Term.mk_fsym_app ~info (T_int.Int Z.(n1 * n2)) []
              | _, _ -> Term.mk_fsym_app ~info T_int.Mul [ t1; t2 ])
        | T_int.Div m, [ t1; t2 ] -> (
            if T_int.is_zero t1 && divisor_is_nonzero t2 then T_int.zero ()
            else if T_int.is_unit t2 then t1
            else if T_int.is_minus_one t2 then nf_app (T_int.mk_neg t1)
            else
              match (t1, t2) with
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _)
                when Z.Compare.(n2 <> Z.zero) ->
                  Term.mk_fsym_app ~info (T_int.Int (Value.div_of m n1 n2)) []
              | _, _ -> Term.mk_fsym_app ~info (T_int.Div m) [ t1; t2 ])
        | T_int.Rem m, [ t1; t2 ] -> (
            if T_int.is_zero t1 && divisor_is_nonzero t2 then T_int.zero ()
            else if T_int.is_unit t2 then T_int.zero ()
            else if T_int.is_minus_one t2 then T_int.zero ()
            else
              match (t1, t2) with
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _)
                when Z.Compare.(n2 <> Z.zero) ->
                  Term.mk_fsym_app ~info (T_int.Int (Value.rem_of m n1 n2)) []
              | _, _ -> Term.mk_fsym_app ~info (T_int.Rem m) [ t1; t2 ])
        | T_int.Power, [ t1; t2 ] -> (
            if T_int.is_zero t1 && exponent_is_positive t2 then T_int.zero ()
            else if T_int.is_unit t1 || T_int.is_zero t2 then T_int.one ()
            else if T_int.is_unit t2 then t1
            else
              match (t1, t2) with
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _)
                when Z.Compare.(n1 <> Z.zero || n2 <> Z.zero)
                     && Z.Compare.(n2 >= Z.zero) ->
                  (* a negative exponent is undefined for Z.pow (it raises) *)
                  Term.mk_fsym_app ~info
                    (T_int.Int Z.(pow n1 (to_int (*ToDo*) n2)))
                    []
              | _, _ -> Term.mk_fsym_app ~info T_int.Power [ t1; t2 ])
        | T_real.RNeg, [ t ] -> (
            match t with
            | FunApp (T_real.Real r, [], _) ->
                Term.mk_fsym_app ~info (T_real.Real Q.(-r)) []
            | FunApp (T_real.RNeg, [ t1 ], _) -> t1
            | FunApp (T_real.RMul, [ Term.FunApp (T_real.Real r, [], _); t1 ], _)
            | FunApp (T_real.RMul, [ t1; Term.FunApp (T_real.Real r, [], _) ], _)
              ->
                (* r is not 0, 1, -1 *)
                T_real.mk_rmul (T_real.mk_real Q.(-r)) t1
            | _ -> Term.mk_fsym_app ~info T_real.RNeg [ t ])
        | ( T_real.RAdd,
            [ FunApp (T_real.RNeg, [ t1 ], _); FunApp (T_real.RNeg, [ t2 ], _) ]
          ) ->
            nf_app @@ T_real.mk_rneg @@ simplify_term (T_real.mk_radd t1 t2)
        | T_real.RAdd, [ FunApp (T_real.RNeg, [ t1 ], _); t2 ] ->
            simplify_term (T_real.mk_rsub t2 t1)
        | T_real.RAdd, [ t1; FunApp (T_real.RNeg, [ t2 ], _) ] ->
            simplify_term (T_real.mk_rsub t1 t2)
        | T_real.RAdd, [ t1; t2 ] -> (
            if T_real.is_rzero t2 then t1
            else if T_real.is_rzero t1 then t2
            else
              match (t1, t2) with
              | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                ->
                  Term.mk_fsym_app ~info (T_real.Real Q.(r1 + r2)) []
              | _, _ -> Term.mk_fsym_app ~info T_real.RAdd [ t1; t2 ])
        | ( T_real.RSub,
            [ FunApp (T_real.RNeg, [ t1 ], _); FunApp (T_real.RNeg, [ t2 ], _) ]
          ) ->
            simplify_term (T_real.mk_rsub t2 t1)
        | T_real.RSub, [ FunApp (T_real.RNeg, [ t1 ], _); t2 ] ->
            nf_app @@ T_real.mk_rneg @@ simplify_term (T_real.mk_radd t1 t2)
        | T_real.RSub, [ t1; FunApp (T_real.RNeg, [ t2 ], _) ] ->
            simplify_term (T_real.mk_radd t1 t2)
        | T_real.RSub, [ t1; t2 ] -> (
            if T_real.is_rzero t2 then t1
            else if T_real.is_rzero t1 then nf_app (T_real.mk_rneg t2)
            else if Stdlib.(t1 = t2) then T_real.rzero ()
            else
              match (t1, t2) with
              | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                ->
                  Term.mk_fsym_app ~info (T_real.Real Q.(r1 - r2)) []
              | _, _ -> Term.mk_fsym_app ~info T_real.RSub [ t1; t2 ])
        | ( T_real.RMul,
            [ FunApp (T_real.RNeg, [ t1 ], _); FunApp (T_real.RNeg, [ t2 ], _) ]
          ) ->
            simplify_term (T_real.mk_rmul t1 t2)
        | T_real.RMul, [ FunApp (T_real.RNeg, [ t1 ], _); t2 ]
        | T_real.RMul, [ t1; FunApp (T_real.RNeg, [ t2 ], _) ] ->
            nf_app @@ T_real.mk_rneg @@ simplify_term (T_real.mk_rmul t1 t2)
        | T_real.RMul, [ t1; t2 ] -> (
            if T_real.is_rzero t1 || T_real.is_rzero t2 then T_real.rzero ()
            else if T_real.is_runit t1 then t2
            else if T_real.is_runit t2 then t1
            else if T_real.is_rminus_one t1 then nf_app (T_real.mk_rneg t2)
            else if T_real.is_rminus_one t2 then nf_app (T_real.mk_rneg t1)
            else
              match (t1, t2) with
              | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                ->
                  Term.mk_fsym_app ~info (T_real.Real Q.(r1 * r2)) []
              | _, _ -> Term.mk_fsym_app ~info T_real.RMul [ t1; t2 ])
        | T_real.RDiv, [ t1; t2 ] -> (
            if T_real.is_rzero t1 && divisor_is_nonzero t2 then T_real.rzero ()
            else if T_real.is_runit t2 then t1
            else if T_real.is_rminus_one t2 then nf_app (T_real.mk_rneg t1)
            else
              match (t1, t2) with
              | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                when Q.(r2 <> zero) ->
                  Term.mk_fsym_app ~info (T_real.Real Q.(r1 / r2)) []
              | _, _ -> Term.mk_fsym_app ~info T_real.RDiv [ t1; t2 ])
        | T_real.RPower, [ t1; t2 ] -> (
            if T_real.is_rzero t1 && exponent_is_positive t2 then
              T_real.rzero ()
            else if T_real.is_runit t1 || T_real.is_rzero t2 then T_real.rone ()
            else if T_real.is_runit t2 then t1
            else
              match (t1, t2) with
              (*| FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                when Q.(r1 <> zero || r2 <> zero) ->
                  FunApp (T_real.Real Q.(pow r1 r2), [], info)*)
              | _, _ -> Term.mk_fsym_app ~info T_real.RPower [ t1; t2 ])
        | T_bv.BVAdd _size, [ t1; t2 ] ->
            if T_bv.is_bvzero t2 then t1
            else if T_bv.is_bvzero t1 then t2
            else Term.mk_fsym_app ~info fsym [ t1; t2 ]
        | T_bv.BVSub size, [ t1; t2 ] ->
            if T_bv.is_bvzero t2 then t1
            else if T_bv.is_bvzero t1 then T_bv.mk_bvneg ~size t2
            else if Stdlib.(t1 = t2) then T_bv.bvzero ~size ()
            else Term.mk_fsym_app ~info fsym [ t1; t2 ]
        | T_bv.BVMul size, [ t1; t2 ] ->
            if T_bv.is_bvzero t1 || T_bv.is_bvzero t2 then T_bv.bvzero ~size ()
            else if T_bv.is_bvunit t1 then t2
            else if T_bv.is_bvunit t2 then t1
            else Term.mk_fsym_app ~info fsym [ t1; t2 ]
        | T_bv.BVDiv (_size, _signed), [ t1; t2 ] ->
            (* no [0 div t = 0] rule: bvudiv 0 0 is all-ones in SMT-LIB *)
            if T_bv.is_bvunit t2 then t1
            else Term.mk_fsym_app ~info fsym [ t1; t2 ]
              (* ToDo: support other bitvector operations *)
        | T_irb.RealToInt, [ FunApp (T_real.Real r, [], _) ] ->
            T_int.mk_int (Z.fdiv (Q.num r) (Q.den r))
            (* SMT-LIB to_int is floor *)
        | T_irb.IntToReal, [ FunApp (T_int.Int i, [], _) ] ->
            T_real.mk_real (Q.of_bigint i)
        | T_irb.IntToBV size, [ FunApp (T_int.Int i, [], _) ] ->
            T_bv.mk_bvnum ~size i
        | ( T_irb.BVToInt (_size, signed),
            [ FunApp (T_bv.BVNum (Some s, i), [], _) ] ) ->
            if s = 0 then T_int.mk_int Z.zero
            else
              T_int.mk_int
                (if T_bv.is_signed signed && Z.testbit i (s - 1) then
                   Z.sub i (Z.shift_left Z.one s)
                 else i)
        | ( T_irb.IntToBV size1,
            [ FunApp (T_irb.BVToInt (size2, Some true), [ t ], _) ] )
          when T_bv.eq_size size1 size2 ->
            t
        | T_trace.TrConcat _, [ FunApp (T_trace.TrEpsilon, [], _); t ]
        | T_trace.TrConcat _, [ t; FunApp (T_trace.TrEpsilon, [], _) ] ->
            t
        | T_regex.RegComplement, [ FunApp (T_regex.RegEmpty, [], _); _ ] ->
            T_regex.mk_full ()
        | T_regex.RegComplement, [ FunApp (T_regex.RegFull, [], _); _ ] ->
            T_regex.mk_empty ()
        | ( T_regex.RegComplement,
            [ FunApp (T_regex.RegComplement, [ t1 ], _); _ ] ) ->
            t1
        | T_regex.RegComplement, [ FunApp (T_regex.RegUnion, [ t1; t2 ], _); _ ]
          ->
            T_regex.mk_inter
              (simplify_term @@ T_regex.mk_complement t1)
              (simplify_term @@ T_regex.mk_complement t2)
        | T_regex.RegComplement, [ FunApp (T_regex.RegInter, [ t1; t2 ], _); _ ]
          ->
            T_regex.mk_union
              (simplify_term @@ T_regex.mk_complement t1)
              (simplify_term @@ T_regex.mk_complement t2)
        | T_regex.RegUnion, [ t1; FunApp (T_regex.RegComplement, [ t2 ], _) ]
          when Stdlib.(t1 = t2) ->
            T_regex.mk_full ()
        | T_regex.RegUnion, [ FunApp (T_regex.RegComplement, [ t1 ], _); t2 ]
          when Stdlib.(t1 = t2) ->
            T_regex.mk_full ()
        | T_regex.RegUnion, [ FunApp (T_regex.RegEmpty, [], _); t1 ]
        | T_regex.RegUnion, [ t1; FunApp (T_regex.RegEmpty, [], _) ] ->
            t1
        | T_regex.RegUnion, [ FunApp (T_regex.RegFull, [], _); _ ]
        | T_regex.RegUnion, [ _; FunApp (T_regex.RegFull, [], _) ] ->
            T_regex.mk_full ()
        | T_regex.RegInter, [ t1; FunApp (T_regex.RegComplement, [ t2 ], _) ]
          when Stdlib.(t1 = t2) ->
            T_regex.mk_empty ()
        | T_regex.RegInter, [ FunApp (T_regex.RegComplement, [ t1 ], _); t2 ]
          when Stdlib.(t1 = t2) ->
            T_regex.mk_empty ()
        | T_regex.RegInter, [ FunApp (T_regex.RegEmpty, [], _); _ ]
        | T_regex.RegInter, [ _; FunApp (T_regex.RegEmpty, [], _) ] ->
            T_regex.mk_empty ()
        | T_regex.RegInter, [ FunApp (T_regex.RegFull, [], _); t1 ]
        | T_regex.RegInter, [ t1; FunApp (T_regex.RegFull, [], _) ] ->
            t1
        | T_regex.RegConcat, [ FunApp (T_regex.RegEmpty, [], _); _ ]
        | T_regex.RegConcat, [ _; FunApp (T_regex.RegEmpty, [], _) ] ->
            T_regex.mk_empty ()
        | T_regex.RegConcat, [ FunApp (T_regex.RegEpsilon, [], _); t1 ]
        | T_regex.RegConcat, [ t1; FunApp (T_regex.RegEpsilon, [], _) ] ->
            t1
        | ( T_array.AStore _,
            [ (FunApp (T_array.AConst _, [ t1 ], _) as t); _; t2 ] )
          when Stdlib.(t1 = t2) ->
            t
        | ( T_array.AStore _,
            [ FunApp (T_array.AStore (s1, s2), [ t1; t2; _ ], _); t3; t4 ] )
          when Stdlib.(t2 = t3) ->
            T_array.mk_store s1 s2 t1 t3 t4
        | ( T_array.AStore (s1, s2),
            [
              FunApp (T_array.AStore (s3, s4), [ tarr; ti1; te1 ], _); ti2; te2;
            ] )
          when (try Stdlib.(Term.value_of ti1 <> Term.value_of ti2)
                with exn_ when not (Common.Timer.is_async exn_) -> false)
               && Stdlib.(ti1 > ti2) ->
            T_array.mk_store s3 s4 (T_array.mk_store s1 s2 tarr ti2 te2) ti1 te1
        (* read over write on sequences.  [seq.store] means "this position
           replaced, if it is a position at all", so the length is the original
           one whatever the index is, and a read splits on whether it is the
           written index -- both facts the three-piece concatenation a solver
           would otherwise see makes it derive from the sequence axioms every
           time.  The index guard is not optional: outside the range the store
           is the original sequence, so the written value is not there. *)
        | T_seq.SqLen _, [ FunApp (T_seq.SqStore se, [ sq; _; _ ], _) ] ->
            simplify_term @@ T_seq.mk_len se sq
        (* Read over write, and it fires only where the READ index is known to
           be inside the sequence.  The tempting form -- [if j = i and i is in
           range then e else nth(s, j)] -- is wrong in its else branch: a read
           outside the sequence is underspecified and the SEQUENCE is part of
           what it is underspecified in, so [nth(store(s,i,e), j)] and
           [nth(s, j)] are two different applications there and a solver may
           give them different values.  With only the written index guarded,
           [nth(store(s,0,v), -1) = nth(s, -1)] came out provable for every [s]
           and [v], which the theory does not give.

           Two repairs were measured and are not here.  Keeping the term
           unrewritten out of range, as the third branch of an [ite], leaves the
           store inside the formula twice and it expands into a concatenation at
           the solver boundary: the read-over-write and frame benchmarks both
           stopped answering.  And the range hypothesis this needs usually sits
           in the clause's PREMISE rather than in the term, which a term rewrite
           cannot see -- making it visible is a change to where simplification
           happens, not a condition to add here. *)
        | T_seq.SqNth _, [ FunApp (T_seq.SqStore se, [ sq; i; e ], _); j ]
          when Option.is_some (seq_index_in_range sq j) ->
            simplify_term
            @@ T_bool.mk_if_then_else
                 (T_bool.of_formula
                 @@ Formula.and_of
                      [
                        Formula.eq i j;
                        Formula.leq (T_int.zero ()) i;
                        Formula.lt i (T_seq.mk_len se sq);
                      ])
                 e (T_seq.mk_nth se sq j)
        (* Three identities of the sequence theory that the simplifier did not
           know, and the cost of not knowing them is not the terms themselves
           but where they end up.  A derived example's GUARD is the clause's
           pure part with a counterexample's values substituted, so it is built
           out of exactly these shapes: measured on a Rust-derived slice
           benchmark, one guard was eight conjuncts of which seven were
           tautologies -- [seq.empty = seq.extract (seq.unit x) 1 (seq.len
           (seq.unit x) - 1)], [x + -1 * seq.nth (seq.unit x) 0 = 0],
           [-1 + seq.len (seq.unit x) >= 0] and so on -- around a single real
           constraint, [x != 0].  That guard travels inside the key the labeling
           phase compares examples by, so two examples saying the same thing
           stay syntactically different, and every satisfiability check carries
           the whole block to the solver.

           All three are unconditional.  [seq_len_of] computes a length only
           when the sequence's own structure gives it, so there is no hypothesis
           about an index being in range; [nth] is rewritten only at index 0 of
           a one-element sequence, where the read cannot be out of bounds; and
           [seq.extract] is specified to return the empty sequence for a
           non-positive length, so that case needs no side condition either. *)
        | T_seq.SqLen _, [ sq ] when Option.is_some (seq_len_of sq) ->
            T_int.mk_int (Option.value_exn (seq_len_of sq))
        | T_seq.SqExtract se, [ _; _; FunApp (T_int.Int n, [], _) ]
          when Z.(leq n zero) ->
            T_seq.mk_empty se
        (* [seq.extract] of a sequence literal at literal bounds is the
           literal's slice.  Exact: [seq.extract s i n] is specified for every
           argument -- the empty sequence when [i] is outside [0, len s) or [n]
           is not positive, and otherwise the [min n (len s - i)] elements from
           [i] -- and a literal fixes [len s] and every element. *)
        | ( T_seq.SqExtract se,
            [ sq; FunApp (T_int.Int i, [], _); FunApp (T_int.Int n, [], _) ] )
          when Option.is_some (seq_elems_of sq) ->
            let es = Option.value_exn (seq_elems_of sq) in
            let len = Z.of_int (List.length es) in
            if Z.(lt i zero || geq i len || leq n zero) then T_seq.mk_empty se
            else
              let i = Z.to_int i in
              let n = Z.to_int (Z.min n Z.(len - of_int i)) in
              seq_of_elems se (List.sub es ~pos:i ~len:n)
        (* A read of a sequence literal at a literal index inside it is the
           element there; [seq_nth_of_literal] states when that is known and
           why it is exact.  A read outside is left alone: it is a term the
           theory leaves open, not the neighbouring element. *)
        | T_seq.SqNth _, [ sq; FunApp (T_int.Int k, [], _) ]
          when Option.is_some (seq_nth_of_literal sq k) ->
            simplify_term (Option.value_exn (seq_nth_of_literal sq k))
        (* Store normalisation.  A [seq.store s i e] replaces position [i] when
           [i] is a position of [s] and is [s] itself otherwise, and keeps the
           length either way; each rule below is an identity of that meaning in
           every model, out-of-range indices included.
           - a store at a literal index into a literal is pushed into the part
             holding that position: before the start, or past the end of a
             unit, it is the identity; into a unit at 0 it is the new unit; into
             [a ++ b] with [len a] syntactic it is a store into [a] below [len a]
             and a store into [b] at [k - len a] otherwise.  The last case is
             exact past the end too: then [k - len a] is past the end of [b] and
             both sides are the unchanged sequence;
           - a store over a store at the same index keeps only the later write
             (both are in range or neither is);
           - storing back a position's own element is the identity: in range it
             writes what is there, out of range the store ignores the (open)
             value it was given;
           - stores at distinct literal indices commute, since they write
             different positions, so they are ordered by index and two examples
             writing the same positions in different orders become one term. *)
        | T_seq.SqStore se, [ sq; FunApp (T_int.Int k, [], _); e ]
          when Option.is_some (push_literal_store se sq k e) ->
            Option.value_exn (push_literal_store se sq k e)
        | T_seq.SqStore se, [ FunApp (T_seq.SqStore _, [ sq; i1; _ ], _); i2; e ]
          when Stdlib.(i1 = i2) ->
            T_seq.mk_store se sq i2 e
        | T_seq.SqStore _, [ sq; i; FunApp (T_seq.SqNth _, [ sq'; i' ], _) ]
          when Stdlib.(sq = sq') && Stdlib.(i = i') ->
            sq
        | ( T_seq.SqStore se,
            [
              FunApp
                ( T_seq.SqStore _,
                  [ sq; (FunApp (T_int.Int k1, [], _) as i1); e1 ],
                  _ );
              (FunApp (T_int.Int k2, [], _) as i2);
              e2;
            ] )
          when Z.Compare.(k1 > k2) ->
            T_seq.mk_store se
              (simplify_term @@ T_seq.mk_store se sq i2 e2)
              i1 e1
        | T_array.ASelect _, [ arr; ti ] -> (
            match T_array.eval_select arr ti with
            | Some te -> simplify_term te
            | None -> Term.mk_fsym_app ~info fsym ts')
        | T_tuple.TupleSel (_, i), [ t ] -> (
            match T_tuple.eval_select t i with
            | Some te -> simplify_term te
            | None -> Term.mk_fsym_app ~info fsym ts')
        | T_dt.DTSel (sel_name, dt, _), [ t ] -> (
            match T_dt.eval_select sel_name dt t with
            | Some te -> simplify_term te
            | None -> Term.mk_fsym_app ~info fsym ts')
        | T_ref.Deref _, [ t ] -> (
            match T_ref.eval_select t with
            | Some te -> simplify_term te
            | None -> Term.mk_fsym_app ~info fsym ts')
        | fsym, ts -> Term.mk_fsym_app ~info fsym ts)
(* including T_int.int, T_real.Real *)

(*val simplify_pred: Predicate.t -> Predicate.t*)
and simplify_pred = function
  | Predicate.Var (var, sort) -> Predicate.Var (var, sort)
  | Psym psym -> Psym psym
  | Fixpoint def -> Fixpoint { def with body = simplify def.body }

(*val simplify_pred_neg: Predicate.t -> Predicate.t option*)
and simplify_pred_neg = function
  | Predicate.Var _ -> None
  | Fixpoint def ->
      Option.return
      @@ Predicate.Fixpoint
           {
             def with
             kind = Predicate.flip_fop def.kind;
             body = simplify_neg def.body;
           }
  | Psym psym -> (
      try Option.return @@ Predicate.Psym (Predicate.negate_psym psym)
      with exn_ when not (Common.Timer.is_async exn_) -> None)

(*val simplify_atom: Atom.t -> Formula.t*)
and can_simplify = function
  | Term.Var (_, _, _) -> false
  | Term.FunApp (FVar _, _, _) -> false
  | Term.FunApp (T_dt.DTSel _, _, _) -> false
  | Term.FunApp (T_tuple.TupleSel _, _, _) -> false
  | Term.FunApp (T_array.ASelect _, _, _) -> false
  (* a read the evaluator cannot see into: turning [t = true] back into a
     formula yields [t = true] again, so answering [true] here recurses without
     end on a Bool-valued read *)
  | Term.FunApp ((T_seq.SqNth _ | T_ref.Deref _), _, _) -> false
  | _ -> true

and simplify_atom = function
  | Atom.True _ -> Formula.mk_true ()
  | False _ -> Formula.mk_false ()
  | App (pred, terms, info) ->
      simplify_atom_app (simplify_pred pred)
        (List.map ~f:simplify_term terms)
        info

(* the rules of [simplify_atom], on a predicate and arguments that are already
   simplified *)
and simplify_atom_app pred' ts' info =
      match (pred', ts') with
      | Predicate.Psym T_bool.Eq, [ t1; t2 ] when alpha_equiv t1 t2 ->
          Formula.mk_true ()
      | Predicate.Psym T_bool.Neq, [ t1; t2 ] when alpha_equiv t1 t2 ->
          Formula.mk_false ()
      | Predicate.Psym (T_bool.(Eq | Neq) as psym), [ t1; t2 ]
        when T_array.is_lambda t1 && T_array.is_lambda t2 ->
          (* extensionality: (lam x. b1) = (lam y. b2) iff forall i. b1[i/x] =
             b2[i/y]; Z3 cannot decide (dis)equalities between lambda arrays
             inside a validity query, but it can handle the quantified form *)
          let (x1, s1), _, b1, _ = T_array.let_lambda t1 in
          let (x2, _), _, b2, _ = T_array.let_lambda t2 in
          let i = Ident.mk_fresh_tvar () in
          let b1 = Term.rename (Map.Poly.singleton x1 i) b1 in
          let b2 = Term.rename (Map.Poly.singleton x2 i) b2 in
          simplify
          @@
          if Stdlib.(psym = T_bool.Eq) then
            Formula.mk_forall [ (i, s1) ] (Formula.eq b1 b2)
          else Formula.mk_exists [ (i, s1) ] (Formula.neq b1 b2)
      (* Equality of sequence literals.  Sequences are extensional: two are
         equal exactly when they have the same length and the same element at
         every position.  So two literals of different syntactic lengths are
         never equal (this needs only the lengths, so a store inside either
         side does not matter), and two literals with all elements known are
         equal exactly when their elements are pairwise equal -- [unit a =
         unit b] is [a = b].  Both are identities in every model. *)
      | Predicate.Psym (T_bool.(Eq | Neq) as psym), [ t1; t2 ]
        when match (seq_len_of t1, seq_len_of t2) with
             | Some n1, Some n2 -> not (Z.equal n1 n2)
             | _ -> false ->
          Formula.mk_bool Stdlib.(psym = T_bool.Neq)
      | Predicate.Psym (T_bool.(Eq | Neq) as psym), [ t1; t2 ]
        when Option.is_some (seq_elems_of t1) && Option.is_some (seq_elems_of t2)
        ->
          let es1 = Option.value_exn (seq_elems_of t1) in
          let es2 = Option.value_exn (seq_elems_of t2) in
          simplify
          @@
          if Stdlib.(psym = T_bool.Eq) then
            Formula.and_of @@ List.map2_exn es1 es2 ~f:Formula.eq
          else Formula.or_of @@ List.map2_exn es1 es2 ~f:Formula.neq
      | ( Predicate.Psym psym,
          [ t1; FunApp (T_bool.IfThenElse, [ t21; t22; t23 ], _) ] )
        when simplify_ite_case && ((not (T_bv.is_sbv t1)) || T_bv.is_bvnum t1)
        ->
          (* the following makes z3 much slower *)
          orient_nf @@ Formula.of_bool_term @@ resimplify ~parts:[ t1; t21; t22; t23 ]
          @@ T_bool.mk_if_then_else t21
               (T_bool.of_atom @@ Atom.mk_psym_app psym [ t1; t22 ])
               (T_bool.of_atom @@ Atom.mk_psym_app psym [ t1; t23 ])
      | ( Predicate.Psym psym,
          [ FunApp (T_bool.IfThenElse, [ t21; t22; t23 ], _); t1 ] )
        when simplify_ite_case && ((not (T_bv.is_sbv t1)) || T_bv.is_bvnum t1)
        ->
          (* the following makes z3 much slower *)
          orient_nf @@ Formula.of_bool_term @@ resimplify ~parts:[ t1; t21; t22; t23 ]
          @@ T_bool.mk_if_then_else t21
               (T_bool.of_atom @@ Atom.mk_psym_app psym [ t22; t1 ])
               (T_bool.of_atom @@ Atom.mk_psym_app psym [ t23; t1 ])
      | Predicate.Psym psym, [ t1; FunApp (T_int.Case n, t2 :: branches, _) ]
        when simplify_ite_case ->
          if elim_case then
            simplify
            @@ Formula.or_of
                 (List.mapi branches ~f:(fun i t ->
                      Formula.and_of
                        [
                          Formula.eq t2 (T_int.mk_int (Z.of_int i));
                          Formula.mk_atom @@ Atom.mk_psym_app psym [ t1; t ];
                        ]))
          else
            orient_nf @@ Formula.of_bool_term @@ resimplify ~parts:(t1 :: t2 :: branches)
            @@ T_int.mk_case n t2
                 (List.map branches ~f:(fun t ->
                      T_bool.of_atom @@ Atom.mk_psym_app psym [ t1; t ]))
      | Predicate.Psym psym, [ FunApp (T_int.Case n, t2 :: branches, _); t1 ]
        when simplify_ite_case ->
          if elim_case then
            simplify
            @@ Formula.or_of
                 (List.mapi branches ~f:(fun i t ->
                      Formula.and_of
                        [
                          Formula.eq t2 (T_int.mk_int (Z.of_int i));
                          Formula.mk_atom @@ Atom.mk_psym_app psym [ t; t1 ];
                        ]))
          else
            orient_nf @@ Formula.of_bool_term @@ resimplify ~parts:(t1 :: t2 :: branches)
            @@ T_int.mk_case n t2
                 (List.map branches ~f:(fun t ->
                      T_bool.of_atom @@ Atom.mk_psym_app psym [ t; t1 ]))
      (*| (Predicate.Psym T_bool.Eq, [t1; t2] | Predicate.Psym T_bool.Neq, [t1; t2])
        when Stdlib.(Term.sort_of t1 <> Term.sort_of t2) ->
        failwith @@ sprintf "inconsistent sorts of %s and %s"
          (Term.str_of_sort @@ Term.sort_of t1) (Term.str_of_sort @@ Term.sort_of t2)*)
      | Predicate.Psym psym, [ t1; t2 ]
        when ((Stdlib.(psym = T_bool.Eq) && T_bool.is_true t1)
             || (Stdlib.(psym = T_bool.Neq) && T_bool.is_false t1))
             && can_simplify t2 ->
          simplify @@ Formula.of_bool_term t2
      | Predicate.Psym psym, [ t1; t2 ]
        when ((Stdlib.(psym = T_bool.Eq) && T_bool.is_false t1)
             || (Stdlib.(psym = T_bool.Neq) && T_bool.is_true t1))
             && can_simplify t2 ->
          simplify_neg @@ Formula.of_bool_term t2
      | Predicate.Psym psym, [ t1; t2 ]
        when ((Stdlib.(psym = T_bool.Eq) && T_bool.is_true t2)
             || (Stdlib.(psym = T_bool.Neq) && T_bool.is_false t2))
             && can_simplify t1 ->
          simplify @@ Formula.of_bool_term t1
      | Predicate.Psym psym, [ t1; t2 ]
        when ((Stdlib.(psym = T_bool.Eq) && T_bool.is_false t2)
             || (Stdlib.(psym = T_bool.Neq) && T_bool.is_true t2))
             && can_simplify t1 ->
          simplify_neg @@ Formula.of_bool_term t1
      | Predicate.Psym T_bool.Eq, [ t1; t2 ]
        when Term.is_bool_sort @@ Term.sort_of t1 ->
          (*ToDo*)
          if Stdlib.(t1 = T_bool.negate t2) then Formula.mk_false ()
          else if
            can_simplify t1 && can_simplify t2
            && not (T_bool.is_atom t1 && T_bool.is_atom t2)
          then
            let p1 = Formula.of_bool_term t1 in
            let p2 = Formula.of_bool_term t2 in
            simplify
            @@ Formula.mk_or ~info (Formula.mk_and p1 p2)
                 (Formula.mk_and (Formula.mk_neg p1) (Formula.mk_neg p2))
          else if
            can_simplify t1 && can_simplify t2
            && not (T_bool.is_atom t1 && T_bool.is_atom t2)
          then
            let p1 = Formula.of_bool_term t1 in
            let p2 = Formula.of_bool_term t2 in
            simplify
            @@ Formula.mk_or ~info (Formula.mk_and p1 p2)
                 (Formula.mk_and (Formula.mk_neg p1) (Formula.mk_neg p2))
          else
            Formula.mk_atom
              (Atom.mk_app ~info (Predicate.Psym T_bool.Eq) [ t1; t2 ]) (*ToDo*)
      | Predicate.Psym T_bool.Neq, [ t1; t2 ]
        when Term.is_bool_sort @@ Term.sort_of t1 ->
          (*ToDo*)
          if Stdlib.(t1 = T_bool.negate t2) then Formula.mk_true ()
          else if
            can_simplify t1 && can_simplify t2
            && not (T_bool.is_atom t1 && T_bool.is_atom t2)
          then
            let p1 = Formula.of_bool_term t1 in
            let p2 = Formula.of_bool_term t2 in
            simplify
            @@ Formula.mk_or ~info
                 (Formula.mk_and (Formula.mk_neg p1) p2)
                 (Formula.mk_and p1 (Formula.mk_neg p2))
          else
            Formula.mk_atom
              (Atom.mk_app ~info (Predicate.Psym T_bool.Neq) [ t1; t2 ])
            (*ToDo*)
      | ( Predicate.Psym (T_bool.(Eq | Neq) as psym),
          [
            Term.FunApp (T_int.Neg, [ t1 ], _);
            t2 (*| [ t2; Term.FunApp (T_int.Neg, [ t1 ], _) ]*);
          ] ) ->
          simplify_atom (Atom.mk_psym_app psym [ t1; T_int.mk_neg t2 ])
      | ( Predicate.Psym (T_int.(Lt | Leq) as op),
          [ Term.FunApp (T_int.Abs, [ t1 ], _); t2 ] ) ->
          abs_bounds_nf ~atom_first:false
            (simplify_atom @@ Atom.mk_psym_app op [ T_int.mk_neg t2; t1 ])
            (Predicate.Psym op) [ t1; t2 ] info
      | ( Predicate.Psym (T_int.(Gt | Geq) as op),
          [ t1; Term.FunApp (T_int.Abs, [ t2 ], _) ] ) ->
          abs_bounds_nf ~atom_first:true
            (simplify_atom @@ Atom.mk_psym_app op [ t2; T_int.mk_neg t1 ])
            (Predicate.Psym op) [ t1; t2 ] info
      | ( Predicate.Psym (T_bool.(Eq | Neq) as psym),
          [
            Term.FunApp (T_real.RNeg, [ t1 ], _);
            t2 (* | [ t2; Term.FunApp (T_real.RNeg, [ t1 ], _) ] *);
          ] ) ->
          simplify_atom (Atom.mk_psym_app psym [ t1; T_real.mk_rneg t2 ])
      | ( Predicate.Psym (T_real.(RLt | RLeq) as op),
          [ Term.FunApp (T_real.RAbs, [ t1 ], _); t2 ] ) ->
          abs_bounds_nf ~atom_first:false
            (simplify_atom @@ Atom.mk_psym_app op [ T_real.mk_rneg t2; t1 ])
            (Predicate.Psym op) [ t1; t2 ] info
      | ( Predicate.Psym (T_real.(RGt | RGeq) as op),
          [ t1; Term.FunApp (T_real.RAbs, [ t2 ], _) ] ) ->
          abs_bounds_nf ~atom_first:true
            (simplify_atom @@ Atom.mk_psym_app op [ t2; T_real.mk_rneg t1 ])
            (Predicate.Psym op) [ t1; t2 ] info
      | ( Predicate.Psym T_bool.Eq,
          [
            Term.FunApp (T_array.AConst _, [ t1 ], _);
            Term.FunApp (T_array.AConst _, [ t2 ], _);
          ] ) ->
          simplify @@ Formula.eq t1 t2
      | ( Predicate.Psym T_bool.Eq,
          ( [
              (Term.FunApp (T_array.AConst _, [ t1 ], _) as t);
              Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
            ]
          | [
              Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
              (Term.FunApp (T_array.AConst _, [ t1 ], _) as t);
            ] ) )
        when non_stored_roomy t21 t22 ->
          simplify @@ Formula.mk_and (Formula.eq t1 t23) (Formula.eq t t21)
      | ( Predicate.Psym T_bool.Eq,
          [
            Term.FunApp (T_array.AStore _, [ t11; t12; t13 ], _);
            Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
          ] )
        when non_stored_roomy t11 t12 && non_stored_roomy t21 t22
             && Stdlib.(t12 = t22) ->
          simplify @@ Formula.mk_and (Formula.eq t11 t21) (Formula.eq t13 t23)
      | ( Predicate.Psym T_bool.Eq,
          [ (Term.FunApp (T_array.AStore _, [ t11; t12; t13 ], _) as t1); t2 ] )
        when non_stored_roomy t11 t12 && non_stored_roomy t2 t12 -> (
          match T_array.eval_select t2 t12 with
          | Some te ->
              simplify @@ Formula.mk_and (Formula.eq t13 te) (Formula.eq t11 t2)
          | None -> Formula.eq t1 t2)
      | ( Predicate.Psym T_bool.Eq,
          [ t1; (Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _) as t2) ] )
        when non_stored_roomy t21 t22 && non_stored_roomy t1 t22 -> (
          match T_array.eval_select t1 t22 with
          | Some te ->
              simplify @@ Formula.mk_and (Formula.eq te t23) (Formula.eq t1 t21)
          | None -> Formula.eq t1 t2)
      | ( Predicate.Psym T_bool.Neq,
          [
            Term.FunApp (T_array.AConst _, [ t1 ], _);
            Term.FunApp (T_array.AConst _, [ t2 ], _);
          ] ) ->
          simplify @@ Formula.neq t1 t2
      | ( Predicate.Psym T_bool.Neq,
          ( [
              (Term.FunApp (T_array.AConst _, [ t1 ], _) as t);
              Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
            ]
          | [
              Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
              (Term.FunApp (T_array.AConst _, [ t1 ], _) as t);
            ] ) )
        when non_stored_roomy t21 t22 ->
          simplify @@ Formula.mk_or (Formula.neq t1 t23) (Formula.neq t t21)
      | ( Predicate.Psym T_bool.Neq,
          [
            Term.FunApp (T_array.AStore _, [ t11; t12; t13 ], _);
            Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _);
          ] )
        when non_stored_roomy t11 t12 && non_stored_roomy t21 t22
             && Stdlib.(t12 = t22) ->
          simplify @@ Formula.mk_or (Formula.neq t11 t21) (Formula.neq t13 t23)
      | ( Predicate.Psym T_bool.Neq,
          [ (Term.FunApp (T_array.AStore _, [ t11; t12; t13 ], _) as t1); t2 ] )
        when non_stored_roomy t11 t12 && non_stored_roomy t2 t12 -> (
          match T_array.eval_select t2 t12 with
          | Some te ->
              simplify
              @@ Formula.mk_or (Formula.neq t13 te) (Formula.neq t11 t2)
          | None -> Formula.neq t1 t2)
      | ( Predicate.Psym T_bool.Neq,
          [ t1; (Term.FunApp (T_array.AStore _, [ t21; t22; t23 ], _) as t2) ] )
        when non_stored_roomy t21 t22 && non_stored_roomy t1 t22 -> (
          match T_array.eval_select t1 t22 with
          | Some te ->
              simplify
              @@ Formula.mk_or (Formula.neq te t23) (Formula.neq t1 t21)
          | None -> Formula.neq t1 t2)
      | ( Predicate.Psym (T_tuple.IsTuple _),
          [ Term.FunApp (T_tuple.TupleCons _, _, _) ] ) ->
          Formula.mk_true ()
      | ( Predicate.Psym (T_tuple.NotIsTuple _),
          [ Term.FunApp (T_tuple.TupleCons _, _, _) ] ) ->
          Formula.mk_false ()
      | ( Predicate.Psym T_bool.Eq,
          [
            Term.FunApp (T_tuple.TupleCons _, ts1, _);
            Term.FunApp (T_tuple.TupleCons _, ts2, _);
          ] ) ->
          simplify @@ Formula.and_of @@ List.map2_exn ts1 ts2 ~f:Formula.eq
      | ( Predicate.Psym T_bool.Eq,
          [ Term.FunApp (T_tuple.TupleCons sorts, ts, _); t ] )
      | ( Predicate.Psym T_bool.Eq,
          [ t; Term.FunApp (T_tuple.TupleCons sorts, ts, _) ] ) ->
          simplify @@ Formula.and_of
          @@ List.mapi ts ~f:(fun i ti ->
              Formula.eq ti @@ T_tuple.mk_tuple_sel sorts t i)
      | ( Predicate.Psym T_bool.Neq,
          [
            Term.FunApp (T_tuple.TupleCons _, ts1, _);
            Term.FunApp (T_tuple.TupleCons _, ts2, _);
          ] ) ->
          simplify @@ Formula.or_of @@ List.map2_exn ts1 ts2 ~f:Formula.neq
      | ( Predicate.Psym T_bool.Neq,
          [ Term.FunApp (T_tuple.TupleCons sorts, ts, _); t ] )
      | ( Predicate.Psym T_bool.Neq,
          [ t; Term.FunApp (T_tuple.TupleCons sorts, ts, _) ] ) ->
          simplify @@ Formula.or_of
          @@ List.mapi ts ~f:(fun i ti ->
              Formula.neq ti @@ T_tuple.mk_tuple_sel sorts t i)
      | ( Predicate.Psym (T_dt.IsCons (name, _)),
          [ Term.FunApp (T_dt.DTCons (name1, _, _), _, _) ] ) ->
          Formula.mk_bool @@ String.(name1 = name)
      | Predicate.Psym (T_dt.IsCons (name, dt)), [ t ]
        when Datatype.is_base dt name ->
          if Atomic.get simplify_normal_forms then
            simplify_atom_app (Predicate.Psym T_bool.Eq)
              [ t; simplify_term (T_dt.mk_cons dt name []) ]
              info
          else Formula.eq t (T_dt.mk_cons dt name [])
      | ( Predicate.Psym (T_dt.NotIsCons (name, _)),
          [ Term.FunApp (T_dt.DTCons (name1, _, _), _, _) ] ) ->
          Formula.mk_bool @@ String.(name1 <> name)
      | Predicate.Psym (T_dt.NotIsCons (name, dt)), [ t ]
        when Datatype.is_base dt name ->
          if Atomic.get simplify_normal_forms then
            simplify_atom_app (Predicate.Psym T_bool.Neq)
              [ t; simplify_term (T_dt.mk_cons dt name []) ]
              info
          else Formula.neq t (T_dt.mk_cons dt name [])
      | ( Predicate.Psym T_bool.Eq,
          [
            Term.FunApp (T_dt.DTCons (name1, _, _), ts1, _);
            Term.FunApp (T_dt.DTCons (name2, _, _), ts2, _);
          ] ) ->
          if String.(name1 <> name2) then Formula.mk_false ()
          else simplify @@ Formula.and_of @@ List.map2_exn ts1 ts2 ~f:Formula.eq
      | ( Predicate.Psym T_bool.Neq,
          [
            Term.FunApp (T_dt.DTCons (name1, _, _), ts1, _);
            Term.FunApp (T_dt.DTCons (name2, _, _), ts2, _);
          ] ) ->
          if String.(name1 <> name2) then Formula.mk_true ()
          else simplify @@ Formula.or_of @@ List.map2_exn ts1 ts2 ~f:Formula.neq
      | pred', ts' -> (
          try Formula.mk_bool @@ eval_atom (Atom.mk_app ~info pred' ts')
          with exn_ when not (Common.Timer.is_async exn_) -> Formula.mk_atom (Atom.mk_app ~info pred' ts'))

(* The two bounds an absolute value splits a comparison into: [phi], already
   simplified, and the atom [pred ts] over simplified arguments.  Off, their
   conjunction as built, the atom first exactly when [atom_first]; with
   [simplify_normal_forms] on, the atom simplified and the conjunction grouped
   as a conjunction is on the next pass.  Equal in every model either way. *)
and abs_bounds_nf ~atom_first phi pred ts info =
  if Atomic.get simplify_normal_forms then
    simplify_and
    @@ Set.union (Formula.conjuncts_of phi)
         (Formula.conjuncts_of (simplify_atom_app pred ts info))
  else
    let atom = Formula.mk_atom @@ Atom.mk_app pred ts in
    if atom_first then Formula.mk_and atom phi else Formula.mk_and phi atom

(* [simplify_term t] for a term [t] a lift has just built around [parts], each
   an output of [simplify_term].  With [simplify_skip_simplified] off this is
   [simplify_term t] itself; with it on, the parts are taken as they are and
   only the nodes around them are simplified. *)
and resimplify ~parts t =
  if Atomic.get simplify_skip_simplified then simplify_known ~parts t
  else (
    if Atomic.get skip_simplified_probe then probe_parts parts;
    simplify_term t)

(* re-simplify every part and record those that do not come back equal; a
   probe's own lifts are not probed again *)
and probe_parts parts =
  let flag = Stdlib.Domain.DLS.get probing in
  if not !flag then (
    flag := true;
    Exn.protect
      ~finally:(fun () -> flag := false)
      ~f:(fun () ->
        List.iter parts ~f:(fun p ->
            Atomic.incr probe_parts_checked;
            let p' = simplify_term p in
            if not (Stdlib.( = ) p p') then (
              Atomic.incr probe_parts_changed;
              if List.length !probe_examples < probe_max_examples then
                probe_examples := (p, p') :: !probe_examples))))

(* [simplify_term t] computed as if every member of [parts] (compared by
   physical identity) were mapped to itself: the nodes of [t] above the parts go
   through the same rules [simplify_term] applies, in the same order, and
   anything this does not recognise is simplified as usual.  So the result is
   [simplify_term t] whenever [simplify_term p = p] for each part [p]. *)
and simplify_known ~parts t =
  if List.exists parts ~f:(fun p -> phys_equal p t) then t
  else
    match t with
    | Term.FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], info) ->
        let t1' = simplify_known ~parts t1 in
        let t2' = simplify_known ~parts t2 in
        let t3' = simplify_known ~parts t3 in
        simplify_ite_parts t1' t2' t3' info
    | FunApp (T_int.Case n, t1 :: branches, info) ->
        let t1' = simplify_known ~parts t1 in
        simplify_case_parts n t1'
          (List.map ~f:(simplify_known ~parts) branches)
          info
    | FunApp ((T_bool.Formula _ as fsym), [], info) ->
        simplify_app ~known:parts fsym [] info
    | FunApp (fsym, ts, info) ->
        simplify_app fsym (List.map ~f:(simplify_known ~parts) ts) info
    | Var _ | LetTerm _ -> simplify_term t

(* [simplify phi] for an embedded formula built around [parts], as
   [simplify_known] does for a term: an atom's arguments are taken through
   [simplify_known], every other formula is simplified as usual *)
and simplify_formula_known ~parts = function
  | Formula.Atom (Atom.App (pred, terms, info), _) ->
      simplify_atom_app (simplify_pred pred)
        (List.map ~f:(simplify_known ~parts) terms)
        info
  | phi -> simplify phi

(*val simplify_atom_neg: Atom.t -> Formula.t*)
and simplify_atom_neg = function
  | Atom.True _ -> Formula.mk_false ()
  | False _ -> Formula.mk_true ()
  | App (Predicate.Var (pvar, sorts), args, _info) ->
      Formula.mk_neg @@ Formula.mk_atom
      @@ Atom.mk_pvar_app pvar sorts
      @@ List.map ~f:simplify_term args
  | App (pred, args, info) as atom -> (
      match simplify_pred_neg pred with
      | None -> Formula.mk_neg @@ Formula.mk_atom atom
      | Some neg_pred ->
          simplify_atom @@ Atom.mk_app ~info neg_pred
          @@ List.map ~f:simplify_term args)

and and_psym psym1 psym2 =
  (* simplification rules for background theories *)
  if Predicate.is_included_psym psym1 psym2 then Some (Set.Poly.singleton psym1)
  else if Predicate.is_included_psym psym2 psym1 then
    Some (Set.Poly.singleton psym2)
  else if Predicate.is_included_psym psym1 (Predicate.negate_psym psym2) then
    (* <> =
       = <>
       = <
       = >
       < =
       < >
       < >=
       > =
       > <
       > <=
       <= >
       >= < *)
    None
  else
    match (psym1, psym2) with
    | T_bool.Neq, T_int.Leq | T_int.Leq, T_bool.Neq ->
        (* <> <=
           <= <> *)
        Some (Set.Poly.singleton T_int.Lt)
    | T_bool.Neq, T_real.RLeq | T_real.RLeq, T_bool.Neq ->
        (* <> <=
           <= <> *)
        Some (Set.Poly.singleton T_real.RLt)
    | T_bool.Neq, T_int.Geq | T_int.Geq, T_bool.Neq ->
        (* <> >=
           >= <> *)
        Some (Set.Poly.singleton T_int.Gt)
    | T_bool.Neq, T_real.RGeq | T_real.RGeq, T_bool.Neq ->
        (* <> >=
           >= <> *)
        Some (Set.Poly.singleton T_real.RGt)
    | T_int.Leq, T_int.Geq
    | T_int.Geq, T_int.Leq
    | T_real.RLeq, T_real.RGeq
    | T_real.RGeq, T_real.RLeq ->
        (* <= >=
           >= <= *)
        Some (Set.Poly.singleton T_bool.Eq)
    | _ ->
        (*not reachable*)
        Some (Set.Poly.of_list [ psym1; psym2 ])

and and_psym_list psyms =
  match Set.choose psyms with
  | None -> Some Set.Poly.empty
  | Some elem ->
      Set.fold
        ~init:(Some (Set.Poly.singleton elem))
        (Set.remove psyms elem)
        ~f:(fun acc psym ->
          match acc with
          | None -> None
          | Some psyms ->
              Set.fold ~init:(Some Set.Poly.empty) psyms ~f:(fun acc psym' ->
                  match (acc, and_psym psym psym') with
                  | None, _ | _, None -> None
                  | Some psyms, Some psyms' -> Some (Set.union psyms psyms')))

(* Whether the grouping of a conjunction or disjunction turns the comparison
   [t1 psym t2] around, to compare it with the others over the same pair of
   terms.  With [simplify_normal_forms] on, an (dis)equation is kept as it is
   when its right side is a negation: the atom rules move a negation from the
   left side to the right ([-a = b] to [a = -b]), so turning such an atom
   around would be undone by the next pass, and the grouping of that pass
   would turn it around again. *)
and flip_for_grouping psym t1 t2 =
  Stdlib.(t1 > t2)
  && Predicate.is_flippable_psym psym
  && not
       (Atomic.get simplify_normal_forms
       && Stdlib.(psym = T_bool.Eq || psym = T_bool.Neq)
       &&
       match t2 with
       | Term.FunApp ((T_int.Neg | T_real.RNeg), [ _ ], _) -> true
       | _ -> false)

(* [phi], the formula a lifted conditional comparison becomes ([t = true],
   how a Boolean term becomes a formula), turned around as the grouping of a
   conjunction or disjunction would turn it ([flip_for_grouping]), when
   [simplify_normal_forms] is on.  Without this, such an atom left alone (not
   grouped in this pass) comes out as [t = true], and grouped on the next
   pass as [true = t], which the atom rules turn back on the pass after.  The
   same equation read the other way round. *)
and orient_nf phi =
  if not (Atomic.get simplify_normal_forms) then phi
  else
    match phi with
    | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], info), _)
      when Predicate.is_negatable_psym psym && flip_for_grouping psym t1 t2 ->
        Formula.mk_atom
          (Atom.mk_app ~info (Predicate.Psym (Predicate.flip_psym psym)) [ t2; t1 ])
    | _ -> phi

and simplify_and phis =
  if not simplify_theory_atoms then Formula.and_of @@ Set.to_list phis
  else if Set.exists phis ~f:Formula.is_false then Formula.mk_false ()
  else
    let map, rest =
      Set.fold phis ~init:(Map.Poly.empty, []) ~f:(fun (map, rest) -> function
        | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _)
          when Predicate.is_negatable_psym psym ->
            (* ToDo: 0 <= -x /\ x >= 0 cannot be simplified *)
            if flip_for_grouping psym t1 t2 then
              ( Map.Poly.update map (t2, t1) ~f:(function
                  | None -> Set.Poly.singleton (Predicate.flip_psym psym)
                  | Some psyms -> Set.add psyms (Predicate.flip_psym psym)),
                rest )
            else
              ( Map.Poly.update map (t1, t2) ~f:(function
                  | None -> Set.Poly.singleton psym
                  | Some psyms -> Set.add psyms psym),
                rest )
        | phi -> (map, phi :: rest))
    in
    Formula.and_of
    @@ Map.Poly.fold map ~init:rest ~f:(fun ~key:(t1, t2) ~data:psyms acc ->
        if false && Set.length psyms = 1 then
          (Formula.mk_atom @@ Atom.mk_psym_app (Set.choose_exn psyms) [ t1; t2 ])
          :: acc
        else
          match and_psym_list psyms with
          | None -> Formula.mk_false () :: acc
          | Some psyms ->
              Set.fold ~init:acc psyms ~f:(fun acc psym ->
                  (Formula.mk_atom @@ Atom.mk_psym_app psym [ t1; t2 ]) :: acc))

and or_psym psym1 psym2 =
  (* simplification rules for background theories *)
  if Predicate.is_included_psym psym1 psym2 then Some (Set.Poly.singleton psym2)
  else if Predicate.is_included_psym psym2 psym1 then
    Some (Set.Poly.singleton psym1)
  else if Predicate.is_included_psym (Predicate.negate_psym psym1) psym2 then
    (* = <>
       <> =
       <> <=
       <> >=
       < >=
       <= >
       <= >=
       > <=
       >= <
       >= <= *)
    None
  else
    match (psym1, psym2) with
    | T_bool.Eq, T_int.Lt | T_int.Lt, T_bool.Eq ->
        (* = <
           < = *)
        Some (Set.Poly.singleton T_int.Leq)
    | T_bool.Eq, T_real.RLt | T_real.RLt, T_bool.Eq ->
        (* = <
           < = *)
        Some (Set.Poly.singleton T_real.RLeq)
    | T_bool.Eq, T_int.Gt | T_int.Gt, T_bool.Eq ->
        (* = >
           > = *)
        Some (Set.Poly.singleton T_int.Geq)
    | T_bool.Eq, T_real.RGt | T_real.RGt, T_bool.Eq ->
        (* = >
           > = *)
        Some (Set.Poly.singleton T_real.RGeq)
    | T_int.Lt, T_int.Gt
    | T_int.Gt, T_int.Lt
    | T_real.RLt, T_real.RGt
    | T_real.RGt, T_real.RLt ->
        (* < >
           > < *)
        Some (Set.Poly.singleton T_bool.Neq)
    | _ ->
        (*not reachable*)
        Some (Set.Poly.of_list [ psym1; psym2 ])

and or_psym_list psyms =
  match Set.choose psyms with
  | None -> Some Set.Poly.empty
  | Some elem ->
      Set.fold
        ~init:(Some (Set.Poly.singleton elem))
        (Set.remove psyms elem)
        ~f:(fun acc psym ->
          match acc with
          | None -> None
          | Some psyms ->
              Set.fold ~init:(Some Set.Poly.empty) psyms ~f:(fun acc psym' ->
                  match (acc, or_psym psym psym') with
                  | None, _ | _, None -> None
                  | Some psyms, Some psyms' -> Some (Set.union psyms psyms')))

and simplify_or phis =
  if not simplify_theory_atoms then Formula.or_of @@ Set.to_list phis
  else if Set.exists phis ~f:Formula.is_true then Formula.mk_true ()
  else
    let map, rest =
      Set.fold phis ~init:(Map.Poly.empty, []) ~f:(fun (map, rest) -> function
        | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _)
          when Predicate.is_negatable_psym psym ->
            (* ToDo: 0 <= -x \/ x >= 0 cannot be simplified *)
            if flip_for_grouping psym t1 t2 then
              ( Map.Poly.update map (t2, t1) ~f:(function
                  | None -> Set.Poly.singleton (Predicate.flip_psym psym)
                  | Some psyms -> Set.add psyms (Predicate.flip_psym psym)),
                rest )
            else
              ( Map.Poly.update map (t1, t2) ~f:(function
                  | None -> Set.Poly.singleton psym
                  | Some psyms -> Set.add psyms psym),
                rest )
        | phi -> (map, phi :: rest))
    in
    Formula.or_of
    @@ Map.Poly.fold map ~init:rest ~f:(fun ~key:(t1, t2) ~data:psyms acc ->
        if false && Set.length psyms = 1 then
          (Formula.mk_atom @@ Atom.mk_psym_app (Set.choose_exn psyms) [ t1; t2 ])
          :: acc
        else
          match or_psym_list psyms with
          | None -> Formula.mk_true () :: acc
          | Some psyms ->
              Set.fold ~init:acc psyms ~f:(fun acc psym ->
                  (Formula.mk_atom @@ Atom.mk_psym_app psym [ t1; t2 ]) :: acc))

(* [phi1 <=> phi2] and [phi1 xor phi2] over simplified operands; with
   [simplify_normal_forms] on, two Boolean constants are folded to the
   constant they denote, which the evaluator would do when the formula is
   simplified again (as part of an embedding term).  Equal in every model to
   the unfolded form. *)
and iff_nf ~info phi1 phi2 =
  match bool_const_of phi1, bool_const_of phi2 with
  | Some b1, Some b2 when Atomic.get simplify_normal_forms ->
      Formula.mk_bool (Bool.equal b1 b2)
  | _ -> Formula.mk_iff phi1 phi2 ~info

and xor_nf ~info phi1 phi2 =
  match bool_const_of phi1, bool_const_of phi2 with
  | Some b1, Some b2 when Atomic.get simplify_normal_forms ->
      Formula.mk_bool (not (Bool.equal b1 b2))
  | _ -> Formula.mk_xor phi1 phi2 ~info

and bool_const_of phi =
  if Formula.is_true phi then Some true
  else if Formula.is_false phi then Some false
  else None

(*val simplify: Formula.t -> Formula.t*)
(* [simplify] and [simplify_neg] with the memo of [with_shared_simplify]: a
   node met again, physically the same, gets the result computed the first
   time, provided that computation drew no fresh name.  [simplify ~next phi]
   is [next (simplify phi)] (the continuation only keeps the recursion off the
   stack), so the continuation passed to [simplify_node] is called exactly
   once, right after [phi]'s own result is known, and the stamps compared
   there bracket [phi]'s computation and nothing else. *)
and simplify ?(next = Fn.id) phi =
  match Stdlib.Domain.DLS.get simplify_scope with
  | None -> simplify_node phi ~next
  | Some tbls -> (
      match PhysFml.find_opt tbls.pos phi with
      | Some r -> next r
      | None ->
          let stamp = Ident.fresh_stamp () in
          simplify_node phi ~next:(fun r ->
              if Ident.fresh_stamp () = stamp then PhysFml.replace tbls.pos phi r;
              next r))

and simplify_node ~next = function
  | Formula.Atom (atom, _) -> next @@ simplify_atom atom
  | UnaryOp (Not, phi, _) -> simplify_neg phi ~next
  | BinaryOp (Imply, phi1, phi2, info) ->
      simplify
        (Formula.mk_binop ~info Or (Formula.mk_unop ~info:Dummy Not phi1) phi2)
        ~next
  | BinaryOp (Iff, phi1, phi2, info) ->
      (*simplify (BinaryOp (And, BinaryOp (Imply, phi1, phi2, Dummy), BinaryOp (Imply, phi2, phi1, Dummy), info)) ~next*)
      simplify phi1 ~next:(fun phi1' ->
          simplify phi2 ~next:(fun phi2' ->
              next @@ iff_nf ~info phi1' phi2'))
  | BinaryOp (Xor, phi1, phi2, info) ->
      simplify phi1 ~next:(fun phi1' ->
          simplify phi2 ~next:(fun phi2' ->
              next @@ xor_nf ~info phi1' phi2'))
  | BinaryOp (And, _, _, _) as phi ->
      (* Group the whole conjunction chain once.  Recursing pairwise rebuilds
         the conjunction at each level and hands the *whole* accumulated set
         back to [simplify_and], which groups its atoms by the pair of terms
         they compare -- so a chain of n conjuncts is grouped n times and the
         cost is quadratic in the chain's length.  [conjuncts_list_of] keeps
         the left-to-right order in which the pairwise recursion reached the
         leaves, and that order is observable: simplifying an atom can
         allocate a fresh variable. *)
      simplify_conj_chain (conj_leaves [] phi) [] ~next
  | BinaryOp (Or, _, _, _) as phi ->
      simplify_disj_chain (disj_leaves [] phi) [] ~next
  | Bind (binder, bounds, phi, info) ->
      simplify phi ~next:(function
        | Bind (binder', bounds', phi'', _) when Stdlib.(binder' = binder) ->
            next @@ Formula.mk_bind ~info binder (bounds' @ bounds) phi''
        | phi' -> next @@ Formula.mk_bind ~info binder bounds phi')
  | LetRec (funcs, phi, info) ->
      if true then assert false
      else
        simplify phi ~next:(fun phi' ->
            next
            @@ Formula.mk_letrec ~info
                 (Formula.map_funcs ~f:(*ToDo*) simplify funcs)
                 phi')
  | LetFormula (var, sort, def, body, info) ->
      let def' = simplify_term def in
      simplify body ~next:(fun body' ->
          let size = let_def_size def' in
          let count = Formula.occur_times var body' in
          if inline_let ~size ~count then
            simplify (Formula.apply_pred (var, body') def') ~next
          else next @@ Formula.mk_let_formula ~info var sort def' body')

and conj_leaves acc = function
  | Formula.BinaryOp (And, phi1, phi2, _) ->
      conj_leaves (conj_leaves acc phi2) phi1
  | phi -> phi :: acc

and disj_leaves acc = function
  | Formula.BinaryOp (Or, phi1, phi2, _) ->
      disj_leaves (disj_leaves acc phi2) phi1
  | phi -> phi :: acc

and simplify_conj_chain phis acc ~next =
  match phis with
  | [] -> next @@ simplify_and @@ Set.Poly.union_list acc
  | phi :: rest ->
      simplify phi ~next:(fun phi' ->
          simplify_conj_chain rest (Formula.conjuncts_of phi' :: acc) ~next)

and simplify_disj_chain phis acc ~next =
  match phis with
  | [] -> next @@ simplify_or @@ Set.Poly.union_list acc
  | phi :: rest ->
      simplify phi ~next:(fun phi' ->
          simplify_disj_chain rest (Formula.disjuncts_of phi' :: acc) ~next)

(* [simplify_with_leaf_cache ~lookup phi] is [simplify phi], with the
   simplified disjuncts of a leaf of [phi]'s top [Or] chain taken from
   [lookup leaf] when that gives them.  Contract: [lookup l], when [Some d],
   is [disjuncts_of (simplify l)] for that very [l]; then the result is the
   one [simplify] gives, since [simplify] of an [Or] chain is [simplify_or]
   of the union of its leaves' simplified disjuncts, a set, whose order of
   construction does not enter -- except that a fresh variable [simplify]
   allocates for a leaf is not allocated again for a cached one, so bound
   names can differ.  For many questions that share most of their leaves. *)
and simplify_with_leaf_cache ~lookup phi =
  match phi with
  | Formula.BinaryOp (Or, _, _, _) ->
      simplify_or @@ Set.Poly.union_list
      @@ List.map (disj_leaves [] phi) ~f:(fun leaf ->
             match lookup leaf with
             | Some d -> d
             | None -> Formula.disjuncts_of (simplify leaf))
  | _ -> simplify phi

and simplify_neg_conj_chain phis acc ~next =
  match phis with
  | [] -> next @@ simplify_or @@ Set.Poly.union_list acc
  | phi :: rest ->
      simplify_neg phi ~next:(fun phi' ->
          simplify_neg_conj_chain rest (Formula.disjuncts_of phi' :: acc) ~next)

and simplify_neg_disj_chain phis acc ~next =
  match phis with
  | [] -> next @@ simplify_and @@ Set.Poly.union_list acc
  | phi :: rest ->
      simplify_neg phi ~next:(fun phi' ->
          simplify_neg_disj_chain rest (Formula.conjuncts_of phi' :: acc) ~next)

(*val simplify_neg: Formula.t -> Formula.t*)
and simplify_neg ?(next = Fn.id) phi =
  match Stdlib.Domain.DLS.get simplify_scope with
  | None -> simplify_neg_node phi ~next
  | Some tbls -> (
      match PhysFml.find_opt tbls.neg phi with
      | Some r -> next r
      | None ->
          let stamp = Ident.fresh_stamp () in
          simplify_neg_node phi ~next:(fun r ->
              if Ident.fresh_stamp () = stamp then PhysFml.replace tbls.neg phi r;
              next r))

and simplify_neg_node ~next = function
  | Formula.Atom (atom, _) -> next @@ simplify_atom_neg atom
  | UnaryOp (Not, phi, _) -> simplify phi ~next
  | BinaryOp (Imply, phi1, phi2, info) ->
      simplify_neg
        (Formula.mk_binop ~info Or (Formula.mk_unop ~info:Dummy Not phi1) phi2)
        ~next
  | BinaryOp (Iff, phi1, phi2, info) ->
      (*simplify_neg (BinaryOp (And, BinaryOp (Imply, phi1, phi2, Dummy), BinaryOp (Imply, phi2, phi1, Dummy), info)) ~next*)
      simplify phi1 ~next:(fun phi1' ->
          simplify phi2 ~next:(fun phi2' ->
              next @@ xor_nf ~info phi1' phi2'))
  | BinaryOp (Xor, phi1, phi2, info) ->
      simplify phi1 ~next:(fun phi1' ->
          simplify phi2 ~next:(fun phi2' ->
              next @@ iff_nf ~info phi1' phi2'))
  | BinaryOp (And, _, _, _) as phi ->
      (* the negation of a conjunction chain is a disjunction of the negated
         leaves; grouped once, for the reason given above *)
      simplify_neg_conj_chain (conj_leaves [] phi) [] ~next
  | BinaryOp (Or, _, _, _) as phi ->
      simplify_neg_disj_chain (disj_leaves [] phi) [] ~next
  | Bind (binder, bounds, phi, info) ->
      simplify
        (Formula.mk_bind ~info
           (Formula.flip_quantifier binder)
           bounds (Formula.mk_neg phi))
        ~next
  | LetRec (funcs, phi, info) ->
      if true then assert false (* ToDo: check *)
      else
        let f =
          let pvars =
            Set.Poly.of_list (List.map funcs ~f:(fun def -> def.name))
          in
          fun phi -> Formula.subst_negs pvars phi
        in
        simplify_neg phi ~next:(fun phi' ->
            next
            @@ Formula.mk_letrec ~info
                 (List.map funcs ~f:(fun def ->
                      {
                        def with
                        kind = Predicate.flip_fop def.kind;
                        body = simplify_neg @@ f def.body;
                      }))
                 (f phi'))
  | LetFormula (var, sort, def, body, info) ->
      let def' = simplify_term def in
      simplify_neg body ~next:(fun body' ->
          let size = let_def_size def' in
          let count = Formula.occur_times var body' in
          if inline_let ~size ~count then
            simplify (Formula.apply_pred (var, body') def') ~next
          else next @@ Formula.mk_let_formula ~info var sort def' body')

and simplify_keep_imply phi =
  Formula.fold phi
    ~f:
      (object
         method fatom atom = simplify_atom atom

         method fand p1 p2 =
           simplify_and
             (Set.union (Formula.conjuncts_of p1) (Formula.conjuncts_of p2))

         method for_ p1 p2 =
           simplify_or
             (Set.union (Formula.disjuncts_of p1) (Formula.disjuncts_of p2))

         method fnot p1 = simplify_neg_keep_imply p1
         method fbind binder senv p1 = Formula.mk_bind binder senv p1
         method fletrec funcs p1 = Formula.mk_letrec funcs p1

         method fimply p1 p2 =
           if Formula.is_imply p2 then
             let p21, p22, _ = Formula.let_imply p2 in
             let lhs = simplify_and (Set.Poly.of_list [ p1; p21 ]) in
             if Formula.is_false lhs || Formula.is_true p22 then
               Formula.mk_true ()
             else if Formula.is_true lhs then p22
             else Formula.mk_imply lhs p22
           else if Formula.is_false p1 || Formula.is_true p2 then
             Formula.mk_true ()
           else if Formula.is_true p1 then p2
           else Formula.mk_imply p1 p2

         method fiff p1 p2 = Formula.mk_iff p1 p2
         method fxor p1 p2 = Formula.mk_xor p1 p2

         method flet var sort def body =
           Formula.mk_let_formula var sort def body
      end)

and simplify_neg_keep_imply phi =
  (*ToDo*)
  Formula.fold phi
    ~f:
      (object
         method fatom atom = simplify_atom_neg atom

         method fand p1 p2 =
           simplify_or
             (Set.union (Formula.disjuncts_of p1) (Formula.disjuncts_of p2))

         method for_ p1 p2 =
           simplify_and
             (Set.union (Formula.conjuncts_of p1) (Formula.conjuncts_of p2))

         method fnot p1 = p1

         method fbind binder senv p1 =
           Formula.mk_bind (Formula.flip_quantifier binder) senv p1

         method fletrec funcs p1 = Formula.mk_letrec funcs p1

         method fimply p1 p2 =
           simplify_and
             (Set.union
                (Formula.conjuncts_of (simplify_neg_keep_imply p1))
                (Formula.conjuncts_of p2))

         method fiff p1 p2 = Formula.mk_xor p1 p2
         method fxor p1 p2 = Formula.mk_iff p1 p2

         method flet var sort def body =
           Formula.mk_let_formula var sort def body
      end)


let () = simplify_hook := fun phi -> simplify phi

let is_sat is_sat phi =
  try eval phi
  with exn_ when not (Common.Timer.is_async exn_) ->
    (* reachable here if phi may cause division by 0 *) is_sat phi

(* a process-global cache read and written from every solver domain; a
   [Hashtbl] is not safe under concurrent [set], so every access takes the
   mutex.  The same convention as
   [Z3Smt.Z3interface]'s [mutex]. *)
let valid_check_records = Hashtbl.PolyDeep.create ()
let valid_check_mutex = Caml_threads.Mutex.create ()

let with_valid_check_records f =
  Caml_threads.Mutex.lock valid_check_mutex;
  match f valid_check_records with
  | ret ->
      Caml_threads.Mutex.unlock valid_check_mutex;
      ret
  | exception exn_ ->
      Caml_threads.Mutex.unlock valid_check_mutex;
      raise exn_

let clean () = with_valid_check_records Hashtbl.Poly.clear

let rec local_is_valid is_valid = function
  | Formula.Atom (atom, _) as phi -> (
      match is_valid_atom atom with Some ret -> ret | None -> is_valid phi)
  | Formula.UnaryOp (_, phi1, _) as phi -> (
      match simplify_neg phi1 with
      | Formula.UnaryOp (_, _, _) -> is_valid phi
      | phi_neg -> local_is_valid is_valid phi_neg)
  | Formula.BinaryOp (Formula.And, phi1, phi2, _) ->
      local_is_valid is_valid phi1 && local_is_valid is_valid phi2
  | Formula.Bind (Formula.Forall, _, phi, _) -> local_is_valid is_valid phi
  | phi -> is_valid phi

(* cons x y = tl z*)
and is_valid_atom (*ToDo: check if this is correct*) = function
  | Atom.True _ -> Some true
  | Atom.False _ -> Some false
  | Atom.App
      (Predicate.Psym (T_int.(Gt | Lt) | T_real.(RGt | RLt)), [ t1; t2 ], _) ->
      if Stdlib.(t1 = t2) then Some false
      else if Term.is_pathexp t1 then
        if Set.mem (Term.pathexps_of t2) t1 then Some false else None
      else if Term.is_pathexp t2 then
        if Set.mem (Term.pathexps_of t1) t2 then Some false else None
      else None
  | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) ->
      if Stdlib.(t1 = t2) then Some false
      else if Term.is_pathexp t1 then
        if Set.mem (Term.pathexps_of t2) t1 then Some false else None
      else if Term.is_pathexp t2 then
        if Set.mem (Term.pathexps_of t1) t2 then Some false else None
      else None
  | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) ->
      if Stdlib.(t1 = t2) then Some true
      else if Term.is_pathexp t1 then
        if Set.mem (Term.pathexps_of t2) t1 then Some false else None
      else if Term.is_pathexp t2 then
        if Set.mem (Term.pathexps_of t1) t2 then Some false else None
      else None
  | Atom.App (Predicate.Psym (T_dt.IsCons _), [ t1 ], _) ->
      if Term.is_pathexp t1 then Some false else None
  | _ -> None

(* [abstract_out_of_range_reads phi]: every read [seq.nth s k] of [phi] whose
   sequence [s] has a length its structure fixes ([seq_len_of]) and whose index
   is an integer literal outside it is replaced by a fresh variable of the
   element sort, one per distinct read; [phi] itself when the conditions below
   do not hold.

   Contract: the result is valid iff [phi] is (and satisfiable iff [phi] is).
   A read outside a sequence is the one term of the sequence theory the theory
   leaves open: SMT-LIB fixes nothing about it but that it is a function of the
   sequence and the index, so across models it takes every value of its sort.
   The rewrite is the reduction of that function to constants (Ackermann's), and
   it needs no functional-consistency premise exactly when no two of the
   replaced reads can denote the same point: the conditions are that
   - [phi] is quantifier-free, let-free and holds no array lambda, so no read
     is under a binder that could vary its arguments;
   - every [seq.nth] of [phi] is such a read, so no read with a symbolic
     argument can meet one of them at the same point, and none is nested in
     another's sequence;
   - two distinct reads have distinct indices: literal indices that differ are
     different points whatever the sequences are, and two syntactically equal
     reads get the same variable.
   Why: Z3 5.1.0 answers [len (nth (unit (unit d)) k) > k] for [k] in the
   tens at once, needs seconds at 100, and does not return in 30 s at 200 or
   above when no budget is given; a truth-table cell over a model's large
   integer asked exactly such a question without a budget and stopped a solve
   for minutes. With the read replaced the question is answered at once. *)
let abstract_out_of_range_reads_on = Atomic.make true

let abstract_out_of_range_reads phi =
  if not (Atomic.get abstract_out_of_range_reads_on) then phi
  else
    let has_nth = ref false in
    let has_lambda =
      Set.exists (Formula.funsyms_of phi) ~f:(function
        | T_seq.SqNth _ ->
            has_nth := true;
            false
        | T_array.ALambda _ -> true
        | _ -> false)
    in
    if
      (not !has_nth) || has_lambda
      || (not (Formula.is_quantifier_free phi))
      || not (Formula.is_let_free phi)
    then phi
    else
      let reads = ref [] in
      let ok = ref true in
      let mentions_nth t =
        Set.exists (Term.funsyms_of t) ~f:(function
          | T_seq.SqNth _ -> true
          | _ -> false)
      in
      let _ =
        Formula.map_term phi ~f:(fun t ->
            (match t with
            | Term.FunApp (T_seq.SqNth se, [ sq; Term.FunApp (T_int.Int k, [], _) ], _)
              -> (
                match seq_len_of sq with
                | Some n
                  when Z.(Compare.(k < zero) || Compare.(k >= n))
                       && not (mentions_nth sq) ->
                    if
                      not
                        (List.exists !reads ~f:(fun (t', _, _) ->
                             Stdlib.( = ) t t'))
                    then reads := (t, se, k) :: !reads
                | _ -> ok := false)
            | Term.FunApp (T_seq.SqNth _, _, _) -> ok := false
            | _ -> ());
            t)
      in
      let distinct_indices =
        let ks = List.map !reads ~f:(fun (_, _, k) -> k) in
        List.length (List.dedup_and_sort ks ~compare:Z.compare) = List.length ks
      in
      if (not !ok) || List.is_empty !reads || not distinct_indices then phi
      else
        let used = Set.Poly.map (Formula.tvs_of phi) ~f:Ident.name_of_tvar in
        let fresh i k =
          let rec go suffix =
            let name =
              sprintf "#oor%d_%s%s" i (Z.to_string k)
                (if suffix = 0 then "" else sprintf "_%d" suffix)
            in
            if Set.mem used name then go (suffix + 1) else Ident.Tvar name
          in
          go 0
        in
        let table =
          List.mapi (List.rev !reads) ~f:(fun i (t, se, k) ->
              (t, Term.mk_var (fresh i k) se))
        in
        Formula.map_term phi ~f:(fun t ->
            match List.find table ~f:(fun (t', _) -> Stdlib.( = ) t t') with
            | Some (_, v) -> v
            | None -> t)

(* [abstract_length_only_sequences phi]: a validity question equivalent to
   [phi] in which every free sequence variable that occurs only as the argument
   of [seq.len] is replaced by a fresh integer variable [n], with [0 <= n] as
   a premise; [phi] itself when it binds anything or nothing is replaced.

   Contract: the result is valid iff [phi] is.  Such a variable is observed
   only through its length, and the lengths of the sequences of a sort are
   exactly the non-negative integers (every sort is non-empty), so quantifying
   over the sequence and quantifying over a non-negative integer give the same
   truth value.  Why: Z3 5.1.0 does not decide [len s > 1000] for a free
   sequence [s] within 20 s (it is quick below 100), and a truth-table cell at
   a model's large integer asked exactly that without a budget, after the
   out-of-range read it held had been replaced by such a variable. *)
let abstract_length_only_sequences_on = Atomic.make true

let abstract_length_only_sequences phi =
  if
    (not (Atomic.get abstract_length_only_sequences_on))
    || (not (Formula.is_quantifier_free phi))
    || (not (Formula.is_let_free phi))
    || Set.exists (Formula.funsyms_of phi) ~f:(function
         | T_array.ALambda _ -> true
         | _ -> false)
  then phi
  else
    let seq_vars =
      Set.filter (Formula.term_sort_env_of phi) ~f:(fun (_, sort) ->
          match sort with T_seq.SSeq _ -> true | _ -> false)
    in
    if Set.is_empty seq_vars then phi
    else
      let used = Set.Poly.map (Formula.tvs_of phi) ~f:Ident.name_of_tvar in
      let name_of (Ident.Tvar x) =
        let rec go k =
          let n = if k = 0 then "#len_" ^ x else sprintf "#len_%s_%d" x k in
          if Set.mem used n then go (k + 1) else n
        in
        Ident.Tvar (go 0)
      in
      let len_var = Map.Poly.of_alist_reduce
          (Set.to_list seq_vars |> List.map ~f:(fun (x, _) -> (x, name_of x)))
          ~f:(fun a _ -> a)
      in
      let replace keep =
        Formula.map_term phi ~f:(function
          | Term.FunApp (T_seq.SqLen _, [ Term.Var (x, _, _) ], _)
            when Map.Poly.mem len_var x && not (Set.mem keep x) ->
              Term.mk_var (Map.Poly.find_exn len_var x) T_int.SInt
          | t -> t)
      in
      (* a variable still present after its lengths are replaced occurs
         elsewhere and is kept *)
      let keep =
        Set.inter (Formula.tvs_of (replace Set.Poly.empty))
          (Set.Poly.of_list (Map.Poly.keys len_var))
      in
      let replaced =
        List.filter (Map.Poly.keys len_var) ~f:(fun x -> not (Set.mem keep x))
      in
      if List.is_empty replaced then phi
      else
        Formula.mk_imply
          (Formula.and_of
             (List.map replaced ~f:(fun x ->
                  Formula.geq
                    (Term.mk_var (Map.Poly.find_exn len_var x) T_int.SInt)
                    (T_int.zero ()))))
          (replace keep)

(* [abstract_out_of_range_reads_guarded phi]: the rewrite of
   [abstract_out_of_range_reads] for a formula WITH binders, where the plain one
   declines.  Every read [seq.nth s k] whose sequence [s] has a length its
   structure fixes ([seq_len_of]), mentions no read and no variable bound
   anywhere in [phi], and whose index is an integer literal outside that length
   is replaced by a fresh variable [c] of the element sort; every OTHER read
   [seq.nth s' t] of the same element sort becomes
   [ite (s' = s /\ t = k) c (seq.nth s' t)] (the conjunct [s' = s] omitted when
   [s'] is [s], the guard omitted when [t] is another literal or [s'] has a
   different structural length); a [seq.len] of such an [ite] is distributed
   over its branches, and a fresh [c] of a sequence sort that then occurs only
   under [seq.len] is replaced by a fresh integer [n] with [0 <= n] as a
   premise.  [phi] itself (physically) when it is quantifier-free (the plain
   rewrite's case), holds a [let] or an array lambda, has no such read, or two
   such reads share an index.

   Contract: the result is valid iff [phi] is, and satisfiable iff [phi] is.
   A read outside a sequence is the term of the sequence theory the theory
   leaves open: a function of the sequence and the index with no other
   constraint, so a model may give the point [(s, k)] any value of the element
   sort.  Given a model [M] of [phi], extending it with [c := M(seq.nth s k)]
   makes every guarded read evaluate as the read it replaces, so the result
   has [phi]'s value there.  Given a model [M'] of the result with any [c],
   the model [M''] that agrees with [M'] except that its read at the point
   [(M'(s), k)] is [M'(c)] gives the result the same value -- the result reads
   that point only in [ite] branches its guards do not select -- and gives
   [phi] that value too.  [s] mentioning no bound variable is what makes the
   point one point for the whole formula; distinct indices keep two replaced
   reads from being one point under two names.  The length step is exact
   because a free sequence observed only through its length ranges over
   exactly the non-negative integers.
   Why: a truth-table cell's validity question over a model's large integer
   held [0 <= k - len (seq.nth (seq.unit (seq.unit d)) k)] beside quantified
   disjuncts reading the same sequence at bound indices; Z3 5.1.0 spends its
   time in the arithmetic solver's bound propagation over the length it
   unfolds (0.6 s at k = 50, 5.6 s at 100, no answer in 20 s at 200 or above),
   and the rewritten question at k = 15215 is answered in under 0.1 s. *)
let abstract_out_of_range_reads_under_binders = Atomic.make false

let abstract_out_of_range_reads_guarded phi =
  if not (Atomic.get abstract_out_of_range_reads_under_binders) then phi
  else
    let has_nth = ref false in
    let has_lambda =
      Set.exists (Formula.funsyms_of phi) ~f:(function
        | T_seq.SqNth _ ->
            has_nth := true;
            false
        | T_array.ALambda _ -> true
        | _ -> false)
    in
    if
      (not !has_nth) || has_lambda
      || Formula.is_quantifier_free phi
      || not (Formula.is_let_free phi)
    then phi
    else
      let bound =
        Set.Poly.map (Formula.quantified_sort_env_of phi) ~f:fst
      in
      let mentions_nth t =
        Set.exists (Term.funsyms_of t) ~f:(function
          | T_seq.SqNth _ -> true
          | _ -> false)
      in
      (* (read, element sort, sequence, index, its structural length) *)
      let cands = ref [] in
      Formula.iter_term phi ~f:(function
        | Term.FunApp
            (T_seq.SqNth se, [ sq; Term.FunApp (T_int.Int k, [], _) ], _) as t
          -> (
            match seq_len_of sq with
            | Some n
              when Z.(Compare.(k < zero) || Compare.(k >= n))
                   && (not (mentions_nth sq))
                   && Set.are_disjoint (Term.tvs_of sq) bound
                   && not
                        (List.exists !cands ~f:(fun (t', _, _, _, _) ->
                             Stdlib.( = ) t t')) ->
                cands := (t, se, sq, k, n) :: !cands
            | _ -> ())
        | _ -> ());
      let cands = List.rev !cands in
      let ks = List.map cands ~f:(fun (_, _, _, k, _) -> k) in
      if
        List.is_empty cands
        || List.length (List.dedup_and_sort ks ~compare:Z.compare)
           <> List.length ks
      then phi
      else
        let used =
          Set.union
            (Set.Poly.map (Formula.tvs_of phi) ~f:Ident.name_of_tvar)
            (Set.Poly.map bound ~f:Ident.name_of_tvar)
        in
        let fresh prefix i k =
          let rec go suffix =
            let name =
              sprintf "%s%d_%s%s" prefix i (Z.to_string k)
                (if suffix = 0 then "" else sprintf "_%d" suffix)
            in
            if Set.mem used name then go (suffix + 1) else Ident.Tvar name
          in
          go 0
        in
        let table =
          List.mapi cands ~f:(fun i (t, se, sq, k, n) ->
              (t, se, sq, k, n, fresh "#oorg" i k))
        in
        let fresh_vars =
          Set.Poly.of_list (List.map table ~f:(fun (_, _, _, _, _, c) -> c))
        in
        let rec len_of se = function
          | Term.FunApp (T_bool.IfThenElse, [ g; a; b ], _) ->
              T_bool.mk_if_then_else g (len_of se a) (len_of se b)
          | t -> T_seq.mk_len se t
        in
        (* (bound variable, literal) for every guard on a bound index *)
        let met = ref [] in
        let is_fresh_ite = function
          | Term.FunApp (T_bool.IfThenElse, [ _; Term.Var (c, _, _); _ ], _)
            ->
              Set.mem fresh_vars c
          | _ -> false
        in
        let phi' =
          Formula.map_term phi ~f:(fun t ->
              match t with
              | Term.FunApp (T_seq.SqNth se, [ sq'; ix ], _) -> (
                  match
                    List.find table ~f:(fun (t', _, _, _, _, _) ->
                        Stdlib.( = ) t t')
                  with
                  | Some (_, se, _, _, _, c) -> Term.mk_var c se
                  | None ->
                      let n' = seq_len_of sq' in
                      List.fold_right table ~init:t
                        ~f:(fun (_, se0, sq, k, n, c) acc ->
                          let distinct =
                            (not (Stdlib.( = ) se se0))
                            || (match ix with
                               | Term.FunApp (T_int.Int k', [], _) ->
                                   not (Z.equal k k')
                               | _ -> false)
                            ||
                            match n' with
                            | Some n' -> not (Z.equal n n')
                            | None -> false
                          in
                          if distinct then acc
                          else (
                            (match ix with
                            | Term.Var (x, _, _)
                              when Set.mem bound x
                                   && not
                                        (List.exists !met ~f:(fun (y, k') ->
                                             Ident.tvar_equal x y && Z.equal k k'))
                              ->
                                met := (x, k) :: !met
                            | _ -> ());
                            let at_k = Formula.eq ix (T_int.mk_int k) in
                            let guard =
                              if Stdlib.( = ) sq' sq then at_k
                              else Formula.mk_and (Formula.eq sq' sq) at_k
                            in
                            T_bool.mk_if_then_else (T_bool.of_formula guard)
                              (Term.mk_var c se) acc)))
              | Term.FunApp (T_seq.SqLen se, [ arg ], _) when is_fresh_ite arg
                ->
                  len_of se arg
              | t -> t)
        in
        (* the length step, for the fresh variables of a sequence sort *)
        let seq_fresh =
          List.filter_map table ~f:(fun (_, se, _, k, _, c) ->
              match se with
              | T_seq.SSeq _ -> Some (c, k)
              | _ -> None)
        in
        let len_var =
          Map.Poly.of_alist_exn
            (List.mapi seq_fresh ~f:(fun i (c, k) -> (c, fresh "#oorglen" i k)))
        in
        let replaced =
          Formula.map_term phi' ~f:(function
            | Term.FunApp (T_seq.SqLen _, [ Term.Var (c, _, _) ], _)
              when Map.Poly.mem len_var c ->
                Term.mk_var (Map.Poly.find_exn len_var c) T_int.SInt
            | t -> t)
        in
        let left = Formula.tvs_of replaced in
        let gone =
          List.filter (Map.Poly.keys len_var) ~f:(fun c -> not (Set.mem left c))
        in
        (* A quantifier whose variable is guarded against a literal [k] also
           gets its instance at [k] beside it ([exists x. b] as
           [b[k/x] \/ exists x. b], [forall x. b] as [b[k/x] /\ forall x. b]),
           an equivalence.  The rewrite removes the ground read that the
           solver's instantiation would have matched to reach [x := k], so
           without the instance a question decided before (a universal whose
           instance at [k] contradicts the length) can come back undecided.
           The instance is simplified, so its guards [k = k] select [c] and
           no read at [k] comes back. *)
        let rec with_instances phi =
          match phi with
          | Formula.UnaryOp (op, p, info) ->
              Formula.mk_unop ~info op (with_instances p)
          | Formula.BinaryOp (op, p1, p2, info) ->
              Formula.mk_binop ~info op (with_instances p1) (with_instances p2)
          | Formula.Bind (((Formula.Forall | Formula.Exists) as b), senv, body, info)
            ->
              let body = with_instances body in
              let q = Formula.mk_bind ~info b senv body in
              List.fold !met ~init:q ~f:(fun acc (x, k) ->
                  if
                    not
                      (List.exists senv ~f:(fun (y, _) -> Ident.tvar_equal x y))
                  then acc
                  else
                    let rest =
                      List.filter senv ~f:(fun (y, _) ->
                          not (Ident.tvar_equal x y))
                    in
                    let instance =
                      simplify
                      @@ Formula.mk_bind_if_bounded b rest
                      @@ Formula.subst
                           (Map.Poly.singleton x (T_int.mk_int k))
                           body
                    in
                    match b with
                    | Formula.Exists -> Formula.mk_or instance acc
                    | _ -> Formula.mk_and instance acc)
          | phi -> phi
        in
        if List.length gone <> Map.Poly.length len_var then
          (* some fresh sequence is still read otherwise: keep every length
             as a length (replacing only some would still be exact, but a
             partial replacement is not what was measured) *)
          with_instances phi'
        else if List.is_empty gone then with_instances phi'
        else
          Formula.mk_imply
            (Formula.and_of
               (List.map gone ~f:(fun c ->
                    Formula.geq
                      (Term.mk_var (Map.Poly.find_exn len_var c) T_int.SInt)
                      (T_int.zero ()))))
            (with_instances replaced)

let is_valid_aux is_valid phi =
  let phi = Formula.nnf_of phi in
  match with_valid_check_records (fun tbl -> Hashtbl.Poly.find tbl phi) with
  | Some rcd -> rcd
  | None ->
      let ret =
        is_valid
          (abstract_length_only_sequences
             (abstract_out_of_range_reads_guarded
                (abstract_out_of_range_reads phi)))
      in
      with_valid_check_records (fun tbl ->
          Hashtbl.Poly.set tbl ~key:phi ~data:ret);
      ret

let is_valid is_valid phi =
  try eval phi
  with exn_ when not (Common.Timer.is_async exn_) ->
    (* reachable here if phi may cause division by 0 *)
    is_valid_aux is_valid phi

(* A COUNT, NOT A PASS: how often [check] could not decide a formula by
   evaluation and fell back to the validity query, split by whether the formula
   mentions a sequence operator, and how many of those fallbacks reached the
   solver rather than the cache in front of it.  Enabled by
   [COAR_EVAL_FALLBACK_COUNT=1], printed once to stderr at exit, and otherwise
   inert: no formula is walked and nothing is decided differently. *)
(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let count_fallbacks =
  Lazy.from_val
    (match Sys.getenv "COAR_EVAL_FALLBACK_COUNT" with
    | Some ("1" | "true" | "yes") -> true
    | _ -> false)

(* [| fallbacks; of which sequence; solver calls; of which sequence |] *)
let fallback_counts = Array.init 4 ~f:(fun _ -> Atomic.make 0)
let fallback_report_registered = Atomic.make false

let count_fallback ~seq ~solver =
  if not (Atomic.exchange fallback_report_registered true) then
    Stdlib.at_exit (fun () ->
        let get i = Atomic.get fallback_counts.(i) in
        Stdlib.Printf.eprintf
          "[eval-fallback] check fallbacks=%d seq=%d solver_calls=%d \
           seq_solver_calls=%d evaluate_sequences=%b\n\
           %!"
          (get 0) (get 1) (get 2) (get 3)
          (Atomic.get evaluate_sequences));
  let base = if solver then 2 else 0 in
  Atomic.incr fallback_counts.(base);
  if seq then Atomic.incr fallback_counts.(base + 1)

let mentions_sequence phi =
  Set.exists (Formula.funsyms_of phi) ~f:(function
    | T_seq.(
        ( SqEmpty _ | SqUnit _ | SqConcat _ | SqLen _ | SqNth _ | SqExtract _
        | SqStore _ )) ->
        true
    | _ -> false)

(* return
   Some true if cond => phi is valid
   Some false if cond => not phi is valid
   None otherwise *)
let check ?(cond = Formula.mk_true ()) is_valid_fun phi =
  let is_valid phi =
    try eval phi
    with exn_ when not (Common.Timer.is_async exn_) ->
      (* reachable here if phi may cause division by 0 *)
      if Lazy.force count_fallbacks then (
        let seq = mentions_sequence phi in
        count_fallback ~seq ~solver:false;
        is_valid_aux
          (fun phi ->
            count_fallback ~seq ~solver:true;
            is_valid_fun phi)
          phi)
      else is_valid_aux is_valid_fun phi
  in
  if is_valid @@ simplify @@ Formula.mk_imply cond phi then
    (* both directions valid means [cond] is unsatisfiable: the atom denotes
       no example and [phi] has no value at it; "true" would be an arbitrary
       verdict.  A trivially true condition (the
       ground case) cannot be unsatisfiable, so the extra check is only made
       for a real side condition -- the ground case costs what it did. *)
    if
      (not (Formula.is_true cond))
      && (is_valid @@ simplify @@ Formula.mk_imply cond @@ Formula.mk_neg phi)
    then None
    else Some true
  else if is_valid @@ simplify @@ Formula.mk_imply cond @@ Formula.mk_neg phi
  then Some false
  else None

(* Unfolding the defined functions of a formula, guided by their guards.

   [unfold_rec_apps ?fuel phi] rewrites every application [f(t1, ..., tn)] of
   a function of the global function environment (a [define-fun-rec], a
   datatype's size function) into the definition's body with the parameters
   replaced by the arguments, and repeats inside the result.  An [ite] whose
   condition simplifies to [true] or [false] is replaced by the chosen branch
   before that branch is looked at, so the recursion of a definition written
   as [ite (base case) value (recursive case)] stops where its guard says.
   It returns [Some phi'] only when [phi'] applies no defined function any
   more, and [None] otherwise: when a condition guarding an application stays
   undecided (it depends on a free variable), when an application names a
   function the environment does not hold, or when more than [fuel]
   applications have been unfolded (a definition that does not terminate on
   its arguments, or one whose evaluation is too large).  [None] is the
   caller's cue to ask what it asked before.

   EXACTNESS.  A [define-fun-rec] asserts the equation
   [forall x1 ... xn. f(x1, ..., xn) = body]; every model of the problem
   satisfies it, so replacing an application by the body instantiated at its
   arguments is an equivalence in every model, whether or not the definition
   terminates.  Choosing an [ite]'s branch when its condition simplifies to a
   constant and [simplify_term] are equivalences too, and the substitution is
   capture-avoiding.  Hence [phi'] holds in exactly the models [phi] holds in,
   and a [phi'] with no defined function left has, at a closed example, the
   value every model gives it: the value the theory fixes, which a solver's
   validity question would also find, without a budget.  Free variables
   (an uninterpreted element sort's values inside a list, say) may remain:
   an application is unfolded whenever its guards decide, and the leaves the
   guards do not read are carried along, which is what lets [length] of a
   list of opaque elements be computed where [eval_term] (which needs every
   leaf to be a value) gives up.

   The traversal does not enter an array [lambda] that applies a defined
   function; it gives up there instead. *)
exception Unfold_stop

(* Why [unfold_rec_apps_why] stopped: at an [ite] whose condition stayed
   undecided while a branch still applies a defined function (the condition,
   as simplified, is carried so a caller can ask which variables it reads),
   or for any other reason (no defined function, an unknown function, an
   array [lambda] over an application, an atom that is not a predicate
   application, the fuel). *)
type unfold_stop = Stop_at_guard of Term.t | Stop_other

exception Unfold_stop_at_guard of Term.t

(* [unfold_rec_apps_why ?fuel phi] is [unfold_rec_apps] with the reason it
   gave up: [Ok phi'] exactly when [unfold_rec_apps] returns [Some phi'], and
   [Error (Stop_at_guard c)] when the first undecided guard met over an
   application was [c] (after unfolding and simplification).  The first such
   guard is reported; the traversal stops there. *)
let unfold_rec_apps_why ?(fuel = 4096) phi =
  let fenv = get_fenv () in
  if Map.Poly.is_empty fenv || Set.is_empty (Formula.fvar_apps_of phi) then
    Error Stop_other
  else
    let fuel = ref fuel in
    let has_app t = not (Set.is_empty (Term.fvar_apps_of t)) in
    let rec unf t =
      match t with
      | Term.Var _ -> t
      | LetTerm _ -> unf (Term.elim_let t)
      | FunApp (T_bool.IfThenElse, [ c; a; b ], info) ->
          let c' = simplify_term (unf c) in
          if T_bool.is_true c' then unf a
          else if T_bool.is_false c' then unf b
          else if has_app a || has_app b then raise (Unfold_stop_at_guard c')
          else Term.mk_fsym_app ~info T_bool.IfThenElse [ c'; a; b ]
      | FunApp (T_bool.Formula phi, [], info) ->
          Term.mk_fsym_app ~info (T_bool.Formula (unf_formula phi)) []
      | FunApp (FVar (f, _, _), ts, _) -> (
          match Map.Poly.find fenv f with
          | None -> raise Unfold_stop
          | Some (params, _, body, _, _) ->
              if !fuel <= 0 then raise Unfold_stop;
              decr fuel;
              let ts' = List.map ts ~f:(fun t -> simplify_term (unf t)) in
              let sub =
                match List.zip (List.map ~f:fst params) ts' with
                | Ok l -> Map.Poly.of_alist_exn l
                | Unequal_lengths -> raise Unfold_stop
              in
              unf (Term.subst sub body))
      | FunApp (T_array.ALambda _, _, _) when has_app t -> raise Unfold_stop
      | FunApp (fsym, ts, info) -> Term.mk_fsym_app ~info fsym (List.map ts ~f:unf)
    and unf_formula phi =
      Formula.map_atom phi ~f:(function
        | Atom.App ((Predicate.Psym _ as pred), ts, info) ->
            Formula.mk_atom (Atom.mk_app ~info pred (List.map ts ~f:unf))
        | atom ->
            if Set.is_empty (Atom.fvar_apps_of atom) then Formula.mk_atom atom
            else raise Unfold_stop)
    in
    match simplify (unf_formula (Formula.elim_let phi)) with
    | phi' when Set.is_empty (Formula.fvar_apps_of phi') -> Ok phi'
    | _ -> Error Stop_other
    | exception Unfold_stop -> Error Stop_other
    | exception Unfold_stop_at_guard c -> Error (Stop_at_guard c)

let unfold_rec_apps ?fuel phi = Result.ok (unfold_rec_apps_why ?fuel phi)
