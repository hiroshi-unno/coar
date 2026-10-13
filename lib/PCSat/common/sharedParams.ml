(* Reading an example clause whose parameters are shared between its atoms.

   A parametric example clause [B1(p) /\ B2(p) => H(p)] denotes every
   instance at the parameters [p] its guard admits.  The template synthesizer
   reads such a clause atom by atom: each atom's qualifiers are decided at a
   truth-table row obtained by renaming that atom's parameters apart and
   grounding them at default points.  For a parameter whose default point is a
   free per-parameter constant -- a sort variable or a sequence, the sorts
   [T_dt.mk_dummy_for] grounds that way -- the row decides a qualifier only when
   it holds (or fails) for EVERY value of the parameter, and an undecided entry
   is read in the worst case for the atom's polarity.  That reading implies the
   clause, but it loses the link between two occurrences of one parameter: a
   candidate that satisfies the clause only through the implication (the body
   atom forces facts about [p] which make the head true) is rejected at every
   template shape.

   This module supplies the clause-level half of the repair.  [analyse] finds
   the parameters of those sorts that occur in more than one atom, and marks
   every atom mentioning one as SYMBOLIC.  A symbolic atom is to be read
   exactly -- its qualifiers kept as formulas over its arguments, decided by the
   solver together with the template parameters -- with every parameter of
   those sorts it mentions one variable across the clause, bound universally.
   [constraint_of] assembles the clause's constraint from per-atom constraints
   the caller builds, binds those variables, and removes every universally
   bound sequence variable by the observation abstraction below, so that the
   query handed to the solver quantifies no sequence.

   Contract of [constraint_of], for a clause with symbolic atoms S and
   per-atom constraints C_a (exact for a in S, the truth-table reading
   otherwise):
     (1) its result implies the clause at every value of the shared
         parameters under the guard, with every other parameter read as the
         caller's grounding reads it;
     (2) the per-atom reading of the whole clause implies its result (with
         one qualification when two shared sequences are compared with each
         other, stated at [abstract_observations]);
     (3) its result binds no sequence and no function-sorted variable
         ([Z3interface.may_not_return] is false of it), or it is [None].
   (1) because the exact reading of a symbolic atom at a value is that atom's
   literal there, and the truth-table reading of any other atom implies its
   literal at every value of its own parameters (a decided entry is valid at a
   free constant, an undecided one is read in the worst case, and a template
   is monotone in its holes).  (2) because the truth-table reading of a
   symbolic atom implies its exact reading at every value, by the same
   argument.  So the result sits between the per-atom reading and the clause.
   "The atom's literal there" holds in every model only if no term the
   theory leaves open is left for the solver to choose: a read of a LITERAL
   sequence out of its range ([seq.nth (seq.unit 5) 1]) is not a variable, so
   the abstraction below does not touch it, and [bind_open_terms] binds each
   such read universally first ([bind_open_terms] says why that is exact, and
   covers division by a literal zero and a selector off its constructor as
   well).  Without it the
   result accepted a candidate the clause refutes in some model.  (2) survives
   the binding: the truth table decides a qualifier over such a read only by a
   validity check, that is, only when it holds whatever the read's value is,
   which is what the universal asks.
   Which atoms are symbolic is [analyse]'s choice, and (1) and (2) hold for
   ANY choice: moving an atom from the exact reading to the per-atom one moves
   its literal's constraint from the exact one to one that implies it, so the
   result still implies the clause and is still implied by the per-atom reading
   of the whole clause.  Reading fewer atoms exactly only accepts fewer of the
   candidates the clause admits beyond the per-atom reading.
   [None] means "use the per-atom reading": no parameter is shared, or the
   abstraction declined, or the result would still be a query the solver may
   not return from.

   The observation abstraction.  A sequence variable [s] that occurs only as
   [seq.len s] and as [seq.nth s c] with [c] an integer literal is replaced by
   a fresh integer [l] for its length and a fresh element [e_c] per literal, all
   bound universally, under the premise [l >= 0].  This is an equivalence and
   not merely a strengthening: every tuple [(l >= 0, e_c ...)] is realised by
   some sequence in some model -- in range, [e_c] is the element at [c]; out of
   range, [seq.nth] is unspecified by the theory and so takes any value across
   models, which is also how the truth table's validity checks read it.  Without
   the premise the result would reject candidates that rely on a length being
   non-negative, which the per-atom reading accepts, and (2) would fail.  An
   equality with a sequence literal is rewritten into lengths and reads first,
   and an equality between two such variables becomes a Boolean of its own
   ([abstract_observations] says how, and what that costs (2)).  Any other
   occurrence of [s] -- a concatenation or extraction over it, a read at a
   non-literal index, an equality with some other sequence term -- makes the
   abstraction decline.
   A universal over a sequence is the shape the solver has been measured not to
   return from, not even under its own timeout, and nothing in this process can
   interrupt it; declining is therefore the only safe answer there. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* the sorts whose parameters the truth table grounds at a free per-parameter
   constant, so that the row decides a qualifier about one only when it holds
   for every value -- the sorts where the per-atom reading loses a link *)
let symbolic_sort = function Sort.SVar _ | T_seq.SSeq _ -> true | _ -> false

type analysis = {
  shared : Ident.tvar Set.Poly.t;
      (** ids occurring in more than one ORIGINAL atom of the clause *)
  symbolic : (bool * ExAtom.t) Set.Poly.t;
      (** the literals (polarity, atom) read exactly: per original atom that
          mentions a shared id, its representative copy *)
  vars : sort_env_map;
      (** every id a symbolic atom mentions, with its sort: these are bound
          universally, each as one variable across the clause *)
  renaming : (Ident.tvar, Ident.tvar) Map.Poly.t;
      (** a dummy constant in [vars] to the variable that stands for it, applied
          to the symbolic atoms only *)
}

let terms_of_atom = function
  | ExAtom.FCon (_, phi) -> ([], Some phi)
  | ExAtom.PApp (_, ts) -> (ts, None)
  | ExAtom.PPApp ((_, cond), (_, ts)) -> (ts, Some cond)

(* The ids an atom mentions: its parameters of a symbolic sort, and the dummy
   constants of such a sort in its arguments or guard.  The second kind is the
   cell route's: its expansion grounds an example's parameters before the atoms
   reach constraint generation, so two atoms that shared a parameter share its
   constant.  A constant named after a parameter of the clause
   ([T_dt.dummy_name_for]) is identified with that parameter, which is what the
   name means; any other constant is its own id. *)
(* the parameter of the clause whose per-parameter constant is [x], if any *)
let param_named_by clause_params x =
  Map.Poly.fold clause_params ~init:None ~f:(fun ~key:p ~data:ps found ->
      match found with
      | Some _ -> found
      | None -> (
          match T_dt.dummy_name_for p ps with
          | Some d when Ident.tvar_equal d x -> Some p
          | _ -> None))

let ids_of_atom ~clause_params ~dummies atom =
  let ts, cond = terms_of_atom atom in
  let tvs =
    Set.Poly.union_list
      (Option.value_map cond ~default:Set.Poly.empty ~f:Formula.tvs_of
      :: List.map ts ~f:Term.tvs_of)
  in
  Set.fold tvs ~init:Map.Poly.empty ~f:(fun acc x ->
      match Map.Poly.find (ExAtom.params_of atom) x with
      | Some s when symbolic_sort s -> Map.Poly.set acc ~key:x ~data:s
      | Some _ -> acc
      | None -> (
          match Map.Poly.find dummies x with
          | Some s when symbolic_sort s ->
              let id =
                Option.value ~default:x (param_named_by clause_params x)
              in
              Map.Poly.set acc ~key:id ~data:s
          | _ -> acc))

(* the variable standing for a dummy constant that no parameter of the clause
   names; deterministic, so that the same clause gives the same constraint *)
let var_for_dummy (Ident.Tvar d) = Ident.Tvar ("#shared_" ^ d)

(* The original atom a cell-route copy was made from.  The cell expansion
   appends the cell columns PAST the predicate's declared arity and keeps the
   declared arguments as they were, so the copies of one atom agree on their
   first [arity] arguments and differ only in the columns after them.  [None]
   from [arity_of] (or an atom no longer than its arity) means the atom is its
   own original. *)
let original_of ~arity_of = function
  | ExAtom.PApp ((pvar, sorts), ts) as atom -> (
      match arity_of pvar with
      | Some n when n < List.length ts ->
          ExAtom.PApp ((pvar, List.take sorts n), List.take ts n)
      | _ -> atom)
  | ExAtom.PPApp (pc, ((pvar, sorts), ts)) as atom -> (
      match arity_of pvar with
      | Some n when n < List.length ts ->
          ExAtom.PPApp (pc, ((pvar, List.take sorts n), List.take ts n))
      | _ -> atom)
  | atom -> atom

(* [arity_of pvar]: the declared arity of [pvar], used to recognise the
   cell-route copies of one atom (see [original_of]).

   Sharing is counted over ORIGINAL atoms: an id is shared when two different
   originals of the clause mention it, and the copies of one original never
   make an id shared on their own.  They all mention the constants of their
   original's arguments, so counting copies made every copy symbolic whenever
   an atom had two cells -- a link between an atom and itself, through its own
   parameter, which the reading without cells never needed.

   Of the copies of an original that mentions a shared id, ONE is read exactly:
   the representative, the least copy in the clause's canonical order (with its
   polarity).  No copy is distinguished otherwise -- the celled truth table has
   a row of its own for every copy and none for the uncelled atom -- and none
   needs to be: the plain qualifiers are over the declared arguments, which all
   copies share, and the cell columns bind only cell variables, so every
   plain qualifier has the same value at every copy.  The link between two
   atoms through a shared parameter is a link between their plain qualifiers
   (the facts one atom forces about the parameter and the other reads), so the
   representative carries it whichever copy it is.  What the other copies would
   add is a link through their cell qualifiers, which is given up; they keep
   the per-atom reading.  Reading fewer atoms exactly is sound (see the
   contract at [constraint_of]), and it bounds the exact atoms of a clause by
   its originals rather than by its copies. *)
let analyse ?(arity_of = fun _ -> None) (clause : ExClause.t) : analysis option
    =
  let lits =
    List.map (Set.to_list clause.ExClause.positive) ~f:(fun a -> (true, a))
    @ List.map (Set.to_list clause.ExClause.negative) ~f:(fun a -> (false, a))
  in
  let clause_params = ExClause.params_of clause in
  let dummies =
    List.fold (get_dummy_term_senv ()) ~init:Map.Poly.empty
      ~f:(fun acc (x, s) -> Map.Poly.set acc ~key:x ~data:s)
  in
  (* original (with its polarity) -> its copies, in the clause's order *)
  let groups =
    List.fold lits ~init:Map.Poly.empty ~f:(fun acc ((pol, a) as lit) ->
        Map.Poly.add_multi acc ~key:(pol, original_of ~arity_of a) ~data:lit)
    |> Map.Poly.map ~f:List.rev
  in
  let per_original =
    List.map (Map.Poly.to_alist groups) ~f:(fun (((_, orig) as key), copies) ->
        (key, copies, ids_of_atom ~clause_params ~dummies orig))
  in
  let counts =
    List.fold per_original ~init:Map.Poly.empty ~f:(fun acc (_, _, ids) ->
        Map.Poly.fold ids ~init:acc ~f:(fun ~key ~data:_ acc ->
            Map.Poly.update acc key ~f:(function None -> 1 | Some n -> n + 1)))
  in
  let shared =
    Set.Poly.of_list @@ Map.Poly.keys
    @@ Map.Poly.filter counts ~f:(fun n -> n >= 2)
  in
  if Set.is_empty shared then None
  else
    (* the representative of every original that mentions a shared id *)
    let sym =
      List.filter_map per_original ~f:(fun (_, copies, ids) ->
          if Map.Poly.existsi ids ~f:(fun ~key ~data:_ -> Set.mem shared key)
          then
            let ((_, rep) as lit) =
              List.min_elt copies ~compare:Stdlib.compare |> Option.value_exn
            in
            Some (lit, ids_of_atom ~clause_params ~dummies rep)
          else None)
    in
    let vars =
      List.fold sym ~init:Map.Poly.empty ~f:(fun acc (_, ids) ->
          Map.Poly.merge_skewed ~combine:(fun ~key:_ a _ -> a) acc ids)
    in
    (* a dummy constant that stands for a parameter maps to that parameter;
       one that does not maps to a variable of its own *)
    let renaming =
      List.fold sym ~init:Map.Poly.empty ~f:(fun acc ((_, a), _) ->
          let ts, cond = terms_of_atom a in
          let tvs =
            Set.Poly.union_list
              (Option.value_map cond ~default:Set.Poly.empty ~f:Formula.tvs_of
              :: List.map ts ~f:Term.tvs_of)
          in
          Set.fold tvs ~init:acc ~f:(fun acc x ->
              if Map.Poly.mem (ExAtom.params_of a) x then acc
              else
                match Map.Poly.find dummies x with
                | Some s when symbolic_sort s ->
                    Map.Poly.set acc ~key:x
                      ~data:
                        (Option.value
                           (param_named_by clause_params x)
                           ~default:(var_for_dummy x))
                | _ -> acc))
    in
    (* the ids of [vars] that are dummy constants are renamed the same way *)
    let vars =
      Map.Poly.fold vars ~init:Map.Poly.empty ~f:(fun ~key ~data acc ->
          let key = Option.value (Map.Poly.find renaming key) ~default:key in
          Map.Poly.set acc ~key ~data)
    in
    Some
      {
        shared;
        symbolic = Set.Poly.of_list (List.map sym ~f:fst);
        vars;
        renaming;
      }

let is_symbolic analysis polarity atom =
  Set.mem analysis.symbolic (polarity, atom)

(* The elements of a sequence literal -- [seq.empty], [seq.unit t] and
   concatenations of those -- or [None] for any other term. *)
let rec literal_elems = function
  | Term.FunApp (T_seq.SqEmpty _, [], _) -> Some []
  | Term.FunApp (T_seq.SqUnit _, [ t ], _) -> Some [ t ]
  | Term.FunApp (T_seq.SqConcat _, [ t1; t2 ], _) -> (
      match (literal_elems t1, literal_elems t2) with
      | Some l1, Some l2 -> Some (l1 @ l2)
      | _ -> None)
  | _ -> None

exception Decline

(* The observation abstraction of the module comment, over the sequence
   variables [seqs].  Returns the rewritten formula, the fresh variables with
   their sorts, and the premises the fresh variables are read under, or [None]
   when some occurrence of a variable in [seqs] is neither an observation nor
   one of the two equalities below.

   An equality between a variable [v] of [seqs] and a sequence LITERAL of [n]
   elements is exactly [len v = n /\ nth v 0 = t0 /\ ...], and is rewritten so.
   An equality between two variables [v] and [w] of [seqs] has no finite form
   (it speaks about every index), so it becomes a fresh Boolean [b] bound
   universally with it, read under two premises that hold of every pair of
   sequences in every model: [b] implies equal lengths and equal reads at every
   literal index either variable is read at ([seq.nth] is a function, so it
   agrees on equal arguments even out of range); and two empty sequences are
   equal.  Every other combination of values stays in the range of the
   universal, so the result is still implied by nothing weaker than the clause;
   it may be stronger than the exact reading where a candidate relies on some
   finer consequence of [v <> w], which the per-atom reading also cannot see
   (the row leaves such an equality undecided). *)
let abstract_observations (seqs : sort_env_map) phi =
  if Map.Poly.is_empty seqs then Some (phi, [], [])
  else
    let mentions t = Set.exists (Term.tvs_of t) ~f:(Map.Poly.mem seqs) in
    let var_of = function
      | Term.Var (v, _, _) when Map.Poly.mem seqs v -> Some v
      | _ -> None
    in
    let pairs = ref Map.Poly.empty in
    let pair_var v w se =
      let v, w = if Ident.tvar_compare v w <= 0 then (v, w) else (w, v) in
      match Map.Poly.find !pairs (v, w) with
      | Some (b, _) -> b
      | None ->
          let b =
            Ident.Tvar
              (sprintf "#eq_%s_%s" (Ident.name_of_tvar v) (Ident.name_of_tvar w))
          in
          pairs := Map.Poly.set !pairs ~key:(v, w) ~data:(b, se);
          b
    in
    (* pass 1: the equalities *)
    let rewrite_eq pos t1 t2 =
      let se =
        match Term.sort_of t1 with T_seq.SSeq se -> Some se | _ -> None
      in
      match se with
      | None -> None
      | Some se ->
          if not (mentions t1 || mentions t2) then None
          else
            let exact v elems =
              Formula.and_of
                (Formula.eq
                   (T_seq.mk_len se (Term.mk_var v (T_seq.SSeq se)))
                   (T_int.mk_int (Z.of_int (List.length elems)))
                :: List.mapi elems ~f:(fun i e ->
                    Formula.eq
                      (T_seq.mk_nth se
                         (Term.mk_var v (T_seq.SSeq se))
                         (T_int.mk_int (Z.of_int i)))
                      e))
            in
            let lit_ok elems = not (List.exists elems ~f:mentions) in
            let phi =
              match
                (var_of t1, var_of t2, literal_elems t1, literal_elems t2)
              with
              | Some v, Some w, _, _ ->
                  let b = pair_var v w se in
                  Formula.of_bool_var b
              | Some v, None, _, Some elems when lit_ok elems -> exact v elems
              | None, Some v, Some elems, _ when lit_ok elems -> exact v elems
              | _ -> raise Decline
            in
            Some (if pos then phi else Formula.mk_neg phi)
    in
    match
      Formula.map_atom phi ~f:(fun atom ->
          match atom with
          | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) -> (
              match rewrite_eq true t1 t2 with
              | Some phi -> phi
              | None -> Formula.mk_atom atom)
          | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) -> (
              match rewrite_eq false t1 t2 with
              | Some phi -> phi
              | None -> Formula.mk_atom atom)
          | _ -> Formula.mk_atom atom)
    with
    | exception Decline -> None
    | phi1 ->
        (* the literal indices each variable is read at *)
        let indices = ref Map.Poly.empty in
        Formula.iter_term phi1 ~f:(function
          | Term.FunApp (T_seq.SqNth _, [ Term.Var (v, _, _); i ], _)
            when Map.Poly.mem seqs v && T_int.is_int i ->
              indices :=
                Map.Poly.update !indices v ~f:(fun cs ->
                    Set.add
                      (Option.value cs ~default:Set.Poly.empty)
                      (T_int.let_int i))
          | _ -> ());
        let pair_premises =
          List.concat_map (Map.Poly.to_alist !pairs)
            ~f:(fun ((v, w), (b, se)) ->
              let sv = Term.mk_var v (T_seq.SSeq se)
              and sw = Term.mk_var w (T_seq.SSeq se) in
              let cs =
                Set.union
                  (Option.value (Map.Poly.find !indices v)
                     ~default:Set.Poly.empty)
                  (Option.value (Map.Poly.find !indices w)
                     ~default:Set.Poly.empty)
              in
              let lv = T_seq.mk_len se sv and lw = T_seq.mk_len se sw in
              [
                Formula.mk_imply (Formula.of_bool_var b)
                  (Formula.and_of
                     (Formula.eq lv lw
                     :: List.map (Set.to_list cs) ~f:(fun c ->
                         let c = T_int.mk_int c in
                         Formula.eq (T_seq.mk_nth se sv c)
                           (T_seq.mk_nth se sw c))));
                Formula.mk_imply
                  (Formula.and_of
                     [
                       Formula.eq lv (T_int.zero ());
                       Formula.eq lw (T_int.zero ());
                     ])
                  (Formula.of_bool_var b);
              ])
        in
        (* pass 2: the observations, over the formula and the premises *)
        let fresh = ref Map.Poly.empty in
        let obs key name sort =
          match Map.Poly.find !fresh key with
          | Some (v, s) -> Term.mk_var v s
          | None ->
              let v = Ident.Tvar name in
              fresh := Map.Poly.set !fresh ~key ~data:(v, sort);
              Term.mk_var v sort
        in
        let f = function
          | Term.FunApp (T_seq.SqLen _, [ Term.Var (s, _, _) ], _)
            when Map.Poly.mem seqs s ->
              obs (s, None) ("#len_" ^ Ident.name_of_tvar s) T_int.SInt
          | Term.FunApp (T_seq.SqNth se, [ Term.Var (s, _, _); i ], _)
            when Map.Poly.mem seqs s && T_int.is_int i ->
              let c = T_int.let_int i in
              obs (s, Some c)
                (sprintf "#nth_%s_%s" (Ident.name_of_tvar s)
                   (if Z.sign c < 0 then "m" ^ Z.to_string (Z.neg c)
                    else Z.to_string c))
                se
          | t -> t
        in
        let phi' = Formula.map_term ~f phi1 in
        let pair_premises = List.map pair_premises ~f:(Formula.map_term ~f) in
        if
          List.exists (phi' :: pair_premises) ~f:(fun p ->
              Set.exists (Formula.tvs_of p) ~f:(Map.Poly.mem seqs))
        then None
        else
          let fresh = Map.Poly.to_alist !fresh in
          let lens =
            List.filter_map fresh ~f:(function
              | (_, None), b -> Some b
              | _ -> None)
          in
          let elems =
            List.filter_map fresh ~f:(function
              | (_, Some _), b -> Some b
              | _ -> None)
          in
          let bools =
            List.map (Map.Poly.data !pairs) ~f:(fun (b, _) -> (b, T_bool.SBool))
          in
          let premises =
            List.map lens ~f:(fun (l, _) ->
                Formula.geq (Term.mk_var l T_int.SInt) (T_int.zero ()))
            @ pair_premises
          in
          Some (phi', lens @ elems @ bools, premises)

(* The body of a hole kept symbolic ("route (a)" of constraint generation):
   for selector [key] and qualifier [phi] over the hole's parameters,
   [(key > 0 => phi) /\ (key < 0 => not phi)].  A qualifier with a positive
   selector occurs positively in the disjunct and one with a negative selector
   negatively, so this is the general form of which the truth table's decided
   holes ([key >= 0] where [phi] holds, [key <= 0] where it fails) are the
   instances.  The hole is applied to an atom's arguments, so [phi] is
   evaluated there by the solver; where that makes a term the theory leaves
   open ground, [close_open_terms] must bind it. *)
let route_a_hole key phi =
  let q = Logic.ExtTerm.of_old_formula phi in
  Logic.BoolTerm.and_of
    [
      Logic.BoolTerm.imply_of Logic.ExtTerm.(gt_of (mk_var key) (zero ())) q;
      Logic.BoolTerm.imply_of
        Logic.ExtTerm.(lt_of (mk_var key) (zero ()))
        (Logic.BoolTerm.neg_of q);
    ]

(* The ground terms the theory leaves open, bound universally.

   Three shapes are covered, each a term whose value the theory fixes within a
   model and leaves free across models:
   - a read [seq.nth t c] whose index the structure of [t] places outside its
     length ([Evaluator.seq_index_in_range] gives [None] while
     [Evaluator.seq_len_of t] gives a length): [seq.nth] is unspecified there;
   - an integer [div] or [mod]/[rem], or a real division, by the LITERAL zero:
     SMT-LIB leaves division by zero unspecified, and [Evaluator.simplify]
     leaves such a term unfolded on purpose;
   - a datatype selector applied to a constructor application of ANOTHER
     constructor ([hd nil]): the selector is unspecified off its own
     constructor, and [Evaluator.simplify] folds only the right-constructor
     case.
   Left in the synthesis query as a ground term such a term is the SOLVER's
   choice, and the query then asks for one model in which the clause holds (the
   existential reading) instead of the clause holding in every model (the
   per-model one) -- measured: a candidate reading [seq.nth (seq.unit 5) 1 <> 0]
   at a head was accepted, the synthesizer returned the candidate the validator
   had just refuted, and the loop took that for non-progress.  Not covered:
   exponentiation ([0 ^ 0], which the evaluator folds to [1] itself), a
   division by a divisor that is not the literal zero (it is open only at the
   values where it is zero, and is left to the solver as before), and a
   selector or read over a variable or an uninterpreted constant (what the
   per-atom reading already has; a bound sequence variable is the observation
   abstraction's to remove).

   Contract: each such term that mentions no variable except the free template
   parameters [temp_param_senv] (and the variables this function introduced
   for inner open terms) is replaced by a fresh variable of its sort, named
   [prefix ^ n] with [n] counting from 0 within this call -- no global fresh
   name is drawn -- and returned for the caller to bind universally.  Two terms
   get one variable exactly when they are the same term -- the same symbol and
   the same arguments, a literal sequence compared by its elements, so two
   spellings of one literal agree.  This is exact under the per-model reading:
   distinct open terms are values of the unspecified functions ([seq.nth]
   off range, division at zero, a selector off its constructor) at distinct
   arguments, independent across models, so every tuple of values for them is
   realised by some model, and quantifying each one universally says exactly
   "in every model".  (Where a template parameter occurs inside a term, two
   terms can coincide at some value of it and are still given two variables;
   that only strengthens the result.)
   [Declined] where such a term cannot be settled that way: a read of a
   known-length sequence at a non-literal index, or an open term mentioning a
   bound variable, whose value depends on that variable in a way one fresh
   variable cannot say.  The caller decides what a decline means.
   [No_open_term] where the formula has none of the three shapes, and then the
   formula is not even rebuilt: the answer is decided by a scan that allocates
   nothing and draws no name, so a caller that keeps its input on
   [No_open_term] is the identity on every formula without an open term. *)
type open_terms =
  | No_open_term
  | Bound of Formula.t * sort_env_list
  | Declined

(* Is this term, by its head, one of the three open shapes?  The children are
   not consulted, so the test is the same before and after they are rewritten. *)
let open_shape = function
  | Term.FunApp (T_seq.SqNth _, [ sq; i ], _) -> (
      match Evaluator.seq_len_of sq with
      | None -> false
      | Some _ -> Option.is_none (Evaluator.seq_index_in_range sq i))
  | Term.FunApp ((T_int.Div _ | T_int.Rem _), [ _; d ], _) -> T_int.is_zero d
  | Term.FunApp (T_real.RDiv, [ _; d ], _) -> T_real.is_rzero d
  | Term.FunApp
      (T_dt.DTSel (sel, dt, _), [ (Term.FunApp (T_dt.DTCons _, _, _) as t) ], _)
    -> (
      match T_dt.eval_select sel dt t with
      | Some _ -> false
      | None -> true
      | exception exn_ when not (Common.Timer.is_async exn_) -> true)
  | _ -> false

(* The allocation-free scan behind [No_open_term]: does some subterm have an
   open shape?  It enters every binder, as the rewrite below does.  A
   [letrec] is not looked into and answers [true], which only sends the
   formula to the rewrite, where it is decided. *)
let rec term_has_open t =
  open_shape t
  ||
  match t with
  | Term.Var _ -> false
  | Term.FunApp (T_bool.Formula phi, _, _) -> formula_has_open phi
  | Term.FunApp (_, args, _) -> List.exists args ~f:term_has_open
  | Term.LetTerm (_, _, def, body, _) -> term_has_open def || term_has_open body

and atom_has_open = function
  | Atom.True _ | Atom.False _ -> false
  | Atom.App (Predicate.Fixpoint def, args, _) ->
      formula_has_open def.body || List.exists args ~f:term_has_open
  | Atom.App (_, args, _) -> List.exists args ~f:term_has_open

and formula_has_open = function
  | Formula.Atom (a, _) -> atom_has_open a
  | Formula.UnaryOp (_, phi, _) | Formula.Bind (_, _, phi, _) ->
      formula_has_open phi
  | Formula.BinaryOp (_, phi1, phi2, _) ->
      formula_has_open phi1 || formula_has_open phi2
  | Formula.LetRec _ -> true
  | Formula.LetFormula (_, _, def, body, _) ->
      term_has_open def || formula_has_open body

let bind_open_terms ~prefix ~temp_param_senv phi =
  if not (formula_has_open phi) then No_open_term
  else
    let table = ref [] in
    let introduced = ref Set.Poly.empty in
    let closed t =
      Set.for_all (Term.tvs_of t) ~f:(fun x ->
          Map.Poly.mem temp_param_senv x || Set.mem !introduced x)
    in
    (* a read of a literal sequence is keyed by the element sort, the
       elements and the index; everything else by itself.  The element sort
       is part of the key because the elements alone do not determine it: an
       out-of-range read of the empty sequence has no element to carry a sort,
       so reads of [seq.empty] at two sort variables would otherwise share one
       variable of the first one's sort, and the formula would equate a value
       of one uninterpreted sort with a value of another -- which the solver
       refuses as ill-sorted rather than answering.  The two reads are values
       of two independent unspecified functions (one per element sort), so two
       variables is also the exact reading. *)
    let key_of t =
      match t with
      | Term.FunApp (T_seq.SqNth elem_sort, [ sq; i ], _) -> (
          match literal_elems sq with
          | Some es -> `Read (elem_sort, es, i)
          | None -> `Term t)
      | _ -> `Term t
    in
    (* structural equality; a key holding a value [=] cannot compare (a
       closure in some [info]) is simply not shared, which gives two variables
       where one would do -- the strengthening direction *)
    let same a b = try Stdlib.( = ) a b with Invalid_argument _ -> false in
    let f t =
      if not (open_shape t) then t
      else
        match t with
        | Term.FunApp (T_seq.SqNth _, [ _; i ], _) when not (T_int.is_int i) ->
            raise Decline
        | _ when not (closed t) -> raise Decline
        | _ -> (
            let key = key_of t in
            match List.Assoc.find !table key ~equal:same with
            | Some (v, s) -> Term.mk_var v s
            | None ->
                let s = Term.sort_of t in
                let v = Ident.Tvar (sprintf "%s%d" prefix (List.length !table)) in
                table := (key, (v, s)) :: !table;
                introduced := Set.add !introduced v;
                Term.mk_var v s)
    in
    match Formula.map_term ~f phi with
    | exception Decline -> Declined
    | _ when List.is_empty !table -> No_open_term
    | phi' -> Bound (phi', List.rev_map !table ~f:snd)

(* How often [close_open_terms] bound an open term and how often it declined,
   so a run can show what it did. *)
let open_terms_bound = Atomic.make 0
let open_terms_declined = Atomic.make 0

(* The route-(a) clause constraint with its open terms bound: [phi] is the
   simplified constraint of one example clause, whose free variables are the
   template parameters [temp_param_senv] (its example parameters are bound
   inside it or grounded).  Where [bind_open_terms] binds something the
   result is [forall v. phi'], the fresh variables outermost; otherwise the
   result is [phi] itself.

   Soundness.  The synthesis query asks for template parameters making every
   clause constraint true.  With an open term [t] left ground, a candidate is
   accepted when the constraint holds for SOME value of [t] (the solver's
   choice); with [t] replaced by [v] under [forall v], only when it holds for
   EVERY value the theory allows, which is the per-model reading.  The new
   constraint implies the old one (instantiate [v] at the model's value of
   [t]), so it rejects at least what the old one rejected and accepts nothing
   the old one did not; what it newly rejects is exactly a candidate that the
   old one accepted only through the solver's choice of [t], that is, a
   candidate that fails the clause in some model.  Putting [v] outermost is
   right because [t] is closed: it mentions no example parameter, so its value
   does not vary with them.  And a universal per clause is the same as one
   over the whole conjunction, since [forall] distributes over [/\].

   A decline keeps [phi] unchanged (the reading the query had before), and so
   does a fresh variable of a sort the solver is measured not to return from
   when it is bound ([Z3interface.unsupported_binder_sort]: a sequence or an
   arrow).  So on a formula without an open term, and on a declined one, this
   function is the identity; it draws no global fresh name either way. *)
let close_open_terms ~temp_param_senv phi =
  match bind_open_terms ~prefix:"#open_term_" ~temp_param_senv phi with
  | No_open_term -> phi
  | Declined ->
      Atomic.incr open_terms_declined;
      phi
  | Bound (_, vars)
    when List.exists vars ~f:(fun (_, s) -> Z3Smt.Z3interface.unsupported_binder_sort s)
    ->
      Atomic.incr open_terms_declined;
      phi
  | Bound (phi', vars) ->
      Atomic.incr open_terms_bound;
      Formula.forall vars phi'

(* How often [constraint_of] produced a constraint and how often it declined,
   by reason -- so a run can show that the switch was read and what it did. *)
let fired = Atomic.make 0
let declined_observation = Atomic.make 0
let declined_guard = Atomic.make 0

let counts () =
  (Atomic.get fired, Atomic.get declined_observation, Atomic.get declined_guard)

(* [ground p s]: how the caller's strategy reads a parameter that is NOT in
   [analysis.vars] -- [Some t] substitutes [t], [None] keeps it a variable
   bound universally.  [atom_constr ~symbolic polarity atom] is the caller's
   per-atom constraint, exact when [symbolic].  [temp_param_senv] are the free
   template parameters.

   The renaming of dummy constants into the shared variables is applied to the
   symbolic atoms only.  A copy that shares a constant with its representative
   but is not itself symbolic keeps its per-atom constraint exactly as the
   per-atom reading builds it, constant included, which is what contract (2)
   compares against.  The open reads are bound after simplification, which is
   where an open term over a literal or a grounded parameter first appears as
   one. *)
(* step times of [constraint_of], accumulated only while [profile_on] (the
   constraint generation's COAR_CGEN_PROFILE); a measurement instrument *)
(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let profile_on =
  Lazy.from_val
    (match Sys.getenv "COAR_CGEN_PROFILE" with
    | None | Some "" -> false
    | Some _ -> true)

let profile_names =
  [| "lits"; "rename"; "ground"; "convert"; "simplify"; "open"; "observe"; "guard" |]

let profile_times = Array.create ~len:(Array.length profile_names) 0.

let profile_reset () =
  Array.fill profile_times ~pos:0 ~len:(Array.length profile_times) 0.

let profile_report () =
  String.concat ~sep:" "
  @@ Array.to_list
  @@ Array.mapi profile_names ~f:(fun i n -> sprintf "%s %.3f" n profile_times.(i))

let ptime i f =
  if not (Lazy.force profile_on) then f ()
  else
    let t0 = Common.Clock.now_float () in
    Exn.protect ~f ~finally:(fun () ->
        profile_times.(i) <-
          profile_times.(i)
          +. Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) t0))

(* [subst] is [Logic.Term.subst] or a substitution alpha-equivalent to it on
   beta-normal input (the atoms' constraints and the maps here are); the
   result is then the same up to the names of bound variables. *)
let constraint_of ?(subst = fun env t -> Logic.Term.subst env t) ~temp_param_senv ~ground
    ~atom_constr analysis (clause : ExClause.t) : Logic.term option =
  let renaming_sub =
    Map.Poly.map analysis.renaming ~f:(fun v -> Logic.Term.mk_var v)
  in
  let lit polarity a =
    let symbolic = is_symbolic analysis polarity a in
    let c = ptime 0 (fun () -> atom_constr ~symbolic polarity a) in
    if symbolic && not (Map.Poly.is_empty renaming_sub) then
      ptime 1 (fun () -> subst renaming_sub c)
    else c
  in
  let disj =
    Logic.BoolTerm.or_of
    @@ List.map (Set.to_list clause.ExClause.positive) ~f:(lit true)
    @ List.map (Set.to_list clause.ExClause.negative) ~f:(lit false)
  in
  let params = ExClause.params_of clause in
  let sub, kept =
    Map.Poly.fold params ~init:(Map.Poly.empty, Map.Poly.empty)
      ~f:(fun ~key ~data (sub, kept) ->
        if Map.Poly.mem analysis.vars key then (sub, kept)
        else
          match ground key (Logic.ExtTerm.of_old_sort data) with
          | Some t -> (Map.Poly.set sub ~key ~data:t, kept)
          | None -> (sub, Map.Poly.set kept ~key ~data))
  in
  let term =
    if Map.Poly.is_empty sub then disj
    else ptime 2 (fun () -> subst sub disj)
  in
  let bound =
    Map.Poly.merge_skewed ~combine:(fun ~key:_ a _ -> a) kept analysis.vars
  in
  let uni_senv =
    Map.Poly.merge_skewed
      ~combine:(fun ~key:_ a _ -> a)
      temp_param_senv
      (Logic.of_old_sort_env_map bound)
  in
  match
    let old = ptime 3 (fun () -> Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv term) in
    ptime 4 (fun () -> Evaluator.simplify old)
  with
  | exception exn_ when not (Common.Timer.is_async exn_) ->
      Atomic.incr declined_observation;
      None
  | phi -> (
      match
        match ptime 5 (fun () -> bind_open_terms ~prefix:"#oob_read_" ~temp_param_senv phi) with
        | No_open_term -> Some (phi, [])
        | Bound (phi, oob) -> Some (phi, oob)
        | Declined -> None
      with
      | None ->
          Atomic.incr declined_observation;
          None
      | Some (phi, oob) -> (
          let seqs =
            Map.Poly.filter bound ~f:(function
              | T_seq.SSeq _ -> true
              | _ -> false)
          in
          match ptime 6 (fun () -> abstract_observations seqs phi) with
          | None ->
              Atomic.incr declined_observation;
              None
          | Some (phi, fresh, premises) ->
              let binders =
                Map.Poly.to_alist
                  (Map.Poly.filteri bound ~f:(fun ~key ~data:_ ->
                       not (Map.Poly.mem seqs key)))
                @ oob @ fresh
              in
              let body =
                if List.is_empty premises then phi
                else Formula.mk_imply (Formula.and_of premises) phi
              in
              let result =
                if List.is_empty binders then body
                else Formula.forall binders body
              in
              if ptime 7 (fun () -> Z3Smt.Z3interface.may_not_return result) then (
                Atomic.incr declined_guard;
                None)
              else (
                Atomic.incr fired;
                Some (Logic.ExtTerm.of_old_formula result))))
