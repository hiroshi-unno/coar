(* Model-based projection of a formula onto a subset of its variables at a
   model, as MuCyc's refinement and MuStrat's chain-pair regions run it: the
   projection of Komuravelli, Gurfinkel and Chaki ("SMT-Based Model Checking
   for Recursive Programs", CAV 2014), per theory as Bjorner and Janota give it
   (LPAR-20, 2015) and as [Mbp] implements it, driven here -- the input reduced
   to the literals the model makes true, the conditionals and let-bound
   definitions inside terms handled by the two choices below, a failing rule
   falling back on the model's value, and the result optionally verified. *)

open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* How a conditional inside a term reaches the model-based projection, one of
   two independent axes (the other is [projection_lets]).  [All_paths] rewrites
   every conditional into the paths through it ([Formula.elim_ite]), which is
   exponential but gives the projection the branches the model does not take
   too; [All_paths_up_to n] does so while the result would have at most [n]
   nodes and follows the model's single path above.
   [Model_path_for_targets]: do not rewrite a conditional into the paths through it at all.
   A conditional is not a connective of the projection's language: A[ite (c, t, e)]
   stands for (c /\ A[t]) \/ (~c /\ A[e]), and rewriting an atom into those paths takes
   the product of the branches of each argument at every level, which on a word-level
   circuit is an atom with a thousand conditionals in it.  Here a conditional
   is instead replaced by the branch the model takes, with its condition conjoined as a
   literal -- a subterm for one of its own subterms, so the formula never grows and no
   bound is needed to keep it from growing.
   A conditional that mentions none of the variables being eliminated is carried
   through whole: what it denotes does not bear on the elimination, and asserting its
   condition would constrain the other variables for no gain.  One that mentions a
   variable being eliminated is settled, which does weaken the projection -- the models
   taking the other branch are left to other calls -- and that is the same bargain the
   projection's other rules make.  The test is applied to the whole conditional, its
   branches included, not to its condition alone.
   [All_paths_up_to n] also falls back on rewriting every branch where the model
   leaves a conditional open. *)
type projection_conditionals =
  | All_paths
  | All_paths_up_to of int
  | Model_path_for_targets
[@@deriving yojson]

(* How the let-bound definitions of a term reach the projection, the second
   axis.  [Inline_lets] inlines them.  [Name_subterms]:
   do not inline the let-bound definitions.  Inlining a definition into each of
   its uses is exponential in the sharing -- 1,837 nodes of one input became
   17,917,748 -- and a conditional left in place is copied along with it.  Here
   every compound subterm is given a fresh name instead and the naming stated as
   an equation, which is an equivalence and is linear in the shared form; the fresh
   variables are existential, so they are removed by the projection's own rule for
   several variables.  This is the definitional encoding of G. S. Tsejtin, "On the
   complexity of derivation in propositional calculus" (1968), taken at the level of
   terms rather than of propositions -- the same move an SMT preprocessor calls
   flattening.
   Each conditional is then settled against the model once, rather than once per use of
   it, the definitions nothing refers to any more are dropped, and a name whose
   definition mentions none of the variables being removed is left alone and
   substituted back once at the end.
   With [Name_subterms], [projection_conditionals] is read only where an atom the
   projection cannot normalise still holds a conditional, which
   [Model_path_for_targets] then resolves against the model; the other two choices
   are alike there.

   It is OFF although it is the better setting on a circuit, because a default is paid
   by every input and the gain is confined to one kind of them.  On the 330 word-level
   bit-vector problems it takes 32 answers to 42 and memory exhaustion from 66 to 3,
   and re-running every problem the two settings disagreed on -- three times each, at
   two and a half times the budget -- leaves 12 that only this answers against 2 that
   only the inlining does, nine of the twelve being inputs the inlining exhausts memory
   on every time.  But on 3,912 CHC-COMP25 problems outside bit-vectors it is slower
   across the board rather than only in a tail: the median of the ratio is 1.16 on the
   array category, 1.13 on the algebraic-datatype one and 1.05 on their combination,
   with a tail reaching 7, and at a 20 s budget that costs 27 answers.  Re-running the
   55 that differed, three times each at 90 s, leaves 11 against 6, which is no longer
   a difference -- so what it costs there is time rather than answers -- but a tax of
   five to sixteen per cent on every non-circuit input is not worth paying by default
   for a gain no non-circuit input sees.
   Turn it on for bit-vector work; `config/solver/mucyc_or_mbp1_bv.json` is that
   configuration.
   The two problems it does not answer and the inlining does are not a defect to fix:
   they need a literal about the branch the model did not take, and an encoding that
   separates the conditionals into different atoms cannot produce one in linear size.
   No answer differs between the two settings anywhere it has been measured -- 4,242
   problems, both settings, no wrong verdict and no disagreement -- and the
   projection's four conditions were checked under `check_validity` on both corpora.
   What would make it a default is deciding it per input rather than per run: the
   gain follows the bit-vector sorts, and nothing here looks at them. *)
(* [compare_branches], read only with [Name_subterms]:
   whether the projection says anything about the branch the model did not take.
   Settling a conditional against the model keeps its condition and the branch taken;
   the published rule signs every atom of the formula, and the naming makes the other
   branch one of them, so it survives as a comparison of the two branches.  That
   comparison is a strengthening of an input that already implies the original, so it
   is optional: unset, the projection covers more models and says less about each.
   What it costs is that the other branch is referred to and so cannot be dropped,
   which puts its whole cone back into the result.
   It is off because it was measured: over the 79 problems at the boundary of the
   bit-vector corpus it gained no answer and cost four, and the reason is the kind of
   literal rather than the number.  What the exhaustive rewriting keeps is the original
   predicate evaluated at the other branch -- a comparison, which bounds an interval --
   while this keeps a comparison of the two branches, which under a model that makes
   them differ is a disequality, the weakest literal there is; on one input 5,242 of
   5,766 of them were disequalities. *)
(* [substitute_tainted], read only with [Name_subterms]:
   whether the names that have to be removed are removed by substituting their
   definitions before the projection's rules run, rather than one at a time by the
   rules.  A name [n] has exactly one definition [d] with [n] not free in [d], so
   [exists n. (n = d /\ phi)] is [phi[d/n]] in every model: the substitution is an
   exact elimination that does not consult the model, and the rules then see only the
   caller's variables.  The rules otherwise remove each name by solving its defining
   equation and normalize every atom again around each such step, which is where the
   projection's time goes on the bit-vector circuits.  What it gives up is the sharing
   the names carry: the substituted terms are trees. *)
type projection_lets =
  | Inline_lets
  | Name_subterms of {
      compare_branches : bool; [@default false]
      substitute_tainted : bool; [@default false]
    }
[@@deriving yojson]

(* a named phase of the run's time account, when [COAR_PHASE_TIME] is set *)
let phase_time = Common.PhaseTime.with_phase

(* The number of nodes of a set of literals, counting a shared subterm once per
   occurrence (the size of the printed literals), and whether it exceeds [bound],
   which stops counting as soon as it does. *)
exception Larger

let atoms_count_upto bound atoms =
  let n = ref 0 in
  let tick () =
    incr n;
    if !n > bound then raise Larger
  in
  let rec term = function
    | Term.Var _ -> tick ()
    | Term.FunApp (sym, args, _) ->
        tick ();
        (match sym with T_bool.Formula phi -> formula phi | _ -> ());
        List.iter args ~f:term
    | Term.LetTerm (_, _, def, body, _) ->
        tick ();
        term def;
        term body
  and atom = function
    | Atom.True _ | Atom.False _ -> tick ()
    | Atom.App (_, args, _) ->
        tick ();
        List.iter args ~f:term
  and formula = function
    | Formula.Atom (a, _) -> atom a
    | Formula.UnaryOp (_, phi, _) | Formula.Bind (_, _, phi, _) ->
        tick ();
        formula phi
    | Formula.BinaryOp (_, phi1, phi2, _) ->
        tick ();
        formula phi1;
        formula phi2
    | Formula.LetRec (_, phi, _) ->
        tick ();
        formula phi
    | Formula.LetFormula (_, _, def, body, _) ->
        tick ();
        term def;
        formula body
  in
  Set.iter atoms ~f:atom;
  !n

(* the node count of [atoms] if it is at most [bound] *)
let atoms_size_upto bound atoms =
  try Some (atoms_count_upto bound atoms) with Larger -> None

(* With COAR_MUCYC_MBP_SIZE set, each projection prints one [mbp-size:] line to
   stderr: how many variables it removes, and the number of literals and their
   node count (as trees, stopped at 10^8 and printed as [>1e8]) before and after
   the elimination loop.  Observation only; off, it is one boolean test per
   projection. *)
let mbp_size_trace = Option.is_some (Sys.getenv "COAR_MUCYC_MBP_SIZE")

let mbp_size_str atoms =
  match atoms_size_upto 100_000_000 atoms with
  | Some n -> string_of_int n
  | None -> ">1e8"

(* With COAR_MUCYC_PHASE_TIME set, each step of the projection loop that removes a
   bit-vector variable [x] counts, as events of that account, the literals mentioning
   [x] that have the shape the BTOR2 reductions take after translation to CHC:
   - [mbp-red-zero]: a comparison (=, <>, or an unsigned/signed order) of a term of width
     at least 2 that mentions [x] with the constant 0.  redor(t) = 1 is t <> 0; but any
     comparison of a word with 0 has the same shape, so this bounds redor from above.
   - [mbp-red-ones]: the same with the all-ones constant (redand(t) = 1 is t = 1...1).
   - [mbp-red-xor]: a literal containing an xor one of whose operands is a 1-bit
     slice of a term of width at least 2 that mentions [x] (redxor(t) is the xor of t's
     bits, which the translation spells out slice by slice).
   [mbp-red-step] counts the steps over a bit-vector variable and [mbp-red-step-hit] the
   ones with at least one such literal; [mbp-red-call] and [mbp-red-call-hit] count the
   same per projection.  Observation only: nothing here changes what is projected. *)
let red_shapes ~bv ~hit x atoms1 =
  let open Common.PhaseTime in
  let width t =
    match Term.sort_of t with T_bv.SBV (Some w) -> w | _ -> 0
  in
  let mentions t = Set.mem (Term.fvs_of t) x in
  let const t =
    match t with
    | Term.FunApp (T_bv.BVNum (Some w, n), [], _) ->
        if Z.equal n Z.zero then `Zero
        else if Z.equal n (Z.pred (Z.shift_left Z.one w)) then `Ones
        else `Other
    | _ -> `Other
  in
  let is_cmp = function
    | T_bool.Eq | T_bool.Neq
    | T_bv.BVLeq _ | T_bv.BVGeq _ | T_bv.BVLt _ | T_bv.BVGt _ ->
        true
    | _ -> false
  in
  let xor_found = ref false in
  let any = ref false in
  bv := true;
  event "mbp-red-step";
  Set.iter atoms1 ~f:(fun atom ->
      (match atom with
       | Atom.App (Predicate.Psym p, [ t1; t2 ], _) when is_cmp p -> (
           let side c t = if width t >= 2 && mentions t then c else `Other in
           match
             (match const t1 with `Other -> side (const t2) t1 | c -> side c t2)
           with
           | `Zero ->
               any := true;
               event "mbp-red-zero"
           | `Ones ->
               any := true;
               event "mbp-red-ones"
           | `Other -> ())
       | _ -> ());
      xor_found := false;
      Atom.iter_term atom ~f:(function
        | Term.FunApp (T_bv.BVXor _, args, _) ->
            if
              List.exists args ~f:(function
                | Term.FunApp (T_bv.BVEXTRACT (_, h, l), [ t ], _) ->
                    h = l && width t >= 2 && mentions t
                | _ -> false)
            then xor_found := true
        | _ -> ());
      if !xor_found then (
        any := true;
        event "mbp-red-xor"));
  if !any then (
    hit := true;
    event "mbp-red-step-hit")

(* The same shapes counted once per projection on its input [phi], before any
   rewriting (conditionals, let-bindings and the naming of subterms all still in
   place): [mbp-red-in-zero], [mbp-red-in-ones] count the comparisons with 0 and with
   all ones of a term of width at least 2 that mentions a variable of [targets];
   [mbp-red-in-xor] counts the 1-bit xors of two 1-bit slices of terms of width at least
   2, one of which mentions a variable of [targets] -- the innermost node of the chain a
   redxor is translated to, so one per redxor.  A let-bound variable mentions a target
   when its definition does.  [mbp-red-in-any-{zero,ones,xor}] count the same shapes
   whether or not they mention a target.  [mbp-red-in-call] counts the projections and
   [mbp-red-in-call-{zero,ones,xor}] the ones with at least one literal of that kind
   mentioning a target.  Observation only. *)
let red_input ~targets phi =
  let open Common.PhaseTime in
  let zero = ref 0 and ones = ref 0 and xor = ref 0 in
  let any_zero = ref 0 and any_ones = ref 0 and any_xor = ref 0 in
  let width t = match Term.sort_of t with T_bv.SBV (Some w) -> w | _ -> 0 in
  let const = function
    | Term.FunApp (T_bv.BVNum (Some w, n), [], _) ->
        if Z.equal n Z.zero then `Zero
        else if Z.equal n (Z.pred (Z.shift_left Z.one w)) then `Ones
        else `Other
    | _ -> `Other
  in
  let is_cmp = function
    | T_bool.Eq | T_bool.Neq
    | T_bv.BVLeq _ | T_bv.BVGeq _ | T_bv.BVLt _ | T_bv.BVGt _ ->
        true
    | _ -> false
  in
  (* the widths carried by the symbols are not relied on: a parsed term may leave them
     to the sort of its operand *)
  let is_slice1 = function
    | Term.FunApp (T_bv.BVEXTRACT (_, h, l), [ t ], _) -> h = l && width t >= 2
    | _ -> false
  in
  (* whether [t] mentions a target, counting the shapes met on the way *)
  let rec term env t =
    match t with
    | Term.Var (v, _, _) -> (
        match Map.Poly.find env v with
        | Some b -> b
        | None -> Set.mem targets v)
    | Term.LetTerm (v, _, def, body, _) ->
        let b = term env def in
        term (Map.Poly.set env ~key:v ~data:b) body
    | Term.FunApp (T_bool.Formula phi, [], _) -> formula env phi
    | Term.FunApp (fsym, args, _) ->
        let ms = List.map args ~f:(term env) in
        (match fsym with
         | T_bv.BVXor _ when List.count args ~f:is_slice1 >= 2 ->
             incr any_xor;
             if List.exists2_exn args ms ~f:(fun a m -> m && is_slice1 a) then
               incr xor
         | _ -> ());
        List.exists ms ~f:Fn.id
  and formula env = function
    | Formula.Atom (Atom.App (Predicate.Psym p, [ t1; t2 ], _), _) when is_cmp p ->
        let m1 = term env t1 in
        let m2 = term env t2 in
        let c, t, m =
          match const t1 with `Other -> (const t2, t1, m1) | c -> (c, t2, m2)
        in
        (if width t >= 2 then
           match c with
           | `Zero ->
               incr any_zero;
               if m then incr zero
           | `Ones ->
               incr any_ones;
               if m then incr ones
           | `Other -> ());
        m1 || m2
    | Formula.Atom (Atom.App (_, args, _), _) ->
        List.fold args ~init:false ~f:(fun acc t -> term env t || acc)
    | Formula.Atom _ -> false
    | Formula.UnaryOp (_, phi, _) | Formula.Bind (_, _, phi, _) -> formula env phi
    | Formula.BinaryOp (_, phi1, phi2, _) ->
        let m1 = formula env phi1 in
        let m2 = formula env phi2 in
        m1 || m2
    | Formula.LetFormula (v, _, def, body, _) ->
        let b = term env def in
        formula (Map.Poly.set env ~key:v ~data:b) body
    | Formula.LetRec _ -> false
  in
  ignore (formula Map.Poly.empty phi);
  event "mbp-red-in-call";
  List.iter
    [ ("zero", !zero); ("ones", !ones); ("xor", !xor) ]
    ~f:(fun (k, n) ->
      if n > 0 then event ("mbp-red-in-call-" ^ k);
      for _ = 1 to n do
        event ("mbp-red-in-" ^ k)
      done);
  List.iter
    [ ("zero", !any_zero); ("ones", !any_ones); ("xor", !any_xor) ]
    ~f:(fun (k, n) ->
      for _ = 1 to n do
        event ("mbp-red-in-any-" ^ k)
      done)

(* Model-based projection of [phi0] onto the variables outside [eliminated0],
   at the model [model0] (which need not assign every variable: the rest is
   completed by one satisfiability call).  Postcondition: the result is
   satisfied by the completed model and implies the existential closure of
   [phi0] over [eliminated0]; a variable whose projection rule fails is
   substituted by its model value, which keeps both halves.  With
   [check_validity] a failing rule is raised instead and the result is
   verified by the four checks at the end.  [conditionals] and [lets] are the two
   independent choices of how a conditional inside a term reaches the projection
   (see [projection_conditionals] and [projection_lets] above);
   [All_paths_up_to] bounds the exhaustive conditional elimination by
   [Mbp.ite_blowup_upto].  An integer quotient or remainder of any rounding mode
   (Euclidean, truncated, flooring, ceiling) is read in its own mode: both paths
   below remove it with [Formula.rm_div_mod], which gives each mode's operation a
   fresh pair under that mode's exact axioms, so no rewriting of the input is due
   here; a projection that read a truncated remainder as the Euclidean one need not
   imply the existential. *)
(* The optional argument repeats the configuration's default, so that a caller which
   reaches this directly rather than through [get_mbp] gets what the shipped
   configuration gets unless it says otherwise.  They were allowed to differ once and
   the one such caller then had the old behaviour by accident. *)
let get_mbp_with ~conditionals ?(lets = Inline_lets)
    ?(bv_reuse_unchanged_prepass = false) ?(bv_normalize_once = false)
    ?(bv_joint_alias_in_projection = false)
    ~check_validity ~print model0 eliminated0 phi0 =
  let resolve_ite_in_projection =
    match conditionals with Model_path_for_targets -> true | _ -> false
  in
  if Set.is_empty eliminated0 then phi0
  else (
    print @@ lazy ("\nMBP input: " ^ Formula.str_of phi0);
    print
    @@ lazy
         ("eliminated: "
         ^ str_of_sort_env_list Term.str_of_sort
         @@ Set.to_list eliminated0);
    print
    @@ lazy
         ("model: "
         ^ String.concat_map_list ~sep:", " (Map.Poly.to_alist model0)
             ~f:(function Ident.Tvar tvar, value ->
               sprintf "%s |-> %s" tvar (Term.str_of value)));
    let senv = Set.to_list @@ Formula.sort_env_of phi0 in
    (* [extend_model model phi]: [model] extended to every free variable of [phi].

       Pre: [model] maps variables to ground terms, and [phi] under [model] does
       not simplify to false (that raises).
       Post: the result agrees with [model] on the domain of [model] and binds
       every free variable of [phi] whose sort has a default value.  When [phi]
       under [model] simplifies to a ground formula, that formula alone decides
       whether the result satisfies [phi] (it does when the formula is true);
       otherwise the variables still free are given a model of the rest by one
       satisfiability call, and the result satisfies [phi].
       Why every free variable: the projection reads the sign of every atom of
       [phi] at the result, and the rule removing a variable looks its value up,
       so an atom over a variable the result does not bind cannot be read.
       Substituting [model] and simplifying drops a variable that occurs only in
       a disjunct the model falsifies (or beside a disjunct the model makes
       true), so neither the ground case nor the satisfiability call asked for
       it: [(x = 0 /\ y > 0) \/ z = 1] at x = 1, z = 1 left y unbound and the
       projection raised "y is not bound".  Such a variable does not bear on
       the truth of [phi] at the model (simplification preserves meaning), so
       any value of its sort keeps the result a model of [phi]; the sort's
       default value is taken.  A sort with no default value leaves the
       variable unbound, as before. *)
    let extend_model model phi =
      let complete model =
        Set.fold (Formula.term_sort_env_of phi) ~init:model
          ~f:(fun model (x, s) ->
            if Map.Poly.mem model x then model
            else
              match Term.mk_dummy s with
              | t -> Map.Poly.set model ~key:x ~data:t
              | exception exn_ when not (Common.Timer.is_async exn_) -> model)
      in
      let phi' = Evaluator.simplify @@ Formula.subst model phi in
      if Formula.is_false phi' then
        failwith "MBP model cannot be extended to the formula"
      else if Formula.is_ground phi' then complete model
      else
        match
          Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ()) [ phi' ]
        with
        | `Sat sub ->
            complete @@ Map.force_merge model @@ Map.Poly.of_alist_exn
            @@ List.map sub ~f:(function
              | (x, _s), Some t -> (x, t)
              | (x, s), None -> (x, Term.mk_dummy s))
        | `Unsat -> failwith "Unreachable here"
        | _ -> failwith "Z3 timeout/unknown"
    in
    let phi_bounded = Formula.mk_exists_if_bounded senv phi0 in
    if !Common.PhaseTime.on then (
      let rec prefix acc = function
        | Formula.Bind (Formula.Exists, senv', phi, _) ->
            prefix (List.map senv' ~f:fst @ acc) phi
        | _ -> acc
      in
      red_input
        ~targets:
          (Set.union
             (Set.Poly.map eliminated0 ~f:fst)
             (Set.Poly.of_list @@ prefix [] phi_bounded))
        phi_bounded);
    (* [Formula.elim_ite] enumerates every path through the conditionals of an atom, which
       is exponential but gives the projection the branches the model does not take too.
       Keep it while the size it would produce is affordable, follow the model's single
       path above. *)
    let elim_ite =
      if resolve_ite_in_projection then (
        (* the model has to cover the input before the rewriting consults it.
           [extend_model] adds free variables only ([Formula.term_sort_env_of] leaves
           out what a quantifier, a let or an array lambda binds), so a name bound
           inside [phi0] is in the model only when it also occurs free in [phi0] or
           the caller's model already holds it.  The rewriting below does not read
           the model under a binder for the bound names; the callers do not rely on
           that: the SMT-LIB reader renames a binder that shadows an enclosing
           variable and gives every lambda a fresh parameter, MuCyc renames bound
           variables fresh, and PCSat's regions complete the model over the free
           variables of the formula they project. *)
        let model0 = extend_model model0 phi0 in
        (* which variables this call is about to remove: the ones the caller named, plus
           the ones the existential prefix below binds.  A conditional mentioning none of
           them is carried through whole, where leaving it alone is free; one that
           mentions any of them is settled here.  The test below is asked about the whole
           conditional, branches included, not about its condition alone. *)
        let targets =
          (* peel the existential prefix by hand: [Formula.split_quantifiers] refuses a
             formula that still carries let-bindings, and this runs before they are
             inlined -- it used to be called here and raised on every input, which put
             the whole projection into its caller's fallback without a word *)
          let rec prefix acc = function
            | Formula.Bind (Formula.Exists, senv', phi, _) ->
                prefix (List.map senv' ~f:fst @ acc) phi
            | _ -> acc
          in
          Set.union
            (Set.Poly.map eliminated0 ~f:fst)
            (Set.Poly.of_list @@ prefix [] phi_bounded)
        in
        fun phi ->
          Mbp.elim_ite_with_model ~lenient:true model0 phi
            ~keep:(fun t -> Set.is_empty @@ Set.inter (Term.fvs_of t) targets))
      else if
        match conditionals with
        | All_paths_up_to limit ->
            Mbp.ite_blowup_upto (limit + 1) phi_bounded <= limit
        | _ -> true
      then Formula.elim_ite
      else
        (* the model has to cover the input before the rewriting consults it *)
        let model0 = extend_model model0 phi0 in
        fun phi ->
          try Mbp.elim_ite_with_model model0 phi
          with Mbp.IteModelUndetermined ->
            print
            @@ lazy
                 "the model leaves a conditional open; falling back on rewriting every \
                  branch";
            Formula.elim_ite phi
    in
    (* Naming the compound subterms instead of inlining the let-bound definitions.
       Everything up to the naming is what the other path does; [elim_ite] and
       [elim_let], the two steps that multiply, are what it replaces.  The result is
       carried in pieces rather than as one formula, because which of the names have to
       be removed is decided from the definitions and cannot be read off the formula
       once they are conjoined. *)
    let flat =
      match lets with
      | Inline_lets -> None
      | Name_subterms { compare_branches; substitute_tainted } ->
        let model0 = extend_model model0 phi0 in
        let flat =
          phase_time "flatten" @@ fun () ->
          let pre =
            Mbp.Flat.fold_ground
            @@ Normalizer.normalize_let ~rename:true
            @@ Normalizer.normalize @@ Formula.rm_div_mod @@ Normalizer.normalize
            @@ phi_bounded
          in
          (* the quotient and remainder variables [rm_div_mod] introduces are not in
             the caller's model; without values for them no conditional whose
             condition mentions one can be settled, and no subterm mentioning one can
             be valued, so the model is extended over the matrix first *)
          let model0 = extend_model model0 (snd @@ Mbp.Flat.peel_exists pre) in
          Mbp.Flat.flatten model0 pre
        in
        (* Which variables this call is about to remove: the ones the caller named, plus
           whatever the preprocessing above bound on top of them -- the quotient and
           remainder variables of [rm_div_mod].  Not the whole prefix: the input is
           closed by binding every free variable of it, so the prefix is all of them, and
           reading it as the set to remove would mark every definition in the circuit as
           one that has to go.  What stays free is exactly the predicate's own arguments,
           and a definition that depends only on those is left alone. *)
        let targets =
          Set.union (Set.Poly.map eliminated0 ~f:fst)
          @@ Set.diff
               (Set.Poly.of_list @@ List.map flat.Mbp.Flat.prefix ~f:fst)
               (Set.Poly.of_list @@ List.map senv ~f:fst)
        in
        let flat, tainted =
          phase_time "settle" @@ fun () ->
          Mbp.Flat.settle ~compare_branches targets
            flat
        in
        Some (Mbp.Flat.prune flat, tainted, substitute_tainted)
    in
    let phi, eliminated, order, expand =
      match flat with
      | None ->
          let bounds, phi =
            Formula.split_quantifiers @@ Evaluator.simplify
            @@ LogicOld.Formula.elim_let
            @@ Normalizer.normalize_let ~rename:true
            @@ Normalizer.normalize @@ Formula.rm_div_mod
            @@ Normalizer.normalize @@ elim_ite phi_bounded
          in
          let eliminated =
            Set.Poly.union_list
            @@ eliminated0
               :: List.map bounds ~f:(function
                 | Formula.Exists, senv' ->
                     Set.(diff (Poly.of_list senv') (Set.Poly.of_list senv))
                 | _ -> failwith "Universal quantifies are not supported")
          in
          (phi, eliminated, Set.to_list eliminated, Fn.id)
      | Some (flat, tainted, substitute_tainted) ->
          let bound =
            Set.diff
              (Set.Poly.of_list flat.Mbp.Flat.prefix)
              (Set.Poly.of_list senv)
          in
          let is_tainted (x, _, _) = Set.mem tainted x in
          let tainted_defs, pure_defs =
            List.partition_tf flat.Mbp.Flat.defs ~f:is_tainted
          in
          print
          @@ lazy
               (sprintf
                  "definitional form: %d definitions, %d of them to remove, %d \
                   guards, %d branch comparisons"
                  (List.length flat.Mbp.Flat.defs)
                  (List.length tainted_defs)
                  (List.length flat.Mbp.Flat.guards)
                  (List.length flat.Mbp.Flat.facts));
          (* With [substitute_tainted] the names to remove are substituted away here,
             innermost first, so that neither the formula nor the order below mentions
             them; a name has one definition and is not free in it, so this is an exact
             elimination.  The definitions not to remove mention no such name (a
             definition is marked as soon as anything below it is), so [expand] at the
             end still sees a closed set. *)
          let phi =
            if substitute_tainted then
              let sub =
                phase_time "subst-tainted" @@ fun () ->
                List.fold tainted_defs ~init:Map.Poly.empty
                  ~f:(fun sub (x, _, def) ->
                    Map.Poly.set sub ~key:x ~data:(Term.subst sub def))
              in
              let subst phi =
                if Map.Poly.is_empty sub then phi else Formula.subst sub phi
              in
              Formula.and_of
              @@ (subst flat.Mbp.Flat.body
                 :: Mbp.minimize_guards
                      (List.map ~f:subst
                         (flat.Mbp.Flat.guards @ flat.Mbp.Flat.facts)))
            else
              Formula.and_of
              @@ (flat.Mbp.Flat.body
                 :: (Mbp.minimize_guards
                       (flat.Mbp.Flat.guards @ flat.Mbp.Flat.facts)
                    @ List.map tainted_defs ~f:Mbp.Flat.def_atom))
          in
          let names =
            if substitute_tainted then []
            else List.map tainted_defs ~f:(fun (x, s, _) -> (x, s))
          in
          let eliminated =
            Set.union (Set.union eliminated0 bound) (Set.Poly.of_list names)
          in
          (* The names first, innermost first, and the caller's variables after them.
             The order is forced rather than chosen.  A name has exactly one defining
             equation, so a rule can always remove it, but the rule that removes one of
             the caller's variables reads every literal that mentions it -- the defining
             equation included -- and what it returns need not be an equation for that
             name any more.  Worse, the defining equation is itself an equation in the
             variable being removed, so it is exactly what such a rule reaches for: on
             [b = bvadd (x, a)] it solves for x, consumes the equation, and leaves b with
             no definition and nothing to substitute.  A name whose definition mentions
             one of the variables being removed therefore has to go first.  A name whose
             definition mentions none of them is in no such literal, is touched by no
             rule, and is put back by [expand] at the end. *)
          ( phi,
            eliminated,
            names @ Set.to_list (Set.union eliminated0 bound),
            Mbp.Flat.expand { flat with Mbp.Flat.defs = pure_defs } )
    in
    print @@ lazy ("preprocessed input: " ^ Formula.str_of phi);
    if false then
      print
      @@ lazy
           ("eliminated': "
           ^ str_of_sort_env_list Term.str_of_sort
           @@ Set.to_list eliminated);
    let model =
      phase_time "extend-model" @@ fun () ->
      extend_model
        (match flat with
        | None -> model0
        | Some (flat, _, _) -> flat.Mbp.Flat.model)
        phi
    in
    if false then
      print
      @@ lazy
           ("model': "
           ^ String.concat_map_list ~sep:", " (Map.Poly.to_alist model)
               ~f:(function Ident.Tvar tvar, value ->
                 sprintf "%s |-> %s" tvar (Term.str_of value)));
    let atoms =
      phase_time "atoms" @@ fun () ->
      let tatoms, fatoms = Formula.atoms_of ~nrec:true phi in
      Set.concat_map
        ~f:
          (Mbp.normalize_mbp model
          >> Set.Poly.map
               ~f:(Mbp.sign ~print model >> Formula.let_atom (*ToDo*) >> fst))
      @@ Set.union tatoms fatoms
    in
    let res =
      let rec preprocess atoms =
        Set.concat_map atoms ~f:(function
          | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _)
            when T_irb.is_sint_sreal t1 ->
              Set.Poly.singleton
              @@
              if
                Value.gt
                  (Evaluator.eval_term @@ Term.subst model t1)
                  (Evaluator.eval_term @@ Term.subst model t2)
              then
                Normalizer.normalize_atom
                @@
                if T_int.is_sint t1 then T_int.mk_gt t1 t2
                else T_real.mk_rgt t1 t2
              else
                Normalizer.normalize_atom
                @@
                if T_int.is_sint t1 then T_int.mk_gt t2 t1
                else T_real.mk_rgt t2 t1
          | Atom.App
              ( Predicate.Psym T_bool.Eq,
                [
                  (Term.Var (_, s, _) as tx);
                  Term.FunApp (T_bool.Formula phi, [], _);
                ],
                _ )
            when Term.is_bool_sort s
                 && Set.exists ~f:(snd >> Term.is_bool_sort >> not)
                    @@ Formula.term_sort_env_of phi ->
              if
                Value.is_true @@ Evaluator.eval_term
                @@ Map.Poly.find_exn model (Term.tvar_of tx)
              then
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model phi)
                @@ Atom.of_bool_term tx
              else
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model @@ Evaluator.simplify_neg phi)
                @@ Atom.of_neg_bool_term tx
          | Atom.App
              ( Predicate.Psym T_bool.Eq,
                [
                  Term.FunApp (T_bool.Formula phi, [], _);
                  (Term.Var (_, s, _) as tx);
                ],
                _ )
            when Term.is_bool_sort s
                 && Set.exists ~f:(snd >> Term.is_bool_sort >> not)
                    @@ Formula.term_sort_env_of phi ->
              if
                Value.is_true @@ Evaluator.eval_term
                @@ Map.Poly.find_exn model (Term.tvar_of tx)
              then
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model phi)
                @@ Atom.of_bool_term tx
              else
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model @@ Evaluator.simplify_neg phi)
                @@ Atom.of_neg_bool_term tx
          | Atom.App
              ( Predicate.Psym T_bool.Neq,
                [
                  (Term.Var (_, s, _) as tx);
                  Term.FunApp (T_bool.Formula phi, [], _);
                ],
                _ )
            when Term.is_bool_sort s
                 && Set.exists ~f:(snd >> Term.is_bool_sort >> not)
                    @@ Formula.term_sort_env_of phi ->
              if
                Value.is_true @@ Evaluator.eval_term
                @@ Map.Poly.find_exn model (Term.tvar_of tx)
              then
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model @@ Evaluator.simplify_neg phi)
                @@ Atom.of_bool_term tx
              else
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model phi)
                @@ Atom.of_neg_bool_term tx
          | Atom.App
              ( Predicate.Psym T_bool.Neq,
                [
                  Term.FunApp (T_bool.Formula phi, [], _);
                  (Term.Var (_, s, _) as tx);
                ],
                _ )
            when Term.is_bool_sort s
                 && Set.exists ~f:(snd >> Term.is_bool_sort >> not)
                    @@ Formula.term_sort_env_of phi ->
              if
                Value.is_true @@ Evaluator.eval_term
                @@ Map.Poly.find_exn model (Term.tvar_of tx)
              then
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model @@ Evaluator.simplify_neg phi)
                @@ Atom.of_bool_term tx
              else
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model phi)
                @@ Atom.of_neg_bool_term tx
          | atm -> Set.Poly.singleton atm)
      in
      (* whether a step of this projection removed a bit-vector variable, and whether
         one met a literal of [red_shapes] *)
      let red_bv = ref false and red_hit = ref false in
      let is_looping =
        let prev = ref ("", Set.Poly.empty) in
        fun x atoms ->
          if Set.equal (snd !prev) atoms then
            String.(Ident.name_of_tvar x = fst !prev)
          else (
            prev := (Ident.name_of_tvar x, atoms);
            false)
      in
      Evaluator.simplify @@ Normalizer.normalize @@ Formula.and_of
      @@ Set.to_list
      @@ Set.Poly.map ~f:Formula.mk_atom
      @@
      (* Which atoms mention which variable, so that selecting the atoms one elimination
         step has to look at does not sweep the whole set.  Recomputing the free variables
         of every atom on every step is the shape that hurts: a projection with a few
         hundred variables to remove over a few hundred atoms spent nearly two thirds of
         its time there, while the atoms it actually rewrote were two or three.  Only
         variables still to be eliminated need an entry; the index is repaired from the
         atoms each step removes and adds. *)
      let index_of targets atoms =
        Set.fold atoms ~init:Map.Poly.empty ~f:(fun idx atm ->
            Set.fold (Set.inter (Atom.fvs_of atm) targets) ~init:idx ~f:(fun idx v ->
                Map.Poly.update idx v ~f:(function
                  | None -> Set.Poly.singleton atm
                  | Some s -> Set.add s atm)))
      in
      let reindex targets idx ~removed ~added =
        let upd idx f atms =
          Set.fold atms ~init:idx ~f:(fun idx atm ->
              Set.fold (Set.inter (Atom.fvs_of atm) targets) ~init:idx
                ~f:(fun idx v -> f idx v atm))
        in
        upd
          (upd idx
             (fun idx v atm ->
               Map.Poly.change idx v ~f:(function
                 | None -> None
                 | Some s ->
                     let s = Set.remove s atm in
                     if Set.is_empty s then None else Some s))
             removed)
          (fun idx v atm ->
            Map.Poly.update idx v ~f:(function
              | None -> Set.Poly.singleton atm
              | Some s -> Set.add s atm))
          added
      in
      let order_has_duplicates =
        List.length order <> Set.length (Set.Poly.map ~f:fst eliminated)
      in
      (* the literals the bit-vector projection returned in normal form during this
         projection, which it does not normalize again ([bv_normalize_once]); local to
         the call *)
      let known =
        if bv_normalize_once then Some (Mbp.BV.known_create ()) else None
      in
      (* [bv_joint_alias_in_projection]: when the variable about to be removed is a
         bit-vector variable with a literal x = y or x = c, every variable still to be
         removed that has such a literal goes in one step.  The bindings are taken one
         literal at a time with the bindings so far applied, so they are triangular and
         compose into one substitution; of the two sides of x = y both still to be
         removed, the one earlier in the order is bound, as the one-at-a-time path would
         bind it.  Each binding is (exists x. x = t /\ phi) <-> phi[t/x] with x not in t,
         every literal is true in the model, so the model still satisfies the result,
         and the literals that mention a bound variable are normalized once instead of
         once per binding. *)
      let alias_side targets = function
        | Term.Var (v, T_bv.SBV _, _) -> Set.mem targets v
        | _ -> false
      in
      let alias_term = function
        | Term.Var (_, T_bv.SBV _, _) | Term.FunApp (T_bv.BVNum _, [], _) -> true
        | _ -> false
      in
      let alias_lit targets = function
        | Atom.App (Predicate.Psym T_bool.Eq, [ l; r ], _) ->
            alias_term l && alias_term r
            && (alias_side targets l || alias_side targets r)
        | _ -> false
      in
      let joint_alias targets idx eliminated atoms =
        match eliminated with
        | (x, T_bv.SBV _) :: _
          when Option.value_map (Map.Poly.find idx x) ~default:false
                 ~f:(Set.exists ~f:(fun a ->
                     alias_lit (Set.Poly.singleton x) a)) ->
            phase_time "joint-alias" @@ fun () ->
            let pos = Hashtbl.Poly.create () in
            List.iteri eliminated ~f:(fun i (v, _) ->
                ignore (Hashtbl.add pos ~key:v ~data:i : [ `Ok | `Duplicate ]));
            let pos v = Option.value ~default:Int.max_value (Hashtbl.find pos v) in
            let sub, bindings, defs =
              Set.fold (Set.filter atoms ~f:(alias_lit targets))
                ~init:(Map.Poly.empty, [], Set.Poly.empty)
                ~f:(fun (sub, bindings, defs) atom ->
                  match atom with
                  | Atom.App (_, [ l; r ], _) -> (
                      let l = Term.subst sub l and r = Term.subst sub r in
                      let bind v t =
                        let one = Map.Poly.singleton v t in
                        ( Map.Poly.add_exn ~key:v ~data:t
                            (Map.Poly.map sub ~f:(Term.subst one)),
                          (v, t) :: bindings,
                          Set.add defs atom )
                      in
                      match (l, r) with
                      | Term.Var (v, _, _), Term.Var (u, _, _)
                        when Ident.tvar_equal v u ->
                          (sub, bindings, Set.add defs atom)
                      | Term.Var (v, _, _), Term.Var (u, _, _)
                        when alias_side targets l && alias_side targets r ->
                          if pos v <= pos u then bind v r else bind u l
                      | Term.Var (v, _, _), _ when alias_side targets l -> bind v r
                      | _, Term.Var (u, _, _) when alias_side targets r -> bind u l
                      | _ -> (sub, bindings, defs))
                  | _ -> (sub, bindings, defs))
            in
            if Map.Poly.is_empty sub then None
            else
              let receivers =
                Set.diff
                  (Set.Poly.union_list
                  @@ List.filter_map (Map.Poly.keys sub) ~f:(Map.Poly.find idx))
                  defs
              in
              List.iter bindings ~f:(fun _ -> phase_time "joint-alias-bound" Fn.id);
              let res =
                Set.concat_map receivers
                  ~f:(Atom.subst sub >> Mbp.normalize_mbp model)
              in
              let targets = Set.diff targets (Map.key_set sub) in
              let idx =
                reindex targets
                  (Map.Poly.filter_keys idx ~f:(Fn.non (Map.Poly.mem sub)))
                  ~removed:(Set.union defs receivers) ~added:res
              in
              Some
                ( targets,
                  idx,
                  List.filter eliminated ~f:(fun (v, _) -> not (Map.Poly.mem sub v)),
                  Set.union (Set.diff atoms (Set.union defs receivers)) res )
        | _ -> None
      in
      let rec loop targets idx eliminated atoms =
        match
          if bv_joint_alias_in_projection then joint_alias targets idx eliminated atoms
          else None
        with
        | Some (targets, idx, eliminated, atoms) ->
            loop targets idx eliminated atoms
        | None -> step targets idx eliminated atoms
      and step targets idx eliminated atoms =
        match eliminated with
        | [] -> atoms
        | (x, s) :: eliminated' -> (
            if true then
              (*Out_channel.output_char stdout '.';*)
              print
              @@ lazy
                   ("eliminating " ^ Ident.name_of_tvar x ^ " in\n"
                   ^ String.concat_map_set ~sep:"\n" ~f:Atom.str_of atoms);
            let atoms1 =
              Option.value ~default:Set.Poly.empty @@ Map.Poly.find idx x
            in
            (match s with
             | T_bv.SBV _ when !Common.PhaseTime.on ->
                 red_shapes ~bv:red_bv ~hit:red_hit x atoms1
             | _ -> ());
            (* Observation only: the phase account counts the steps that remove a name
               given by [Mbp.Flat.flatten] apart from those removing one of the
               caller's variables, by how many literals the step reads (a name read by
               its definition alone is removed by dropping that literal). *)
            phase_time
              (sprintf "step-%s-%s"
                 (if String.is_prefix (Ident.name_of_tvar x) ~prefix:"#df" then
                    "name"
                  else "var")
                 (match Set.length atoms1 with
                 | (0 | 1 | 2 | 3) as n -> string_of_int n
                 | _ -> "4+"))
              Fn.id;
            let atoms2 = phase_time "diff" (fun () -> Set.diff atoms atoms1) in
            (* The theory rules read the shape of a literal -- which side the variable
               is on, its coefficient, whether a bit-vector atom is a mask -- so a
               conditional still inside one has to be settled before a rule sees it.
               Only in these: the atoms of [atoms2] do not mention the variable and
               travel on untouched, conditionals and all, which is what the projection's
               own definition says to do with them. *)
            (* A conditional that mentions none of the variables being eliminated was
               carried through the preprocessing as one opaque term, because what it
               denotes does not bear on any of them.  A theory rule reads the shape of a
               literal, though, so if one cannot make sense of a literal that still
               carries such a term, settle the conditionals in it against the model and
               try that rule once more before giving up on the variable. *)
            let resolved1 =
              lazy (Set.concat_map atoms1 ~f:(Mbp.resolve_ite_in_atom model))
            in
            let has_ite = lazy (Set.exists atoms1 ~f:Mbp.has_ite_in_atom) in
            let continue_with res =
              (* [targets] is the set of the variables still in [eliminated'].  Rebuilding
                 it from the list on every step made the loop quadratic in the number of
                 variables: a projection removing a few thousand spent nine tenths of
                 its time here.  When no variable occurs twice in the order, the step
                 removes exactly [x]; otherwise the set is rebuilt as before. *)
              let targets =
                phase_time "targets" (fun () ->
                    if order_has_duplicates then
                      Set.Poly.map ~f:fst @@ Set.Poly.of_list eliminated'
                    else Set.remove targets x)
              in
              let idx =
                phase_time "reindex" (fun () ->
                    reindex targets idx ~removed:atoms1 ~added:res)
              in
              let atoms = phase_time "union" (fun () -> Set.union atoms2 res) in
              loop targets idx eliminated' atoms
            in
            let project atoms1 =
              (match s with
               | T_bool.SBool -> Mbp.Boolean.model_based_projection
               | T_int.SInt -> Mbp.LIA.model_based_projection
               | T_real.SReal -> Mbp.LRA.model_based_projection
               | T_dt.SDT _ -> Mbp.ADT.model_based_projection
               | T_array.SArray (_, _) -> Mbp.ARR.model_based_projection
               | T_bv.SBV _ ->
                   Mbp.BV.model_based_projection_with
                     ~reuse_unchanged:bv_reuse_unchanged_prepass ?known
               | _ -> failwith "not supported")
                ~print model x atoms1
            in
            let by_value () =
              phase_time "by-value" @@ fun () ->
              let sub = Map.Poly.singleton x (Map.Poly.find_exn model x) in
              Set.concat_map
                (if resolve_ite_in_projection && Lazy.force has_ite then
                   Lazy.force resolved1
                 else atoms1)
                ~f:(Atom.subst sub >> Mbp.normalize_mbp model)
            in
            (* Every step ends in a tail call of [loop], outside the handlers below: the
               handlers only decide what to continue with.  When the recursive call sat
               inside them, each eliminated variable left a frame on the stack holding
               the atom set and index it was given, so a projection removing thousands of
               variables kept every intermediate atom set alive until it returned (one
               such call removed 8505 variables, and the run grew past 1.9 GB in under
               30 s, against 0.5 GB with the frames released).  It also meant that an
               exception escaping a later step was caught here and made this variable
               fall back to its model value as well; now only the step that failed falls
               back, and an exception raised by the fallback itself propagates. *)
            let project atoms1 = phase_time "rule" (fun () -> project atoms1) in
            let step =
              try
                try `Next (project atoms1)
                with Mbp.NotNormalized
                when resolve_ite_in_projection && Lazy.force has_ite ->
                  `Next (project (Lazy.force resolved1))
              with
              | Mbp.NotNormalized -> `Rotate
              | e when not (Common.Timer.is_async e) ->
                  (* this used to catch [Failure _] only, so a projection rule that
                     raised anything else -- [Invalid_argument] from a shift helper
                     given an amount past the width, [Assert_failure] from comparing
                     a Bool array index -- aborted the whole run instead of falling
                     back to the model's values.  The two backups further down catch
                     by the same test.  The timeout is raised from a signal handler
                     into whatever frame is running, so it has to stay excluded:
                     swallowing it here would turn "we ran out of time" into a
                     successful projection. *)
                  if check_validity then raise e
                  else (
                    print
                    @@ lazy
                         (sprintf
                            "projecting %s failed (%s); substituting its model value"
                            (Ident.name_of_tvar x) (Exn.to_string e));
                    `Fallback)
            in
            match step with
            | `Next res -> continue_with res
            | `Fallback -> continue_with @@ by_value ()
            | `Rotate ->
                if phase_time "loop-check" (fun () -> is_looping x atoms) then (
                  if check_validity then failwith "loop detected";
                  continue_with @@ by_value ())
                else loop targets idx (eliminated' @ [ (x, s) ]) atoms)
      in
      let atoms = preprocess atoms in
      let targets = Set.Poly.map ~f:fst eliminated in
      let res =
        phase_time "project" @@ fun () ->
        loop targets (index_of targets atoms) order atoms
      in
      if !red_bv then (
        Common.PhaseTime.event "mbp-red-call";
        if !red_hit then Common.PhaseTime.event "mbp-red-call-hit");
      if mbp_size_trace then
        eprintf "mbp-size: targets=%d atoms=%d nodes=%s out-atoms=%d out-nodes=%s\n%!"
          (Set.length targets) (Set.length atoms)
          (mbp_size_str atoms) (Set.length res) (mbp_size_str res);
      res
    in
    (* the names that survived stand for terms, and what this feeds has no let, so they
       are substituted back here -- once, at the end, over what the projection left *)
    let res =
      phase_time "expand" @@ fun () -> Evaluator.simplify @@ expand res
    in
    print @@ lazy ("MBP output: " ^ Formula.str_of res);
    if check_validity then (
      if Fn.non Formula.is_quantifier_free phi0 then failwith "wrong MBP @1";
      if Fn.non Evaluator.eval (Evaluator.simplify (Formula.subst model0 res))
      then failwith "wrong MBP @2";
      if
        Fn.non Set.is_empty
        @@ Set.inter (Formula.fvs_of res) (Set.Poly.map ~f:fst eliminated0)
      then failwith "wrong MBP @3";
      let vc =
        Formula.mk_imply res
        @@ Formula.mk_exists_if_bounded (Set.to_list eliminated0) phi0
      in
      match
        Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ())
          [ Formula.negate vc ]
      with
      | `Sat _ -> failwith "wrong MBP @4"
      | _ -> res)
    else res)
