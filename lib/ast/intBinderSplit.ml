(* Split an integer binder at the threshold of an [ite] in its body, and shift
   the upper part so that it starts at zero.

   WHAT.  [rewrite phi] replaces, bottom-up, a quantifier [Q x. B] over an
   integer [x] (with [Q] [forall] or [exists], possibly binding other variables
   in the same block) whose body holds an [ite] whose condition is a linear
   comparison of [x] with coefficient one or minus one -- equivalently
   [x < c] or [x >= c] for a term [c] free of [x] -- by

     forall x. B  ~>  (forall x. x < c  => B_lo)
                      /\ (forall x. x >= 0 => B_hi[x := x + c])
     exists x. B  ~>  (exists x. x < c  /\ B_lo)
                      \/ (exists x. x >= 0 /\ B_hi[x := x + c])

   where [B_lo] ([B_hi]) is [B] with, in the condition of every [ite], each
   comparison of that threshold replaced by the value it takes when [x < c]
   ([x >= c]), and an [ite] whose condition that decides replaced by its
   branch.  The same block of variables is bound in both parts, under the same
   names.  The threshold is taken from an [ite] whose whole condition is such
   a comparison; when there is none, from a comparison inside a compound
   condition (a conjunction, disjunction or negation of comparisons) -- the
   range tests [0 <= x /\ x < len a] and [len a <= x /\ x < len a + len b]
   with which a read of a concatenation [a ++ b] at [x] is split into reads of
   [a] at [x] and of [b] at [x - len a] -- except the literal zero, at which a
   split shifts nothing.

   WHY IT IS EXACT.  Within [B] the replaced comparisons are those that,
   analysed in the same way, give the same threshold term [c] and are reached
   from the binder without crossing any binder (no quantifier, let, array
   lambda, or letrec), so [c] means the same in each of them and each has one
   truth value on each side of [c].  Hence [B] is equivalent to [B_lo]
   wherever [x < c] and to [B_hi] wherever [x >= c], and [x |-> x - c] is a
   bijection of the integers [x >= c] onto [x >= 0].  So each rewrite is an
   equivalence in every model, the result keeps the meaning of [phi], and a
   validity or satisfiability answer about the result is one about [phi].
   The substitution is capture-avoiding, [c] does not mention [x], and no
   fresh name is drawn.

   WHY IT IS WANTED.  A solver instantiates a universal hypothesis (or the
   negation of an existential goal) by matching the terms it reads, and a read
   at [x - c] cannot be matched by a ground read at [k]: the instance needed is
   [x := k + c], which no trigger produces.  Such a question is then decided,
   if at all, by model-based instantiation, whose path depends on things that
   do not belong to the question -- on recorded questions, on the spelling of
   an uninterpreted sort's name or of bound variables, and on the random seed.
   After the shift the read is at [x] and the instance is found by matching.
   On one recorded question over a concatenation's range tests, two spellings
   of the same question took 185,606 resource units and more than 8 million
   (no proof in 20 s); split at [len a], both took under 50,000, under every
   seed tried.

   BOUND.  Each rewrite at most doubles the body of the binder it applies to.
   The number of rewrites per call is at most [max_splits], and a rewrite is
   not made when the bodies it would copy would take the formula past
   [max_growth] times its input size (counted as the input's size plus the
   size of every body copied so far); past either bound the rest of the
   formula is left as it is.  A binder that is shadowed inside
   its body is still rewritten: the substitution stops at the inner binder,
   and the [ite]s are looked for only outside every inner binder.

   The result binds the same name in two sibling quantifiers, so it is for
   asking a solver, not for passes that assume alpha-converted input. *)
open Core
open Common.Ext
open LogicOld

(* [Some (c, then_is_low)] when the formula [phi] is a comparison
   equivalent to [x < c] ([then_is_low]) or to [x >= c] ([not then_is_low]),
   possibly under negations, with [c] an integer term free of [x] *)
let rec atom_threshold x phi =
  match phi with
  | Formula.UnaryOp (Formula.Not, p, _) ->
      Option.map (atom_threshold x p) ~f:(fun (c, lo) -> (c, not lo))
  | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) -> (
      match (Evaluator.affine_part_in x t1, Evaluator.affine_part_in x t2) with
      | Some (a1, r1), Some (a2, r2) -> (
          let a = Z.sub a1 a2 and r = T_int.mk_sub r1 r2 in
          (* as [A * x + R >= 0] *)
          let norm =
            match psym with
            | T_int.Geq -> Some (a, r)
            | T_int.Gt -> Some (a, T_int.mk_sub r (T_int.one ()))
            | T_int.Leq -> Some (Z.neg a, T_int.mk_neg r)
            | T_int.Lt ->
                Some (Z.neg a, T_int.mk_sub (T_int.mk_neg r) (T_int.one ()))
            | _ -> None
          in
          match norm with
          | Some (a, r) when Z.equal a Z.one ->
              (* x >= -R *)
              Some (Evaluator.simplify_term (T_int.mk_neg r), false)
          | Some (a, r) when Z.equal a Z.minus_one ->
              (* x <= R, i.e. x < R + 1 *)
              Some
                (Evaluator.simplify_term (T_int.mk_add r (T_int.one ())), true)
          | _ -> None)
      | _ -> None)
  | _ -> None

(* [Some (c, then_is_low)] when [cond] (an [ite]'s condition term) is
   equivalent to [x < c] ([then_is_low]) or to [x >= c] ([not then_is_low]),
   with [c] an integer term free of [x] *)
let threshold x cond =
  match cond with
  | Term.FunApp (T_bool.Formula phi, [], _) -> atom_threshold x phi
  | _ -> None

(* whether two thresholds are the same integer term up to the polynomial
   normal form ([Normalizer.normalize_term] of their difference is the literal
   zero), so that [len s - 1 + 1] and [len s] count as one threshold; never
   raises, and [false] only stops a replacement *)
let same_term (a : Term.t) (b : Term.t) =
  try
    match Normalizer.normalize_term (T_int.mk_sub a b) with
    | Term.FunApp (T_int.Int n, [], _) -> Z.equal n Z.zero
    | _ -> false
  with exn when not (Common.Timer.is_async exn) -> false

(* the [ite]s reached without crossing a binder, rebuilt by [f] bottom-up *)
let rec map_ites_term ~f t =
  match t with
  | Term.Var _ | Term.LetTerm _ -> t
  | Term.FunApp (T_array.ALambda _, _, _) -> t
  | Term.FunApp (T_bool.Formula phi, [], info) ->
      Term.mk_fsym_app ~info (T_bool.Formula (map_ites_formula ~f phi)) []
  | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], info) ->
      f
        (Term.mk_fsym_app ~info T_bool.IfThenElse
           [ map_ites_term ~f c; map_ites_term ~f a; map_ites_term ~f b ])
  | Term.FunApp (fsym, args, info) ->
      Term.mk_fsym_app ~info fsym (List.map args ~f:(map_ites_term ~f))

and map_ites_formula ~f phi =
  match phi with
  | Formula.Atom (Atom.App (pred, args, ai), info) ->
      Formula.mk_atom ~info
        (Atom.mk_app ~info:ai pred (List.map args ~f:(map_ites_term ~f)))
  | Formula.Atom _ -> phi
  | Formula.UnaryOp (op, p, info) ->
      Formula.mk_unop ~info op (map_ites_formula ~f p)
  | Formula.BinaryOp (op, p, q, info) ->
      Formula.mk_binop ~info op (map_ites_formula ~f p) (map_ites_formula ~f q)
  | Formula.Bind _ | Formula.LetRec _ | Formula.LetFormula _ -> phi

(* the first comparison of [x] with a threshold inside a Boolean combination
   (negations and binary connectives, no binder) *)
let rec first_atom_threshold x phi =
  match atom_threshold x phi with
  | Some _ as r -> r
  | None -> (
      match phi with
      | Formula.UnaryOp (Formula.Not, p, _) -> first_atom_threshold x p
      | Formula.BinaryOp (_, p, q, _) -> (
          match first_atom_threshold x p with
          | Some _ as r -> r
          | None -> first_atom_threshold x q)
      | _ -> None)

let is_literal_zero = function
  | Term.FunApp (T_int.Int n, [], _) -> Z.equal n Z.zero
  | _ -> false

(* the threshold to split [x] at: the first [ite] (in traversal order) whose
   whole condition is a comparison of [x]; failing that, the first comparison
   of [x] inside a compound condition, such as the range test
   [0 <= x /\ x < len a] or [len a <= x /\ x < len a + len b] that reading a
   concatenation [a ++ b] at [x] is rewritten with.  A threshold found only
   inside a compound condition is not taken when it is the literal zero: the
   shift by zero moves no read, so that split would only duplicate the body. *)
let first_threshold x body =
  let whole = ref None and inner = ref None in
  ignore
    (map_ites_formula body ~f:(fun t ->
         (match t with
         | Term.FunApp (T_bool.IfThenElse, [ c; _; _ ], _) -> (
             (if Option.is_none !whole then whole := threshold x c);
             match (!inner, c) with
             | None, Term.FunApp (T_bool.Formula phi, [], _) -> (
                 match first_atom_threshold x phi with
                 | Some (c, _) as r when not (is_literal_zero c) -> inner := r
                 | _ -> ())
             | _ -> ())
         | _ -> ());
         t));
  match !whole with Some _ as r -> r | None -> !inner

(* a condition with every comparison of threshold [c] for [x] replaced by the
   value it takes on one side of [c]: [Decided b] when that decides the whole
   condition, [Open phi'] otherwise ([phi'] physically the input when nothing
   was replaced) *)
type settled = Decided of bool | Open of Formula.t

let rec settle x c ~low phi =
  match atom_threshold x phi with
  | Some (c', then_is_low) when same_term c c' ->
      (* on the side [x < c] a comparison equivalent to [x < c] holds *)
      Decided (Bool.equal then_is_low low)
  | _ -> (
      match phi with
      | Formula.Atom (Atom.True _, _) -> Decided true
      | Formula.Atom (Atom.False _, _) -> Decided false
      | Formula.UnaryOp (Formula.Not, p, info) -> (
          match settle x c ~low p with
          | Decided b -> Decided (not b)
          | Open p' ->
              if phys_equal p p' then Open phi
              else Open (Formula.mk_neg ~info p'))
      | Formula.BinaryOp (op, p, q, info) -> (
          let sp = settle x c ~low p and sq = settle x c ~low q in
          let formula_of = function
            | Decided true -> Formula.mk_true ()
            | Decided false -> Formula.mk_false ()
            | Open f -> f
          in
          let rebuild () =
            match (sp, sq) with
            | Open p', Open q' when phys_equal p p' && phys_equal q q' ->
                Open phi
            | _ ->
                Open
                  (Formula.mk_binop ~info op (formula_of sp) (formula_of sq))
          in
          match (op, sp, sq) with
          | Formula.And, Decided false, _ | Formula.And, _, Decided false ->
              Decided false
          | Formula.And, Decided true, r | Formula.And, r, Decided true -> r
          | Formula.Or, Decided true, _ | Formula.Or, _, Decided true ->
              Decided true
          | Formula.Or, Decided false, r | Formula.Or, r, Decided false -> r
          | Formula.Imply, Decided false, _ | Formula.Imply, _, Decided true ->
              Decided true
          | Formula.Imply, Decided true, r -> r
          | (Formula.Iff | Formula.Xor), Decided b1, Decided b2 ->
              Decided
                (match op with
                | Formula.Iff -> Bool.equal b1 b2
                | _ -> not (Bool.equal b1 b2))
          | _ -> rebuild ())
      | _ -> Open phi)

(* [body] with, in each [ite], every comparison of threshold [c] for [x] in
   its condition replaced by the value it takes on the side [low] ([x < c]) or
   not, and the [ite] replaced by its branch when that decides the condition *)
let choose x c ~low body =
  map_ites_formula body ~f:(function
    | Term.FunApp
        ( T_bool.IfThenElse,
          [ Term.FunApp (T_bool.Formula phi, [], _); a; b ],
          info )
      as t -> (
        match settle x c ~low phi with
        | Decided true -> a
        | Decided false -> b
        | Open phi' ->
            if phys_equal phi phi' then t
            else
              Term.mk_fsym_app ~info T_bool.IfThenElse
                [ T_bool.of_formula phi'; a; b ])
    | t -> t)

let splits_done = Atomic.make 0

(* [rewrite] with the number of splits it made *)
let rewrite_counted ?(max_splits = 32) ?(max_growth = 4) phi =
  let budget = ref max_splits in
  let size0 = Formula.ast_size phi in
  let size = ref size0 in
  let rec formula phi =
    match phi with
    | Formula.Atom _ -> phi
    | Formula.UnaryOp (op, p, info) -> Formula.mk_unop ~info op (formula p)
    | Formula.BinaryOp (op, p, q, info) ->
        Formula.mk_binop ~info op (formula p) (formula q)
    | Formula.LetRec _ | Formula.LetFormula _ -> phi
    | Formula.Bind
        (((Formula.Forall | Formula.Exists) as binder), senv, body, info) ->
        split binder senv (formula body) info
    | Formula.Bind (binder, senv, body, info) ->
        Formula.mk_bind ~info binder senv (formula body)
  and split binder senv body info =
    let candidate =
      if !budget <= 0 then None
      else
        List.find_map senv ~f:(fun (x, s) ->
            match s with
            | T_int.SInt ->
                Option.map (first_threshold x body) ~f:(fun c -> (x, c))
            | _ -> None)
    in
    let body_size = lazy (Formula.ast_size body) in
    match candidate with
    | Some _ when !size + Lazy.force body_size > max_growth * size0 ->
        Formula.mk_bind ~info binder senv body
    | None -> Formula.mk_bind ~info binder senv body
    | Some (x, (c, _)) -> (
        decr budget;
        size := !size + Lazy.force body_size;
        Atomic.incr splits_done;
        let xv = Term.mk_var x T_int.SInt in
        let lo = choose x c ~low:true body in
        let hi =
          Formula.subst
            (Map.Poly.singleton x (T_int.mk_add xv c))
            (choose x c ~low:false body)
        in
        let lo_guard = Formula.lt xv c
        and hi_guard = Formula.geq xv (T_int.zero ()) in
        let part guard b =
          match binder with
          | Formula.Forall -> Formula.mk_or (Formula.mk_neg guard) b
          | _ -> Formula.mk_and guard b
        in
        (* each part may hold a further threshold, on [x] or another variable *)
        let lo = split binder senv (part lo_guard lo) info
        and hi = split binder senv (part hi_guard hi) info in
        match binder with
        | Formula.Forall -> Formula.mk_and lo hi
        | _ -> Formula.mk_or lo hi)
  in
  if !budget <= 0 then (phi, 0)
  else
    let psi = formula phi in
    (psi, max_splits - !budget)

let rewrite ?max_splits ?max_growth phi =
  fst (rewrite_counted ?max_splits ?max_growth phi)

(* Tallies per solver site that hands its questions to [rewrite_at]: how many
   questions it handed over, how many of them the rewrite changed, and how many
   splits it made in them.  Atomic, so domains may share them; they change no
   answer. *)
type tally = { asked : int Atomic.t; changed : int Atomic.t; splits : int Atomic.t }

let new_tally () =
  { asked = Atomic.make 0; changed = Atomic.make 0; splits = Atomic.make 0 }

(* the predicate eliminator's validity questions, and the zero-unknown
   verdict's (the ladder's) *)
let elim_tally = new_tally ()
let ladder_tally = new_tally ()

(* [rewrite phi], counted in [tally] *)
let rewrite_at tally phi =
  let psi, n = rewrite_counted phi in
  Atomic.incr tally.asked;
  if n > 0 then (
    Atomic.incr tally.changed;
    ignore (Atomic.fetch_and_add tally.splits n : int));
  psi

let tally_line () =
  let f t =
    Printf.sprintf "asked=%d rewritten=%d splits=%d" (Atomic.get t.asked)
      (Atomic.get t.changed) (Atomic.get t.splits)
  in
  Printf.sprintf "int-binder-split: pid=%d elim %s ladder %s"
    (Core_unix.getpid () |> Pid.to_int)
    (f elim_tally) (f ladder_tally)

(* [report_tallies ()], called by each switch that turns a site on when its
   configuration is verbose: from then
   on the process prints [tally_line ()] as one line on stderr when it exits
   normally and, where the phase-time report's watcher is running, on SIGTERM
   or SIGINT before that report.  Once per process however often it is called;
   a forked copy that exits normally prints its own line, labelled by its own
   pid.  A diagnostic: it changes no answer. *)
let report_registered = Atomic.make false

let report_tallies () =
  if Atomic.compare_and_set report_registered false true then (
    let print () =
      try
        Stdlib.prerr_endline (tally_line ());
        Stdlib.flush Stdlib.stderr
      with Sys_error _ -> ()
    in
    Stdlib.at_exit print;
    Common.PhaseTime.at_signal print)
