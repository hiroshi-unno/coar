(* Arrays of a positive example derived by resolution, varied away from the
   solver's cheapest choice.

   Resolution against a clause [pure \/ P(t)] derives the positive example
   [P(t)[sub]] from a model [sub] of the matching condition [cond] (the
   negation of [pure]): the example is licensed exactly when [cond[sub]] holds,
   and any model of [cond] licenses it equally.  A solver's model assigns the
   cheapest values it finds, and for arrays that is a constant array, the same
   constant for every array the condition relates: [cond = (a[0] = b[i])] comes
   back as [a |-> const 0, b |-> const 0].  An example over equal constant
   arrays agrees with itself at EVERY pair of cells, so a candidate that
   relates the two arrays by value alone ([a[ka] = b[kb]], with no relation
   between [ka] and [kb]) fits it, and a loop fed only such positives has no
   example forcing the index relation between the arrays.

   [vary] replaces the value of each array variable that the condition reads
   only through [select] by an array that
   - agrees with the model's value at every position the condition READS
     (defined below), and
   - holds, everywhere else, a default of its own: an integer larger in
     absolute value than every integer in the model, the condition and the
     atom, and different for each varied array.
   Then it evaluates [cond] on the new values and keeps them only if it
   evaluates to [true]; otherwise it returns [sub] unchanged.  Evaluation is
   [Evaluator.eval]; for a symbol it has no case for, the simplifier's normal
   form is used when it is the literal [true] (or, for an index, a literal
   value) -- the same simplifier that writes the derived example's guard.

   The positions read.  For an array variable [x] of [sub], a position [j] is
   read when [cond] contains a subterm [select(x, e)] and [e] evaluates to [j]
   under [sub] -- the ORIGINAL substitution.  The index [e] may itself read an
   array, or apply a selector to a tuple or a datatype value; it is evaluated
   as a whole.  An array is varied only when it satisfies all of:
   - it is a variable of [sub] occurring in the atom, and its value is a closed
     array term of element sort [Int] that evaluates to an array value;
   - every occurrence of the variable in [cond] is the array argument of a
     [select] whose index evaluates, under [sub], to a closed value;
   and [cond] is quantifier-free and is not interpretation-dependent (it
   mentions no symbol whose value the theory leaves open).  An array reached
   only through a selector or a tuple component is not a variable of [sub] and
   is never varied; an array that is stored to, compared, passed on or read
   through a curried read keeps the model's value.

   Why the check passes whenever those conditions hold (the check is still
   made, and decides).  By induction on the nesting of reads, innermost first:
   an innermost read [select(x, e)] has an index [e] with no read of a varied
   array, so [e] has the same value under both substitutions; it is a read
   position of [x], where the new array agrees with the old, so the read has
   the same value.  A read whose index contains reads has, by induction, the
   same index value, which is again a read position.  So every read, hence
   every atom of [cond], has the same value under both, and [cond] stays true.

   The contract, for a caller:
   - requires: [sub] is a model of [cond] that the caller derives
     [P(t)[sub]] from; [cond] and [atm] are over the variables of [sub];
   - guarantees: the returned substitution [sub'] differs from [sub] only at
     array variables, [Evaluator.eval (cond[sub'])] is [true] whenever
     [sub' <> sub], and [sub'] agrees with [sub] at every read position; so
     [P(t)[sub']] is licensed by the same resolution step;
   - preserves: no fresh name is drawn and nothing global is written, so with
     the switch off (or when nothing is varied) the trajectory is untouched.

   What this does NOT do: it does not make the derivation stronger.  The
   example still states [P] at one point; the point differs from the solver's
   at positions the derivation did not constrain. *)

open Core
open Ast
open Ast.LogicOld

type outcome =
  | Off
  | Nothing_to_vary of string
  | Varied of (Ident.tvar * Term.t) list
  | Refused_by_check

let str_of_outcome = function
  | Off -> "off"
  | Nothing_to_vary r -> "nothing to vary (" ^ r ^ ")"
  | Varied l ->
      "varied "
      ^ String.concat ~sep:", "
          (List.map l ~f:(fun (x, t) ->
               Ident.name_of_tvar x ^ " |-> " ^ Term.str_of t))
  | Refused_by_check -> "refused: the condition does not evaluate to true"

(* The value of a closed term: [Evaluator.eval_term], and where it has no case
   for a symbol (a tuple projection, for one), the simplifier's normal form when
   that is a literal. *)
let eval_term_opt t =
  try Some (Evaluator.eval_term t)
  with exn_ when not (Common.Timer.is_async exn_) -> (
    try Some (Term.value_of (Evaluator.simplify_term t))
    with exn_ when not (Common.Timer.is_async exn_) -> None)

(* The truth value of a closed formula, by the same two routes. *)
let eval_opt phi =
  try Some (Evaluator.eval phi)
  with exn_ when not (Common.Timer.is_async exn_) ->
    let phi' = Evaluator.simplify phi in
    if Formula.is_true phi' then Some true
    else if Formula.is_false phi' then Some false
    else None

(* every integer inside a value *)
let rec ints_of_value acc = function
  | Value.Int n -> Z.abs n :: acc
  | Value.Arr (d, v, m) ->
      Map.Poly.fold m
        ~init:(ints_of_value (ints_of_value acc d) v)
        ~f:(fun ~key ~data acc -> ints_of_value (ints_of_value acc key) data)
  | Value.TupleCons vs | Value.DTCons (_, _, vs) ->
      List.fold vs ~init:acc ~f:ints_of_value
  | _ -> acc

let int_literal_of_term acc = function
  | Term.FunApp (T_int.Int n, [], _) -> Z.abs n :: acc
  | _ -> acc

(* The reads of [cond]: for each variable, how often it occurs and the index
   terms of the [select]s whose array argument it is. *)
let occurrences cond =
  let vars = Hashtbl.Poly.create () and reads = Hashtbl.Poly.create () in
  let lits = ref [] in
  Formula.iter_term cond ~f:(fun t ->
      lits := int_literal_of_term !lits t;
      match t with
      | Term.Var (x, _, _) -> Hashtbl.incr vars x
      | Term.FunApp (T_array.ASelect _, [ Term.Var (x, _, _); e ], _) ->
          Hashtbl.add_multi reads ~key:x ~data:e
      | _ -> ());
  (vars, reads, !lits)

(* [unsafe_vary_all] is for tests only: it skips the requirement that every
   occurrence of a varied array in [cond] be a read, so that the evaluation
   check alone decides whether the modification is kept. *)
let vary ?(unsafe_vary_all = false) ~cond ~atm
    (sub : (Ident.tvar, Term.t) Map.Poly.t) =
  if not (Formula.is_quantifier_free cond) then
    (sub, Nothing_to_vary "the condition has a binder")
  else if ClauseOld.interpretation_dependent cond then
    (sub, Nothing_to_vary "the condition is interpretation-dependent")
  else
    let vars, reads, lits = occurrences cond in
    let atm_vars = Atom.tvs_of atm in
    let array_value x t =
      match Term.sort_of t with
      | T_array.SArray (_, T_int.SInt)
        when Set.mem atm_vars x && Set.is_empty (Term.tvs_of t) -> (
          match eval_term_opt t with
          | Some (Value.Arr (d, v, m)) -> Some (d, v, m)
          | _ -> None)
      | _ -> None
    in
    (* the read positions of [x] under the original [sub], or [None] when some
       occurrence is not a read or some index does not evaluate *)
    let read_positions x =
      let es = Hashtbl.find_multi reads x in
      if
        (not unsafe_vary_all)
        && Option.value ~default:0 (Hashtbl.find vars x) <> List.length es
      then None
      else
        Option.all
        @@ List.map es ~f:(fun e ->
            let e' = Term.subst sub e in
            if Set.is_empty (Term.tvs_of e') then eval_term_opt e' else None)
    in
    let candidates =
      List.filter_map (Map.Poly.to_alist sub) ~f:(fun (x, t) ->
          match array_value x t with
          | None -> None
          | Some (d, v, m) -> (
              match read_positions x with
              | None -> None
              | Some js -> Some (x, d, v, m, js)))
      |> List.sort ~compare:(fun (x, _, _, _, _) (y, _, _, _, _) ->
          String.compare (Ident.name_of_tvar x) (Ident.name_of_tvar y))
    in
    if List.is_empty candidates then
      (sub, Nothing_to_vary "no array read only through select")
    else
      let bound =
        let from_sub =
          Map.Poly.fold sub ~init:[] ~f:(fun ~key:_ ~data acc ->
              match eval_term_opt data with
              | Some v -> ints_of_value acc v
              | None -> acc)
        in
        let from_atm = ref [] in
        Atom.iter_term atm ~f:(fun t ->
            from_atm := int_literal_of_term !from_atm t);
        List.fold (lits @ from_sub @ !from_atm) ~init:Z.zero ~f:Z.max
      in
      let dtenv = get_dtenv () in
      let varied =
        List.mapi candidates ~f:(fun rank (x, d, v, m, js) ->
            let default = Z.add bound (Z.of_int (rank + 1)) in
            let kept =
              List.fold js ~init:Map.Poly.empty ~f:(fun acc j ->
                  Map.Poly.set acc ~key:j
                    ~data:
                      (match Map.Poly.find m j with Some w -> w | None -> v))
            in
            (x, Term.of_value dtenv (Value.Arr (d, Value.Int default, kept))))
      in
      let sub' =
        List.fold varied ~init:sub ~f:(fun acc (x, t) ->
            Map.Poly.set acc ~key:x ~data:t)
      in
      match eval_opt (Formula.subst sub' cond) with
      | Some true -> (sub', Varied varied)
      | _ -> (sub, Refused_by_check)

(* The entry point the resolver calls, with its switch, so that the switch-off
   path a test exercises is the one the resolver takes. *)
let apply ~on ~cond ~atm sub =
  if not on then (sub, Off) else vary ~cond ~atm sub
