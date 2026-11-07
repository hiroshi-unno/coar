(* The helpers of Spacer's blocking loop over one binary interpolation query
   [phi1 => phi2] (Komuravelli, Gurfinkel and Chaki, CAV 2014, for the
   procedure): the entry tests on the query's sorts, the implicant of a
   formula at a model and the cube literals built from it, the views of a
   literal as bounds and bits, the normal form of a cube's equalities, the Z3
   contexts and per-level solvers kept between calls, and the checks of an
   antecedent's argument bounds.  Theory-generic except where a function says
   it reads bit-vectors.  Then the loop itself ([blocking_interpolant]),
   which may ask a caller-supplied bit-level checker ([BIT_CHECKER]) instead
   of Z3, and its driver ([interpolate]): which queries it may answer, its
   premises and the counters it reports.  Nothing here depends on MuCyc's
   configuration or on a SAT solver. *)

open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* [convert_model res_dc senv model]: [model] as a substitution over [senv],
   a dummy for each variable of [senv] the model leaves out.  An entry whose
   name [senv] holds at another sort is dropped first ([model_restrict]): a
   pooled solver context offers names left by earlier queries, at their sorts,
   and such an entry says nothing about the variable of [senv]. *)
let convert_model res_dc senv model =
  let model = model_restrict ~target:senv model in
  let model =
    let model =
      if res_dc then remove_dontcare model
      else
        List.filter_map model ~f:(function
          | (_, _), None -> None
          | (x, _), Some t -> Some (x, t))
    in
    try Map.Poly.of_alist_exn model
    with exn_ when not (Common.Timer.is_async exn_) ->
      (* z3 may return a model like  [x |-> 1, x |-> 0]*)
      List.classify (fun x y -> Stdlib.(fst x = fst y)) model
      |> List.map ~f:List.hd_exn |> Map.Poly.of_alist_exn
  in
  Set.fold senv ~init:model ~f:(fun model (x, sort) ->
      match Map.Poly.find model x with
      | Some _ -> model
      | None -> Map.Poly.add_exn model ~key:x ~data:(Term.mk_dummy sort))

(* The values of [model], a map [convert_model] built, or [None] when one of
   its terms is not closed: Z3 names an element of an uninterpreted sort
   [<sort>!val!<n>], and [convert_model] stands a dummy constant of such a
   sort for a variable the model leaves out; both are variables here, which
   the evaluator has no value for.  A query over such a sort whose models
   happen to hold no such element still gets its values. *)
let model_values model =
  if Map.Poly.exists model ~f:(fun t -> not (Set.is_empty (Term.fvs_of t)))
  then None
  else Some (Map.Poly.map model ~f:(fun t -> Evaluator.eval_term t))

(* [t] with a double negation at its root removed, repeatedly: [bvneg]
   and [bvmul] by the numeral [-1] (either side) each negate, so
   [bvmul(-1, bvneg x)] and [bvneg (bvneg x)] are [x] modulo 2^w.  Only the
   root is looked at. *)
let rec unneg t =
  let minus_one = function
    | Term.FunApp (T_bv.BVNum (s, n), [], _) ->
        let m = Z.shift_left Z.one (T_bv.bits_of s) in
        Z.equal (Z.erem n m) (Z.pred m)
    | _ -> false
  in
  let neg_arg = function
    | Term.FunApp (T_bv.BVNeg _, [ x ], _) -> Some x
    | Term.FunApp (T_bv.BVMul _, [ c; x ], _) when minus_one c -> Some x
    | Term.FunApp (T_bv.BVMul _, [ x; c ], _) when minus_one c -> Some x
    | _ -> None
  in
  match neg_arg t with
  | Some u -> ( match neg_arg u with Some x -> unneg x | None -> t)
  | None -> t

(* Everything the query mentions is a bit-vector or a Boolean. *)
let bit_vector_only args phi1 phi2 =
  let ok = function T_bv.SBV _ | T_bool.SBool -> true | _ -> false in
  List.for_all args ~f:(snd >> ok)
  && Set.for_all (Formula.term_sort_env_of phi1) ~f:(snd >> ok)
  && Set.for_all (Formula.term_sort_env_of phi2) ~f:(snd >> ok)

(* [ClauseOld.interpretation_dependent phi], except that with [rem_numeral]
   an integer division or remainder whose divisor is a non-zero integer
   literal does not count: for a divisor [d <> 0] both rounding modes define
   [t div d] and [t mod d] from [t] alone (SMT-LIB's Ints theory leaves only
   division by zero open), so every standard model gives such a term the
   same value once it agrees on [t].  The dividend is still inspected: the
   rewrite replaces only the operator, keeping the dividend and the divisor
   as the arguments of a sum.  It may go under binders and into formulas
   embedded in terms (an [ite] condition is one), since whether the divisor
   is a non-zero literal is a fact about the term itself and not about the
   scope it sits in; a subterm the traversal does not rebuild keeps its
   operator, which the test then still counts. *)
let interpretation_dependent_upto ~rem_numeral phi =
  let fixed_divrem = function
    | Term.FunApp ((T_int.Div _ | T_int.Rem _), [ t; d ], _)
      when T_int.is_int d && not (Z.equal (T_int.let_int d) Z.zero) ->
        T_int.mk_add t d
    | t -> t
  in
  ClauseOld.interpretation_dependent
    (if rem_numeral then Formula.map_term ~f:fixed_divrem phi
     else phi)

(* Everything the query mentions is a bit-vector, a Boolean, an integer or a
   real, and neither side has a term whose value a model of the theory leaves
   open.  Then every model of the background theory interprets both sides
   alike, so a model of [phi1] and a separate model of [~phi2] agreeing on
   [args] together realise a refutation in one model, which is what the
   blocking loop's [`Answer None] assumes. *)
let arith_blocking_ok ?(rem_numeral = false) args phi1 phi2 =
  let ok = function
    | T_bv.SBV _ | T_bool.SBool | T_int.SInt | T_real.SReal -> true
    | _ -> false
  in
  List.for_all args ~f:(snd >> ok)
  && Set.for_all (Formula.term_sort_env_of phi1) ~f:(snd >> ok)
  && Set.for_all (Formula.term_sort_env_of phi2) ~f:(snd >> ok)
  && (not (interpretation_dependent_upto ~rem_numeral phi1))
  && not (interpretation_dependent_upto ~rem_numeral phi2)

(* The blocking loop's entry test, over any sorts but function sorts:
   neither side has a term whose value a model of the theory leaves open.
   Outside [arith_blocking_ok] the two-model argument above is not made, so
   the loop reads a refutation from one checked model ([check_refutation]);
   its other answers rest on unsatisfiability only and hold in every model.
   The proviso stays because the cube's simplification and projection fold
   terms as standard models interpret them. *)
let blocking_ok ?(rem_numeral = false) args phi1 phi2 =
  let ok s = not (Sort.is_arrow s) in
  List.for_all args ~f:(snd >> ok)
  && Set.for_all (Formula.term_sort_env_of phi1) ~f:(snd >> ok)
  && Set.for_all (Formula.term_sort_env_of phi2) ~f:(snd >> ok)
  && (not (interpretation_dependent_upto ~rem_numeral phi1))
  && not (interpretation_dependent_upto ~rem_numeral phi2)

(* Why [blocking_ok] fails, for tracing: the function sorts among [args] and
   the two sides' variables, and the symbols of each side that
   [interpretation_dependent_upto] reports (listed over the formula as
   written, so a [rem_numeral] division by a literal may be listed while the
   side's verdict, printed beside it, is the test's own).  Observation only. *)
let blocking_declined_reasons ~rem_numeral args phi1 phi2 =
  let arrows env =
    List.filter_map env ~f:(fun (x, s) ->
        if Sort.is_arrow s then
          Some (Ident.name_of_tvar x ^ ":" ^ Term.str_of_sort s)
        else None)
  in
  let open_syms phi =
    Set.to_list (Formula.funsyms_of phi)
    |> List.filter_map ~f:(function
      | (T_dt.DTSel _ | FVar _ | T_int.Div _ | T_int.Rem _ | T_real.RDiv
        | T_seq.SqNth _ | T_int.Power | T_real.RPower) as f ->
          Some (Term.str_of_funsym f)
      | _ -> None)
    |> List.dedup_and_sort ~compare:String.compare
  in
  let side name phi =
    sprintf "%s[arrow %s; dependent %b; open %s]" name
      (String.concat ~sep:"," @@ arrows @@ Set.to_list
     @@ Formula.term_sort_env_of phi)
      (interpretation_dependent_upto ~rem_numeral phi)
      (String.concat ~sep:"," @@ open_syms phi)
  in
  sprintf "args[arrow %s] %s %s"
    (String.concat ~sep:"," @@ arrows args)
    (side "phi1" phi1) (side "phi2" phi2)

(* [lits] with the tester [is_C(s)] added for every selector [sel(s)] of a
   constructor [C] of a datatype with several constructors that occurs in
   them: on the other constructors the theory leaves [sel(s)] open, and the
   tester makes the cube's meaning independent of it.  Adding a literal keeps
   a cube that [phi1] excludes excluded, so a lemma stays implied by [phi1];
   a tester false at a cube's model makes that cube fail its model check. *)
let guard_selectors lits =
  let several_conses dt =
    match Datatype.look_up_dt dt @@ Datatype.name_of dt with
    | Some dt -> List.length (Datatype.conses_of_dt dt) > 1
    | None -> true
  in
  let present = Set.Poly.of_list lits in
  let testers =
    Set.Poly.filter_map
      (Formula.filtered_terms_of (Formula.and_of lits) ~f:(function
        | Term.FunApp (T_dt.DTSel _, [ _ ], _) -> true
        | _ -> false))
      ~f:(function
        | Term.FunApp (T_dt.DTSel (sel, dt, _), [ s ], _) when several_conses dt
          -> (
            match Datatype.look_up_cons_of_sel dt sel with
            | Some cons ->
                let tester =
                  Formula.mk_atom
                    (T_dt.mk_is_cons dt (Datatype.name_of_cons cons) s)
                in
                if Set.mem present tester then None else Some tester
            | None -> None)
        | _ -> None)
  in
  lits @ Set.to_list testers

(* [Evaluator.eval ~env phi], with each tester atom of [phi] whose argument
   evaluates at [env] to a constructor value decided first.  The evaluator
   decides a tester only on a syntactic constructor term, while a model binds
   a datatype variable to a constructor value, so [is_C x] (or [is_C (sel x)])
   would raise there.  A tester inside a term (an [ite] condition) is not
   reached and raises as before. *)
let eval_at ~env phi =
  Evaluator.eval ~env
  @@ Formula.map_atom phi ~f:(function
       | Atom.App
           ( Predicate.Psym
               ((T_dt.IsCons (n1, _) | T_dt.NotIsCons (n1, _)) as psym),
             [ t ],
             _ ) as atom -> (
           match Evaluator.eval_term ~env t with
           | Value.DTCons (n2, _, _) ->
               let is_n1 = String.(n1 = n2) in
               let holds =
                 match psym with T_dt.IsCons _ -> is_n1 | _ -> not is_n1
               in
               if holds then Formula.mk_true () else Formula.mk_false ()
           | _ -> Formula.mk_atom atom
           | exception exn_ when not (Common.Timer.is_async exn_) ->
               Formula.mk_atom atom)
       | atom -> Formula.mk_atom atom)

(* The literals of a cube of [phi] at [env]: a conjunction of literals of
   [phi], each true at [env], that implies [phi] (an implicant, as Z3's
   [compute_implicant_literals] takes it for Spacer: every conjunct, one true
   disjunct, both sides of an equivalence as they evaluate).  [phi] is in
   negation normal form and true at [env].  A [let] contributes the equality
   of its variable with its definition, so that every literal is closed under
   the variables [env] assigns and the [let] variables; the value of each
   [let] variable is added to [lets].  A conditional term inside an atom is
   kept whole, unless [lift_ite]: then each literal [A[ite c a b]] (the
   conditional term found outside binders: neither an array lambda's body
   nor a [let] term's body is entered) is replaced by the implicant literals
   of [c] and [A[a]] when [c] holds at [env], of [~c] and [A[b]] otherwise,
   until no conditional term is left outside binders (Z3's
   [compute_implicant_literals] sees atoms from which its rewriter has
   lifted conditional terms).  Either replacement is true at [env] and
   implies [A[ite c a b]], so the result is still an implicant of [phi] at
   [env]; generalisation may then drop the condition and the branch
   separately.  With [absent] (variables to which the solver's partial
   assignment gives no value, while [env] gives them a default one), a
   disjunction takes, where it can, a disjunct that holds whatever values
   those variables take: one [forced] by the other variables, judged
   bottom-up (a literal, or any node other than a conjunction or a
   disjunction, true at [env] and mentioning no variable of [absent]; a
   conjunction of forced formulas; a disjunction with a forced disjunct).
   Such a disjunct is true at [env] too, so the result is still an
   implicant; it just does not lean on the default values, as an implicant
   read off the partial assignment would not.  Raises on a quantifier.

   One pass: [walk] returns a subformula's value at [env], as a lazy value,
   together with a thunk computing its literals.  A value is forced only
   where a disjunction or an equivalence above it asks, as before, but at
   most once (the earlier form evaluated a disjunct and then walked into it,
   evaluating every disjunction nested in it again: up to k times under k
   nested ones).  The value is [Evaluator.eval]'s, with the same
   left-to-right short-circuit, and the thunks are forced for the nodes
   chosen, in the same order, so the list is the one the earlier form
   returned.  An atom is evaluated alone at the environment of its own
   [let]s, where [eval_at] on a whole subformula decided testers at the outer
   environment; this can only answer where that raised.  A false side of an
   equivalence is negated and walked afresh, as before. *)
let rec implicant ?(lift_ite = false) ?(absent = Set.Poly.empty) ~lets env
    phi =
  let partial = not (Set.is_empty absent) in
  let free_of_absent phi =
    Set.are_disjoint (Formula.tvs_of phi) absent
  in
  (* each node gives its value, whether it is [forced] (forced only with
     [absent]) and a thunk computing its literals *)
  let leaf phi value = lazy (free_of_absent phi && Lazy.force value) in
  let rec walk env phi =
    match phi with
    | Formula.Atom (atom, info) ->
        let value = lazy (eval_at ~env phi) in
        ( value,
          leaf phi value,
          fun () ->
            if lift_ite then
              lift_ite_literal ~lets env (fun a -> Formula.mk_atom ~info a)
                atom phi
            else [ phi ] )
    | Formula.UnaryOp (Formula.Not, Formula.Atom (atom, ainfo), info) ->
        let value = lazy (eval_at ~env phi) in
        ( value,
          leaf phi value,
          fun () ->
            if lift_ite then
              lift_ite_literal ~lets env
                (fun a ->
                  Formula.mk_unop ~info Formula.Not
                    (Formula.mk_atom ~info:ainfo a))
                atom phi
            else [ phi ] )
    | Formula.BinaryOp (Formula.And, phi1, phi2, _) ->
        let l1, f1, k1 = walk env phi1 in
        let l2, f2, k2 = walk env phi2 in
        ( lazy (Lazy.force l1 && Lazy.force l2),
          lazy (Lazy.force f1 && Lazy.force f2),
          fun () -> k1 () @ k2 () )
    | Formula.BinaryOp (Formula.Or, phi1, phi2, _) ->
        let l1, f1, k1 = walk env phi1 in
        let l2, f2, k2 = walk env phi2 in
        ( lazy (Lazy.force l1 || Lazy.force l2),
          lazy (Lazy.force f1 || Lazy.force f2),
          fun () ->
            if partial && Lazy.force f1 then k1 ()
            else if partial && Lazy.force f2 then k2 ()
            else if Lazy.force l1 then k1 ()
            else k2 () )
    | Formula.BinaryOp (((Formula.Iff | Formula.Xor) as op), phi1, phi2, _) ->
        let side (l, _, k) phi () =
          if Lazy.force l then k ()
          else
            (trd3 @@ walk env @@ Formula.nnf_of @@ Formula.mk_neg phi) ()
        in
        let ((l1, _, _) as r1) = walk env phi1 in
        let ((l2, _, _) as r2) = walk env phi2 in
        let value =
          lazy
            (let b1 = Lazy.force l1 in
             let b2 = Lazy.force l2 in
             match op with Formula.Iff -> Bool.(b1 = b2) | _ -> Bool.(b1 <> b2))
        in
        (value, leaf phi value, fun () -> side r1 phi1 () @ side r2 phi2 ())
    | Formula.LetFormula (var, sort, def, body, _) ->
        let inner =
          lazy
            (let value = Evaluator.eval_term ~env def in
             (value, walk (Map.Poly.set env ~key:var ~data:value) body))
        in
        let value =
          lazy
            (let _, (l, _, _) = Lazy.force inner in
             Lazy.force l)
        in
        ( value,
          leaf phi value,
          fun () ->
            let value, (_, _, k) = Lazy.force inner in
            lets := Map.Poly.set !lets ~key:var ~data:value;
            Formula.eq (Term.mk_var var sort) def :: k () )
    | _ ->
        let value = lazy (eval_at ~env phi) in
        ( value,
          leaf phi value,
          fun () ->
            failwith ("[implicant] unexpected formula: " ^ Formula.str_of phi) )
  in
  (trd3 @@ walk env phi) ()

(* The literal [lit], built by [rebuild] from [atom], with its conditional
   terms outside binders lifted by the model [env], as [implicant] describes
   for [lift_ite]; [[lit]] when there is none.  One walk does what lifting
   the leftmost outermost conditional term and starting again would: each
   conditional term met in pre-order contributes the implicant literals of
   its condition (or of its negation) and is replaced by its taken branch,
   whose own conditional terms are then lifted in turn, so the literals come
   in the order of those repeated lifts.  A conditional term structurally
   equal to one already lifted is replaced by the same result and adds no
   literal (the repeated lifts would only have repeated them).  This matters
   for the atoms of bit-level circuits: one atom of a hardware model held
   114,333 term nodes but 3,856 distinct ones and 20,968 copies of
   conditional terms, and lifting one copy at a time rebuilt the whole atom
   per copy. *)
and lift_ite_literal ~lets env rebuild atom lit =
  match atom with
  | Atom.App (pred, args, ainfo) ->
      let lifted = Common.Ext.Hashtbl.PolyDeep.create () in
      let cond_lits = ref [] in
      let any = ref false in
      (* a conditional term below an array lambda or a [let] term may mention
         its bound variable, so neither body is entered *)
      let rec lift t =
        match t with
        | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _) -> (
            any := true;
            match Hashtbl.find lifted t with
            | Some t' -> t'
            | None ->
                let cond =
                  match c with
                  | Term.FunApp (T_bool.Formula phi, [], _) -> phi
                  | _ -> Formula.of_bool_term c
                in
                let taken = Evaluator.eval ~env cond in
                cond_lits :=
                  List.rev_append
                    (implicant ~lift_ite:true ~lets env
                    @@ Formula.nnf_of
                    @@ if taken then cond else Formula.mk_neg cond)
                    !cond_lits;
                let t' = lift (if taken then a else b) in
                Hashtbl.set lifted ~key:t ~data:t';
                t')
        | Term.FunApp (T_array.ALambda _, _, _) -> t
        | Term.FunApp (sym, ts, info) ->
            let ts' = List.map ts ~f:lift in
            if List.for_all2_exn ts ts' ~f:Stdlib.( == ) then t
            else Term.mk_fsym_app ~info sym ts'
        | _ -> t
      in
      let args' = List.map args ~f:lift in
      if not !any then [ lit ]
      else
        List.rev !cond_lits
        @ [ rebuild (Atom.mk_app ~info:ainfo pred args') ]
  | _ -> [ lit ]

(* The integer or real bounds a cube literal states, each as
   [(int, strict, d)] meaning [d >= 0] ([d > 0] when [strict]) over integers
   when [int], over reals otherwise: one for an inequality or a negated one,
   two (both directions) for an equality, none for any other literal.  Each
   bound is implied by the literal. *)
let bound_views lit =
  let view neg psym t1 t2 =
    (* [t1 psym t2], negated when [neg] *)
    let int = T_int.is_sint t1 in
    let sub a b = if int then T_int.mk_sub a b else T_real.mk_rsub a b in
    match (psym, neg) with
    | (T_int.Geq | T_real.RGeq), false | (T_int.Lt | T_real.RLt), true ->
        [ (int, false, sub t1 t2) ]
    | (T_int.Gt | T_real.RGt), false | (T_int.Leq | T_real.RLeq), true ->
        [ (int, true, sub t1 t2) ]
    | (T_int.Leq | T_real.RLeq), false | (T_int.Gt | T_real.RGt), true ->
        [ (int, false, sub t2 t1) ]
    | (T_int.Lt | T_real.RLt), false | (T_int.Geq | T_real.RGeq), true ->
        [ (int, true, sub t2 t1) ]
    | T_bool.Eq, false
      when Term.is_int_sort (Term.sort_of t1)
           || Term.is_real_sort (Term.sort_of t1) ->
        [ (int, false, sub t1 t2); (int, false, sub t2 t1) ]
    | _ -> []
  in
  match lit with
  | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) ->
      view false psym t1 t2
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _),
        _ ) ->
      view true psym t1 t2
  | _ -> []

(* The sums of a bound of [l1] and a bound of [l2] over the same sort
   ([bound_views]), each as a normalised literal implied by [l1 /\ l2] (a sum
   of non-negative terms is non-negative, positive when one is positive).
   The numerals of the two bounds are added, so two bounds whose constants
   cancel give a bound without one. *)
let bound_sums l1 l2 =
  List.concat_map (bound_views l1) ~f:(fun (int1, strict1, d1) ->
      List.filter_map (bound_views l2) ~f:(fun (int2, strict2, d2) ->
          if Bool.(int1 <> int2) then None
          else
            let atom =
              if int1 then
                (if strict1 || strict2 then T_int.mk_gt else T_int.mk_geq)
                  (T_int.mk_add d1 d2) (T_int.zero ())
              else
                (if strict1 || strict2 then T_real.mk_rgt else T_real.mk_rgeq)
                  (T_real.mk_radd d1 d2) (T_real.rzero ())
            in
            Some (Normalizer.normalize @@ Formula.mk_atom atom)))

(* The equality of a bit-vector term with a numeral, split into its bits as
   Z3's [expand_literals] does for Spacer's inductive generaliser: [t = n] of
   width [w] becomes the [w] literals [#b1 = ((_ extract j j) t)], negated
   where bit [j] of [n] is 0.  [None] for any other literal. *)
let bits_of_numeral_eq lit =
  let split t size n =
    let w = T_bv.bits_of size in
    let one = T_bv.mk_bvnum ~size:(Some 1) Z.one in
    Some
      (List.init w ~f:(fun j ->
           let bit =
             Formula.eq one (T_bv.mk_bvextract ~size j j t)
           in
           if Z.testbit n j then bit else Formula.mk_neg bit))
  in
  match lit with
  | Formula.Atom
      ( Atom.App
          ( Predicate.Psym T_bool.Eq,
            [ t; Term.FunApp (T_bv.BVNum (size, n), [], _) ],
            _ ),
        _ )
    when not (T_bv.is_bvnum t) ->
      split t size n
  | Formula.Atom
      ( Atom.App
          ( Predicate.Psym T_bool.Eq,
            [ Term.FunApp (T_bv.BVNum (size, n), [], _); t ],
            _ ),
        _ )
    when not (T_bv.is_bvnum t) ->
      split t size n
  | _ -> None

(* [phi] with each comparison of a one-bit term with a numeral opened into
   Boolean connectives, as Z3's [th_rewriter] does to every rule before Spacer
   picks an implicant (the [bv_rewriter] option [bit2bool], on by default):
   [(ite c t e) = k] becomes [c /\ t = k \/ ~c /\ e = k], [(bvnot a) = k]
   becomes [a = 1-k], [(bvneg a) = k] becomes [a = k] (Z3 rewrites [bvneg a]
   to [bvmul (-1) a], and -1 is 1 modulo 2), [(bvor a b) = #b1] becomes
   [a = #b1 \/ b = #b1] (negated for [#b0]), [bvxor] likewise with [xor], and
   [bvand]/[bvnand]/[bvnor]/[bvxnor] are first rewritten into
   [bvnot]/[bvor]/[bvxor] as Z3 does (so [(bvand a b) = #b1] ends as
   [~(a = #b0 \/ b = #b0)]).  A variable or any other one-bit term is left in
   its comparison.  Equivalent to [phi]. *)
let rec bit2bool phi =
  let one_bit = function
    | Term.FunApp (T_bv.BVNum (size, n), [], _) when T_bv.bits_of size = 1 ->
        Some n
    | _ -> None
  in
  let num k = T_bv.mk_bvnum ~size:(Some 1) k in
  let nots = List.map ~f:(T_bv.mk_bvnot ~size:(Some 1)) in
  let bvor = function
    | [ a; b ] -> T_bv.mk_bvor ~size:(Some 1) a b
    | _ -> assert false
  in
  let rec eq t k =
    let flip = Z.(one - k) in
    let bit1 t = eq t Z.one in
    match t with
    | Term.FunApp (T_bv.BVNum _, [], _) -> (
        match one_bit t with
        | Some n when Z.equal n k -> Formula.mk_true ()
        | _ -> Formula.mk_false ())
    | Term.FunApp (T_bool.IfThenElse, [ c; t1; t2 ], _) ->
        let c =
          match c with
          | Term.FunApp (T_bool.Formula phi, [], _) -> bit2bool phi
          | _ -> Formula.of_bool_term c
        in
        Formula.or_of
          [
            Formula.and_of [ c; eq t1 k ];
            Formula.and_of [ Formula.mk_neg c; eq t2 k ];
          ]
    | Term.FunApp (T_bv.BVNot _, [ a ], _) -> eq a flip
    | Term.FunApp (T_bv.BVNeg _, [ a ], _) -> eq a k
    | Term.FunApp (T_bv.BVOr _, args, _) ->
        let d = Formula.or_of @@ List.map args ~f:bit1 in
        if Z.equal k Z.one then d else Formula.mk_neg d
    | Term.FunApp (T_bv.BVXor _, [ a; b ], _) ->
        let d = Formula.mk_xor (bit1 a) (bit1 b) in
        if Z.equal k Z.one then d else Formula.mk_neg d
    | Term.FunApp (T_bv.BVAnd _, args, _) -> eq (bvor (nots args)) flip
    | Term.FunApp (T_bv.BVNand _, args, _) -> eq (bvor (nots args)) k
    | Term.FunApp (T_bv.BVNor _, args, _) -> eq (bvor args) flip
    | Term.FunApp (T_bv.BVXnor _, [ a; b ], _) ->
        eq (T_bv.mk_bvxor ~size:(Some 1) a b) flip
    | _ -> Formula.eq t (num k)
  in
  Formula.map_atom phi ~f:(function
    | Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as op), [ t1; t2 ], _)
      as atom -> (
        let opened =
          match (one_bit t1, one_bit t2) with
          | None, Some k -> Some (eq t1 k)
          | Some k, None -> Some (eq t2 k)
          | _ -> None
        in
        match (opened, op) with
        | Some phi, T_bool.Eq -> phi
        | Some phi, _ -> Formula.mk_neg phi
        | None, _ -> Formula.mk_atom atom)
    | atom -> Formula.mk_atom atom)

(* [lits] (a cube over [args]) with its equalities between variables and
   numerals rewritten into equivalence classes, the shape Z3's model-based
   projection (its term graph) gives a cube when it eliminates the head
   constants of a query with arguments: for each class of variables and
   numerals joined by those equalities, one representative variable (the
   first in [args]) is stated equal to the class's numeral and to each other
   member, and the representative replaces every member in the remaining
   literals.  Only the representative's equality with the numeral is then a
   candidate for [bits_of_numeral_eq]; the members' equalities are word
   equalities.  Equivalent to the conjunction of [lits].  The class literals
   come first, in the order of [args]; Z3's literal order and its choice of
   representative among variables (by term age) were not reproduced.
   Before the classes are formed, each side of an equality or a disequality
   is put through [unneg], the part of Z3's polynomial rewriter that matters here: Z3
   rewrites [bvneg x] to [bvmul(-1, x)] and folds nested numeral factors,
   and [1 * x] is [x], so [bvmul(-1, bvneg x)] and [bvneg (bvneg x)] become
   [x] before its term graph is built.  Both are identities modulo 2^w, so
   the cube stays equivalent.
   With [deqrep], a numeral side of a disequality is also replaced by the
   representative of the class holding that numeral: Z3's term graph prints
   both sides of a disequality as their classes' representatives, preferring
   a constant to a value, so [x != 0] next to [y = 0] reads [x != y].  The
   class literal [y = 0] stays, so the cube stays equivalent; the gain is
   that generalisation may then drop [y = 0] and keep the relation. *)
let eqclass_normal ~deqrep args lits =
  let pos v =
    Option.value_map ~default:Int.max_value ~f:fst
    @@ List.findi args ~f:(fun _ (x, _) -> Stdlib.( = ) x v)
  in
  let same t1 t2 =
    match (t1, t2) with
    | Term.Var (x1, _, _), Term.Var (x2, _, _) -> Stdlib.( = ) x1 x2
    | ( Term.FunApp (T_bv.BVNum (s1, n1), [], _),
        Term.FunApp (T_bv.BVNum (s2, n2), [], _) ) ->
        Stdlib.( = ) (T_bv.bits_of s1) (T_bv.bits_of s2) && Z.equal n1 n2
    | _ -> false
  in
  let member t =
    match t with Term.Var _ -> true | _ -> T_bv.is_bvnum t
  in
  let unneg_eq = function
    | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _) ->
        Formula.eq (unneg t1) (unneg t2)
    | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _) ->
        Formula.neq (unneg t1) (unneg t2)
    | Formula.UnaryOp
        ( Formula.Not,
          Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
          _ ) ->
        Formula.mk_neg @@ Formula.eq (unneg t1) (unneg t2)
    | l -> l
  in
  let classes, others =
    List.fold (List.map lits ~f:unneg_eq) ~init:([], [])
      ~f:(fun (classes, others) l ->
        match l with
        | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _)
          when member t1 && member t2
               && (Term.is_var t1 || Term.is_var t2) ->
            let has t c = List.exists c ~f:(same t) in
            let joined, apart =
              List.partition_tf classes ~f:(fun c -> has t1 c || has t2 c)
            in
            let c =
              List.fold (List.concat joined @ [ t1; t2 ]) ~init:[]
                ~f:(fun c t -> if has t c then c else c @ [ t ])
            in
            (apart @ [ c ], others)
        | _ -> (classes, others @ [ l ]))
  in
  let var_of = function Term.Var (x, _, _) -> Some x | _ -> None in
  let classes =
    List.map classes ~f:(fun c ->
        let vars, nums = List.partition_tf c ~f:Term.is_var in
        let vars =
          List.stable_sort vars ~compare:(fun t1 t2 ->
              Int.compare
                (pos @@ Option.value_exn (var_of t1))
                (pos @@ Option.value_exn (var_of t2)))
        in
        (List.hd_exn vars, List.tl_exn vars, nums))
    |> List.sort ~compare:(fun (r1, _, _) (r2, _, _) ->
           Int.compare
             (pos @@ Option.value_exn (var_of r1))
             (pos @@ Option.value_exn (var_of r2)))
  in
  let sub =
    Map.Poly.of_alist_exn
    @@ List.concat_map classes ~f:(fun (rep, members, _) ->
        List.map members ~f:(fun m -> (Option.value_exn (var_of m), rep)))
  in
  let rep_of_num t =
    if not (T_bv.is_bvnum t) then t
    else
      Option.value ~default:t
      @@ List.find_map classes ~f:(fun (rep, _, nums) ->
          if List.exists nums ~f:(same t) then Some rep else None)
  in
  let deq_rep l =
    if not deqrep then l
    else
      match l with
      | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _)
        ->
          Formula.neq (rep_of_num t1) (rep_of_num t2)
      | Formula.UnaryOp
          ( Formula.Not,
            Formula.Atom
              (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
            _ ) ->
          Formula.mk_neg @@ Formula.eq (rep_of_num t1) (rep_of_num t2)
      | l -> l
  in
  List.concat_map classes ~f:(fun (rep, members, nums) ->
      List.map nums ~f:(Formula.eq rep) @ List.map members ~f:(Formula.eq rep))
  @ List.filter
      (List.map others ~f:(fun l ->
           deq_rep
           @@ if Map.Poly.is_empty sub then l
              else Evaluator.simplify @@ Formula.subst sub l))
      ~f:(Formula.is_true >> not)

(* The two-clause system [phi1 => I(args)], [I(args) /\ not_phi2 => Q(ys)]
   in the fixedpoint format of the z3 binary, with [ys] the free constants of
   the second clause: the shape Z3's [rule_manager::mk_query] gives a formula
   query through the API, which is how [interpolate_untimed]'s Spacer fallback
   asks.  For replaying one interpolation query of a traced run in the z3
   binary; [None] when an argument occurs in neither formula (its sort is read
   off the formulas). *)
let fixedpoint_text_of_interp_query e1 e2 args =
  let consts e =
    let seen = Hash_set.Poly.create () in
    let found = ref [] in
    let rec go e =
      let id = Z3.AST.get_id (Z3.Expr.ast_of_expr e) in
      if not (Hash_set.mem seen id) then (
        Hash_set.add seen id;
        (* bound variables are de Bruijn indices, not constants *)
        if Z3.AST.is_var (Z3.Expr.ast_of_expr e) then ()
        else if Z3.Expr.is_const e then (
          let d = Z3.Expr.get_func_decl e in
          if Stdlib.( = ) (Z3.FuncDecl.get_decl_kind d) Z3enums.OP_UNINTERPRETED
          then
            found :=
              ( Z3.Symbol.to_string (Z3.FuncDecl.get_name d),
                Z3.Sort.to_string (Z3.Expr.get_sort e) )
              :: !found)
        else if Z3.AST.is_quantifier (Z3.Expr.ast_of_expr e) then
          go Z3.Quantifier.(get_body @@ quantifier_of_expr e)
        else List.iter (Z3.Expr.get_args e) ~f:go)
    in
    go e;
    List.rev !found
  in
  let c1 = consts e1 and c2 = consts e2 in
  let sort_of x = List.Assoc.find (c1 @ c2) x ~equal:String.equal in
  let xs = List.map args ~f:(fst >> Ident.name_of_tvar) in
  match Option.all (List.map xs ~f:sort_of) with
  | None -> None
  | Some sorts ->
      let union xs cs =
        xs
        @ List.filter_map cs ~f:(fun (y, _) ->
              if List.mem xs y ~equal:String.equal then None else Some y)
      in
      let vs1 = union xs c1 and vs2 = union xs c2 in
      let binders vs =
        String.concat ~sep:" "
        @@ List.map vs ~f:(fun v ->
               sprintf "(|%s| %s)" v (Option.value_exn (sort_of v)))
      in
      let app p vs =
        sprintf "(%s %s)" p
          (String.concat ~sep:" " @@ List.map vs ~f:(sprintf "|%s|"))
      in
      Some
        (String.concat ~sep:"\n"
           [
             sprintf "(declare-rel interp (%s))" (String.concat ~sep:" " sorts);
             sprintf "(declare-rel qq (%s))"
               (String.concat ~sep:" " @@ List.map vs2 ~f:(fun v ->
                    Option.value_exn (sort_of v)));
             sprintf "(rule (forall (%s) (=> %s %s)))" (binders vs1)
               (Z3.Expr.to_string e1) (app "interp" xs);
             sprintf "(rule (forall (%s) (=> (and %s %s) %s)))" (binders vs2)
               (app "interp" xs) (Z3.Expr.to_string e2) (app "qq" vs2);
             "(query qq)";
           ])

(* The Z3 context and cube solver kept between blocking calls.  Making a context per call paid the
   set-up each time and forced a full major collection before it (the
   collection is what frees the contexts dropped by earlier calls); with one
   kept context there is none to free.  Domain-local, so a context is never
   used by two domains; a call takes the entry out and puts it back when it
   ends, so a call made while another holds the entry (none is made today)
   makes a context of its own.  A
   kept solver is empty: it is reset when put back, which releases what the
   call asserted at once rather than when a collection finalises it.  The
   same questions are asked of an empty solver, so every answer keeps its
   guarantee; models and cores may differ, as Z3's term ids differ. *)
let blocking_contexts :
    (Z3.context * Z3.Solver.solver) option ref Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> ref None)

(* the kept context and solver, if no other call holds them *)
let take_blocking_context () =
  let kept = Stdlib.Domain.DLS.get blocking_contexts in
  let entry = !kept in
  kept := None;
  entry

let put_back_blocking_context ((_, solver) as entry) =
  Z3.Solver.reset solver;
  let kept = Stdlib.Domain.DLS.get blocking_contexts in
  if Option.is_none !kept then kept := Some entry

(* A solver kept across blocking calls for one (predicate, level), in the
   kept context.  [versions]: each antecedent asserted so far (as a Z3
   expression, which the context hash-conses) with the selector [s] of its
   assertion [s => antecedent]; [indicators]: the indicator [a] of each
   literal asserted as [a => literal].  Every assertion is an implication
   from a constant no other assertion constrains, so the solver with the
   selector of one antecedent and some indicators assumed is satisfiable
   exactly when that antecedent and those literals are: the history only
   changes how the solver gets there.  [converted]: the Z3 expression of
   each subformula below the conjunctions and disjunctions of an antecedent
   converted so far, so that a new antecedent sharing subformulas with
   earlier ones (the clause bodies, most lemmas of the frames) converts only
   its new ones.  Conversion into one context is a function of the formula,
   and the conjunctions and disjunctions are rebuilt over their members'
   sets, so equal antecedents up to the order of those members give the same
   expression; emptied with the solver. *)
type level_solver = {
  solver : Z3.Solver.solver;
  mutable versions : (Z3.Expr.expr * Z3.Expr.expr) list;
  mutable indicators : (Formula.t, Z3.Expr.expr) Map.Poly.t;
  converted : (Formula.t, Z3.Expr.expr) Hashtbl.t;
  mutable selectors_made : int;
  mutable last_used : int;
}

(* antecedents one solver holds before it is emptied: a selector left
   unassumed still leaves its antecedent's atoms in the solver *)
let level_solver_versions = 16

(* the kept solvers, by predicate name and level, of the context they were
   made in; domain-local like the context *)
let level_solvers :
    (Z3.context * (string * int, level_solver) Hashtbl.Poly.t * int ref)
    option
    ref
    Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> ref None)

(* the solver of [solvers] for [key], made in [ctx] if there is none; at most
   [cap] are kept, the least recently used ([clock]) is emptied and dropped
   first *)
let level_solver_lru ctx solvers clock ~cap key =
  incr clock;
  match Hashtbl.find solvers key with
  | Some e ->
      e.last_used <- !clock;
      e
  | None ->
      if Hashtbl.length solvers >= cap then (
        let oldest =
          Hashtbl.fold solvers ~init:None ~f:(fun ~key ~data acc ->
              match acc with
              | Some (_, e') when e'.last_used <= data.last_used -> acc
              | _ -> Some (key, data))
        in
        Option.iter oldest ~f:(fun (k, e) ->
            Z3.Solver.reset e.solver;
            Hashtbl.remove solvers k));
      let e =
        {
          solver = Z3.Solver.mk_solver ctx None;
          versions = [];
          indicators = Map.Poly.empty;
          converted = Common.Ext.Hashtbl.PolyDeep.create ();
          selectors_made = 0;
          last_used = !clock;
        }
      in
      Hashtbl.set solvers ~key ~data:e;
      e

(* the solver kept for [key] in [ctx], made if there is none; at most [cap]
   are kept, the least recently used is emptied and dropped first *)
let level_solver_of ctx ~cap key =
  let table = Stdlib.Domain.DLS.get level_solvers in
  let solvers, clock =
    match !table with
    | Some (ctx', solvers, clock) when Stdlib.( == ) ctx ctx' -> (solvers, clock)
    | _ ->
        (* the solvers of another context are not reached any more *)
        Option.iter !table ~f:(fun (_, solvers, _) ->
            Hashtbl.iter solvers ~f:(fun e -> Z3.Solver.reset e.solver));
        let solvers = Hashtbl.Poly.create () and clock = ref 0 in
        table := Some (ctx, solvers, clock);
        (solvers, clock)
  in
  level_solver_lru ctx solvers clock ~cap key

(* the selector under which [e]'s solver holds the antecedent [phi1]
   ([true] when it was asserted by an earlier call) *)
let level_solver_select ctx e phi1 =
  match
    List.find e.versions ~f:(fun (phi, _) -> Z3.Expr.equal phi phi1)
  with
  | Some (_, s) -> (s, true)
  | None ->
      if List.length e.versions >= level_solver_versions then (
        Z3.Solver.reset e.solver;
        e.versions <- [];
        e.indicators <- Map.Poly.empty;
        Hashtbl.clear e.converted);
      (* the count is never restarted, so a selector name is never reused *)
      let s =
        Z3.Boolean.mk_const_s ctx (sprintf "pf_version_%d" e.selectors_made)
      in
      e.selectors_made <- e.selectors_made + 1;
      Z3.Solver.add e.solver [ Z3.Boolean.mk_implies ctx s phi1 ];
      e.versions <- (phi1, s) :: e.versions;
      (s, false)

(* With [COAR_MUCYC_INTERP_STAGE] in the environment, the blocking route prints
   an [interp-stage: <stage> start|end at <s> s] pair on stderr around each of
   its Z3 checks, model conversions and cube extractions (seconds since this
   module was initialised; a cube check is labelled by the generalisation
   step that asked it, or [cube] for a round's own check, followed by an
   [interp-stage: answer <step> sat|unsat|undecided] line; with
   [phi1_bounds] of [Blocking] the model filter before it is the stage
   [model-filter <step>]), so that a call left open when the run is killed
   shows the stage it is in, plus an [interp-stage: blocking raised <exn>]
   line when the route gives up on an exception and an [interp-stage: horn
   route] line when a call is handed to the external CHC solver.  Observation
   only; off, it is one boolean test per stage. *)
let interp_stage = Option.is_some (Sys.getenv "COAR_MUCYC_INTERP_STAGE")

(* [COAR_MUCYC_LEVEL_CHECK] in the environment checks every cube a level
   store seeds unchecked (see [blocking_interpolant]); observation only *)
let level_check = Option.is_some (Sys.getenv "COAR_MUCYC_LEVEL_CHECK")

let interp_stage_origin = Common.Clock.now_float ()

let staged stage f =
  if not interp_stage then f ()
  else
    let line what =
      prerr_endline
        (sprintf "interp-stage: %s %s at %.3f s" (Lazy.force stage) what
           (Time_float.Span.to_sec
              (Time_float.diff (Common.Clock.now_float ()) interp_stage_origin)))
    in
    line "start";
    let r = f () in
    line "end";
    r

(* a literal about divisibility: it mentions an integer division or
   remainder, or is an atom of [|] or [!|] (possibly negated) *)
let divisibility_lit l =
  Set.exists (Formula.funsyms_of l) ~f:(function
    | T_int.Div _ | T_int.Rem _ -> true
    | _ -> false)
  ||
  match l with
  | Formula.Atom (Atom.App (Predicate.Psym (T_int.PDiv | T_int.NotPDiv), _, _), _)
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom
          (Atom.App (Predicate.Psym (T_int.PDiv | T_int.NotPDiv), _, _), _),
        _ ) ->
      true
  | _ -> false

(* The Z3 session kept for [with_base_checks], one per domain
   so that it is never used by two domains; a call takes it out and puts it
   back when it ends, so a call made while another holds it makes its own. *)
let base_check_session : Z3Smt.Z3interface.base_session option ref
    Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> ref None)

(* [f check] where [check phis] asks Z3 about [base /\ phis] and answers as
   [Z3interface.check_sat ~id:None] does on [base :: phis]: [base] is
   converted and asserted once in the domain's kept session and each [phis] in a scope of
   it; the session's [`Sat]/[`Unsat] are Z3's answers about the same
   conjunction (an [`Unsat] there holds in every model exactly when the plain
   one does), and on anything else, or when the session refuses [base], the
   check is asked the plain way. *)
let with_base_checks base f =
  let plain phis =
    Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ()) (base :: phis)
  in
  let kept = Stdlib.Domain.DLS.get base_check_session in
  let session =
    match !kept with
    | Some s ->
        kept := None;
        s
    | None -> Z3Smt.Z3interface.base_session_create ~id:None ()
  in
  Exn.protect
    ~finally:(fun () -> kept := Some session)
    ~f:(fun () ->
      if
        not
          (Z3Smt.Z3interface.base_session_set ~id:None session
             (FunEnv.mk_empty ()) [ base ])
      then f plain
      else
        f (fun phis ->
            match
              Z3Smt.Z3interface.base_session_check ~id:None session
                ~timeout:None (FunEnv.mk_empty ()) (Formula.and_of phis)
            with
            | (`Sat _ | `Unsat) as answer -> answer
            | _ -> plain phis))

(* The bounds on one argument each that [phi1] implies among those stated
   by a top-level conjunct of one of its top-level disjuncts ([bound_views];
   an equality gives both), as normalised literals over that argument only,
   without duplicates; literals about divisibility are left out.  With one
   disjunct each bound is implied by its conjunct; otherwise a bound [b] is
   kept only when Z3 finds [phi1 /\ ~b] unsatisfiable, which holds in no
   model, so [phi1 => b] holds in every one.  [None] when such a check is
   undecided.  A conjunct over several arguments (and nothing else) is read
   the same way, so an equality between arguments gives its two halves.
   The checks go through [with_base_checks].  Each round asks whether [phi1] holds with the negation of
   one of the bounds not yet refuted, and leaves out every bound false in
   the model's values of the arguments, until the answer is unsatisfiable:
   a bound left out is false in a model of [phi1], and those remaining are
   implied as their disjunction's negation is, so the same bounds are kept
   as by one check each (the result keeps the order of the candidates).  A
   round whose model refutes none (it leaves the arguments unvalued) goes
   back to one check per remaining bound. *)
let phi1_arg_bounds args phi1 =
  let argset = Set.Poly.of_list @@ List.map args ~f:fst in
  let disjuncts = Set.to_list (Formula.disjuncts_of (Formula.nnf_of phi1)) in
  let bounds_of disjunct =
    Set.to_list (Formula.conjuncts_of disjunct)
    |> List.concat_map ~f:(fun l ->
        let tvs = Formula.tvs_of l in
        if
          (not (Set.is_empty tvs))
          && Set.is_subset tvs ~of_:argset
          && not (divisibility_lit l)
        then
          List.map (bound_views l) ~f:(fun (int, strict, d) ->
              Normalizer.normalize @@ Formula.mk_atom
              @@
              if int then
                (if strict then T_int.mk_gt else T_int.mk_geq)
                  d (T_int.zero ())
              else
                (if strict then T_real.mk_rgt else T_real.mk_rgeq)
                  d (T_real.rzero ()))
        else [])
  in
  let candidates =
    List.stable_dedup ~compare:Stdlib.compare
      (List.concat_map disjuncts ~f:bounds_of)
  in
  (* the bounds of [bs] false in the arguments' values in [model] *)
  let refuted_by model bs =
    let env = convert_model false Set.Poly.empty model in
    let env = Map.Poly.filter_keys env ~f:(Set.mem argset) in
    match model_values env with
    | None -> []
    | Some env ->
        List.filter bs ~f:(fun b ->
            Set.for_all (Formula.tvs_of b) ~f:(Map.Poly.mem env)
            &&
            try not (Evaluator.eval ~env b)
            with exn_ when not (Common.Timer.is_async exn_) -> false)
  in
  (match disjuncts with
  | [ _ ] -> Some candidates
  | _ ->
      with_base_checks phi1 (fun check ->
          let one_by_one bs =
            List.fold bs ~init:(Some []) ~f:(fun acc b ->
                match acc with
                | None -> None
                | Some kept -> (
                    match
                      staged (lazy "bound-check") (fun () ->
                          check [ Formula.negate b ])
                    with
                    | `Unsat ->
                        if interp_stage then
                          prerr_endline "interp-stage: answer bound unsat";
                        Some (b :: kept)
                    | `Sat _ ->
                        if interp_stage then
                          prerr_endline "interp-stage: answer bound sat";
                        Some kept
                    | _ -> None))
            |> Option.map ~f:List.rev
          in
          let rec rounds bs =
            if List.is_empty bs then Some []
            else
              match
                staged (lazy "bound-round") (fun () ->
                    check [ Formula.or_of (List.map bs ~f:Formula.negate) ])
              with
              | `Unsat ->
                  if interp_stage then
                    prerr_endline "interp-stage: answer bound-round unsat";
                  Some bs
              | `Sat model -> (
                  if interp_stage then
                    prerr_endline "interp-stage: answer bound-round sat";
                  match refuted_by model bs with
                  | [] -> one_by_one bs
                  | out ->
                      rounds
                        (List.filter bs ~f:(fun b ->
                             not (List.mem out b ~equal:Stdlib.( == )))))
              | _ -> None
          in
          rounds candidates))

(* [interp] without those of its top-level conjuncts among [candidates]
   that the rest does not need to imply [phi2], tried one at a time in the
   order of [candidates]: a conjunct is dropped only when Z3 finds the
   remaining conjuncts with [~phi2] unsatisfiable, and is kept on any other
   answer.  Each conjunct being implied by [interp], whatever implies
   [interp] still implies the result.  Only for formulas where an
   unsatisfiable answer holds in every model (no interpretation-dependent
   term), as in the blocking loop over its sorts.  A conjunct also counts as
   a candidate when it normalises to one (the loop may print a premise
   differently from how it was given).  The checks go through
   [with_base_checks]. *)
let drop_unneeded_conjuncts candidates interp phi2 =
  let not_phi2 = Formula.negate phi2 in
  let conjuncts = Set.to_list (Formula.conjuncts_of interp) in
  let is_b b c =
    Stdlib.( = ) c b || Stdlib.( = ) (Normalizer.normalize c) b
  in
  let kept =
    with_base_checks not_phi2 (fun check ->
        List.fold candidates ~init:conjuncts ~f:(fun kept b ->
            if not (List.exists kept ~f:(is_b b)) then kept
            else
              let rest = List.filter kept ~f:(fun c -> not (is_b b c)) in
              match check rest with
              | `Unsat -> rest
              | _ -> kept
              | exception exn_ when not (Common.Timer.is_async exn_) -> kept))
  in
  Formula.and_of kept

(* the most cubes a level store keeps per predicate (oldest dropped first,
   which only loses seeds); a cube is a few literals, so the cap bounds
   pathological runs, not ordinary ones *)
let level_store_cap = 4096

(* The bit-level checker the loop may ask a cube check of instead of Z3: a
   propositional encoding of bit-vector formulas kept per domain, whose
   [checker_check] answers [`Sat] only on a model of the conjunction and
   [`Unsat core] with the assumed literals' tags of an unsatisfiable subset.
   [Decline] is raised for a formula it does not encode; the loop then asks
   Z3.  The library holds no implementation (one needs a SAT solver); the
   caller passes its own, and without one every check goes to Z3. *)
module type BIT_CHECKER = sig
  type checker
  type lit
  type model

  exception Decline of string

  val checker :
    ?domain:bool ->
    ?def_templates:bool ->
    ?nl_relevant:bool ->
    ?leaf_ctx:bool ->
    unit ->
    checker

  val checker_lit :
    ?lazy_nonlinear:bool -> ?leaf_templates:bool -> checker -> Formula.t -> lit

  val lit_equal : lit -> lit -> bool

  val checker_check :
    ?pin:lit -> checker -> ('a * lit) list -> [ `Sat | `Unsat of 'a list ]

  val model_words : Formula.t -> (string * int) list
  val last_model : checker -> (string * int) list -> model
  val holds : checker -> model -> Formula.t -> bool
  val debug_model_value : checker -> Formula.t -> string
end

(* no bit-level checker: declines every formula *)
module No_bits : BIT_CHECKER = struct
  type checker = unit
  type lit = unit
  type model = unit

  exception Decline of string

  let checker ?domain:_ ?def_templates:_ ?nl_relevant:_ ?leaf_ctx:_ () = ()

  let checker_lit ?lazy_nonlinear:_ ?leaf_templates:_ () _ =
    raise (Decline "no bit-level checker")

  let lit_equal () () = true
  let checker_check ?pin:_ () _ = raise (Decline "no bit-level checker")
  let model_words _ = []
  let last_model () _ = ()
  let holds () () _ = false
  let debug_model_value () _ = ""
end

let phase_time = Common.PhaseTime.with_phase

(* An interpolant of [phi1 => phi2] over [args] by Spacer's blocking loop on
   the two-clause system [phi1 => X(args)], [X(args) /\ ~phi2 => false], with
   plain unsat cores (Spacer with [spacer.use_iuc] false; Komuravelli, Gurfinkel
   and Chaki, CAV 2014, for the procedure).  Each round takes a model of
   [I /\ ~phi2], where [I] is the conjunction of the lemmas so far, and builds
   a cube over [args] from it: the implicant literals of [~phi2] at the model
   ([implicant]; [phi2]'s one-bit circuits are first opened by [bit2bool], as
   Z3 rewrites a rule's body before Spacer's implicant sees it), then each other variable eliminated by an implicant equality
   solved for it (after splitting each equality with a constructor term by
   testers and selectors), else (with [project], for an integer, a real, a
   datatype or an array variable) by [project], a model-based projection of
   the literals at the model, else
   replaced by its model value.  The cube implies the
   existential closure of [~phi2] over the other variables and is true at the
   model.  If [phi1 /\ cube] is unsatisfiable, the cube is generalised as
   Spacer's [lemma_inductive_generalizer] does on this system, where its
   inductiveness check is [phi1 /\ cube' unsat] because [X] has no recursive
   rule: (1) drop each literal in turn, and on success keep only the
   literals in the returned core; (2) split each remaining equality with a
   numeral into its bits ([bits_of_numeral_eq]) and drop bits the same way,
   restoring the equality when no bit can be dropped.  The lemma is the
   negated cube.  Every lemma is implied by [phi1], so on exit (when
   [I /\ ~phi2] is unsatisfiable) [I] is an interpolant over [args].
   Termination: each lemma is false at the model its cube came from, so no
   cube is built twice; over bit-vectors and Booleans no assignment to [args]
   is visited twice, and over integers and reals the cubes range over a
   finite set when [project] has a finite image and no model value enters a
   cube for an unbounded sort; the bound is exponential, hence
   [max_rounds].
   Not done as Spacer does: an [extract]/[bvadd] equation is not solved for a
   variable and no equal-valued term is sought before falling back on the
   model value (both only make the cube less general), and a conditional term
   inside an atom is kept whole unless [bit2bool] opens it (Z3 also lifts
   other conditional terms out of atoms, up to a size bound).
   [`Answer (Some i)] an interpolant; [`Answer None] when [phi1 /\ cube] is
   satisfiable and [~phi2] is satisfiable at that model's values of [args],
   which refutes the query (the two clauses quantify the variables outside
   [args] separately); [`Fallback] when the rounds run out, a check is
   undecided, a quantifier or an unexpected formula is met, or a model or a
   cube fails its check.  Every lemma, and the exit, rest on
   unsatisfiability, so [`Answer (Some i)] holds in every model of the
   theory.  A refutation holds in the model of [phi1 /\ cube] it is read
   from, because the cube implies the existential closure of [~phi2] in
   every model (implicant literals, solved equalities, a projection and
   closed model values each give such a cube) provided the cube's
   simplification and projection interpret terms as every model does: no
   term whose value a model leaves open.  Over bit-vectors, Booleans,
   integers and reals that model is a standard one and Z3's is taken as it
   comes; with [check_refutation] (for the other sorts, where Z3 is known to
   return a model contradicting an equality of array literals) that model is
   first evaluated on [phi1 /\ cube], and a refutation whose model fails is
   [`Fallback].
   [cache], when given, holds the generalised cubes of earlier calls for the
   same predicate (so over the same [args]), most recent first.  Each is
   checked against this [phi1] first and, when [phi1 /\ cube] is
   unsatisfiable, its negation seeds the lemmas, so the interpolant's
   guarantee above is unchanged (every lemma is still implied by [phi1]);
   [phi1] may change in any way between calls.  Each cube carries the
   [seed_key]s of the last (at most [max_keys]) calls that found
   [phi1 /\ cube] unsatisfiable, most recent first; when one is structurally
   equal to this call's [seed_key] (given), the cube seeds the lemmas
   without a check.  The caller guarantees that equal keys mean [phi1]s
   equivalent over [args]; the cubes that pass a check or are seeded take
   this call's key.  [key_covers k k'], when given, also seeds a cube
   carrying [k] unchecked under this call's key [k']; the caller guarantees
   that it holds only when this [phi1] implies (up to the renaming of
   variables other than [args]) the one of the call keyed [k], so that the
   cube stays excluded.  An exception it raises counts as [false].  With
   [negative], each cube also carries the keys (at most [max_keys]) of the
   calls whose check found [phi1 /\ cube] satisfiable, and is left out of
   the seeds without a check when this call's key equals or covers one of
   them as [key_covers k' nk] (so this [phi1] is at most as strong); leaving
   a cube out is always sound, and gives the seeds the check would give;
   [refuted] is set to the number of cubes left out so.  [skipped] is set to the number of cubes
   seeded unchecked.  The cubes this call learns are pushed onto it with
   this call's key, keeping at most [max_rounds]; [max_rounds] bounds the
   cubes learned per call, not the seeds.  A call answering [`Answer None]
   or [`Fallback] adds no cube to it.  [reused] is set to the number of seeds,
   [cached] to the number of cubes checked for them and [seed_secs] to the
   wall-clock seconds of those checks (with the solver's set-up);
   [exit_secs] to the seconds of the [I /\ ~phi2] checks and of reading their
   models, [block_secs] to the seconds of building, checking and
   generalising the cubes, [cube_secs] to the part of those spent building
   them from models, and [checks] to the number of cube checks.
   [setup_secs] is set to the seconds of making the call's Z3 context and
   cube solver (included in whichever stage first needs them) and [gc_secs]
   to the part of those spent in the forced full major collection.
   The cube checks' context and solver are taken from [blocking_contexts]
   (made there by the first call) and put back emptied when the call ends,
   by return or by raise; no collection is forced then, and [gc_secs] is 0
   for a call that found one kept.
   [premises] are formulas over [args] that the caller guarantees [phi1]
   implies; they are lemmas from the start, unchecked, so the guarantee above
   holds exactly when the caller's does.
   [level_store] and [level], given together: the store holds cubes with the
   levels at which a call found them excluded.  The caller guarantees that a
   cube excluded by the [phi1] of an earlier call at [level] is excluded by
   this [phi1] (frames only ever strengthened, and [phi1] monotone in them);
   such cubes seed the lemmas unchecked, so the guarantee above again holds
   exactly when the caller's does.  Cubes recorded at [level - 1] are checked
   (a push), cubes recorded only lower are not seeded, and the store's
   decisions take precedence over the cache's; this call's seeds and learned
   cubes are recorded at [level].  [level_seeded] is set to the number of
   unchecked level seeds and [pushed] to the number of successful pushes;
   with [level_check] every unchecked level seed is checked anyway and a
   satisfiable one reported on stderr. *)
let blocking_interpolant ?(premises = []) ?(rounds = ref 0) ?(reused = ref 0) ?(cached = ref 0)
    ?(seed_secs = ref 0.) ?(exit_secs = ref 0.) ?(block_secs = ref 0.) ?(cube_secs = ref 0.)
    ?(checks = ref 0) ?(skipped = ref 0) ?(setup_secs = ref 0.)
    ?(gc_secs = ref 0.) ?(first_check_secs = ref 0.) ?(check_secs = ref 0.)
    ?(sat_checks = ref 0) ?(sat_check_secs = ref 0.) ?(sat_models = false)
    ?(sat_model_hits = ref 0) ?cache ?seed_key ?(max_keys = 1)
    ?level_store ?level ?(level_check = false) ?(level_seeded = ref 0)
    ?solver_key ?(kept_solvers = 0) ?(kept_hits = ref 0) ?bit_checker
    ?(lazy_nonlinear = false) ?(definition_templates = false)
    ?(lazy_nonlinear_relevant = false) ?(leaf_contexts = false)
    ?(leaf_templates = false)
    ?(kept_bit_models = false) ?(model_answers = ref 0)
    ?(incremental_exit = false) ?(exit_simple = false) ?(bit_domain = false)
    ?(bit_domain_pin = false)
    ?(pushed = ref 0) ?key_covers ?(negative = false) ?(refuted = ref 0)
    ?(sum_bounds = false) ?(expand_bounds = false) ?(expand_strict = false) ?(check_refutation = false) ?(narrow_first = false)
    ?project ~print ~max_rounds ~eqclass
    args phi1 phi2 =
  let bit_level = Option.is_some bit_checker in
  let module B =
    (val Option.value bit_checker ~default:(module No_bits : BIT_CHECKER))
  in
  (* elapsed time of the stages of a blocking check, printed with [print]:
     [restart] starts the clock, [lap s] reports the time since the last
     report as stage [s] *)
  let stamp = ref (Time_float.now ()) in
  let restart () = stamp := Time_float.now () in
  let lap stage =
    let now = Time_float.now () in
    let span = Time_float.Span.to_sec (Time_float.diff now !stamp) in
    print @@ lazy (sprintf "  blocking time %s: %.3f s" stage span);
    stamp := now
  in
  let argset = Set.Poly.of_list @@ List.map args ~f:fst in
  let check phis =
    Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ()) phis
  in
  let not_phi2 = Formula.nnf_of @@ Formula.negate @@ bit2bool phi2 in
  (* a converted model kept at the variables of [senv] only; the formulas
     evaluated under it mention no others.  A model over arrays also names
     the auxiliary functions Z3 interprets arrays by ([as-array]), which
     have function sorts, no value the loop can hold, and nothing to do with
     the question; kept, such a model makes the loop give up on the call *)
  let in_scope senv model =
    let xs = Set.Poly.map senv ~f:fst in
    Map.Poly.filter_keys model ~f:(Set.mem xs)
  in
  (* the model is read on [~phi2] and on [I], which mentions [args] only *)
  let senv2 =
    Set.union (Formula.term_sort_env_of not_phi2) (Set.Poly.of_list args)
  in
  (* One Z3 context and solver for every cube check of this call: [phi1] is
     asserted once, each literal [l] met in a cube once as [a_l => l] with a
     fresh Boolean constant [a_l], and a check assumes the [a_l] of its cube,
     as Spacer keeps one solver per frame and passes a cube as assumptions.
     A fresh context per check paid the context set-up each time and held
     memory until the OCaml finaliser of its handle ran, which a small OCaml
     heap delays (one single-threaded run held 4 GB after 30 s); scoping each
     cube with push/pop instead stalled checks a fresh solver answered (Z3
     preprocesses less inside a scope).  The contexts of earlier calls are
     still freed only by their finalisers, which the collector runs late
     (it does not see a context's memory), so a context made here (none was
     kept) is counted with
     the ones [Z3interface] makes and the same forced full major collection
     precedes it: without it one single-threaded run (with Z3's proofs on) grew to
     4.7 GB and did not answer in 30 s, with it the same input was answered
     in 19 s and 0.9 GB. *)
  (* the context and solver to put back when the call ends *)
  let held = ref None in
  (* the indicator of each literal asserted so far, by the literal *)
  let indicators = ref Map.Poly.empty in
  (* with [solver_key] and [kept_solvers > 0]: the kept solver for the key
     and the selector of [phi1] in it, assumed by every check *)
  let level_entry = ref None in
  (* [phi1] as a Z3 expression of the call's context, set with [z3] *)
  let phi1_z3 = ref None in
  let secs_since t =
    Time_float.Span.to_sec (Time_float.diff (Time_float.now ()) t)
  in
  (* the call's context, its cube solver (the kept one, if any), the
     environments of [phi1] and [~phi2] in it, and the seconds this took;
     shared by the cube checks ([z3]) and, with [incremental_exit], the exit
     check, either of which may come first *)
  let context =
    lazy
      (let open Z3Smt.Z3interface in
       let set_up_at = Time_float.now () in
       let ctx, kept_solver =
         match take_blocking_context () with
         | Some (ctx, solver) ->
             held := Some (ctx, solver);
             (ctx, Some solver)
         | None ->
             if
               Atomic.fetch_and_add new_contexts 1
               % Atomic.get new_context_full_major_every
               = 0
             then Gc.full_major ();
             gc_secs := secs_since set_up_at;
             ( Z3.mk_context [ ("model", "true"); ("unsat_core", "true") ],
               None )
       in
       (* the set-up's steps are phases [blk-env], [blk-convert] and
          [blk-assert] under COAR_MUCYC_PHASE_TIME; observation only *)
       let dtenv, fenv =
         phase_time "blk-env" @@ fun () ->
         let dtenv =
           z3_dtenv_of_formula ctx @@ Formula.and_of [ phi1; not_phi2 ]
         in
         ( dtenv,
           z3_fenv_of ~id:None ctx [] []
             (fenv_for_query (FunEnv.mk_empty ()) [ phi1 ])
             dtenv )
       in
       let solver =
         match kept_solver with
         | Some solver -> solver
         | None -> Z3.Solver.mk_solver ctx None
       in
       held := Some (ctx, solver);
       (ctx, kept_solver, solver, dtenv, fenv, secs_since set_up_at))
  in
  let z3 =
    lazy
      (let open Z3Smt.Z3interface in
       let ctx, kept_solver, solver, dtenv, fenv, context_secs =
         Lazy.force context
       in
       let set_up_at = Time_float.now () in
       (* the kept solver for this call, only in the kept context, which
          outlives the call *)
       let entry =
         match (solver_key, kept_solver) with
         | Some key, Some _ when kept_solvers > 0 ->
             Some (level_solver_of ctx ~cap:kept_solvers key)
         | _ -> None
       in
       let e1 =
         phase_time "blk-convert" @@ fun () ->
         let convert = of_formula_with_z3fenv ~id:None ctx [] [] fenv dtenv in
         match entry with
         | Some e ->
             (* through the conjunctions and disjunctions, each other
                subformula through the memo of the kept solver; the
                antecedent is rebuilt by every call, and its frame lemmas
                come back in another order, so converting it whole cost
                one input 10 s in 30 s and missed the version it already
                held.  With COAR_MUCYC_PHASE_TIME, [kept-memo-miss] counts
                the subformulas converted; observation only *)
             let rec conv phi =
               if Formula.is_and phi then
                 Z3.Boolean.mk_and ctx
                 @@ List.map ~f:conv @@ Set.to_list
                 @@ Formula.conjuncts_of phi
               else if Formula.is_or phi then
                 Z3.Boolean.mk_or ctx
                 @@ List.map ~f:conv @@ Set.to_list
                 @@ Formula.disjuncts_of phi
               else
                 Hashtbl.find_or_add e.converted phi ~default:(fun () ->
                     Common.PhaseTime.event "kept-memo-miss";
                     convert phi)
             in
             conv phi1
         | _ -> convert phi1
       in
       phi1_z3 := Some e1;
       let solver =
         phase_time "blk-assert" @@ fun () ->
         match entry with
         | Some e ->
             let s, hit = level_solver_select ctx e e1 in
             (* with COAR_MUCYC_PHASE_TIME, counts of the calls served by a
                kept solver, by whether it already held the antecedent;
                observation only *)
             Common.PhaseTime.event
               (if hit then "pf-kept-hit" else "pf-kept-version");
             if hit then incr kept_hits;
             level_entry := Some (e, s);
             e.solver
         | _ ->
             Z3.Solver.add solver [ e1 ];
             solver
       in
       setup_secs := context_secs +. secs_since set_up_at;
       (ctx, solver, fenv, dtenv))
  in
  (* with [incremental_exit]: the call's exit solver and the number of
     lemmas asserted in it so far, made at the first exit check; [None] in
     [exit_off] once the solver refused a formula (conversion failed, or a
     quantifier, which [check_sat] asks differently), after which the call's
     exit checks are asked as without it *)
  let exit_solver = ref None in
  let exit_off = ref (not incremental_exit) in
  let incremental_check lemmas =
    let open Z3Smt.Z3interface in
    let ctx, _, _, dtenv, fenv, _ = Lazy.force context in
    (* [check_sat] rewrites the array-literal equalities Z3 does not decide
       before converting; the same rewrite is applied here *)
    let convert phi =
      of_formula_with_z3fenv ~id:None ctx [] [] fenv dtenv
        (expand_finite_array_eqs phi)
    in
    let solver, asserted =
      match !exit_solver with
      | Some entry -> entry
      | None ->
          Common.PhaseTime.event "blk-exit-incremental-solver";
          (* with [exit_simple], Z3's plain incremental core, without the
             preprocessing tactics the default solver runs on a first check:
             the same assertions, so the same question *)
          let solver =
            if exit_simple then (
              Common.PhaseTime.event "blk-exit-simple-solver";
              Z3.Solver.mk_simple_solver ctx)
            else Z3.Solver.mk_solver ctx None
          in
          let e =
            Common.PhaseTime.with_phase "to-z3" (fun () -> convert not_phi2)
          in
          Common.PhaseTime.with_phase "assert" (fun () ->
              Z3.Solver.add solver [ e ]);
          exit_solver := Some (solver, 0);
          (solver, 0)
    in
    (* [lemmas] is the previous round's list with new lemmas in front *)
    let fresh = List.take lemmas (List.length lemmas - asserted) in
    let es =
      Common.PhaseTime.with_phase "to-z3" (fun () -> List.map fresh ~f:convert)
    in
    Common.PhaseTime.with_phase "assert" (fun () -> Z3.Solver.add solver es);
    exit_solver := Some (solver, List.length lemmas);
    check_sat_z3 ~query:(`Query (not_phi2 :: lemmas)) ctx solver dtenv []
  in
  (* the exit check: [lemmas] together with [~phi2], asked as [check] asks
     it, or of the call's exit solver *)
  let exit_check lemmas =
    if
      !exit_off
      || Atomic.get Z3Smt.Z3interface.int_to_bv_range
      || not
           (List.for_all (not_phi2 :: lemmas) ~f:Formula.is_quantifier_free)
    then check [ Formula.and_of lemmas; not_phi2 ]
    else
      try incremental_check lemmas
      with exn_ when not (Common.Timer.is_async exn_) ->
        Common.PhaseTime.event "blk-exit-incremental-declined";
        exit_off := true;
        check [ Formula.and_of lemmas; not_phi2 ]
  in
  let indicator_of l =
    let ctx, solver, fenv, dtenv = Lazy.force z3 in
    (* a kept solver's indicators are its own, kept with it *)
    let known () =
      match !level_entry with Some (e, _) -> e.indicators | None -> !indicators
    in
    match Map.Poly.find (known ()) l with
    | Some a -> a
    | None ->
        let a =
          Z3.Boolean.mk_const_s ctx
            (sprintf "interp_lit_%d" (Map.Poly.length (known ())))
        in
        let l' =
          Z3Smt.Z3interface.of_formula_with_z3fenv ~id:None ctx [] [] fenv
            dtenv l
        in
        Z3.Solver.add solver [ Z3.Boolean.mk_implies ctx a l' ];
        (match !level_entry with
        | Some (e, _) -> e.indicators <- Map.Poly.set e.indicators ~key:l ~data:a
        | None -> indicators := Map.Poly.set !indicators ~key:l ~data:a);
        a
  in
  (* with [sat_models], the models of this call's cube checks answered
     satisfiable: each satisfies [phi1], so a
     cube true in one is satisfiable with [phi1].  Z3's model with
     completion is a model of the asserted formulas, so this answers as the
     check would have (in the sense of Z3's [sat]) *)
  let kept_models = ref [] in
  let true_in_a_kept_model lits =
    (not (List.is_empty !kept_models))
    &&
    let ctx, _, fenv, dtenv = Lazy.force z3 in
    let es =
      List.map lits ~f:(fun l ->
          Z3Smt.Z3interface.of_formula_with_z3fenv ~id:None ctx [] [] fenv
            dtenv l)
    in
    List.exists !kept_models ~f:(fun m ->
        List.for_all es ~f:(fun e ->
            match Z3.Model.eval m e true with
            | Some v -> Z3.Boolean.is_true v
            | None -> false))
  in
  (* [`Unsat core] with the members of [lits] in the core, or [`Sat];
     [tag] only names the asking step on the stage lines *)
  let check_cube_z3 ?(tag = "cube") lits =
    if
      sat_models
      && staged
           (lazy (sprintf "model-filter %s" tag))
           (fun () -> true_in_a_kept_model lits)
    then (
      incr sat_model_hits;
      `Sat)
    else
    let first = !checks = 0 in
    incr checks;
    let _, solver, _, _ =
      if Lazy.is_val z3 then Lazy.force z3
      else staged (lazy "setup") (fun () -> Lazy.force z3)
    in
    let assumed = List.map lits ~f:(fun l -> (l, indicator_of l)) in
    (* the seconds of the check itself, of the call's first check and of
       the satisfiable ones, for the timing line; observation only *)
    let checked_at = Time_float.now () in
    let answer =
      try
        Ok
          (staged
             (lazy
               (sprintf "cube-check %s first %b lits %d" tag first
                  (List.length lits)))
             (fun () ->
               Z3Smt.Z3interface.z3_check solver
                 (List.map assumed ~f:snd
                 @ Option.to_list (Option.map !level_entry ~f:snd))))
      with Z3.Error _ as exn_ -> Error exn_
    in
    let secs =
      Time_float.Span.to_sec (Time_float.diff (Time_float.now ()) checked_at)
    in
    check_secs := !check_secs +. secs;
    if first then first_check_secs := !first_check_secs +. secs;
    if interp_stage then
      prerr_endline
        (sprintf "interp-stage: answer %s %s" tag
           (match answer with
           | Ok Z3.Solver.SATISFIABLE -> "sat"
           | Ok Z3.Solver.UNSATISFIABLE -> "unsat"
           | _ -> "undecided"));
    (match answer with
    | Ok Z3.Solver.SATISFIABLE ->
        incr sat_checks;
        sat_check_secs := !sat_check_secs +. secs;
        if sat_models then
          Option.iter (Z3.Solver.get_model solver) ~f:(fun m ->
              kept_models := m :: !kept_models)
    | _ -> ());
    match Result.ok_exn answer with
    | Z3.Solver.UNSATISFIABLE ->
        let core =
          List.map ~f:Z3.Expr.to_string
          @@ Z3Smt.Z3interface.z3_solver_get_unsat_core solver
        in
        `Unsat
          (List.filter_map assumed ~f:(fun (l, a) ->
               if List.mem core (Z3.Expr.to_string a) ~equal:String.equal then
                 Some l
               else None))
    | Z3.Solver.SATISFIABLE -> `Sat
    | Z3.Solver.UNKNOWN -> `Undecided
    | exception Z3.Error _ -> `Undecided
  in
  (* with a [bit_checker], for a call a kept solver would serve: the domain's
     propositional checker and the literal of [phi1] in it, encoded on the
     first check; [None] when the checker declines [phi1] (the reason is
     printed), and then every check of the call goes to Z3 *)
  let bits =
    lazy
      (if bit_level && kept_solvers > 0 && Option.is_some solver_key then (
         let c = B.checker ~domain:bit_domain
             ~def_templates:definition_templates
             ~nl_relevant:lazy_nonlinear_relevant ~leaf_ctx:leaf_contexts () in
         match
           phase_time "blk-bits-encode" (fun () ->
               B.checker_lit ~lazy_nonlinear ~leaf_templates c phi1)
         with
         | root -> Some (c, root)
         | exception B.Decline reason ->
             (* the reason's first two words name its kind *)
             Common.PhaseTime.event
               ("blk-bits-declined "
               ^ String.concat ~sep:" "
                   (List.take (String.split reason ~on:' ') 2));
             print @@ lazy (sprintf "  bit-level checks declined: %s" reason);
             None)
       else None)
  in
  (* with [kept_bit_models], the words' values of the models of this call's
     checker [sat] answers, each a model of [phi1] (see
     [B.last_model]), with the truth of the literals evaluated on it
     so far (by their literal in the checker) and the literal that last
     falsified it, tested first.  All of the call's models are kept: a
     model is rejected by a lookup of that literal, and a call asks a
     bounded number of checks *)
  let bit_models = ref [] in
  let phi1_words = lazy (B.model_words phi1) in
  (* whether a kept model makes every literal of [lits] true; then [phi1]
     and [lits] have a common model and the check would answer [sat] *)
  let answered_by_a_bit_model c lits =
    (not (List.is_empty !bit_models))
    &&
    match List.map lits ~f:(fun l -> (l, B.checker_lit ~lazy_nonlinear ~leaf_templates c l)) with
    | exception B.Decline _ -> false
    | keyed ->
        List.exists !bit_models ~f:(fun (m, memo, last) ->
            let holds (l, k) =
              Hashtbl.find_or_add memo k ~default:(fun () ->
                  B.holds c m l)
            in
            (match !last with
            | Some k0 -> (
                match
                  List.find keyed ~f:(fun (_, k) -> B.lit_equal k k0)
                with
                | Some lk -> holds lk
                | None -> true)
            | None -> true)
            &&
            match List.find keyed ~f:(fun lk -> not (holds lk)) with
            | Some (_, k) ->
                last := Some k;
                false
            | None -> true)
  in
  (* the check of [check_cube_z3] asked of the checker; [None] when there
     is none for the call or it declines a literal of [lits] *)
  let check_cube_bits ?tag lits =
    match Lazy.force bits with
    | None -> None
    | Some (c, _)
      when kept_bit_models && Option.is_some tag
           && phase_time "blk-bits-model-filter" (fun () ->
                  answered_by_a_bit_model c lits) ->
        Common.PhaseTime.event "blk-bits-model-answer";
        incr model_answers;
        Some `Sat
    | Some (c, root) -> (
        match
          phase_time "blk-bits-encode" (fun () ->
              List.map lits ~f:(fun l ->
                  (Some l, B.checker_lit ~lazy_nonlinear ~leaf_templates c l)))
        with
        | exception B.Decline reason ->
            Common.PhaseTime.event "blk-bits-declined-literal";
            print @@ lazy (sprintf "  bit-level check declined: %s" reason);
            None
        | assumed ->
            let first = !checks = 0 in
            incr checks;
            let checked_at = Time_float.now () in
            match
              phase_time "blk-bits-check" (fun () ->
                  B.checker_check
                    ?pin:(if bit_domain_pin then Some root else None)
                    c
                    ((None, root) :: assumed))
            with
            | exception B.Decline reason ->
                (* a definition [lazy_nonlinear] needed was declined: the
                   instance cannot answer [sat] *)
                Common.PhaseTime.event "blk-bits-declined-definition";
                print @@ lazy (sprintf "  bit-level check declined: %s" reason);
                None
            | answer ->
            let secs =
              Time_float.Span.to_sec
                (Time_float.diff (Time_float.now ()) checked_at)
            in
            check_secs := !check_secs +. secs;
            if first then first_check_secs := !first_check_secs +. secs;
            Some
              (match answer with
              | `Sat ->
                  if Option.is_some (Sys.getenv "COAR_BITS_SAT_CHECK") then
                    eprintf "bits-sat-check %s\n%!"
                      (B.debug_model_value c
                         (Formula.and_of (phi1 :: lits)));
                  incr sat_checks;
                  sat_check_secs := !sat_check_secs +. secs;
                  if kept_bit_models then
                    phase_time "blk-bits-model-read" (fun () ->
                        bit_models :=
                          ( B.last_model c (Lazy.force phi1_words),
                            Hashtbl.Poly.create (),
                            ref None )
                          :: !bit_models);
                  `Sat
              | `Unsat core -> `Unsat (List.filter_map core ~f:Fn.id)))
  in
  let check_cube ?tag lits =
    match check_cube_bits ?tag lits with
    | Some answer -> answer
    | None -> check_cube_z3 ?tag lits
  in
  (* Spacer's round 1 on [lits] (all of which are needed for unsat with
     [phi1] as a set, not one by one): try each literal of [candidates] in
     turn; [None] when a check is undecided *)
  let drop lits candidates =
    let rec go lits = function
      | [] -> Some lits
      | l :: rest ->
          if not (List.mem lits l ~equal:Stdlib.( == )) then go lits rest
          else (
            match
              check_cube ~tag:"drop"
                (List.filter lits ~f:(fun l' -> not (Stdlib.( == ) l l')))
            with
            | `Unsat core -> go core rest
            | `Sat -> go lits rest
            | `Undecided -> None)
    in
    go lits candidates
  in
  let weaken lits =
    let rec go lits = function
      | [] -> Some lits
      | l :: rest -> (
          match bits_of_numeral_eq l with
          | None -> go lits rest
          | Some bits -> (
              if not (List.mem lits l ~equal:Stdlib.( == )) then go lits rest
              else
                let others =
                  List.filter lits ~f:(fun l' -> not (Stdlib.( == ) l l'))
                in
                match drop (others @ bits) bits with
                | None -> None
                | Some lits' ->
                    if
                      List.for_all bits ~f:(fun b ->
                          List.mem lits' b ~equal:Stdlib.( == ))
                    then go lits rest
                    else go lits' rest))
    in
    go lits lits
  in
  (* replace each integer or real equality of [lits] by one of the two
     bounds it implies ([bound_views]), the first that [phi1] still
     excludes; the result is weaker as a cube and still holds at the model
     [lits] came from, and each literal is tried once, so the step stops.
     An equality neither bound of which is excluded is kept, and a cube
     without integer or real equalities (a bit-vector cube) is returned as
     it was.  So a cube [x = -4] read off one model can become the bound
     [x <= -4], which the bound expansion can then widen, instead of one
     lemma per value of [x]; the negation of the weaker cube is a stronger
     lemma that [phi1] still implies.  Each tried bound costs one check.
     [None] when a check is undecided *)
  let weaken_eq lits =
    let rec go lits = function
      | [] -> Some lits
      | l :: rest -> (
          match bound_views l with
          | [ _; _ ] as views when List.mem lits l ~equal:Stdlib.( == ) ->
              let others =
                List.filter lits ~f:(fun l' -> not (Stdlib.( == ) l l'))
              in
              let bound (int, strict, d) =
                Normalizer.normalize @@ Formula.mk_atom
                @@
                if int then
                  (if strict then T_int.mk_gt else T_int.mk_geq)
                    d (T_int.zero ())
                else
                  (if strict then T_real.mk_rgt else T_real.mk_rgeq)
                    d (T_real.rzero ())
              in
              (* [bound_views] gives [t1 - t2 >= 0] first; [t1 <= t2] is
                 tried first, as the second *)
              let rec try_bounds = function
                | [] -> go lits rest
                | b :: bs -> (
                    match check_cube ~tag:"weaken-eq" (bound b :: others) with
                    | `Unsat core -> go core rest
                    | `Sat -> try_bounds bs
                    | `Undecided -> None)
              in
              try_bounds (List.rev views)
          | _ -> go lits rest)
    in
    go lits lits
  in
  (* with [sum_bounds], replace two literals of [lits] by a sum of their
     integer or real bounds ([bound_sums]) while [phi1] still excludes the
     result, first pair first, until no pair passes; the result is weaker as
     a cube (it holds wherever [lits] does), so its negation is a stronger
     lemma, and it still holds at the model [lits] came from.  A sum whose
     numerals cancel drops the constants a cube read off one model, so that
     one lemma can stand for the family a deeper and deeper search would
     otherwise exclude one member at a time.  [None] when a check is
     undecided *)
  let sum lits =
    let pairs lits =
      List.concat_mapi lits ~f:(fun i l1 ->
          List.filter_mapi lits ~f:(fun j l2 ->
              if i < j then Some (l1, l2) else None))
    in
    (* with [expand_bounds], a pair of two literals of the input cube whose
       sum alone is not excluded is also tried as the sum next to one of the
       two, again a weaker cube; such a step replaces an input literal by a
       sum, and a step of the plain kind shortens the cube, so (input
       literals left, length) decreases and the loop stops *)
    let input l = List.mem lits l ~equal:Stdlib.( == ) in
    let rec go lits =
      let rec try_pairs = function
        | [] -> Some lits
        | (l1, l2) :: rest -> (
            let others =
              List.filter lits ~f:(fun l ->
                  not (Stdlib.( == ) l l1 || Stdlib.( == ) l l2))
            in
            let rec try_cubes = function
              | [] -> `Next
              | cube :: cubes -> (
                  let r = check_cube ~tag:"sum" cube in
                  print
                  @@ lazy
                       (sprintf "  blocking sum candidate (%s): %s"
                          (match r with
                          | `Unsat _ -> "excluded"
                          | `Sat -> "not excluded"
                          | `Undecided -> "undecided")
                          (String.concat ~sep:" /\\ "
                             (List.map cube ~f:Formula.str_of)));
                  match r with
                  | `Unsat core -> `Found core
                  | `Sat -> try_cubes cubes
                  | `Undecided -> `Undecided)
            in
            let sums =
              List.filter (bound_sums l1 l2)
                ~f:(Fn.non Formula.is_true)
            in
            let kept =
              if expand_bounds && input l1 && input l2 then
                List.concat_map sums ~f:(fun s ->
                    [ s :: l1 :: others; s :: l2 :: others ])
              else []
            in
            match
              try_cubes (List.map sums ~f:(fun s -> s :: others) @ kept)
            with
            | `Found core -> go core
            | `Next -> try_pairs rest
            | `Undecided -> None)
      in
      try_pairs (pairs lits)
    in
    if sum_bounds then go lits else Some lits
  in
  (* with [expand_bounds], Spacer's bound expansion (Z3's
     lemma_expand_bnd_generalizer): replace the numeral of each integer or
     real inequality [t + c >= 0] (or [> 0]) of [lits] by a larger one taken
     from the numerals of [phi1] and [phi2] and their negations, weakest
     first, keeping the first that [phi1] still excludes; the cube only gets
     weaker, and the candidates are finitely many; the first excluded one is
     found by bisection, in about log2 of the candidates' checks.  The numeral [c] is the
     value of the bound at all variables zero, the bound being linear.
     With [expand_strict], a non-strict real literal also tries [t + c' > 0]
     after [t + c' >= 0]; for [c' > c] it still contains [t + c >= 0] and is
     contained in [t + c' >= 0], so the order stays weakest first.
     [None] when a check is undecided *)
  let numerals =
    lazy
      (let ns = ref [] in
       let collect t =
         match t with
         | Term.FunApp (T_int.Int n, [], _) ->
             ns := Q.of_bigint n :: Q.of_bigint (Z.neg n) :: !ns
         | Term.FunApp (T_real.Real r, [], _) -> ns := r :: Q.neg r :: !ns
         | _ -> ()
       in
       Formula.iter_term ~f:collect phi1;
       Formula.iter_term ~f:collect phi2;
       List.dedup_and_sort ~compare:Q.compare (Q.zero :: !ns))
  in
  let expand lits =
    let rec go lits = function
      | [] -> Some lits
      | l :: rest -> (
          if not (List.mem lits l ~equal:Stdlib.( == )) then go lits rest
          else
            match bound_views l with
            | [ (int, strict, d) ] -> (
                let zero =
                  Map.Poly.of_alist_exn
                  @@ List.map (Set.to_list (Term.tvs_of d)) ~f:(fun x ->
                      (x, if int then T_int.zero () else T_real.rzero ()))
                in
                match Evaluator.eval_term (Term.subst zero d) with
                | (Value.Int _ | Value.Real _) as v ->
                    let c =
                      match v with
                      | Value.Int n -> Q.of_bigint n
                      | v -> Value.real_of v
                    in
                    let others =
                      List.filter lits ~f:(fun l' -> not (Stdlib.( == ) l l'))
                    in
                    let candidate ?(strict = strict) c' =
                      let shifted =
                        if int then
                          T_int.mk_add d (T_int.mk_int (Q.to_bigint (Q.sub c' c)))
                        else T_real.mk_radd d (T_real.mk_real (Q.sub c' c))
                      in
                      Normalizer.normalize @@ Formula.mk_atom
                      @@
                      if int then
                        (if strict then T_int.mk_gt else T_int.mk_geq)
                          shifted (T_int.zero ())
                      else
                        (if strict then T_real.mk_rgt else T_real.mk_rgeq)
                          shifted (T_real.rzero ())
                    in
                    (* the first excluded candidate of the weakest-first
                       array, by bisection: a weaker bound gives a weaker
                       cube, so the excluded candidates are a suffix of the
                       array.  Every candidate below [lo] is satisfiable,
                       every one from [hi] on excluded, and [found] holds the
                       core of the check at [hi] *)
                    let bisect cands =
                      let cands = Array.of_list cands in
                      let rec search lo hi found =
                        if lo >= hi then
                          match found with
                          | None -> go lits rest
                          | Some core -> go core rest
                        else
                          let mid = (lo + hi) / 2 in
                          match
                            check_cube ~tag:"expand" (cands.(mid) :: others)
                          with
                          | `Unsat core -> search lo mid (Some core)
                          | `Sat -> search (mid + 1) hi found
                          | `Undecided -> None
                      in
                      search 0 (Array.length cands) None
                    in
                    bisect
                      (List.concat_map
                         (List.rev
                         @@ List.filter (Lazy.force numerals) ~f:(fun c' ->
                             Q.(c' > c)
                             && ((not int) || Z.equal (Q.den c') Z.one)))
                         ~f:(fun c' ->
                           if expand_strict && (not int) && not strict then
                             [ candidate c'; candidate ~strict:true c' ]
                           else [ candidate c' ]))
                | _ -> go lits rest
                | exception exn_ when not (Common.Timer.is_async exn_) ->
                    go lits rest)
            | _ -> go lits rest)
    in
    if expand_bounds then go lits lits else Some lits
  in
  let cube_of model =
    let lets = ref Map.Poly.empty in
    let lits =
      phase_time "blk-cube-implicant" (fun () ->
          implicant ~lets model not_phi2)
    in
    let elim x = not (Set.mem argset x) in
    (* equality elimination, one solved equality at a time *)
    let rec solve lits =
      let solved =
        List.find_map lits ~f:(fun l ->
            match l with
            | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _)
              -> (
                let solved_for v t =
                  elim v && not (Set.mem (Term.fvs_of t) v)
                in
                match (t1, t2) with
                | Term.Var (v, _, _), t when solved_for v t -> Some (l, v, t)
                | t, Term.Var (v, _, _) when solved_for v t -> Some (l, v, t)
                | _ -> None)
            | _ -> None)
      in
      match solved with
      | None -> lits
      | Some (l, v, t) ->
          let sub = Map.Poly.singleton v t in
          solve
          @@ List.filter_map lits ~f:(fun l' ->
              if Stdlib.( == ) l l' then None else Some (Formula.subst sub l'))
    in
    (* an equality [s = C(t1, ..., tn)] is first read as
       [is_C(s) /\ sel_1(s) = t1 /\ ... /\ sel_n(s) = tn] (two constructor
       terms: as [ti = si], or as false for two constructors), equivalent in
       every model of the datatype theory: [solve] can then take a variable
       under the constructor to a selector term of [s] instead of its model
       value, as Spacer's datatype projection does, and the generalisation can
       drop or weaken one component of an argument instead of the whole
       constructor term *)
    let rec decompose l =
      let split s c =
        match (s, c) with
        | Term.Var (v, _, _), _ when elim v -> None
        | ( Term.FunApp (T_dt.DTCons (n1, _, _), ss, _),
            Term.FunApp (T_dt.DTCons (n2, _, _), ts, _) ) ->
            if String.(n1 = n2) && List.length ss = List.length ts then
              Some (List.concat @@ List.map2_exn ss ts ~f:(fun si ti ->
                  decompose (Formula.eq si ti)))
            else Some [ Formula.mk_false () ]
        | _, Term.FunApp (T_dt.DTCons (name, _, dt), ts, _) ->
            Some
              (Formula.mk_atom (T_dt.mk_is_cons dt name s)
              :: List.concat
                   (List.mapi ts ~f:(fun i ti ->
                        decompose
                          (Formula.eq (T_dt.mk_sel_by_cons dt name i s) ti))))
        | _ -> None
      in
      match l with
      | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _)
      | Formula.UnaryOp
          ( Formula.Not,
            Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _),
            _ ) -> (
          match split t1 t2 with
          | Some ls -> ls
          | None -> ( match split t2 t1 with Some ls -> ls | None -> [ l ]))
      | _ -> [ l ]
    in
    let lits = List.concat_map lits ~f:decompose in
    print
    @@ lazy
         (let rest =
            Set.filter
              (Formula.term_sort_env_of @@ Formula.and_of lits)
              ~f:(fst >> elim)
          in
          "  blocking implicant eliminates: "
          ^ str_of_sort_env_list Term.str_of_sort (Set.to_list rest));
    let lits = phase_time "blk-cube-solve" (fun () -> solve lits) in
    let values = Map.force_merge model !lets in
    let lits =
      match project with
      | None -> Some lits
      | Some project -> (
          let ys =
            Set.filter
              (Formula.term_sort_env_of @@ Formula.and_of lits)
              ~f:(fun (x, s) ->
                elim x
                && (Term.is_int_sort s || Term.is_real_sort s
                   || Term.is_dt_sort s || Term.is_array_sort s))
          in
          if Set.is_empty ys then Some lits
          else
            (* the projection may decline a literal it cannot read (a
               non-linear one, say); the round then falls back *)
            try
              let projected =
                project
                  (Map.Poly.map values ~f:(Term.of_value (get_dtenv ())))
                  ys (Formula.and_of lits)
              in
              let ynames = Set.Poly.map ys ~f:fst in
              if Set.is_empty (Set.inter (Formula.fvs_of projected) ynames)
              then Some (Formula.conjuncts_list_of projected)
              else None
            with exn_ when not (Common.Timer.is_async exn_) -> None)
    in
    match lits with
    | None -> None
    | Some lits ->
    let dtenv = get_dtenv () in
    let lits =
      phase_time "blk-cube-values" @@ fun () ->
      List.map lits ~f:(fun l ->
          let rest = Set.filter (Formula.fvs_of l) ~f:elim in
          Evaluator.simplify
          @@ Formula.subst
               (Map.Poly.of_alist_exn
               @@ List.map (Set.to_list rest) ~f:(fun x ->
                   (x, Term.of_value dtenv @@ Map.Poly.find_exn values x)))
               l)
    in
    let lits = List.filter lits ~f:(Formula.is_true >> not) in
    let lits =
      if eqclass then (
        let normal = eqclass_normal ~deqrep:true args lits in
        (* With COAR_MUCYC_PHASE_TIME set, a census of where the class form
           acts: [blk-cube] counts the cubes reaching it, [blk-eqclass-changed]
           those whose literals (as a set of printed literals) it changes,
           [blk-eqclass-reordered] those it only reorders, and
           [blk-deqrep-changed] those whose literals differ with and without
           [deqrep].  Observation only: the cube kept is [normal] either way. *)
        if !Common.PhaseTime.on then (
          (* a literal printed with the sides of an (in)equality ordered, so
             that turning [x = y] into [y = x] is not counted as a change *)
          let str = function
            | Formula.Atom
                (Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as p),
                           [ t1; t2 ], _), _) ->
                let s1 = Term.str_of t1 and s2 = Term.str_of t2 in
                let s1, s2 = if String.(s1 <= s2) then (s1, s2) else (s2, s1) in
                (if Stdlib.( = ) p T_bool.Eq then "=" else "!=")
                ^ " " ^ s1 ^ " " ^ s2
            | l -> Formula.str_of l
          in
          let strs ls = List.sort ~compare:String.compare (List.map ls ~f:str) in
          let plain = eqclass_normal ~deqrep:false args lits in
          Common.PhaseTime.event "blk-cube";
          if not (List.equal String.equal (strs plain) (strs lits)) then
            Common.PhaseTime.event "blk-eqclass-changed"
          else if not (List.equal String.equal
                         (List.map plain ~f:Formula.str_of)
                         (List.map lits ~f:Formula.str_of)) then
            Common.PhaseTime.event "blk-eqclass-reordered";
          if not (List.equal String.equal (strs normal) (strs plain))
          then Common.PhaseTime.event "blk-deqrep-changed");
        normal)
      else lits
    in
    let lits = guard_selectors lits in
    print
    @@ lazy
         ("  blocking cube: "
         ^ String.concat ~sep:" /\\ " (List.map lits ~f:Formula.str_of));
    if
      List.for_all lits ~f:(fun l ->
          (not (Formula.is_false l))
          && Set.for_all (Formula.fvs_of l) ~f:(Set.mem argset)
          && eval_at ~env:model l)
    then Some lits
    else None
  in
  (* the generalisation of an excluded cube: each step keeps a cube [phi1]
     still excludes and only weakens it; [None] when a step fails *)
  let generalise core =
    Option.bind
      (Option.bind (drop core core) ~f:weaken)
      ~f:(fun lits ->
        Option.bind (weaken_eq lits) ~f:(fun lits ->
            Option.bind (sum lits) ~f:expand))
    |> Option.map ~f:guard_selectors
  in
  (* the cached cubes [phi1] still excludes; [None] when a check is
     undecided, which is not taken as a failure of the cube; called inside
     the handler below, as its checks build the solver *)
  (* [keys] with this call's [seed_key] moved or put first, at most
     [max_keys] long *)
  let equal_key k k' =
    Stdlib.( == ) k k'
    || try Stdlib.( = ) k k'
       with exn_ when not (Common.Timer.is_async exn_) -> false
  in
  let add_key keys =
    match seed_key with
    | None -> keys
    | Some k ->
        List.take
          (k
          :: List.filter keys ~f:(fun k' -> not (equal_key k k')))
          (max 1 max_keys)
  in
  (* with [level_store] and [level]: the stored cubes recorded at [level],
     seeded without a check, and those recorded only at [level - 1] that a
     check finds still blocked (recorded at [level] too); a push whose check
     is undecided is left out, which is sound; and the stored cubes a push
     check found satisfiable.  A push found satisfiable at [level] under
     frames keyed [nk] is not checked again at [level] while this call's key
     is [nk] or covered by it (these frames are at most as strong), as the
     cache's negative keys do.  A stored cube recorded only below
     [level - 1] is not checked at all (as IC3 moves a lemma up one frame
     at a time): leaving a seed out is always sound *)
  let level_seeds () =
    let failed_before nfail j =
      match seed_key with
      | None -> false
      | Some k' ->
          List.exists nfail ~f:(fun (l, nk) ->
              l = j
              && (equal_key k' nk
                 ||
                 match key_covers with
                 | Some f -> (
                     try f k' nk
                     with exn_ when not (Common.Timer.is_async exn_) ->
                       false)
                 | None -> false))
    in
    let add_failed nfail j =
      match seed_key with
      | None -> nfail
      | Some k -> List.take ((j, k) :: nfail) (max 1 max_keys)
    in
    match (level_store, level) with
    | Some store, Some j ->
        let entries =
          List.map !store ~f:(fun (cube, lvls, nfail) ->
              if Set.mem lvls j then (
                incr level_seeded;
                Common.PhaseTime.event "pf-level-seed";
                (* With COAR_MUCYC_LEVEL_CHECK set, each cube seeded by its
                   level is checked all the same and a satisfiable check is
                   reported: the store's soundness argument says it never
                   is.  Observation only. *)
                if level_check then (
                  match check_cube ~tag:"level-check" cube with
                  | `Sat ->
                      Common.PhaseTime.event "pf-level-disagree";
                      prerr_endline
                        (sprintf "pf-level-disagree: level %d cube %s" j
                           (Formula.str_of (Formula.and_of cube)))
                  | `Unsat _ | `Undecided -> ());
                ((cube, lvls, nfail), `Seed))
              else if Set.mem lvls (j - 1) then
                if failed_before nfail j then (
                  Common.PhaseTime.event "pf-push-skip";
                  ((cube, lvls, nfail), `Sat))
                else (
                  Common.PhaseTime.event "pf-push-check";
                  match check_cube ~tag:"push" cube with
                  | `Unsat _ ->
                      incr pushed;
                      Common.PhaseTime.event "pf-push-ok";
                      ((cube, Set.add lvls j, nfail), `Seed)
                  | `Sat -> ((cube, lvls, add_failed nfail j), `Sat)
                  | `Undecided -> ((cube, lvls, nfail), `No))
              else if
                match Set.max_elt lvls with Some l -> l < j - 1 | None -> false
              then (
                Common.PhaseTime.event "pf-low-skip";
                ((cube, lvls, nfail), `Sat))
              else ((cube, lvls, nfail), `No))
        in
        store := List.map entries ~f:fst;
        ( List.filter_map entries ~f:(fun ((cube, _, _), seed) ->
              match seed with `Seed -> Some cube | _ -> None),
          List.filter_map entries ~f:(fun ((cube, _, _), seed) ->
              match seed with `Sat -> Some cube | _ -> None) )
    | _ -> ([], [])
  in
  (* records [cubes], each blocked by this call's [phi1], at [level] *)
  let record_level cubes =
    match (level_store, level) with
    | Some store, Some j ->
        let fresh =
          List.filter cubes ~f:(fun cube ->
              not (List.exists !store ~f:(fun (c, _, _) -> phys_equal c cube)))
        in
        store :=
          List.take
            (List.map fresh ~f:(fun cube -> (cube, Int.Set.singleton j, []))
            @ List.map !store ~f:(fun (c, lvls, nfail) ->
                if List.exists cubes ~f:(phys_equal c) then
                  (c, Set.add lvls j, nfail)
                else (c, lvls, nfail)))
            level_store_cap
    | _ -> ()
  in
  let seeds () =
    let level_started = Time_float.now () in
    let by_level, level_sat = phase_time "blk-level-seeds" level_seeds in
    let level_secs =
      Time_float.Span.to_sec (Time_float.diff (Time_float.now ()) level_started)
    in
    let by_level_hit cube = List.exists by_level ~f:(phys_equal cube) in
    let level_sat_hit cube = List.exists level_sat ~f:(phys_equal cube) in
    (* [seed_secs] also counts the level store's checks *)
    Exn.protect ~finally:(fun () -> seed_secs := !seed_secs +. level_secs)
    ~f:(fun () ->
    Option.map ~f:(fun seeds ->
        let seeds =
          seeds @ List.filter by_level ~f:(fun c ->
              not (List.exists seeds ~f:(phys_equal c)))
        in
        phase_time "blk-seed-record" (fun () -> record_level seeds);
        seeds)
    @@
    match cache with
    | None -> Some []
    | Some cache ->
        let covers k k' =
          equal_key k k'
          ||
          match key_covers with
          | Some f -> (
              try f k k'
              with exn_ when not (Common.Timer.is_async exn_) -> false)
          | None -> false
        in
        (* [covers k k'] and [covers k' nk] for this call's key [k'],
           remembered by the physical identity of the other key: the cached
           cubes share key values (a call puts its one key on every cube it
           seeds or learns), so without it the same few pairs of frames are
           compared once per cube, which was most of the seeding's time on
           BV inputs with large caches.  A key's answer is a function of the
           key, as [k'] is fixed for the call; buckets are found by the
           bounded structural hash and searched by physical equality *)
        let memo_by_identity f =
          let tbl = Stdlib.Hashtbl.create 16 in
          fun k ->
            let h = Stdlib.Hashtbl.hash k in
            let bucket =
              Option.value ~default:[] (Stdlib.Hashtbl.find_opt tbl h)
            in
            match List.find bucket ~f:(fun (k0, _) -> phys_equal k0 k) with
            | Some (_, b) -> b
            | None ->
                let b = f k in
                Stdlib.Hashtbl.replace tbl h ((k, b) :: bucket);
                b
        in
        let covered_by_call, covers_call =
          match seed_key with
          | Some k' ->
              ( memo_by_identity (fun k -> covers k k'),
                memo_by_identity (fun nk -> covers k' nk) )
          | None -> ((fun _ -> false), fun _ -> false)
        in
        let same keys =
          match seed_key with
          | Some _ -> (
              match List.findi keys ~f:(fun _ k -> covered_by_call k) with
              | None -> false
              | Some (i, _) ->
                  (* With COAR_MUCYC_PHASE_TIME set, a census of what keys
                     beyond the most recent buy: [blk-key-hit-first] counts the
                     cubes seeded by their first key, [blk-key-hit-later] those
                     seeded only by a later one.  Observation only. *)
                  Common.PhaseTime.event
                    (if i = 0 then "blk-key-hit-first" else "blk-key-hit-later");
                  true)
          | None -> false
        in
        (* with [negative]: some frames under which the cube's check
           answered [`Sat] are at most as strong as this call's *)
        let known_sat nkeys =
          negative
          &&
          List.exists nkeys ~f:covers_call
        in
        (* counted as the cubes reach their check below *)
        cached := 0;
        let started = Time_float.now () in
        Exn.protect
          ~finally:(fun () ->
            seed_secs :=
              Time_float.Span.to_sec (Time_float.diff (Time_float.now ()) started))
          ~f:(fun () ->
            List.fold_until !cache ~init:[]
              ~finish:(fun acc ->
                let acc = List.rev acc in
                (* re-key the cubes that passed under this call's [phi1] *)
                cache :=
                  List.map acc ~f:(function
                    | `Seed (keys, nkeys, cube) -> (add_key keys, nkeys, cube)
                    | `Keep entry -> entry);
                Some
                  (List.filter_map acc ~f:(function
                    | `Seed (_, _, cube) -> Some cube
                    | `Keep _ -> None)))
              ~f:(fun acc (keys, nkeys, cube) ->
                if phase_time "blk-seed-hit" (fun () -> by_level_hit cube) then
                  Continue (`Seed (keys, nkeys, cube) :: acc)
                else if phase_time "blk-seed-hit" (fun () -> level_sat_hit cube) then
                  (* the store decided it: a failed push (remembered there)
                     or a cube recorded only at lower levels *)
                  Continue (`Keep (keys, nkeys, cube) :: acc)
                else if
                  phase_time "blk-seed-same" (fun () -> same keys)
                then (
                  incr skipped;
                  Continue (`Seed (keys, nkeys, cube) :: acc))
                else if phase_time "blk-seed-known-sat" (fun () -> known_sat nkeys)
                then (
                  incr refuted;
                  Continue (`Keep (keys, nkeys, cube) :: acc))
                else (
                  incr cached;
                  match check_cube ~tag:"seed" cube with
                  | `Unsat _ -> Continue (`Seed (keys, nkeys, cube) :: acc)
                  | `Sat ->
                      let nkeys = if negative then add_key nkeys else nkeys in
                      Continue (`Keep (keys, nkeys, cube) :: acc)
                  | `Undecided -> Stop None))))
  in
  let timed acc f =
    let started = Time_float.now () in
    Exn.protect ~f ~finally:(fun () ->
        acc :=
          !acc
          +. Time_float.Span.to_sec (Time_float.diff (Time_float.now ()) started))
  in
  (* [learned]: the cubes this call blocked, most recent first.  With
     COAR_MUCYC_PHASE_TIME set, the loop's steps are phases of their own
     ([blk-exit], [blk-model], [blk-eval], [blk-cube-of], [blk-first],
     [blk-generalise], [blk-answer], [blk-record-level]), so that the OCaml
     work around the solver checks is accounted step by step; observation
     only *)
  let rec loop n lemmas learned =
    let interp = Formula.and_of lemmas in
    match
      timed exit_secs (fun () ->
          staged
            (lazy
              (sprintf "exit-check lemmas %d" (List.length lemmas)))
            (fun () ->
              phase_time "blk-exit" (fun () -> exit_check lemmas)))
    with
    | `Unsat ->
        let interp =
          phase_time "blk-answer" (fun () ->
              Evaluator.simplify (Formula.and_of lemmas))
        in
        print
        @@ lazy
             (sprintf "  interpolant by %d blocking rounds (%d reused): %s" n
                !reused (Formula.str_of interp));
        rounds := n;
        Option.iter cache ~f:(fun cache ->
            cache :=
              List.take
                (List.map learned ~f:(fun cube -> (add_key [], [], cube)) @ !cache)
                max_rounds);
        phase_time "blk-record-level" (fun () -> record_level learned);
        `Answer (Some interp)
    | `Sat model when n < max_rounds -> (
        match
          timed exit_secs (fun () ->
              staged (lazy "convert-model") (fun () ->
                  phase_time "blk-model" (fun () ->
                      model_values
                        (in_scope senv2 (convert_model true senv2 model)))))
        with
        | None ->
            print @@ lazy "  blocking: a model value is not closed";
            if interp_stage then
              Map.Poly.iteri (convert_model true senv2 model)
                ~f:(fun ~key ~data ->
                  if not (Set.is_empty (Term.fvs_of data)) then
                    prerr_endline
                      (sprintf "interp-stage: open model value %s = %s"
                         (Ident.name_of_tvar key)
                         (String.prefix (Term.str_of data) 300)));
            `Fallback
        | Some model -> (
        match
        timed block_secs @@ fun () ->
        if
          not
            (staged (lazy "eval-model") (fun () ->
                 phase_time "blk-eval" (fun () ->
                     eval_at ~env:model (Formula.mk_and interp not_phi2))))
        then (
          print @@ lazy "  blocking: the model fails";
          `Fallback)
        else
          match
            timed cube_secs (fun () ->
                staged (lazy "cube-of") (fun () ->
                    phase_time "blk-cube-of" (fun () -> cube_of model)))
          with
          | None ->
              print @@ lazy "  blocking: a cube fails";
              `Fallback
          | Some cube -> (
              (* Spacer takes the interpolating core of the blocking check
                 only; its generaliser's checks use plain cores.  The core is
                 rechecked against [phi1], which Spacer does not do *)
              restart ();
              (* the loop's choice among the literals of the cube: with
                 [narrow_first], first the cube's non-divisibility literals
                 (no integer division or remainder, no [|]/[!|]) over one
                 variable each, when [phi1] still excludes them; otherwise,
                 or when it does not, the core of the whole cube.  A lemma
                 bounding one argument (as [a >= -1] against [a + b <= -1])
                 keeps that argument bounded whatever the others do.  It is
                 a subset of [cube], so it holds at [model] and the lemma is
                 as valid *)
              let narrowed =
                if not narrow_first then None
                else
                  let rest =
                    List.filter cube ~f:(fun l ->
                        (not (divisibility_lit l))
                        && Set.length (Formula.tvs_of l) = 1)
                  in
                  if List.is_empty rest || List.length rest = List.length cube
                  then None
                  else
                    match check_cube ~tag:"narrow-first" rest with
                    | `Unsat core ->
                        print @@ lazy "  blocking: narrow first";
                        Some (`Unsat core)
                    | `Sat | `Undecided -> None
              in
              let first =
                match narrowed with
                | Some first -> first
                | None ->
                phase_time "blk-first" (fun () -> check_cube cube)
              in
              match first with
              | `Undecided -> `Fallback
              | `Sat -> (
                  (* the solver's model is restricted to the cube's
                     variables; a model of [phi1] itself is asked for *)
                  match check (phi1 :: cube) with
                  | `Sat model1
                    when check_refutation
                         && not
                              (let senv1 =
                                 Set.union
                                   (Formula.term_sort_env_of phi1)
                                   (Set.Poly.of_list args)
                               in
                               try
                                 Evaluator.eval
                                   ~env:
                                     (Map.Poly.map
                                        (in_scope senv1
                                           (convert_model true senv1 model1))
                                        ~f:Evaluator.eval_term)
                                   (Formula.and_of (phi1 :: cube))
                               with exn_ when not (Common.Timer.is_async exn_)
                               -> false) ->
                      print @@ lazy "  blocking: a refutation's model fails";
                      `Fallback
                  | `Sat model1 -> (
                      let model1 = convert_model true (Set.Poly.of_list args) model1 in
                      let at_args =
                        Map.Poly.filter_keys model1 ~f:(Set.mem argset)
                      in
                      match check [ Formula.subst at_args not_phi2 ] with
                      | `Sat _ ->
                          print @@ lazy "  blocking: jointly satisfiable";
                          `Answer None
                      | _ ->
                          print @@ lazy "  blocking: a refutation fails its check";
                          `Fallback)
                  | _ -> `Fallback)
              | `Unsat core -> (
                  restart ();
                  let generalised =
                    phase_time "blk-generalise" (fun () -> generalise core)
                  in
                  lap "generalise";
                  match generalised with
                  | None -> `Fallback
                  | Some cube ->
                      let lemma = Formula.negate @@ Formula.and_of cube in
                      print
                      @@ lazy ("  blocking lemma: " ^ Formula.str_of lemma);
                      `Next (lemma, cube)))
        with
        | `Next (lemma, cube) ->
            loop (n + 1) (lemma :: lemmas) (cube :: learned)
        | (`Answer _ | `Fallback) as res -> res))
    | `Sat _ ->
        print @@ lazy (sprintf "  blocking exceeds %d rounds" max_rounds);
        `Fallback
    | _ -> `Fallback
  in
  Stdlib.Fun.protect
    ~finally:(fun () ->
      (* released now rather than when a collection finalises it *)
      Option.iter !exit_solver ~f:(fun (solver, _) -> Z3.Solver.reset solver);
      Option.iter !held ~f:put_back_blocking_context)
  @@ fun () ->
  (* the text is built in a context of its own: forcing [z3] here would set up
     the loop's context under verbose only -- taking a kept context even
     when [seeds] falls back without
     the loop asking anything, creating the query's terms in it before the
     loop does, and keeping the set-up time out of its "setup" stage *)
  print
  @@ lazy
       (let open Z3Smt.Z3interface in
        let ctx = Z3.mk_context [] in
        let dtenv =
          z3_dtenv_of_formula ctx @@ Formula.and_of [ phi1; not_phi2 ]
        in
        let fenv =
          z3_fenv_of ~id:None ctx [] []
            (fenv_for_query (FunEnv.mk_empty ()) [ phi1 ])
            dtenv
        in
        let conv = of_formula_with_z3fenv ~id:None ctx [] [] fenv dtenv in
        match
          fixedpoint_text_of_interp_query (conv phi1) (conv not_phi2) args
        with
        | Some text -> "  blocking query as a fixedpoint:\n" ^ text
        | None -> "  blocking query as a fixedpoint: an argument is unused"
        | exception exn_ when not (Common.Timer.is_async exn_) ->
            "  blocking query as a fixedpoint: " ^ Exn.to_string exn_);
  try
    match phase_time "blk-seeds" seeds with
    | None ->
        print @@ lazy "  blocking: a cached cube's check is undecided";
        `Fallback
    | Some seeds ->
        reused := List.length seeds;
        (* With COAR_MUCYC_PHASE_TIME set, a census of where the cube cache
           acts: [blk-call] counts the calls reaching the loop and
           [blk-call-seeded] those it seeds with a cached cube.  Observation
           only. *)
        Common.PhaseTime.event "blk-call";
        if not (List.is_empty seeds) then
          Common.PhaseTime.event "blk-call-seeded";
        loop 0
          (List.map seeds ~f:(fun cube -> Formula.negate @@ Formula.and_of cube)
          @ premises)
          []
  with exn_ when not (Common.Timer.is_async exn_) ->
    print @@ lazy ("  blocking: " ^ Exn.to_string exn_);
    if interp_stage then
      prerr_endline
        ("interp-stage: blocking raised "
        ^ String.prefix (Exn.to_string exn_) 300);
    `Fallback

(* The counters of one call of [blocking_interpolant] through [interpolate]
   (see there for each), with the call's wall-clock seconds [call_secs] and
   which of the kept state the call actually used: [cache_used] when a cube
   cache was passed and the query admits it, [level] the level of the level
   store, [solver_level] that of the kept per-level solvers.  For the
   caller's timing line; no answer depends on them. *)
type stats = {
  rounds : int;
  reused : int;
  cached : int;
  seed_secs : float;
  exit_secs : float;
  block_secs : float;
  cube_secs : float;
  checks : int;
  skipped : int;
  refuted : int;
  setup_secs : float;
  gc_secs : float;
  first_check_secs : float;
  check_secs : float;
  sat_checks : int;
  sat_check_secs : float;
  sat_model_hits : int;
  level_seeded : int;
  pushed : int;
  kept_hits : int;
  model_answers : int;
  call_secs : float;
  cache_used : bool;
  level : int option;
  solver_level : int option;
}

(* [frames_cover old_frames frames] when, frame by frame, every conjunct of
   the old frame is a conjunct of the present one (or the old frame is
   [true]), so each present frame implies the old one.  A syntactic witness
   only: [false] says nothing.  Polymorphic comparison is sound for the
   positive answer, as it reports equality only of structurally equal
   formulas. *)
let frames_cover ?(conjuncts_of = Formula.conjuncts_of) old_frames frames =
  match
    List.for_all2 old_frames frames ~f:(fun old_phi phi ->
        Formula.is_true old_phi
        || Set.is_subset (conjuncts_of old_phi) ~of_:(conjuncts_of phi))
  with
  | List.Or_unequal_lengths.Ok b -> b
  | List.Or_unequal_lengths.Unequal_lengths -> false

(* [frames_cover] with the conjunct sets remembered by the physical identity
   of the frame formula, for the comparisons of one interpolation call: there
   the call's key is compared with the keys of every cached cube, several
   times each, and cached cubes share key formulas, so without it the
   conjunct sets of the same few frames are rebuilt for every comparison
   (on small inputs most of a call's time).  The answers are those of
   [frames_cover]: a formula's conjunct set is a function of the formula. *)
let frames_cover_memo () =
  let module H = Stdlib.Hashtbl.Make (struct
    type t = Formula.t

    let equal = Stdlib.( == )
    let hash = Stdlib.Hashtbl.hash
  end) in
  let memo = H.create 16 in
  let conjuncts_of phi =
    match H.find_opt memo phi with
    | Some s -> s
    | None ->
        let s = Formula.conjuncts_of phi in
        H.add memo phi s;
        s
  in
  frames_cover ~conjuncts_of

(* The loop's choices fixed for one search (all off in [default_options]):
   the number of kept per-level solvers, the bit-level checker, and the
   switches of [blocking_interpolant] of the same names ([exit_simple] there
   is [exit_simple]).  Choices, not state: they change no kept data. *)
type options = {
  kept_solvers : int;
  bit_checker : (module BIT_CHECKER) option;
  lazy_nonlinear : bool;
  definition_templates : bool;
  lazy_nonlinear_relevant : bool;
  leaf_contexts : bool;
  leaf_templates : bool;
  kept_bit_models : bool;
  incremental_exit : bool;
  exit_simple : bool;
  bit_domain : bool;
  bit_domain_pin : bool;
}

let default_options =
  {
    kept_solvers = 0;
    bit_checker = None;
    lazy_nonlinear = false;
    definition_templates = false;
    lazy_nonlinear_relevant = false;
    leaf_contexts = false;
    leaf_templates = false;
    kept_bit_models = false;
    incremental_exit = false;
    exit_simple = false;
    bit_domain = false;
    bit_domain_pin = false;
  }

(* What the loop keeps between the calls of one search, per predicate name:
   the cube cache (each blocked cube with the seed keys under which it was
   excluded and those under which a check failed) and the level store (each
   cube with the levels at which it was excluded and its failed pushes), the
   [cache] and [level_store] of [blocking_interpolant].  The caller makes
   one per search ([create_session]) and passes it with every call; the kept
   Z3 contexts and per-level solvers are not in it, as they live as long as
   the domain. *)
type session = {
  options : options;
  preds :
    ( string,
      (Formula.t list list * Formula.t list list * Formula.t list) list ref
      * (Formula.t list * Int.Set.t * (int * Formula.t list) list) list ref )
    Hashtbl.t;
}

let create_session ?(options = default_options) () =
  { options; preds = Hashtbl.Poly.create () }

(* Where one call sits in the caller's search: the predicate [pred] whose
   frame is interpolated, the frame's [level] counted from the bottom, and
   [frames] the lower frames [phi1] is built from (the seed key, forced only
   on bit-vector and Boolean queries).  [levels_ok] is the caller's statement
   that, between calls, [pred]'s frames at one level only strengthen and
   [phi1] is monotone in them (the level store's seeds are unchecked and
   sound only then); [solvers_ok] admits the kept per-level solvers, which
   need no such property. *)
type at = {
  pred : string;
  level : int;
  frames : Formula.t list Lazy.t;
  levels_ok : bool;
  solvers_ok : bool;
}

(* the cubes [session]'s cube cache holds for [pred], each as its literals *)
let cached_cubes session ~pred =
  match Hashtbl.find session.preds pred with
  | None -> []
  | Some (cache, _) -> List.map !cache ~f:(fun (_, _, cube) -> cube)

(* The blocking loop as a method of answering [phi1 => phi2] over [args]:
   decides whether the loop may run on the query, prepares its premises, runs
   [blocking_interpolant] and tidies its answer.  [`Declined] when the query's
   shape is outside what the loop answers soundly ([blocking_ok]); otherwise
   [`Ran (answer, stats)] with the loop's [`Answer _] or [`Fallback] (see
   [blocking_interpolant] for what each guarantees).

   Over bit-vectors and Booleans only ([bit_vector_only]) the loop's
   refutation is taken from Z3's model unchecked, and its rounds are bounded
   because a cube's model values range over finite sorts; over integers and
   reals because their variables are projected ([project]) instead; over the
   other sorts the refutation's model is checked and only [max_rounds] bounds
   the rounds.  The options are [session]'s ([default_options] without
   one).  The kept state is used only when [session] and [at] are both
   given: [at.pred]'s cube cache keyed by [at.frames], with [at.levels_ok]
   its level store at [at.level], with [at.solvers_ok] the kept solver of
   ([at.pred], [at.level]); and on bit-vector and Boolean queries only: the cube cache was measured only there, where
   removing it lost inputs and made the decided ones slower, while on integer
   queries it lost inputs of its own; the level store's seeds are unchecked,
   so a check's [unsat] must hold in every model.  With [phi1_bounds], the
   bounds [phi1] implies on [args] ([phi1_arg_bounds]) are the loop's
   premises, and the conjuncts of the answer that only restate them and are
   not needed to exclude [~phi2] are dropped afterwards
   ([drop_unneeded_conjuncts]).  [expand_bounds] and [expand_strict] are the
   loop's; [rem_numeral] widens the shapes admitted by [blocking_ok]. *)
let interpolate ?session ?at ?project ~print ~max_rounds ~sum_bounds
    ~expand_bounds ~expand_strict ~rem_numeral ~phi1_bounds args phi1 phi2 =
  let o =
    match session with Some s -> s.options | None -> default_options
  in
  let cube_cache, levels, solver_key, seed_key, key_covers =
    match (session, at) with
    | Some s, Some at ->
        let cache, store =
          Hashtbl.find_or_add s.preds at.pred ~default:(fun () ->
              (ref [], ref []))
        in
        ( Some cache,
          (if at.levels_ok then Some (store, at.level) else None),
          (if at.solvers_ok then Some (at.pred, at.level) else None),
          Some at.frames,
          (* one memo per call: the call's key is compared with the keys of
             every cached cube *)
          Some (frames_cover_memo ()) )
    | _ -> (None, None, None, None, None)
  in
  let bv_only = bit_vector_only args phi1 phi2 in
  (* With COAR_MUCYC_PHASE_TIME set, [blk-bv-only] counts the queries over
     bit-vectors and Booleans only.  Observation only. *)
  if bv_only then Common.PhaseTime.event "blk-bv-only";
  let cube_cache = if bv_only then cube_cache else None in
  let levels = if bv_only then levels else None in
  let solver_key = if bv_only then solver_key else None in
  let seed_key =
    phase_time "blk-seed-key" @@ fun () ->
    if bv_only then Option.map seed_key ~f:Lazy.force else None
  in
  if
    bv_only
    || staged (lazy "blocking-ok") (fun () ->
           blocking_ok ~rem_numeral args phi1 phi2)
  then (
    let rounds = ref 0 and reused = ref 0 and cached = ref 0 in
    let seed_secs = ref 0. in
    let exit_secs = ref 0. and block_secs = ref 0. in
    let cube_secs = ref 0. and checks = ref 0 in
    let skipped = ref 0 and refuted = ref 0 in
    let setup_secs = ref 0. and gc_secs = ref 0. in
    let first_check_secs = ref 0. and check_secs = ref 0. in
    let sat_checks = ref 0 and sat_check_secs = ref 0. in
    let sat_model_hits = ref 0 in
    let level_seeded = ref 0 and pushed = ref 0 in
    let kept_hits = ref 0 and model_answers = ref 0 in
    let called_at = Time_float.now () in
    let answer =
      let seeded, minimise =
        if phi1_bounds then
          match
            staged (lazy "phi1-bounds") (fun () -> phi1_arg_bounds args phi1)
          with
          | None -> ([], false)
          | Some bs -> (bs, true)
        else ([], false)
      in
      let premises = match seeded with [] -> None | bs -> Some bs in
      let drop_unneeded = function
        | `Answer (Some interp) when minimise ->
            `Answer
              (Some
                 (staged (lazy "drop-unneeded") (fun () ->
                      drop_unneeded_conjuncts seeded interp phi2)))
        | answer -> answer
      in
      drop_unneeded @@ phase_time "blk-loop"
      @@ fun () ->
      blocking_interpolant ?premises ~rounds ~reused ~cached ~seed_secs
        ~exit_secs ~block_secs ~cube_secs ~checks ~skipped ~setup_secs
        ~gc_secs ~first_check_secs ~check_secs ~sat_checks ~sat_check_secs
        ?cache:cube_cache ?seed_key
        ?level_store:(Option.map levels ~f:fst)
        ?level:(Option.map levels ~f:snd)
        ~level_check ~level_seeded ~pushed ?solver_key
        ~kept_solvers:o.kept_solvers ~kept_hits ?bit_checker:o.bit_checker
        ~lazy_nonlinear:o.lazy_nonlinear
        ~definition_templates:o.definition_templates
        ~lazy_nonlinear_relevant:o.lazy_nonlinear_relevant
        ~leaf_contexts:o.leaf_contexts ~leaf_templates:o.leaf_templates
        ~kept_bit_models:o.kept_bit_models ~model_answers
        ~incremental_exit:o.incremental_exit ~exit_simple:o.exit_simple
        ~bit_domain:o.bit_domain ~bit_domain_pin:o.bit_domain_pin
        (* one key decided an input fewer than eight on the bit-vector
           inputs and took longer; the number is not a choice *)
        ~max_keys:8 ?key_covers ~negative:true ~refuted ~sum_bounds
        ~expand_bounds
        (* the model filter was measured only with [phi1_bounds] on
           (integer, real, array and datatype queries); the bit-vector
           configurations never set it *)
        ~sat_models:phi1_bounds ~sat_model_hits ~expand_strict
        ~check_refutation:
          (not
             (bv_only
             || staged (lazy "arith-blocking-ok") (fun () ->
                    arith_blocking_ok ~rem_numeral args phi1 phi2)))
          (* one extra core check per cube; it was measured on integer
             queries only, so a pure bit-vector query keeps the whole cube's
             core *)
        ~narrow_first:(not bv_only)
        ?project:(if bv_only then None else project)
        ~print ~max_rounds
        (* the class form was measured only on queries over bit-vectors and
           Booleans, where it decided more inputs than the cube as the
           implicant gives it; a cube of any other sort keeps the
           implicant's literals *)
        ~eqclass:bv_only args phi1 phi2
    in
    let call_secs =
      Time_float.Span.to_sec (Time_float.diff (Time_float.now ()) called_at)
    in
    `Ran
      ( answer,
        {
          rounds = !rounds;
          reused = !reused;
          cached = !cached;
          seed_secs = !seed_secs;
          exit_secs = !exit_secs;
          block_secs = !block_secs;
          cube_secs = !cube_secs;
          checks = !checks;
          skipped = !skipped;
          refuted = !refuted;
          setup_secs = !setup_secs;
          gc_secs = !gc_secs;
          first_check_secs = !first_check_secs;
          check_secs = !check_secs;
          sat_checks = !sat_checks;
          sat_check_secs = !sat_check_secs;
          sat_model_hits = !sat_model_hits;
          level_seeded = !level_seeded;
          pushed = !pushed;
          kept_hits = !kept_hits;
          model_answers = !model_answers;
          call_secs;
          cache_used = Option.is_some cube_cache;
          level = Option.map levels ~f:snd;
          solver_level =
            (match solver_key with
            | Some (_, j) when o.kept_solvers > 0 -> Some j
            | _ -> None);
        } ))
  else (
    if interp_stage then
      prerr_endline
        ("interp-stage: blocking declined "
        ^ blocking_declined_reasons ~rem_numeral args phi1 phi2);
    `Declined)
