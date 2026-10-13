(* A cooperative teacher for the integer part of a counterexample.

   A counterexample query may be answered by any of its models, and a solver
   returns the cheapest: on a loop whose bound S is only constrained by
   [1 <= S], every counterexample has S = 1 or 2.  Then every bound of the
   form [kS - 1] or [kS - i - 1] (k = 2..5) takes one of a handful of values
   at the examples, a cell bound [j <= 5i] is indistinguishable from
   [j <= 5S - 1], and literals about the examples' own constants ([S <= 1],
   [i = 0]) are free in every disjunct that covers them: the version space
   holds the intended invariant and countless cubes the data cannot tell
   apart from it.

   This asks the query a second time with a preference added: the integer
   variables of the first model, taken together, must be at Manhattan
   distance at least [m] from those of the counterexample last returned for
   the same set of variables.  The distance [m] adapts as in the cooperative
   verifiers of Batz, Chen, Junges, Kaminski, Katoen and Matheja,
   "Probabilistic Program Verification via Inductive Synthesis of Inductive
   Invariants" (TACAS 2023, Definition 5 and its implementation): doubled
   when a distant model is found, halved (never below 1) when it is not.

   Contract: [reask] returns either [model] unchanged or a model the [ask]
   callback returned for [phi] conjoined with the distance condition, so
   whatever it returns is a model of [phi] whenever [ask] answers models of
   the formula it is given -- a counterexample all the same.  It only chooses
   WHICH counterexample is used, so it cannot change a verdict.  No integer
   variable in the model, or a model whose integers already lie at distance
   [m] or more, asks nothing.  The state (last point and current [m] per set
   of variable names) is process-global and grows by one entry per distinct
   set. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

type model = ((Ident.tvar * Sort.t) * Term.t option) list

(* the integer variables the model gives a numeral to, sorted by name *)
let int_point (model : model) : (Ident.tvar * Z.t) list =
  List.sort ~compare:(fun (x, _) (y, _) -> Ident.tvar_compare x y)
  @@ List.filter_map model ~f:(fun ((x, s), t) ->
      match (s, t) with
      | T_int.SInt, Some t -> (
          match Term.value_of (Evaluator.simplify_term t) with
          | Value.Int z -> Some (x, z)
          | _ -> None
          | exception exn when not (Common.Timer.is_async exn) -> None)
      | _ -> None)

let key_of point =
  String.concat ~sep:","
    (List.map point ~f:(fun (x, _) -> Ident.name_of_tvar x))

let distance p q =
  List.fold2_exn p q ~init:Z.zero ~f:(fun acc (_, a) (_, b) ->
      Z.add acc (Z.abs (Z.sub a b)))

(* [sum_x |x - last_x| >= m] over the variables of [last], quantifier-free
   and linear *)
let distance_condition ~(last : (Ident.tvar * Z.t) list) ~(m : Z.t) =
  let abs_diff (x, c) =
    let v = Term.mk_var x T_int.SInt and c = T_int.mk_int c in
    T_bool.ifte (Formula.geq v c) (T_int.mk_sub v c) (T_int.mk_sub c v)
  in
  Formula.geq
    (T_int.mk_sum (T_int.zero ()) (List.map last ~f:abs_diff))
    (T_int.mk_int m)

(* per set of variable names: the last point returned and the current [m] *)
let state : (string, (Ident.tvar * Z.t) list * Z.t) Hashtbl.t =
  Hashtbl.create (module String)

let initial_m = Z.of_int 4
let reset () = Hashtbl.clear state
let asked = ref 0
let moved = ref 0

let reask ~(ask : Formula.t -> model option) (phi : Formula.t) (model : model) :
    model =
  let point = int_point model in
  if List.is_empty point then model
  else
    let key = key_of point in
    match Hashtbl.find state key with
    | None ->
        Hashtbl.set state ~key ~data:(point, initial_m);
        model
    | Some (last, m) ->
        if Z.geq (distance point last) m then (
          Hashtbl.set state ~key ~data:(point, m);
          model)
        else (
          incr asked;
          match ask (Formula.mk_and phi (distance_condition ~last ~m)) with
          | Some model' when String.equal (key_of (int_point model')) key ->
              incr moved;
              Hashtbl.set state ~key
                ~data:(int_point model', Z.mul m (Z.of_int 2));
              model'
          | Some model' ->
              (* a model naming other variables (one the solver completed
                 differently) is still a model of [phi]; keep the measure *)
              incr moved;
              Hashtbl.set state ~key ~data:(point, Z.mul m (Z.of_int 2));
              model'
          | None ->
              Hashtbl.set state ~key
                ~data:(point, Z.max Z.one (Z.div m (Z.of_int 2)));
              model)
