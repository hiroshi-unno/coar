(* Guards that separate finite sets of argument points, for combining the
   terms a model-guided selection chose at different points of one function
   into a single guarded definition.  Over integer or real parameters; the
   only solver call is one small Z3 satisfiability question for a linear
   separator. *)

open Core
open Common.Ext
open Ast

(* Guards by separation ([refine_guards = Separation]).

   A refinement problem may hold several copies [K$1 .. K$m] of one
   opponent key [K], one per visit of the derivation to [K]'s decision
   point.  Each copy is a separate unknown, so the selection gives each its
   own function [y = t_i(x)], selected at its own argument point
   [P_i = a_i(M)]; the caller then adds all of them to [K]'s term set.  When
   the [t_i] differ, [K]'s move depends on where it is made, and a single
   guarded definition says so where the term set only lists the moves:

     y = ite(g_1(x), t_1(x), ite(g_2(x), t_2(x), .. t_k(x)))

   The copies are grouped by their term (copies with one term share one
   branch), the groups are ordered, and guard [g_i] holds at every point of
   group [i] and at no point of a later group, so the definition takes
   [P_i] to [t_i(P_i)] for every copy: exactly the graph point each copy was
   selected for.  The last group needs no guard.

   The guard is the cheapest separator that exists: a threshold on one
   parameter ([x_j >= c] or [x_j <= c], [c] halfway between the two groups'
   values, rounded towards the separated group over the integers), else a
   linear one [w . x + b > 0] from one Z3 query over [w] and [b]
   ([w . P >= 1] on the group, [<= -1] on the rest; over the integers an
   integral [w], [b] exists whenever a rational one does, by clearing
   denominators).  A projection of the formula at the model onto [K]'s
   parameters would generalise further but needs the other keys' results
   eliminated first; soundness does not need either, because the guard only
   decides which of the selected terms is used where, the definition is a
   single-valued total function whatever the guard, and the whole problem
   is checked valid with it substituted before it is used.

   When a group's points cannot be separated -- two copies selected at one
   argument point with different terms, which is where the move would have
   to read something outside [K]'s parameters -- the key is left ungrouped;
   forcing the copies to agree there is not built. *)
let separator_timeout_ms = 1000

(* a formula over [xs] true at every point of [pos] and false at every point
   of [neg] (both non-empty), or [None] *)
let separator ~real xs pos neg =
  let open LogicOld in
  let old_sort = if real then T_real.SReal else T_int.SInt in
  let const q =
    if real then T_real.mk_real q else T_int.mk_int (Q.to_bigint q)
  in
  let var x = Term.mk_var x old_sort in
  let n = List.length xs in
  let coord i = List.map ~f:(fun p -> List.nth_exn p i) in
  let min_of l = Option.value_exn (List.min_elt l ~compare:Q.compare) in
  let max_of l = Option.value_exn (List.max_elt l ~compare:Q.compare) in
  let half a b = Q.((a + b) / of_int 2) in
  let axis =
    List.find_map (List.zip_exn (List.init n ~f:Fn.id) xs) ~f:(fun (i, x) ->
        let s = coord i pos and r = coord i neg in
        if Q.(max_of r < min_of s) then
          let c = half (max_of r) (min_of s) in
          let c =
            if real then c else Q.of_bigint (Z.cdiv (Q.num c) (Q.den c))
          in
          Some (Formula.geq (var x) (const c))
        else if Q.(min_of r > max_of s) then
          let c = half (max_of s) (min_of r) in
          let c =
            if real then c else Q.of_bigint (Z.fdiv (Q.num c) (Q.den c))
          in
          Some (Formula.leq (var x) (const c))
        else None)
  in
  match axis with
  | Some g -> Some g
  | None when n = 0 -> None
  | None -> (
      let taken =
        ref (Set.Poly.of_list (xs @ Map.Poly.keys (LogicOld.get_fenv ())))
      in
      let fresh prefix =
        let v =
          Ident.mk_fresh_tvar_avoiding ~prefix
            ~taken:(fun v -> Set.mem !taken v) ()
        in
        taken := Set.add !taken v;
        v
      in
      let ws = List.init n ~f:(fun _ -> fresh "sep_w") in
      let b = fresh "sep_b" in
      let lin p =
        List.fold (List.zip_exn ws p) ~init:(var b) ~f:(fun acc (w, pi) ->
            if real then
              T_real.mk_radd acc (T_real.mk_rmul (var w) (const pi))
            else T_int.mk_add acc (T_int.mk_mul (var w) (const pi)))
      in
      let phi =
        Formula.and_of
          (List.map pos ~f:(fun p -> Formula.geq (lin p) (const Q.one))
          @ List.map neg ~f:(fun p ->
              Formula.leq (lin p) (const Q.minus_one)))
      in
      match
        Z3Smt.Z3interface.check_sat ~timeout:(Some separator_timeout_ms)
          ~id:None (LogicOld.get_fenv ()) [ phi ]
      with
      | `Sat model ->
          (* read by name and sort over the query's own variables *)
          let model =
            LogicOld.model_subst ~target:(Formula.term_sort_env_of phi) model
          in
          let value v =
            match Map.Poly.find model v with
            | Some t -> Value.cast_real_of (Evaluator.eval_term t)
            | None -> Q.zero
          in
          let sum =
            List.fold (List.zip_exn ws xs) ~init:(const (value b))
              ~f:(fun acc (w, x) ->
                if real then
                  T_real.mk_radd acc
                    (T_real.mk_rmul (const (value w)) (var x))
                else T_int.mk_add acc (T_int.mk_mul (const (value w)) (var x)))
          in
          Some (Evaluator.simplify (Formula.gt sum (const Q.zero)))
      | _ -> None)

(* The combined body over the formal parameters [xs] for the copies
   [members] of one key -- each its argument point (the arguments' values at
   the final model, [None] when a value could not be read) and its body over
   given parameters -- together with a line for the trace; or the reason
   there is none. *)
let guarded_body ~real xs members =
  let same t1 t2 = try Stdlib.(t1 = t2) with _ -> false in
  let classes =
    List.fold members ~init:[] ~f:(fun classes (point, body_of) ->
        let body = body_of xs in
        if List.exists classes ~f:(fun (b, _) -> same b body) then
          List.map classes ~f:(fun (b, ps) ->
              if same b body then (b, ps @ [ point ]) else (b, ps))
        else classes @ [ (body, [ point ]) ])
  in
  match classes with
  | [ (body, _) ] -> Ok (body, "one term for every copy; no guard needed")
  | _ -> (
      match
        Option.all
          (List.map classes ~f:(fun (b, ps) ->
               Option.map (Option.all ps) ~f:(fun ps -> (b, ps))))
      with
      | None -> Error "an argument value not readable off the model"
      | Some classes -> (
          let equal_point p q = List.equal Q.equal p q in
          let clash =
            List.existsi classes ~f:(fun i (_, ps) ->
                List.existsi classes ~f:(fun j (_, qs) ->
                    i < j
                    && List.exists ps ~f:(fun p ->
                        List.mem qs p ~equal:equal_point)))
          in
          if clash then
            Error
              "two copies selected at one argument point with different \
               terms (agreement there is not built)"
          else
            let rec decision_list = function
              | [] -> None
              | [ (b, _) ] -> Some ([], b)
              | classes ->
                  List.find_mapi classes ~f:(fun i (b, ps) ->
                      let rest = List.filteri classes ~f:(fun j _ -> j <> i) in
                      match
                        separator ~real xs ps (List.concat_map rest ~f:snd)
                      with
                      | None -> None
                      | Some g ->
                          Option.map (decision_list rest)
                            ~f:(fun (branches, default) ->
                              ((g, b) :: branches, default)))
            in
            match decision_list classes with
            | None -> Error "no separator over the key's parameters"
            | Some (branches, default) ->
                let sort =
                  if real then Logic.RealTerm.SReal else Logic.IntTerm.SInt
                in
                let body =
                  List.fold_right branches ~init:default
                    ~f:(fun (g, b) acc ->
                      Logic.BoolTerm.ite_of sort
                        (Logic.ExtTerm.of_old_formula g)
                        b acc)
                in
                Ok
                  ( body,
                    sprintf "%d terms under %d guards: %s"
                      (List.length classes) (List.length branches)
                      (String.concat_map_list ~sep:"; " branches
                         ~f:(fun (g, _) -> LogicOld.Formula.str_of g)) )))
