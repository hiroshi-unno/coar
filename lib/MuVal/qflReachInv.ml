open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* An invariant of the states a QFL query reaches: one box (an interval per
   real argument) per recursive function, closed under the equations -- for
   every state in a function's box and every application [Y t] of its body
   whose path condition holds there (the guards of the enclosing conditionals,
   [0 <= r <= 1] for each enclosing [unif r]), [t] lies in [Y]'s box -- and
   containing the query's application points.  For such a family the least
   solution restricted to it is the least solution of the equations restricted
   to it, so a lower-bound check may state its obligations on it only.

   The box is computed by interval abstract interpretation (widening, then
   descending rounds) and is returned only after an SMT solver has proved
   every closure obligation valid; the analysis is a heuristic and soundness
   rests on that check alone.  [None] when no proof was obtained. *)

(* [None] is an infinite bound *)
type itv = { lo : Q.t option; hi : Q.t option }

let top = { lo = None; hi = None }
let point c = { lo = Some c; hi = Some c }

let join a b =
  { lo = Option.map2 a.lo b.lo ~f:Q.min; hi = Option.map2 a.hi b.hi ~f:Q.max }

let tighter f a b =
  match (a, b) with
  | Some x, Some y -> Some (f x y)
  | (Some _ as x), None | None, (Some _ as x) -> x
  | None, None -> None

let is_empty a =
  match (a.lo, a.hi) with Some l, Some h -> Q.(l > h) | _ -> false

let equal_bound = Option.equal Q.equal
let equal_itv a b = equal_bound a.lo b.lo && equal_bound a.hi b.hi

let add a b =
  { lo = Option.map2 a.lo b.lo ~f:Q.add; hi = Option.map2 a.hi b.hi ~f:Q.add }

let neg a = { lo = Option.map a.hi ~f:Q.neg; hi = Option.map a.lo ~f:Q.neg }

let scale c a =
  if Q.(equal c zero) then point Q.zero
  else
    let s =
      { lo = Option.map a.lo ~f:(Q.mul c); hi = Option.map a.hi ~f:(Q.mul c) }
    in
    if Q.(c > zero) then s else { lo = s.hi; hi = s.lo }

let mul a b =
  match (a, b) with
  | { lo = Some l; hi = Some h }, x when Q.equal l h -> scale l x
  | x, { lo = Some l; hi = Some h } when Q.equal l h -> scale l x
  | { lo = Some l1; hi = Some h1 }, { lo = Some l2; hi = Some h2 } ->
      let ps = Q.[ l1 * l2; l1 * h2; h1 * l2; h1 * h2 ] in
      {
        lo = List.min_elt ps ~compare:Q.compare;
        hi = List.max_elt ps ~compare:Q.compare;
      }
  | _ -> top

let find env x = Option.value (Map.Poly.find env x) ~default:top

(* an interval containing every value of [t] for values of its variables in
   [env] (a variable not in [env] is unbounded) *)
let rec eval env t =
  match t with
  | Term.Var (x, _, _) -> find env x
  | Term.FunApp ((T_real.RAdd | T_int.Add | T_num.NAdd _), [ a; b ], _) ->
      add (eval env a) (eval env b)
  | Term.FunApp ((T_real.RSub | T_int.Sub | T_num.NSub _), [ a; b ], _) ->
      add (eval env a) (neg (eval env b))
  | Term.FunApp ((T_real.RNeg | T_int.Neg | T_num.NNeg _), [ a ], _) ->
      neg (eval env a)
  | Term.FunApp ((T_real.RMul | T_int.Mul | T_num.NMul _), [ a; b ], _) ->
      mul (eval env a) (eval env b)
  | Term.FunApp ((T_real.RDiv | T_num.NDiv _), [ a; b ], _) -> (
      match eval env b with
      | { lo = Some l; hi = Some h } when Q.equal l h && not (Q.equal l Q.zero)
        ->
          scale Q.(one / l) (eval env a)
      | _ -> top)
  | _ -> ( match QFL.Unif.constant_of t with Some c -> point c | None -> top)

(* [refine env phi]: [env] narrowed by the atoms [y >= e], [y <= e] (strict or
   not, either side) of [phi]'s top-level conjunction; [None] when [phi] is
   unsatisfiable in [env].  Other formulas leave [env] as it is, which only
   loses precision. *)
let rec refine env phi =
  match phi with
  | Formula.BinaryOp (And, p1, p2, _) ->
      Option.bind (refine env p1) ~f:(fun env -> refine env p2)
  | Formula.UnaryOp (Not, Formula.Atom (a, _), _) -> refine_atom env ~neg:true a
  | Formula.Atom (a, _) -> refine_atom env ~neg:false a
  | _ -> Some env

and refine_atom env ~neg = function
  | Atom.App (Predicate.Psym psym, [ t1; t2 ], _) -> (
      let geq =
        match psym with
        | T_real.(RGeq | RGt) | T_int.(Geq | Gt) | T_num.(NGeq _ | NGt _) ->
            Some true
        | T_real.(RLeq | RLt) | T_int.(Leq | Lt) | T_num.(NLeq _ | NLt _) ->
            Some false
        | _ -> None
      in
      let bound x other geq =
        (* [x >= other] (resp. [<=]): [x] is at least [other]'s lower bound *)
        let cur = find env x in
        let nw =
          if geq then { cur with lo = tighter Q.max cur.lo other.lo }
          else { cur with hi = tighter Q.min cur.hi other.hi }
        in
        if is_empty nw then None else Some (Map.Poly.set env ~key:x ~data:nw)
      in
      match Option.map geq ~f:(fun g -> if neg then not g else g) with
      | None -> Some env
      | Some geq -> (
          match (t1, t2) with
          | Term.Var (x, _, _), _ -> bound x (eval env t2) geq
          | _, Term.Var (x, _, _) -> bound x (eval env t1) (not geq)
          | _ -> Some env))
  | _ -> Some env

(* every application of a function in [recursive] in [t], with its arguments
   and its path condition (innermost last) *)
let rec apps_of ~recursive path t =
  match QFL.Unif.let_unif t with
  | Some (r, body) ->
      let rv = Term.mk_var r T_real.SReal in
      apps_of ~recursive
        (path @ [ Formula.geq rv (T_real.rzero ()); Formula.leq rv (T_real.rone ()) ])
        body
  | None -> (
      match t with
      | Term.FunApp (T_bool.IfThenElse, [ c; t1; t2 ], _) ->
          let phi = Formula.of_bool_term c in
          apps_of ~recursive path c
          @ apps_of ~recursive (path @ [ phi ]) t1
          @ apps_of ~recursive (path @ [ Formula.mk_neg phi ]) t2
      | Term.FunApp (FVar (name, _, _), args, _) when Set.mem recursive name ->
          ((name, args), path) :: List.concat_map args ~f:(apps_of ~recursive path)
      | Term.FunApp (_, args, _) -> List.concat_map args ~f:(apps_of ~recursive path)
      | _ -> [])

let str_of_bound = function None -> "oo" | Some q -> Q.to_string q

let str_of st =
  String.concat_map_list ~sep:"; " (Map.Poly.to_alist st)
    ~f:(fun (name, box) ->
      sprintf "%s: %s" (Ident.name_of_tvar name)
        (String.concat_map_list ~sep:" x " box ~f:(fun i ->
             sprintf "[%s, %s]"
               (match i.lo with None -> "-oo" | b -> str_of_bound b)
               (str_of_bound i.hi))))

let box_formulas args box =
  List.concat_map (List.zip_exn args box) ~f:(fun ((x, s), itv) ->
      if not (Term.is_real_sort s) then []
      else
        let v = Term.mk_var x s in
        Option.to_list (Option.map itv.lo ~f:(fun l -> Formula.geq v (T_real.mk_real l)))
        @ Option.to_list
            (Option.map itv.hi ~f:(fun h -> Formula.leq v (T_real.mk_real h))))

(* [compute ~is_valid ~recursive preds query_params query_left query_head]:
   [Some inv] with [inv name] the box of [name] ([None] for a function the
   query does not reach, i.e. the empty set), when the closure obligations of
   the candidate are all proved by [is_valid]; [None] otherwise.  [preds] are
   the recursive equations, [query_head] the query's function application with
   the non-recursive functions inlined. *)
let compute ~is_valid ~(preds : QFL.Pred.t list) ~query_params ~query_left
    query_head =
  let recursive = Set.Poly.of_list @@ List.map preds ~f:(fun p -> p.name) in
  let query_path = Option.to_list query_left in
  let query_apps = apps_of ~recursive query_path query_head in
  let body_apps =
    List.map preds ~f:(fun (p : QFL.Pred.t) ->
        (p, apps_of ~recursive [] p.body))
  in
  let real_args args =
    List.for_all args ~f:(fun (_, s) -> Term.is_real_sort s)
  in
  let images env0 apps =
    List.filter_map apps ~f:(fun ((name, args), path) ->
        let env =
          List.fold path ~init:(Some env0) ~f:(fun e phi ->
              Option.bind e ~f:(fun e -> refine e phi))
        in
        Option.map env ~f:(fun env -> (name, List.map args ~f:(eval env))))
  in
  let add_image st (name, box) =
    Map.Poly.update st name ~f:(function
      | None -> box
      | Some b -> List.map2_exn b box ~f:join)
  in
  let seed =
    let env0 =
      Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
      @@ List.map query_params ~f:(fun (x, _) -> (x, top))
    in
    List.fold (images env0 query_apps) ~init:Map.Poly.empty ~f:add_image
  in
  let transfer st =
    List.fold body_apps ~init:seed ~f:(fun acc ((p : QFL.Pred.t), apps) ->
        match Map.Poly.find st p.name with
        | None -> acc
        | Some box ->
            let env0 =
              Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
              @@ List.zip_exn (List.map p.args ~f:fst) box
            in
            List.fold (images env0 apps) ~init:acc ~f:add_image)
  in
  let widen old nw =
    Map.Poly.merge old nw ~f:(fun ~key:_ -> function
      | `Both (o, n) ->
          Some
            (List.map2_exn o n ~f:(fun o n ->
                 {
                   lo = (if equal_bound o.lo n.lo then o.lo else None);
                   hi = (if equal_bound o.hi n.hi then o.hi else None);
                 }))
      | `Left o -> Some o
      | `Right n -> Some n)
  in
  let equal_st = Map.Poly.equal (List.equal equal_itv) in
  let rec ascend k st =
    let nw = Map.Poly.merge st (transfer st) ~f:(fun ~key:_ -> function
      | `Both (o, n) -> Some (List.map2_exn o n ~f:join)
      | `Left o -> Some o
      | `Right n -> Some n)
    in
    if equal_st nw st || k > 50 then st
    else ascend (k + 1) (if k >= 3 then widen st nw else nw)
  in
  let st = ascend 0 seed in
  let st = transfer (transfer st) in
  let inv name = Map.Poly.find st name in
  let guard name args =
    match inv name with
    | None -> [ Formula.mk_false () ]
    | Some box -> box_formulas args box
  in
  let obligation hyps ((name, args), path) =
    let pred =
      List.find_exn preds ~f:(fun (p : QFL.Pred.t) ->
          Ident.tvar_equal p.name name)
    in
    let concl =
      match inv name with
      | None -> [ Formula.mk_false () ]
      | Some box -> box_formulas pred.args box
    in
    let sub =
      Map.Poly.of_alist_exn @@ List.zip_exn (List.map pred.args ~f:fst) args
    in
    Formula.mk_imply
      (Formula.and_of (hyps @ path))
      (Formula.and_of (List.map concl ~f:(Formula.subst sub)))
  in
  if
    (not (List.for_all preds ~f:(fun p -> real_args p.args)))
    || Map.Poly.for_all st ~f:(List.for_all ~f:(equal_itv top))
       && Map.length st = List.length preds
  then None (* nothing to restrict, or an argument the boxes do not read *)
  else
    let obligations =
      List.map query_apps ~f:(obligation [])
      @ List.concat_map body_apps ~f:(fun ((p : QFL.Pred.t), apps) ->
          match inv p.name with
          | None -> [] (* the empty set: closure is vacuous *)
          | Some box -> List.map apps ~f:(obligation (box_formulas p.args box)))
    in
    if List.for_all obligations ~f:is_valid then Some (guard, str_of st)
    else None
