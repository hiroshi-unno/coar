open Core
open Common.Combinator
open LogicOld

let separate_atoms atoms rvar =
  List.partition_tf atoms ~f:(Atom.tvs_of >> Fn.flip Set.mem rvar)

let rec is_eq = function
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, _, _), _) -> true
  | Formula.Atom _ -> false
  | Formula.BinaryOp (And, phi1, phi2, _) -> is_eq phi1 || is_eq phi2
  | Formula.BinaryOp (Or, phi1, phi2, _) -> is_eq phi1 && is_eq phi2
  | _ -> assert false

let lb_ub atom var =
  match atom with
  | Atom.App (Predicate.Psym T_bool.Eq, [ t; _t0 ], _) -> (
      if T_real.is_sreal t then assert false
      else
        match
          AffineTerm.find_var_monomial (Term.mk_var var T_int.SInt)
          @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) t
        with
        | Some (c, rest) ->
            (*to real term*)
            let c = Value.Real (Q.of_bigint @@ Value.int_of c) in
            let rest = AffineTerm.int_to_real rest in
            let rest = AffineTerm.real_div rest (Value.neg c) in
            let term = AffineTerm.mk_real_term rest in
            (Some term, Some term)
        | None -> assert false)
  | Atom.App (Predicate.Psym (T_real.RGeq | T_real.RGt), [ t; _t0 ], _) -> (
      match
        AffineTerm.find_var_monomial (Term.mk_var var T_real.SReal)
        @@ Normalizer.linear_real_monomials_of (Value.Real Q.one) t
      with
      | Some (c, rest) ->
          let rest = AffineTerm.real_div rest (Value.neg c) in
          let term = AffineTerm.mk_real_term rest in
          let c = Value.real_of c in
          if Q.(c > zero) then (Some term, None) else (None, Some term)
      | None -> assert false)
  | Atom.App (Predicate.Psym T_int.Geq, [ t; _t0 ], _) -> (
      match
        AffineTerm.find_var_monomial (Term.mk_var var T_int.SInt)
        @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) t
      with
      | Some (c, rest) ->
          (*to real term*)
          let c = Value.Real (Q.of_bigint @@ Value.int_of c) in
          let rest = AffineTerm.int_to_real rest in
          let rest = AffineTerm.real_div rest (Value.neg c) in
          let term = AffineTerm.mk_real_term rest in
          let c = Value.real_of c in
          if Q.(c > zero) then (Some term, None) else (None, Some term)
      | None -> assert false)
  | Atom.App (Predicate.Psym (T_int.PDiv | T_int.NotPDiv), [ _c; _t ], _) ->
      failwith "pdiv not supported"
  | _ -> assert false

let union pred ts1 vop1 ts2 vop2 =
  match (vop1, vop2) with
  | Some r1, Some r2 ->
      if Q.(r1 = r2) then (Set.union ts1 ts2, Some r1)
      else if pred r1 r2 then (ts1, vop1)
      else (ts2, vop2)
  | Some _, None -> (ts1, vop1)
  | None, Some _ -> (ts2, vop2)
  | None, None -> (Set.Poly.empty, None)

let and_ephi ((lb1, lbv1), (ub1, ubv1)) ((lb2, lbv2), (ub2, ubv2)) =
  let lb, lbv =
    if Q.(lbv1 = lbv2) then (Set.union lb1 lb2, lbv1)
    else if Q.(lbv1 < lbv2) then (lb2, lbv2)
    else (lb1, lbv1)
  in
  let ub, ubv =
    if Q.(ubv1 = ubv2) then (Set.union ub1 ub2, ubv1)
    else if Q.(ubv1 < ubv2) then (ub1, ubv1)
    else (ub2, ubv2)
  in
  if Q.(lbv <= ubv) then [ ((lb, lbv), (ub, ubv)) ] else []

let rec or_ephi e1l e2l =
  match (e1l, e2l) with
  | [], [] -> []
  | e1l, [] -> e1l
  | [], e2l -> e2l
  | ((lb1, lbv1), (ub1, ubv1)) :: tl1, ((lb2, lbv2), (ub2, ubv2)) :: tl2 ->
      if Q.(lbv1 = lbv2) then
        let lb = (Set.union lb1 lb2, lbv1) in
        if Q.(ubv1 = ubv2) then
          (lb, (Set.union ub1 ub2, ubv1)) :: or_ephi tl1 tl2
        else if Q.(ubv1 < ubv2) then or_ephi tl1 ((lb, (ub2, ubv2)) :: tl2)
        else or_ephi ((lb, (ub1, ubv1)) :: tl1) tl2
      else if Q.(lbv1 < lbv2) then
        if Q.(lbv2 <= ubv1) then
          if Q.(ubv1 = ubv2) then
            ((lb1, lbv1), (Set.union ub1 ub2, ubv1)) :: or_ephi tl1 tl2
          else if Q.(ubv2 < ubv1) then or_ephi e1l tl2
          else or_ephi tl1 (((lb1, lbv1), (ub2, ubv2)) :: tl2)
        else ((lb1, lbv1), (ub1, ubv1)) :: or_ephi tl1 e2l
      else if Q.(lbv1 <= ubv2) then
        if Q.(ubv1 = ubv2) then
          ((lb2, lbv2), (Set.union ub1 ub2, ubv1)) :: or_ephi tl1 tl2
        else if Q.(ubv1 < ubv2) then or_ephi tl1 e2l
        else or_ephi (((lb2, lbv2), (ub1, ubv1)) :: tl1) tl2
      else ((lb2, lbv2), (ub2, ubv2)) :: or_ephi e1l tl2

let rec eval_ephi model var phi t1 r1 t2 r2 =
  match phi with
  | Formula.Atom (atom, _) ->
      let lb, ub = lb_ub atom var in
      let lb, lbv =
        match lb with
        | Some term ->
            let r =
              Value.real_of @@ Evaluator.eval_term @@ Term.subst model term
            in
            if Q.(r = r1) then (Set.add t1 term, r)
            else if Q.(r < r1) then (t1, r1)
            else (Set.Poly.singleton term, r)
        | None -> (t1, r1)
      in
      let ub, ubv =
        match ub with
        | Some term ->
            let r =
              Value.real_of @@ Evaluator.eval_term @@ Term.subst model term
            in
            if Q.(r = r2) then (Set.add t2 term, r)
            else if Q.(r2 < r) then (t2, r2)
            else (Set.Poly.singleton term, r)
        | None -> (t2, r2)
      in
      if Q.(lbv <= ubv) then [ ((lb, lbv), (ub, ubv)) ] else []
  | BinaryOp (And, phi1, phi2, _) ->
      let e1l = eval_ephi model var phi1 t1 r1 t2 r2 in
      let e2l = eval_ephi model var phi2 t1 r1 t2 r2 in
      List.fold e1l ~init:[] ~f:(fun l e1 ->
          l @ List.concat_map e2l ~f:(and_ephi e1))
  | BinaryOp (Or, phi1, phi2, _) ->
      let e1l = eval_ephi model var phi1 t1 r1 t2 r2 in
      let e2l = eval_ephi model var phi2 t1 r1 t2 r2 in
      or_ephi e1l e2l
  | _ -> assert false

let lb_and_ub vertex rvar ephi t1 t2 =
  let r1 = Value.real_of @@ Evaluator.eval_term @@ Term.subst vertex t1 in
  let r2 = Value.real_of @@ Evaluator.eval_term @@ Term.subst vertex t2 in
  let t1 = Set.Poly.singleton t1 in
  let t2 = Set.Poly.singleton t2 in
  let e = eval_ephi vertex rvar ephi t1 r1 t2 r2 in
  let e = List.map e ~f:(fun ((s1, _), (s2, _)) -> (s1, s2)) in
  (vertex, e)

let compute_real_sub (model, glb, lub) t1 t2 =
  let r1 = Value.real_of @@ Evaluator.eval_term @@ Term.subst model t1 in
  let r2 = Value.real_of @@ Evaluator.eval_term @@ Term.subst model t2 in
  let rlb, rub = if Q.(r1 < r2) then (r1, r2) else (r2, r1) in
  if Q.(rlb = rub) then Q.zero
  else
    let glb =
      match Set.nth glb 0 with
      | None -> assert false
      | Some term ->
          Value.real_of @@ Evaluator.eval_term @@ Term.subst model term
    in
    let lub =
      match Set.nth lub 0 with
      | None -> assert false
      | Some term ->
          Value.real_of @@ Evaluator.eval_term @@ Term.subst model term
    in
    if Q.(glb > lub) then Q.zero
    else
      let _ = 1 in
      if false then (
        print_endline ("num = " ^ Q.to_string Q.(lub - glb));
        print_endline ("den = " ^ Q.to_string Q.(rub - rlb)));
      Q.((lub - glb) / (rub - rlb))

let compute_real (model, e) t1 t2 =
  List.fold e ~init:Q.zero ~f:(fun p (glb, lub) ->
      Q.(p + compute_real_sub (model, glb, lub) t1 t2))

let rec separate_vt vte t1 t2 theta compute =
  match vte with
  | [] -> ([], [], [])
  | (vt, e) :: tl ->
      let tvt, thetavt, fvt = separate_vt tl t1 t2 theta compute in
      let pro = compute (vt, e) t1 t2 in
      if false then (
        print_endline (TermSubst.str_of vt);
        print_endline ("Pr = " ^ Q.to_string pro));
      if Q.(pro = theta) then (tvt, (vt, e) :: thetavt, fvt)
      else if Q.(pro > theta) then ((vt, e) :: tvt, thetavt, fvt)
      else (tvt, thetavt, (vt, e) :: fvt)

let find_same e =
  List.find_map ~f:(fun (vt, e') ->
      if List.length e = List.length e' then
        let op =
          List.fold2_exn e e' ~init:(Some []) ~f:(fun op (lb, ub) (lb', ub') ->
              match op with
              | Some l ->
                  let lb = Set.inter lb lb' in
                  let ub = Set.inter ub ub' in
                  Some ((lb, ub) :: l)
              | None -> None)
        in
        match op with Some l -> Some (vt, l) | None -> None
      else None)

let midpoint model model' =
  Map.Poly.mapi model ~f:(fun ~key:tvar ~data:term ->
      let term' = Map.Poly.find_exn model' tvar in
      let r = Value.real_of @@ Evaluator.eval_term term in
      let r' = Value.real_of @@ Evaluator.eval_term term' in
      let value = Q.((r + r') / of_float 2.0) in
      T_real.mk_real value)

let mk_numterm (model, e) =
  let terms =
    List.map e ~f:(fun (lb, ub) ->
        let glb, _ =
          Set.fold lb
            ~init:(T_real.rzero (), Q.minus_inf)
            ~f:(fun (t, m) term ->
              let r =
                Value.real_of @@ Evaluator.eval_term @@ Term.subst model term
              in
              if Q.(r >= m) then (term, r) else (t, m))
        in
        let lub, _ =
          Set.fold ub
            ~init:(T_real.rzero (), Q.inf)
            ~f:(fun (t, m) term ->
              let r =
                Value.real_of @@ Evaluator.eval_term @@ Term.subst model term
              in
              if Q.(r <= m) then (term, r) else (t, m))
        in
        T_real.mk_rsub lub glb)
  in
  Normalizer.normalize_term @@ T_real.mk_rsum (T_real.rzero ()) terms

let mk_denterm model t1 t2 =
  let r1 = Value.real_of @@ Evaluator.eval_term @@ Term.subst model t1 in
  let r2 = Value.real_of @@ Evaluator.eval_term @@ Term.subst model t2 in
  if Q.(r1 = r2) then assert false
  else
    let t, t' = if Q.(r1 > r2) then (t1, t2) else (t2, t1) in
    Normalizer.normalize_term @@ T_real.mk_rsub t t'

let mk_newterm num den theta =
  let th = T_real.mk_real theta in
  Normalizer.normalize_term @@ T_real.mk_rsub (T_real.mk_rmul th den) num

let is_line vertex ray vertex' =
  let var, t = Map.Poly.nth_exn vertex 0 in
  (* t1 + coeff * t2 = t3*)
  let coeff t1 t2 t3 =
    let v1 = Value.real_of @@ Evaluator.eval_term t1 in
    let v2 = Value.real_of @@ Evaluator.eval_term t2 in
    let v3 = Value.real_of @@ Evaluator.eval_term t3 in
    Q.((v3 - v1) / v2)
  in
  let c = coeff t (Map.Poly.find_exn ray var) (Map.Poly.find_exn vertex' var) in
  if Q.(c < zero) then false
  else
    Map.Poly.for_alli vertex ~f:(fun ~key:var ~data:t ->
        Q.(
          c
          = coeff t (Map.Poly.find_exn ray var) (Map.Poly.find_exn vertex' var)))

let mk_raytv vertex ray =
  Map.Poly.mapi vertex ~f:(fun ~key:var ~data:t ->
      Evaluator.simplify_term @@ T_real.mk_radd t @@ Map.Poly.find_exn ray var)

let mk_rayvertex vt ray =
  let vertex, e =
    List.fold (List.tl_exn vt) ~init:(List.hd_exn vt)
      ~f:(fun (vertex, e) (vertex', e') ->
        if is_line vertex ray vertex' then (vertex', e') else (vertex, e))
  in
  ((vertex, e), mk_raytv vertex ray)

let number_of_int r1 r2 =
  let lb = Float.iround_up_exn (Q.to_float r1) in
  let ub = Float.iround_down_exn (Q.to_float r2) in
  Z.of_int (ub - lb + 1)

let compute_int_sub (model, glb, lub) t1 t2 =
  let r1 = Value.real_of @@ Evaluator.eval_term @@ Term.subst model t1 in
  let r2 = Value.real_of @@ Evaluator.eval_term @@ Term.subst model t2 in
  let rlb, rub = if Q.(r1 < r2) then (r1, r2) else (r2, r1) in
  let glb =
    match Set.nth glb 0 with
    | None -> assert false
    | Some term -> Value.real_of @@ Evaluator.eval_term @@ Term.subst model term
  in
  let lub =
    match Set.nth lub 0 with
    | None -> assert false
    | Some term -> Value.real_of @@ Evaluator.eval_term @@ Term.subst model term
  in
  let num = number_of_int glb lub in
  let num = if Z.Compare.(num < Z.zero) then Z.zero else num in
  let den = number_of_int rlb rub in
  if false then (
    print_endline ("num = " ^ Z.to_string num);
    print_endline ("den = " ^ Z.to_string den));
  Q.make num den

let compute_int (model, e) t1 t2 =
  List.fold e ~init:Q.zero ~f:(fun p (glb, lub) ->
      Q.(p + compute_int_sub (model, glb, lub) t1 t2))

let mk_int_numterm (model, e) =
  let terms =
    List.map e ~f:(fun (lb, ub) ->
        let lbterm, glb =
          Set.fold lb
            ~init:(T_real.rzero (), Q.minus_inf)
            ~f:(fun (t, m) term ->
              let r =
                Value.real_of @@ Evaluator.eval_term @@ Term.subst model term
              in
              if Q.(r >= m) then (term, r) else (t, m))
        in
        let ubterm, lub =
          Set.fold ub
            ~init:(T_real.rzero (), Q.inf)
            ~f:(fun (t, m) term ->
              let r =
                Value.real_of @@ Evaluator.eval_term @@ Term.subst model term
              in
              if Q.(r <= m) then (term, r) else (t, m))
        in
        let num = number_of_int glb lub in
        if Z.Compare.(num < Z.zero) then T_real.rzero ()
        else T_real.mk_rsub ubterm lbterm)
  in
  Normalizer.normalize_term @@ T_real.mk_rsum (T_real.rzero ()) terms

let mk_int_denterm model t1 t2 =
  let r1 = Value.real_of @@ Evaluator.eval_term @@ Term.subst model t1 in
  let r2 = Value.real_of @@ Evaluator.eval_term @@ Term.subst model t2 in
  let t, t' = if Q.(r1 > r2) then (t1, t2) else (t2, t1) in
  let term =
    Normalizer.normalize_term
    @@ T_real.mk_radd (T_real.mk_rsub t t') (T_real.rone ())
  in
  if false then print_endline ("den term is " ^ Term.str_of term);
  term
