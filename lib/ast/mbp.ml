open Core
open Common.Ext
open LogicOld
open ArithTerm
open Normalizer

let sign model atom =
  if Evaluator.eval_atom @@ Atom.subst model atom then Formula.mk_atom atom else Formula.negate (Formula.mk_atom atom)

module LRA = struct
  let let_sort names model =
    Map.Poly.fold model ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term newmodel ->
        match Evaluator.eval_term term with
        | Value.Real r -> Map.Poly.add_exn newmodel ~key:tvar ~data:(T_real.mk_real r)
        | Value.Int n -> Map.Poly.add_exn newmodel ~key:tvar ~data:(T_real.mk_real (Q.of_bigint n))
        | Value.Bool b ->
          if Set.Poly.mem names (Ident.name_of_tvar tvar) then newmodel
          else if b then Map.Poly.add_exn newmodel ~key:tvar ~data:(T_bool.mk_true ())
          else Map.Poly.add_exn newmodel ~key:tvar ~data:(T_bool.mk_true ()))

  let eq_atom model tvar = function
    | Atom.App (Predicate.Psym sym, [t; _t0], _)
      when (match sym with | T_bool.Eq | T_real.RGeq -> true | _ -> false) ->
      let monomial = linear_real_monomials_of (Value.Real Q.one) t in
      let varterm = Term.mk_var tvar T_real.SReal in
      (match Linear.find_var_monomial varterm monomial with
       | Some (c, rest) ->
         let eqterm = Linear.mk_real_term @@ Map.Poly.map rest ~f:(fun c' -> Value.div c' (Value.neg c)) in
         if Value.compare Z.Compare.(=) Q.(=)
             (Evaluator.eval_term @@ Term.subst model varterm)
             (Evaluator.eval_term @@ Term.subst model eqterm)
         then Some eqterm else None
       | None -> None)
    | _ -> None
  let rec eq model tvar = function
    | [] -> None
    | a::tl -> begin
        match eq_atom model tvar a with
        | Some t -> Some t
        | None -> eq model tvar tl
      end
  let ub_atom model tvar = function
    | Atom.App (Predicate.Psym sym, [t; _t0], _)
      when (match sym with | T_real.RGeq | T_real.RGt | T_bool.Neq -> true | _ -> false) ->
      let monomial = linear_real_monomials_of (Value.Real Q.one) t in
      let varterm = Term.mk_var tvar T_real.SReal in
      (match (Linear.find_var_monomial varterm monomial, sym) with
       | (Some (Real r, rest), T_real.RGeq)
       | (Some (Real r, rest), T_real.RGt) ->
         if Q.(r >= Q.zero) then Set.Poly.empty
         else let ubterm = Linear.mk_real_term @@Map.Poly.map rest ~f:(fun c' -> Value.div c' (Value.neg (Real r))) in
           if Value.compare Z.Compare.(<) Q.(<)
               (Evaluator.eval_term @@ Term.subst model varterm)
               (Evaluator.eval_term @@ Term.subst model ubterm)
           then Set.Poly.singleton ubterm else Set.Poly.empty
       | (Some (Real r, rest), T_bool.Neq) ->
         let ubterm = Linear.mk_real_term @@Map.Poly.map rest ~f:(fun c' -> Value.div c' (Value.neg (Real r))) in
         if Value.compare Z.Compare.(<) Q.(<)
             (Evaluator.eval_term @@ Term.subst model varterm)
             (Evaluator.eval_term @@ Term.subst model ubterm)
         then Set.Poly.singleton ubterm else Set.Poly.empty
       | _ -> Set.Poly.empty)
    | _ -> Set.Poly.empty
  let lb_atom model tvar = function
    | Atom.App (Predicate.Psym sym, [t; _t0], _)
      when (match sym with | T_real.RGeq | T_real.RGt | T_bool.Neq -> true | _ -> false) ->
      let monomial = linear_real_monomials_of (Value.Real Q.one) t in
      let varterm = Term.mk_var tvar T_real.SReal in
      (match (Linear.find_var_monomial varterm monomial, sym) with
       | (Some (Real r, rest), T_real.RGeq)
       | (Some (Real r, rest), T_real.RGt) ->
         if Q.(r <= Q.zero) then Set.Poly.empty
         else let lbterm = Linear.mk_real_term @@ Map.Poly.map rest ~f:(fun c' -> Value.div c' (Value.neg (Real r))) in
           if Value.compare Z.Compare.(>) Q.(>)
               (Evaluator.eval_term @@ Term.subst model varterm)
               (Evaluator.eval_term @@ Term.subst model lbterm)
           then Set.Poly.singleton lbterm else Set.Poly.empty
       | (Some (Real r, rest), T_bool.Neq) ->
         let lbterm = Linear.mk_real_term @@ Map.Poly.map rest ~f:(fun c' -> Value.div c' (Value.neg (Real r))) in
         if Value.compare Z.Compare.(>) Q.(>)
             (Evaluator.eval_term @@Term.subst model varterm)
             (Evaluator.eval_term @@Term.subst model lbterm)
         then Set.Poly.singleton lbterm else Set.Poly.empty
       | _ -> Set.Poly.empty)
    | _ -> Set.Poly.empty
  let ub_and_lb model tvar l =
    List.fold l ~init:(Set.Poly.empty, Set.Poly.empty) ~f:(fun (ub, lb) atom ->
        (Set.Poly.union ub (ub_atom model tvar atom)),
        Set.Poly.union lb (lb_atom model tvar atom))
  let lub model ub =
    let m_lub = Value.Real (Set.Poly.fold ub ~init:Q.inf ~f:(fun lub t ->
        let value = Evaluator.eval_term @@Term.subst model t in
        match value with
        | Real r -> Q.min lub r
        | _ -> lub)) in
    Set.Poly.find ub ~f:(fun t ->
        Value.compare Z.Compare.(=) Q.(=) m_lub (Evaluator.eval_term @@Term.subst model t))
  let glb model lb =
    let m_glb = Value.Real (Set.Poly.fold lb ~init:Q.minus_inf ~f:(fun glb t ->
        let value = Evaluator.eval_term @@Term.subst model t in
        match value with
        | Real r -> Q.max glb r
        | _ -> glb)) in
    Set.Poly.find lb ~f:(fun t ->
        Value.compare Z.Compare.(=) Q.(=) m_glb (Evaluator.eval_term @@Term.subst model t))
  let model_based_projection model tvar phis =
    let atoms = List.map phis ~f:(fun phi -> Normalizer.normalize_atom @@Formula.to_atom phi) in
    match eq model tvar atoms with
    | Some t ->
      List.map phis ~f:(Formula.subst (Map.Poly.singleton tvar t))
    | None ->
      let (ub, lb) = ub_and_lb model tvar atoms in begin
        match (lub model ub, glb model lb) with
        | (Some lub, Some glb) ->
          let t = T_real.mk_rmult (T_real.mk_radd lub glb) (T_real.mk_real (Q.of_float 0.5)) in
          List.map phis ~f:(fun phi -> Evaluator.simplify @@ Normalizer.normalize @@ Formula.subst (Map.Poly.singleton tvar t) phi)
        | (Some lub, None) ->
          let t = T_real.mk_rsub lub (T_real.rone ()) in
          List.map phis ~f:(fun phi -> Evaluator.simplify @@ Normalizer.normalize @@ Formula.subst (Map.Poly.singleton tvar t) phi)
        | (None, Some glb) ->
          let t = T_real.mk_radd glb (T_real.rone ()) in
          List.map phis ~f:(fun phi -> Evaluator.simplify @@ Normalizer.normalize @@ Formula.subst (Map.Poly.singleton tvar t) phi)
        | (None, None) -> phis
      end
end

module LIA = struct
  open Formula

  let let_sort names model =
    Map.Poly.fold model ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term newmodel ->
        match Evaluator.eval_term term with
        | Value.Int n -> Map.Poly.add_exn newmodel ~key:tvar ~data:(T_int.mk_int n)
        | Value.Bool b ->
          if Set.Poly.mem names (Ident.name_of_tvar tvar) then newmodel
          else if b then Map.Poly.add_exn newmodel ~key:tvar ~data:(T_bool.mk_true ())
          else Map.Poly.add_exn newmodel ~key:tvar ~data:(T_bool.mk_true ())
        | _ -> assert false)

  let is_pdiv atom tvar =
    let open Atom in
    let varterm = Term.mk_var tvar T_int.SInt in
    match atom with
    | App (psym, [d; t], _) when
        (match psym with | Predicate.Psym T_int.PDiv | Predicate.Psym T_int.NPDiv -> true | _ -> false) ->
      let monomial = linear_int_monomials_of (Value.Int Z.one) t in
      (match Linear.find_var_monomial varterm monomial with
       | Some (c, rest) -> Some (psym, Evaluator.eval_term d, c, rest)
       | None -> None)
    | _ -> None

  let rm_pdiv pdivs model tvar =
    let lcm = List.fold pdivs ~init:Z.one ~f:(fun d1 (_, value, _, _) ->
        match value with
        | Value.Int d2 -> Z.lcm d1 d2
        | _ -> d1) in
    let varmodel = Term.subst model (Term.mk_var tvar T_int.SInt) in
    let u = Term.of_value @@Evaluator.eval_term @@T_int.mk_mod varmodel (T_int.mk_int lcm) in
    let newtvar = Ident.mk_fresh_tvar () in
    let newterm = T_int.mk_add u (T_int.mk_mult (T_int.mk_int lcm) (Term.mk_var newtvar T_int.SInt)) in
    (*print_endline @@Term.str_of (T_int.mk_div (T_int.mk_sub varmodel u) (T_int.mk_int lcm));*)
    let newvalue = Term.of_value @@Evaluator.eval_term @@T_int.mk_div (T_int.mk_sub varmodel u) (T_int.mk_int lcm) in
    let newmodel = Map.Poly.add_exn model ~key:newtvar ~data:newvalue in
    (*print_endline ("newvar:" ^ (Ident.name_of_tvar newtvar) ^ "|->" ^ (Term.str_of newvalue));*)
    let pdivs = List.map pdivs ~f:(fun (psym, d, c, t) ->
        mk_atom @@Atom.mk_app psym [(Term.of_value d); (T_int.mk_add (T_int.mk_mult (Term.of_value c) u) (Linear.mk_int_term t))]) in
    (newmodel, newtvar, newterm, pdivs)

  let ub_atom model tvar = function
    | Atom.App (Predicate.Psym sym, [t; _t0], _)
      when (match sym with | T_bool.Eq | T_int.Geq | T_bool.Neq -> true | _ -> false) ->
      let monomial = linear_int_monomials_of (Value.Int Z.one) t in
      let varterm = Term.mk_var tvar T_int.SInt in
      (match (Linear.find_var_monomial varterm monomial, sym) with
       | (Some (Int n, rest), T_bool.Eq) ->
         if Z.Compare.(n = Z.zero) then None
         else
           let (ubterm, cterm) = if Z.Compare.(n > Z.zero)
             then (Linear.mk_int_term @@ Linear.int_mult rest (Value.Int Z.minus_one), T_int.mk_int n)
             else (Linear.mk_int_term rest, T_int.mk_int Z.(-n)) in
           if Value.compare Z.Compare.(=) Q.(=)
               (Evaluator.eval_term @@ Term.subst model (T_int.mk_mult cterm varterm))
               (Evaluator.eval_term @@ Term.subst model ubterm)
           then Some (Set.Poly.singleton (cterm, ubterm)) else assert false
       | (Some (Int n, rest), T_int.Geq) ->
         if Z.Compare.(n >= Z.zero) then None
         else let ubterm = Linear.mk_int_term rest in
           let cterm = T_int.mk_int Z.(-n) in
           if Value.compare Z.Compare.(<=) Q.(<=)
               (Evaluator.eval_term @@ Term.subst model (T_int.mk_mult cterm varterm))
               (Evaluator.eval_term @@ Term.subst model ubterm)
           then Some (Set.Poly.singleton (cterm, ubterm)) else None
       | (Some (Int n, rest), T_bool.Neq) ->
         let (ubterm, cterm) = if Z.Compare.(n >= Z.zero)
           then (Linear.mk_int_term @@ Map.Poly.map rest ~f:(fun c' -> Value.div c' (Int Z.minus_one)), T_int.mk_int n)
           else (Linear.mk_int_term rest, T_int.mk_int Z.(-n)) in
         if Value.compare Z.Compare.(<=) Q.(<=)
             (Evaluator.eval_term @@ Term.subst model (T_int.mk_mult cterm varterm))
             (Evaluator.eval_term @@ Term.subst model ubterm)
         then Some (Set.Poly.singleton (cterm, T_int.mk_sub ubterm (T_int.one ()))) else None
       | _ -> None)
    | _ -> None
  let lb_atom model tvar = function
    | Atom.App (Predicate.Psym sym, [t; _t0], _)
      when (match sym with | T_bool.Eq | T_int.Geq | T_bool.Neq -> true | _ -> false) ->
      let monomial = linear_int_monomials_of (Value.Int Z.one) t in
      let varterm = Term.mk_var tvar T_int.SInt in
      (match (Linear.find_var_monomial varterm monomial, sym) with
       | (Some (Int n, rest), T_bool.Eq) ->
         if Z.Compare.(n = Z.zero) then None
         else
           let (lbterm, cterm) = if Z.Compare.(n > Z.zero)
             then (Linear.mk_int_term @@ Linear.int_mult rest (Value.Int Z.minus_one), T_int.mk_int n)
             else (Linear.mk_int_term rest, T_int.mk_int Z.(-n)) in
           if Value.compare Z.Compare.(=) Q.(=)
               (Evaluator.eval_term @@ Term.subst model (T_int.mk_mult cterm varterm))
               (Evaluator.eval_term @@ Term.subst model lbterm)
           then Some (Set.Poly.singleton (cterm, lbterm)) else assert false
       | (Some (Int n, rest), T_int.Geq) ->
         if Z.Compare.(n <= Z.zero) then None
         else let lbterm = Linear.mk_int_term @@Map.Poly.map rest ~f:(fun c' -> Value.div c' (Int Z.minus_one)) in
           let cterm = T_int.mk_int n in
           if Value.compare Z.Compare.(>=) Q.(>=)
               (Evaluator.eval_term @@ Term.subst model (T_int.mk_mult cterm varterm))
               (Evaluator.eval_term @@ Term.subst model lbterm)
           then Some (Set.Poly.singleton (cterm, lbterm)) else None
       | (Some (Int n, rest), T_bool.Neq) ->
         let (lbterm, cterm) = if Z.Compare.(n >= Z.zero)
           then (Linear.mk_int_term @@ Map.Poly.map rest ~f:(fun c' -> Value.div c' (Int Z.minus_one)), T_int.mk_int n)
           else (Linear.mk_int_term rest, T_int.mk_int Z.(-n)) in
         if Value.compare Z.Compare.(>=) Q.(>=)
             (Evaluator.eval_term @@ Term.subst model (T_int.mk_mult cterm varterm))
             (Evaluator.eval_term @@ Term.subst model lbterm)
         then Some (Set.Poly.singleton (cterm, T_int.mk_add lbterm (T_int.one ()))) else None
       | _ -> None)
    | _ -> None

  let ub_and_lb model tvar l =
    List.fold l ~init:(Set.Poly.empty, Set.Poly.empty, []) ~f:(fun (ub, lb, rest) atom ->
        match (ub_atom model tvar atom, lb_atom model tvar atom) with
        | (None, None) -> (ub, lb, (mk_atom atom)::rest)
        | (Some s, None) -> ((Set.Poly.union ub s), lb, rest)
        | (None, Some s) -> (ub, (Set.Poly.union lb s), rest)
        | (Some s1, Some s2) -> ((Set.Poly.union ub s1), (Set.Poly.union lb s2), rest))
  let glb model lb =
    let (_, c, t) =
      Set.Poly.fold lb ~init:(Q.minus_inf, Term.mk_dummy T_int.SInt, Term.mk_dummy T_int.SInt)
        ~f:(fun (glb, c, t) (c', t') ->
            let cv = Value.int_of @@ Evaluator.eval_term c' in
            let tv = Value.int_of @@ Evaluator.eval_term @@Term.subst model t' in
            let v = Q.make tv cv in
            if Q.(glb < v) then (v, c', t') else (glb, c, t))
    in
    (c, t)
  (* resolve(M, t<= ax, bx <= s) *)
  let resolve model a t b s =
    let av = Value.int_of @@ Evaluator.eval_term a in
    let tv = Value.int_of @@ Evaluator.eval_term (Term.subst model t) in
    let bv = Value.int_of @@ Evaluator.eval_term b in
    let sv = Value.int_of @@ Evaluator.eval_term (Term.subst model s) in
    let btt = T_int.mk_mult b t in
    let ast = T_int.mk_mult a s in
    let a_1b_1 = Z.mul (Z.(av - Z.one)) (Z.(bv - Z.one)) in
    let as_bt = Z.((av * sv) - (bv * tv)) in
    if Z.Compare.(a_1b_1 <= as_bt) then
      let atom = mk_atom @@T_int.mk_leq (T_int.mk_add btt (T_int.mk_int a_1b_1)) ast in
      [atom]
    else if Z.Compare.(av <= bv) then
      let d = Z.erem (Z.neg tv) av in
      let td = T_int.mk_add t (T_int.mk_int d) in
      let atom1 = mk_atom @@ T_int.mk_leq btt ast in
      let atom2 = mk_atom @@ T_int.mk_pdiv a td in
      let atom3 = mk_atom @@ T_int.mk_leq (T_int.mk_mult b td) ast in
      [atom1; atom2; atom3]
    else
      let d = Z.erem sv bv in
      let sd = T_int.mk_sub s (T_int.mk_int d) in
      let atom1 = mk_atom @@ T_int.mk_leq btt ast in
      let atom2 = mk_atom @@ T_int.mk_pdiv b sd in
      let atom3 = mk_atom @@ T_int.mk_leq btt (T_int.mk_mult a sd) in
      [atom1; atom2; atom3]

  let model_based_projection_sub model tvar atoms =
    (*print_endline ("Mbpsub: " ^ (Ident.name_of_tvar tvar));
      print_endline ("atoms: " ^ (List.to_string ~f:Atom.str_of atoms));*)
    let (ub, lb, rest) = ub_and_lb model tvar atoms in
    (*print_endline ("ub: " ^ (List.to_string ~f:(fun (t1, t2) -> (Term.str_of t1) ^ "," ^ (Term.str_of t2)) (Set.Poly.to_list ub)));
      print_endline ("lb: " ^ (List.to_string ~f:(fun (t1, t2) -> (Term.str_of t1) ^ "," ^ (Term.str_of t2)) (Set.Poly.to_list lb)));
      print_endline ("rest: " ^ (List.to_string ~f:str_of rest));*)
    if Set.Poly.is_empty ub && Set.Poly.is_empty lb then rest
    else
      let (c0, t0) = glb model lb in
      let lbformulas = List.map (Set.Poly.to_list lb) ~f:(fun (c, t) ->
          mk_atom @@T_int.mk_leq (T_int.mk_mult t c0) (T_int.mk_mult t0 c)) in
      let ubformulas = List.concat_map (Set.Poly.to_list ub) ~f:(fun (c, t) -> resolve model c0 t0 c t) in
      (*print_endline ("lbformulas: " ^ (List.to_string ~f:str_of lbformulas));
        print_endline ("ubformulas: " ^ (List.to_string ~f:str_of ubformulas));*)
      lbformulas @ ubformulas @ rest

  let rec model_based_projection model tvar phis =
    let atoms = List.map phis ~f:(fun phi -> Normalizer.normalize_atom @@Formula.to_atom phi) in
    (*print_endline ("Mbp: " ^ (Ident.name_of_tvar tvar));
      print_endline ("atoms: " ^ (List.to_string ~f:Atom.str_of atoms));
      print_endline ("model: " ^ (TermSubst.str_of model));*)
    let (pdivs, rest) = List.fold atoms ~init:([], []) ~f:(fun (pdivs, rest) atom ->
        match is_pdiv atom tvar with
        | Some (psym, d, c, t) -> ((psym, d, c, t)::pdivs, rest)
        | None -> (pdivs, atom::rest)) in
    if List.is_empty pdivs then model_based_projection_sub model tvar atoms
    else let (newmodel, newtvar, newterm, pdivs) = rm_pdiv pdivs model tvar in
      (*print_endline ("newterm: " ^ (Ident.name_of_tvar tvar) ^ " -> " ^ (Term.str_of newterm));
        print_endline ("newmodel: " ^ (TermSubst.str_of newmodel));*)
      let newatoms = List.map rest ~f:(fun atom ->
          mk_atom @@Normalizer.normalize_atom @@ Atom.subst (Map.Poly.singleton tvar newterm) atom) in
      (model_based_projection newmodel newtvar newatoms) @ pdivs
end

module Boolean = struct
  let let_sort names model =
    Map.Poly.fold model ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term newmodel ->
        match Evaluator.eval_term term with
        | Value.Bool b ->
          if Set.Poly.mem names (Ident.name_of_tvar tvar) then newmodel
          else if b then Map.Poly.add_exn newmodel ~key:tvar ~data:(T_bool.mk_true ())
          else Map.Poly.add_exn newmodel ~key:tvar ~data:(T_bool.mk_true ())
        | _ -> assert false)

  let find_bool_var tvar phi =
    let open Formula in
    let name = Ident.name_of_tvar tvar in
    match phi with
    | Atom (App (Predicate.Var (Ident.Pvar name', _), [], _), _)
    | UnaryOp (Not, Atom (App (Predicate.Var (Ident.Pvar name', _), [], _), _), _) ->
      Stdlib.(name = name')
    | _ -> assert false

  let model_based_projection _model tvar = List.filter ~f:(Fn.non @@ find_bool_var tvar)
end
