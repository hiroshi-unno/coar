open Core
open Common.Ext
open Common.Combinator
open LogicOld
open ArithTerm
open Normalizer

let sign model atom =
  Normalizer.normalize_atom
  @@
  if Evaluator.eval_atom @@ Atom.subst model atom then atom
  else Atom.negate atom

exception NotNormalized

let rec atoms_of model = function
  | Formula.Atom (phi, _) -> Set.Poly.singleton phi
  | UnaryOp (Not, Atom (phi, _), _) -> Set.Poly.singleton @@ Atom.negate phi
  | UnaryOp (Not, UnaryOp (Not, phi', _), _) -> atoms_of model phi'
  | BinaryOp (And, phi1, phi2, _) ->
      Set.union (atoms_of model phi1) (atoms_of model phi2)
  | BinaryOp (Or, phi1, phi2, _) ->
      let s1 =
        if Evaluator.eval @@ Formula.subst model phi1 then atoms_of model phi1
        else Set.Poly.empty
      in
      let s2 =
        if Evaluator.eval @@ Formula.subst model phi2 then atoms_of model phi2
        else Set.Poly.empty
      in
      Set.union s1 s2
  | _phi -> raise NotNormalized
(*failwith (Formula.str_of phi ^ " is not atomic formula")*)

let normalize_mbp model atm =
  Set.concat
  @@ Set.Poly.map ~f:(fun atm ->
         Set.Poly.map ~f:Normalizer.normalize_atom
         @@ atoms_of model
         @@ Evaluator.simplify_atom atm)
  @@ Set.Poly.map ~f:Normalizer.normalize_atom
  @@ atoms_of model
  @@ Evaluator.simplify_atom atm

module LRA = struct
  let let_sort names =
    Map.Poly.fold ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term model ->
        if Set.mem names (Ident.name_of_tvar tvar) then model (*ToDo*)
        else
          match Evaluator.eval_term term with
          | Value.Bool b ->
              Map.Poly.add_exn model ~key:tvar ~data:(T_bool.make b)
          | Value.Int n ->
              Map.Poly.add_exn model ~key:tvar
                ~data:(T_real.mk_real (Q.of_bigint n))
              (*ToDo*)
          | Value.Real r ->
              Map.Poly.add_exn model ~key:tvar ~data:(T_real.mk_real r))

  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; _ ], _) -> (
        let varterm = Term.mk_var tvar T_real.SReal in
        match
          Linear.find_var_monomial varterm
          @@ linear_real_monomials_of (Value.Real Q.one) t
        with
        | Some (c, rest) ->
            if
              Map.Poly.existsi rest ~f:(fun ~key ~data:_ ->
                  match key with
                  | None -> false
                  | Some t -> Set.mem (Term.fvs_of t) tvar)
            then raise NotNormalized;
            Option.return @@ Linear.mk_real_term
            @@ Map.Poly.map rest ~f:(Fn.flip Value.div (Value.neg c))
        | None -> None)
    | _ -> None

  (*let neq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Neq, [t; _], _) as atm ->
      let varterm = Term.mk_var tvar T_real.SReal in
      (match Linear.find_var_monomial varterm @@
         linear_real_monomials_of (Value.Real Q.one) t with
      | Some (c, rest) ->
        if Map.Poly.existsi rest ~f:(fun ~key ~data:_ -> match key with None -> false | Some t -> Set.mem (Term.fvs_of t) tvar) then raise NotNormalized;
        Option.return @@
        (Linear.mk_real_term @@ Map.Poly.map rest ~f:(Fn.flip Value.div (Value.neg c)), atm)
      | None -> None)
    | _ -> None*)
  let ub_and_lb tvar =
    Set.fold ~init:(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
      ~f:(fun (ub, lb, others) -> function
      | Atom.App (Predicate.Psym T_real.(RGeq | RGt (*ToDo*)), [ t; _ ], _) as
        atom -> (
          let varterm = Term.mk_var tvar T_real.SReal in
          match
            Linear.find_var_monomial varterm
            @@ linear_real_monomials_of (Value.Real Q.one) t
          with
          | Some (Real r, rest) ->
              if
                Map.Poly.existsi rest ~f:(fun ~key ~data:_ ->
                    match key with
                    | None -> false
                    | Some t -> Set.mem (Term.fvs_of t) tvar)
              then raise NotNormalized;
              if Q.(r < zero) then
                ( Set.add ub @@ Linear.mk_real_term
                  @@ Map.Poly.map rest
                       ~f:(Fn.flip Value.div (Value.neg (Real r))),
                  lb,
                  others )
              else if Q.(r > zero) then
                ( ub,
                  Set.add lb @@ Linear.mk_real_term
                  @@ Map.Poly.map rest
                       ~f:(Fn.flip Value.div (Value.neg (Real r))),
                  others )
              else failwith "ub_and_lb"
          | _ -> (ub, lb, Set.add others atom))
      | atom -> (ub, lb, Set.add others atom))

  let lub model ub =
    fst
    @@ Set.fold ub ~init:(None, Q.inf) ~f:(fun (lub, lub_val) t ->
           match Evaluator.eval_term @@ Term.subst model t with
           | Real r -> if Q.(r < lub_val) then (Some t, r) else (lub, lub_val)
           | _ -> failwith "lub")

  let glb model lb =
    fst
    @@ Set.fold lb ~init:(None, Q.minus_inf) ~f:(fun (glb, glb_val) t ->
           match Evaluator.eval_term @@ Term.subst model t with
           | Real r -> if Q.(r > glb_val) then (Some t, r) else (glb, glb_val)
           | _ -> failwith "glb")

  let model_based_projection model tvar atoms =
    match Set.find_map atoms ~f:(eq_atom tvar) with
    | Some t ->
        let sub = Map.Poly.singleton tvar t in
        Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
    | None -> (
        (*let rec elim_neq atoms =
            match Set.find_map atoms ~f:(neq_atom tvar) with
            | Some (t, atom) ->
              elim_neq @@
              Set.add (Set.remove atoms atom) @@
              if Value.compare Z.Compare.(>) Q.(>)
                  (Evaluator.eval_term @@ Map.Poly.find_exn model tvar)
                  (Evaluator.eval_term @@ Term.subst model t) then
                Normalizer.normalize_atom @@
                T_real.mk_rgt (Term.mk_var tvar T_real.SReal) t
              else if Value.compare Z.Compare.(<) Q.(<)
                  (Evaluator.eval_term @@ Map.Poly.find_exn model tvar)
                  (Evaluator.eval_term @@ Term.subst model t) then
                Normalizer.normalize_atom @@
                T_real.mk_rgt t (Term.mk_var tvar T_real.SReal)
              else failwith "elim_neq"
            | None -> atoms
          in
          let atoms = elim_neq atoms in*)
        let ub, lb, rest = ub_and_lb tvar atoms in
        match (lub model ub, glb model lb) with
        | Some lub, Some glb ->
            let sub =
              Map.Poly.singleton tvar
              @@ T_real.mk_rmult (T_real.mk_radd lub glb)
                   (T_real.mk_real (Q.of_float 0.5))
            in
            Set.concat_map rest ~f:(Atom.subst sub >> normalize_mbp model)
        | Some lub, None ->
            let sub =
              Map.Poly.singleton tvar @@ T_real.mk_rsub lub (T_real.rone ())
            in
            Set.concat_map rest ~f:(Atom.subst sub >> normalize_mbp model)
        | None, Some glb ->
            let sub =
              Map.Poly.singleton tvar @@ T_real.mk_radd glb (T_real.rone ())
            in
            Set.concat_map rest ~f:(Atom.subst sub >> normalize_mbp model)
        | None, None ->
            if Set.exists rest ~f:(fun atom -> Set.mem (Atom.fvs_of atom) tvar)
            then raise NotNormalized
              (*failwith @@ "no constraint on " ^ Ident.name_of_tvar tvar*)
            else rest (* reachable here when simplification eliminated tvar *))
end

module LIA = struct
  let let_sort names =
    Map.Poly.fold ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term model ->
        if Set.mem names (Ident.name_of_tvar tvar) then model (*ToDo*)
        else
          match Evaluator.eval_term term with
          | Value.Bool b ->
              Map.Poly.add_exn model ~key:tvar ~data:(T_bool.make b)
          | Value.Int n ->
              Map.Poly.add_exn model ~key:tvar ~data:(T_int.mk_int n)
          | Value.Real _ -> failwith "LIA")

  let is_pdiv atom tvar =
    match atom with
    | Atom.App
        (Predicate.Psym ((T_int.PDiv | T_int.NotPDiv) as psym), [ d; t ], _)
      -> (
        match
          Linear.find_var_monomial (Term.mk_var tvar T_int.SInt)
          @@ linear_int_monomials_of (Value.Int Z.one) t
        with
        | Some (c, rest) ->
            if
              Map.Poly.existsi rest ~f:(fun ~key ~data:_ ->
                  match key with
                  | None -> false
                  | Some t -> Set.mem (Term.fvs_of t) tvar)
            then raise NotNormalized;
            Some (psym, Evaluator.eval_term d, c, rest)
        | None -> None)
    | _ -> None

  let rm_pdiv pdivs model tvar =
    let lcm =
      Set.fold pdivs ~init:Z.one ~f:(fun d1 (_, value, _, _) ->
          match value with Value.Int d2 -> Z.lcm d1 d2 | _ -> d1)
    in
    (*print_endline @@ "lcm: " ^ Z.to_string lcm;*)
    let varmodel = Term.subst model (Term.mk_var tvar T_int.SInt) in
    let u_val =
      Evaluator.eval_term @@ T_int.mk_mod varmodel (T_int.mk_int lcm)
    in
    let u = Term.of_value u_val in
    let newtvar = Ident.mk_fresh_tvar () in
    let newterm =
      T_int.mk_add u
        (T_int.mk_mult (T_int.mk_int lcm) (Term.mk_var newtvar T_int.SInt))
    in
    let newmodel =
      let newvalue =
        Term.of_value @@ Evaluator.eval_term
        @@ T_int.mk_div (T_int.mk_sub varmodel u) (T_int.mk_int lcm)
      in
      (*print_endline @@ sprintf "newvar: %s |-> %s" (Ident.name_of_tvar newtvar) (Term.str_of newvalue);*)
      Map.Poly.add_exn model ~key:newtvar ~data:newvalue
    in
    let pdivs =
      Set.Poly.map pdivs ~f:(fun (psym, d, c, t) ->
          match psym with
          | T_int.PDiv ->
              Normalizer.normalize_atom
              @@ Atom.mk_app (Predicate.Psym psym)
              @@ [
                   Term.of_value d;
                   T_int.mk_add
                     (T_int.mk_int
                        Z.(mul (Value.int_of c) (Value.int_of u_val)))
                     (Linear.mk_int_term t);
                 ]
          | _ ->
              failwith
              @@ sprintf "[rm_pdiv] %s not supported"
                   (Predicate.str_of_psym psym))
    in
    (newmodel, newtvar, newterm, pdivs)

  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; _ ], _) as atm -> (
        let varterm = Term.mk_var tvar T_int.SInt in
        match
          Linear.find_var_monomial varterm
          @@ linear_int_monomials_of (Value.Int Z.one) t
        with
        | Some (c, rest) ->
            if
              Map.Poly.existsi rest ~f:(fun ~key ~data:_ ->
                  match key with
                  | None -> false
                  | Some t -> Set.mem (Term.fvs_of t) tvar)
            then raise NotNormalized;
            if
              Map.Poly.for_all rest ~f:(fun v ->
                  Z.Compare.(Value.int_of @@ Value.bmod v c = Z.zero))
            then
              Some
                ( Z.one,
                  Linear.mk_int_term
                  @@ Map.Poly.map rest ~f:(Fn.flip Value.div (Value.neg c)),
                  atm )
            else if Z.Compare.(Value.int_of c > Z.zero) then
              Some
                ( Value.int_of c,
                  Linear.mk_int_term
                  @@ Map.Poly.map rest ~f:(Fn.flip Value.mult (Int Z.minus_one)),
                  atm )
            else Some (Z.(-Value.int_of c), Linear.mk_int_term rest, atm)
        | _ -> None)
    | _ -> None

  (*let neq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Neq, [t; _], _) as atm ->
      let varterm = Term.mk_var tvar T_int.SInt in
      (match Linear.find_var_monomial varterm @@
         linear_int_monomials_of (Value.Int Z.one) t with
      | Some (c, rest) ->
        if Map.Poly.existsi rest ~f:(fun ~key ~data:_ -> match key with None -> false | Some t -> Set.mem (Term.fvs_of t) tvar) then raise NotNormalized;
        if Map.Poly.for_all rest ~f:(fun v -> Z.Compare.(Value.int_of @@ Value.bmod v c = Z.zero)) then
          Some (Z.one, Linear.mk_int_term @@
                Map.Poly.map rest ~f:(Fn.flip Value.div (Value.neg c)),
                atm)
        else if Z.Compare.(Value.int_of c > Z.zero) then
          Some (Value.int_of c, Linear.mk_int_term @@
                Map.Poly.map rest ~f:(Fn.flip Value.mult (Int Z.minus_one)),
                atm)
        else Some (Z.(- Value.int_of c), Linear.mk_int_term rest, atm)
      | _ -> None)
    | _ -> None*)
  let ub_and_lb tvar =
    Set.fold ~init:(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
      ~f:(fun (ub, lb, others) -> function
      | Atom.App (Predicate.Psym T_int.Geq, [ t; _ ], _) as atom -> (
          let varterm = Term.mk_var tvar T_int.SInt in
          match
            Linear.find_var_monomial varterm
            @@ linear_int_monomials_of (Value.Int Z.one) t
          with
          | Some (Int n, rest) ->
              if
                Map.Poly.existsi rest ~f:(fun ~key ~data:_ ->
                    match key with
                    | None -> false
                    | Some t -> Set.mem (Term.fvs_of t) tvar)
              then raise NotNormalized;
              if Z.Compare.(n < Z.zero) then
                (Set.add ub (Z.(-n), Linear.mk_int_term rest), lb, others)
              else if Z.Compare.(n > Z.zero) then
                ( ub,
                  Set.add lb
                    ( n,
                      Linear.mk_int_term
                      @@ Map.Poly.map rest
                           ~f:(Fn.flip Value.mult (Int Z.minus_one)) ),
                  others )
              else failwith "ub_and_lb"
          | _ -> (ub, lb, Set.add others atom))
      | atom -> (ub, lb, Set.add others atom))

  let lub model ub =
    fst
    @@ Set.fold ub ~init:(None, Q.inf) ~f:(fun (lub, lub_val) (c, t) ->
           let tv = Evaluator.eval_term @@ Term.subst model t in
           let v = Q.make (Value.int_of tv) c in
           if Q.(lub_val > v) then (Some (c, t), v) else (lub, lub_val))

  let glb model lb =
    fst
    @@ Set.fold lb ~init:(None, Q.minus_inf) ~f:(fun (glb, glb_val) (c, t) ->
           let tv = Evaluator.eval_term @@ Term.subst model t in
           let v = Q.make (Value.int_of tv) c in
           if Q.(glb_val < v) then (Some (c, t), v) else (glb, glb_val))

  (* resolve(M, t <= ax, bx <= s) *)
  let resolve model av t bv s =
    let tv = Value.int_of @@ Evaluator.eval_term (Term.subst model t) in
    let sv = Value.int_of @@ Evaluator.eval_term (Term.subst model s) in
    let btt = T_int.mk_mult (T_int.mk_int bv) t in
    let ast = T_int.mk_mult (T_int.mk_int av) s in
    let a_1b_1 = Z.((av - one) * (bv - one)) in
    let as_bt = Z.((av * sv) - (bv * tv)) in
    if Z.Compare.(a_1b_1 <= as_bt) then
      Set.Poly.singleton
      @@ T_int.mk_leq (T_int.mk_add btt (T_int.mk_int a_1b_1)) ast
    else if Z.Compare.(av <= bv) then
      let d = Z.erem (Z.neg tv) av in
      let td = T_int.mk_add t (T_int.mk_int d) in
      let atom1 = T_int.mk_leq btt ast in
      let atom2 = T_int.mk_pdiv (T_int.mk_int av) td in
      let atom3 = T_int.(mk_leq (mk_mult (mk_int bv) td) ast) in
      Set.Poly.of_list [ atom1; atom2; atom3 ]
    else
      let d = Z.erem sv bv in
      let sd = T_int.mk_sub s (T_int.mk_int d) in
      let atom1 = T_int.mk_leq btt ast in
      let atom2 = T_int.mk_pdiv (T_int.mk_int bv) sd in
      let atom3 = T_int.(mk_leq btt (mk_mult (mk_int av) sd)) in
      Set.Poly.of_list [ atom1; atom2; atom3 ]

  let model_based_projection_sub model tvar atoms =
    let ub, lb, rest = ub_and_lb tvar atoms in
    (*print_endline @@ "ub: " ^ List.to_string ~f:(fun (t1, t2) -> Term.str_of t1 ^ "," ^ Term.str_of t2) (Set.to_list ub);
      print_endline @@ "lb: " ^ List.to_string ~f:(fun (t1, t2) -> Term.str_of t1 ^ "," ^ Term.str_of t2) (Set.to_list lb);
      print_endline @@ "rest: " ^ List.to_string ~f:str_of rest;*)
    (*if Set.mem (Set.concat_map ~f:Formula.fvs_of rest) tvar then
      let sub = Map.Poly.singleton tvar (Map.Poly.find_exn model tvar) in
      Set.concat_map atoms ~f:(Atom.subst sub >> Formula.mk_atom)
      else*)
    match (lub model ub, glb model lb) with
    | Some (cub, tub), Some (clb, tlb) ->
        let lbformulas =
          Set.Poly.map lb ~f:(fun (c, t) ->
              T_int.mk_leq
                (T_int.mk_mult t @@ T_int.mk_int clb)
                (T_int.mk_mult tlb @@ T_int.mk_int c))
        in
        let ubformulas =
          Set.concat_map ub ~f:(fun (c, t) -> resolve model clb tlb c t)
        in
        let sub =
          let glb = T_int.mk_div tlb @@ T_int.mk_int clb in
          let lub =
            T_int.mk_add (T_int.mk_div tub @@ T_int.mk_int cub) (T_int.one ())
          in
          Map.Poly.singleton tvar
            (T_int.mk_div (T_int.mk_add glb lub) (T_int.from_int 2))
        in
        (*print_endline @@ "lbformulas: " ^ List.to_string ~f:str_of lbformulas;
          print_endline @@ "ubformulas: " ^ List.to_string ~f:str_of ubformulas;*)
        Set.concat_map ~f:(normalize_mbp model)
        @@ Set.Poly.union_list
             [ lbformulas; ubformulas; Set.Poly.map rest ~f:(Atom.subst sub) ]
    | Some (cub, tub), None ->
        let sub =
          Map.Poly.singleton tvar @@ T_int.mk_div tub @@ T_int.mk_int cub
        in
        Set.concat_map rest ~f:(Atom.subst sub >> normalize_mbp model)
    | None, Some (clb, tlb) ->
        let sub =
          Map.Poly.singleton tvar
          @@ T_int.mk_add (T_int.mk_div tlb @@ T_int.mk_int clb) (T_int.one ())
        in
        Set.concat_map rest ~f:(Atom.subst sub >> normalize_mbp model)
    | None, None ->
        if Set.exists rest ~f:(fun atom -> Set.mem (Atom.fvs_of atom) tvar) then
          raise NotNormalized
          (*failwith @@ "no constraint on " ^ Ident.name_of_tvar tvar*)
        else rest (* reachable here when simplification eliminated tvar *)

  let rec model_based_projection model tvar atoms =
    match Set.find_map atoms ~f:(eq_atom tvar) with
    | Some (c, t, atom) ->
        if Z.Compare.(c = Z.one) then
          let sub = Map.Poly.singleton tvar t in
          Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
        else
          let cx =
            T_int.mk_mult (T_int.mk_int c) @@ Term.mk_var tvar T_int.SInt
          in
          model_based_projection model tvar
          @@ Set.union (Set.remove atoms atom)
          @@ Set.concat_map ~f:(normalize_mbp model)
          @@ Set.Poly.of_list [ T_int.mk_geq t cx; T_int.mk_geq cx t ]
    | None ->
        (*let rec elim_neq atoms =
            match Set.find_map atoms ~f:(neq_atom tvar) with
            | Some (c, t, atom) ->
              let cx = T_int.mk_mult (T_int.mk_int c) @@ Term.mk_var tvar T_int.SInt in
              elim_neq @@
              Set.add (Set.remove atoms atom) @@
              if Value.compare Z.Compare.(>) Q.(>)
                  (Evaluator.eval_term @@ Term.subst model cx)
                  (Evaluator.eval_term @@ Term.subst model t) then
                Normalizer.normalize_atom @@ T_int.mk_gt cx t
              else if Value.compare Z.Compare.(<) Q.(<)
                  (Evaluator.eval_term @@ Term.subst model cx)
                  (Evaluator.eval_term @@ Term.subst model t) then
                Normalizer.normalize_atom @@ T_int.mk_gt t cx
              else failwith "elim_neq"
            | None -> atoms
          in
          let atoms = elim_neq atoms in*)
        let pdivs, rest =
          Set.fold atoms ~init:(Set.Poly.empty, Set.Poly.empty)
            ~f:(fun (pdivs, rest) atom ->
              match is_pdiv atom tvar with
              | Some (psym, d, c, t) -> (Set.add pdivs (psym, d, c, t), rest)
              | None -> (pdivs, Set.add rest atom))
        in
        if Set.is_empty pdivs then model_based_projection_sub model tvar rest
        else
          let newmodel, newtvar, newterm, pdivs = rm_pdiv pdivs model tvar in
          (*print_endline @@ sprintf "newterm: %s -> %s" (Ident.name_of_tvar tvar) (Term.str_of newterm);
            print_endline @@ sprintf "newmodel: %s" (TermSubst.str_of newmodel);*)
          let pdivs = Set.concat_map pdivs ~f:(normalize_mbp model) in
          Set.union pdivs
          @@ model_based_projection newmodel newtvar
          @@
          let sub = Map.Poly.singleton tvar newterm in
          Set.concat_map rest ~f:(Atom.subst sub >> normalize_mbp model)
end

module Boolean = struct
  let let_sort names =
    Map.Poly.fold ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term model ->
        if Set.mem names (Ident.name_of_tvar tvar) then model (*ToDo*)
        else
          match Evaluator.eval_term term with
          | Value.Bool b ->
              Map.Poly.add_exn model ~key:tvar ~data:(T_bool.make b)
          | Value.Int _ -> failwith "Boolean"
          | Value.Real _ -> failwith "Boolean")

  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Neq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some (Evaluator.simplify_term @@ T_bool.neg t)
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some (Evaluator.simplify_term @@ T_bool.neg t)
    | _ -> None

  let model_based_projection model tvar atoms =
    match Set.find_map atoms ~f:(eq_atom tvar) with
    | Some t ->
        let sub = Map.Poly.singleton tvar t in
        Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
    | None ->
        if Set.exists atoms ~f:(fun atom -> Set.mem (Atom.fvs_of atom) tvar)
        then raise NotNormalized
          (*failwith @@ "no constraint on " ^ Ident.name_of_tvar tvar*)
        else atoms (* reachable here when simplification eliminated tvar *)
end
