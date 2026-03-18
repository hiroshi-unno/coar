open Core
open Common.Ext
open Common.Combinator
open LogicOld

let sign ~print model atom =
  let res =
    if Evaluator.eval_atom @@ Atom.subst model atom then (
      print @@ lazy (sprintf "[sign] pos: %s" (Atom.str_of atom));
      Formula.mk_atom @@ Normalizer.normalize_atom atom)
    else (
      print @@ lazy (sprintf "[sign] neg: %s" (Atom.str_of atom));
      match Atom.negate atom with
      | None ->
          if true then Formula.negate @@ Formula.mk_atom atom
          else failwith @@ sprintf "[sign] %s" (Atom.str_of atom)
      | Some neg_atom -> Formula.mk_atom @@ Normalizer.normalize_atom neg_atom)
  in
  match res with
  | Formula.Atom (Atom.App (Predicate.Psym T_int.NotPDiv, [ t1; t2 ], _), _)
    -> (
      assert (T_int.is_int t1);
      let res =
        List.filter_map
          (List.from_to 1 ((Z.to_int @@ T_int.let_int t1) - 1))
          ~f:(fun i ->
            let atom =
              T_int.mk_pdiv t1 @@ Evaluator.simplify_term
              @@ T_int.mk_add t2 (T_int.mk_int (Z.of_int i))
            in
            if Evaluator.eval_atom @@ Atom.subst model atom then
              Option.return @@ Normalizer.normalize_atom atom
            else None)
      in
      match res with [ atom ] -> Formula.mk_atom atom | _ -> assert false)
  | fml -> fml

exception NotNormalized

let rec atoms_of model = function
  | Formula.Atom (atm, _) -> Set.Poly.singleton atm
  | Formula.UnaryOp (Not, Atom (phi, _), _) -> (
      match Atom.negate phi with
      | None -> (*failwith "[atoms_of]"*) Set.Poly.empty
      | Some neg_atom -> Set.Poly.singleton neg_atom)
  | Formula.UnaryOp (Not, UnaryOp (Not, phi', _), _) -> atoms_of model phi'
  | Formula.BinaryOp (And, phi1, phi2, _) ->
      Set.union (atoms_of model phi1) (atoms_of model phi2)
  | Formula.BinaryOp (Or, phi1, phi2, _) ->
      let s1 =
        if Evaluator.eval @@ Formula.subst model phi1 then atoms_of model phi1
        else Set.Poly.empty
      in
      let s2 =
        if Evaluator.eval @@ Formula.subst model phi2 then atoms_of model phi2
        else Set.Poly.empty
      in
      Set.union s1 s2
  | _ ->
      (*failwith (Formula.str_of phi ^ " is not atomic formula")*)
      raise NotNormalized

let normalize_mbp model =
  Evaluator.simplify_atom >> atoms_of model
  >> Set.Poly.map ~f:Normalizer.normalize_atom
  >> Set.concat_map
       ~f:
         (Evaluator.simplify_atom >> atoms_of model
         >> Set.Poly.map ~f:Normalizer.normalize_atom)

let occur tvar rest =
  Map.Poly.existsi rest ~f:(fun ~key ~data:_ ->
      match key with None -> false | Some t -> Set.mem (Term.fvs_of t) tvar)

module LRA = struct
  let let_sort names =
    Map.Poly.fold ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term model ->
        if Set.mem names (Ident.name_of_tvar tvar) then model (*ToDo*)
        else
          let data =
            match Evaluator.eval_term term with
            | Value.Bool b -> T_bool.make b
            | Value.Int n -> T_real.mk_real (Q.of_bigint n) (*ToDo*)
            | Value.Real r -> T_real.mk_real r
            | Value.BV _ -> failwith "LRA: bitvector not supported"
            | Value.Arr _ -> failwith "LRA: array not supported"
            | Value.TupleCons _ -> failwith "LRA: tuple not supported"
            | Value.DTCons _ -> failwith "LRA: datatype not supported"
          in
          Map.Poly.add_exn model ~key:tvar ~data)

  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; _ ], _) -> (
        match
          AffineTerm.find_var_monomial (Term.mk_var tvar T_real.SReal)
          @@ Normalizer.linear_real_monomials_of (Value.Real Q.one) t
        with
        | Some (c, rest) ->
            if occur tvar rest then raise NotNormalized;
            Option.return @@ AffineTerm.mk_real_term
            @@ Map.Poly.map rest ~f:(Fn.flip Value.rdiv (Value.neg c))
        | None -> None)
    | _ -> None

  let neq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; _ ], _) as atm -> (
        match
          AffineTerm.find_var_monomial (Term.mk_var tvar T_real.SReal)
          @@ Normalizer.linear_real_monomials_of (Value.Real Q.one) t
        with
        | Some (c, rest) ->
            if occur tvar rest then raise NotNormalized;
            First
              (AffineTerm.mk_real_term
              @@ Map.Poly.map rest ~f:(Fn.flip Value.rdiv (Value.neg c)))
        | None -> Second atm)
    | atm -> Second atm

  let ub_and_lb tvar =
    Set.fold ~init:(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
      ~f:(fun (ub, lb, others) -> function
      | Atom.App (Predicate.Psym (T_real.(RGeq | RGt) as op), [ t; _ ], _) as
        atom -> (
          match
            AffineTerm.find_var_monomial (Term.mk_var tvar T_real.SReal)
            @@ Normalizer.linear_real_monomials_of (Value.Real Q.one) t
          with
          | Some (Real r, rest) ->
              if occur tvar rest then raise NotNormalized;
              let eps =
                match op with
                | T_real.RGeq -> false
                | T_real.RGt -> true
                | _ -> assert false
              in
              let t =
                AffineTerm.mk_real_term
                @@ Map.Poly.map rest
                     ~f:(Fn.flip Value.rdiv (Value.neg (Real r)))
              in
              if Q.(r < zero) then (Set.add ub (t, eps), lb, others)
              else if Q.(r > zero) then (ub, Set.add lb (t, eps), others)
              else failwith "ub_and_lb"
          | _ -> (ub, lb, Set.add others atom))
      | atom -> (ub, lb, Set.add others atom))

  let lt (r1, eps1) (r2, eps2) = Q.(r1 < r2) || (Q.(r1 = r2) && eps1 && not eps2)

  let lub model ub =
    match
      Set.fold
        ~init:(None, (Q.inf, false))
        ub
        ~f:(fun (lub, (lub_val, lub_eps)) (t, eps) ->
          match Evaluator.eval_term @@ Term.subst model t with
          | Real r ->
              if lt (r, eps) (lub_val, lub_eps) then (Some t, (r, eps))
              else (lub, (lub_val, lub_eps))
          | _ -> failwith "lub")
    with
    | None, _ -> None
    | Some t, (_, eps) -> Some (t, eps)

  let gt (r1, eps1) (r2, eps2) = Q.(r1 > r2) || (Q.(r1 = r2) && eps1 && not eps2)

  let glb model lb =
    match
      Set.fold
        ~init:(None, (Q.minus_inf, false))
        lb
        ~f:(fun (glb, (glb_val, glb_eps)) (t, eps) ->
          match Evaluator.eval_term @@ Term.subst model t with
          | Real r ->
              if gt (r, eps) (glb_val, glb_eps) then (Some t, (r, eps))
              else (glb, (glb_val, glb_eps))
          | _ -> failwith "glb")
    with
    | None, _ -> None
    | Some t, (_, eps) -> Some (t, eps)

  let model_based_projection ~print model tvar atoms =
    match Set.find_map atoms ~f:(eq_atom tvar) with
    | Some t ->
        let sub = Map.Poly.singleton tvar t in
        Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
    | None -> (
        let atoms =
          Set.Poly.map atoms
            ~f:
              ( neq_atom tvar >> function
                | First t ->
                    Normalizer.normalize_atom
                    @@
                    let lhs =
                      Evaluator.eval_term @@ Map.Poly.find_exn model tvar
                    in
                    let rhs = Evaluator.eval_term @@ Term.subst model t in
                    if Value.compare true Z.Compare.( > ) Q.( > ) lhs rhs then
                      T_real.mk_rgt (Term.mk_var tvar T_real.SReal) t
                    else if Value.compare true Z.Compare.( < ) Q.( < ) lhs rhs
                    then T_real.mk_rgt t (Term.mk_var tvar T_real.SReal)
                    else failwith "elim_neq"
                | Second atm -> atm )
        in
        let ub, lb, rest = ub_and_lb tvar atoms in
        let lub = lub model ub in
        let glb = glb model lb in
        print
        @@ lazy
             ("[mbp lra] lb: "
             ^ String.concat_map_set ~sep:", " lb ~f:(fun (t, eps) ->
                   sprintf "%s %s %s" (Term.str_of t)
                     (if eps then "<" else "<=")
                     (Ident.name_of_tvar tvar)));
        print
        @@ lazy
             ("[mbp lra] ub: "
             ^ String.concat_map_set ~sep:", " ub ~f:(fun (t, eps) ->
                   sprintf "%s %s %s" (Term.str_of t)
                     (if eps then ">" else ">=")
                     (Ident.name_of_tvar tvar)));
        (match glb with
        | None -> ()
        | Some (t, eps) ->
            print
            @@ lazy
                 ("[mbp lra] glb: "
                 ^ sprintf "%s %s %s" (Term.str_of t)
                     (if eps then "<" else "<=")
                     (Ident.name_of_tvar tvar)));
        (match lub with
        | None -> ()
        | Some (t, eps) ->
            print
            @@ lazy
                 ("[mbp lra] lub: "
                 ^ sprintf "%s %s %s" (Term.str_of t)
                     (if eps then ">" else ">=")
                     (Ident.name_of_tvar tvar)));
        print
        @@ lazy
             ("[mbp lra] rest: "
             ^ String.concat_map_set ~sep:", " rest ~f:(fun atm ->
                   sprintf "%s" (Atom.str_of atm)));
        match (lub, glb) with
        | Some (_, _), Some (glb, glb_eps) ->
            Set.Poly.union_list
              [
                rest;
                Set.concat_map lb ~f:(fun (t, eps) ->
                    normalize_mbp model
                    @@ (if Stdlib.(glb_eps = eps) || glb_eps (*ToDo*) then
                          T_real.mk_rgeq
                        else T_real.mk_rgt)
                         glb t);
                Set.concat_map ub ~f:(fun (t, eps) ->
                    normalize_mbp model
                    @@ (if (not glb_eps) && not eps then T_real.mk_rgeq
                        else T_real.mk_rgt)
                         t glb);
              ]
        | Some (lub, lub_eps), None ->
            Set.union rest
              (Set.concat_map ub ~f:(fun (t, eps) ->
                   normalize_mbp model
                   @@ (if Stdlib.(lub_eps = eps) || lub_eps (*ToDo*) then
                         T_real.mk_rgeq
                       else T_real.mk_rgt)
                        t lub))
        | None, Some (glb, glb_eps) ->
            Set.union rest
              (Set.concat_map lb ~f:(fun (t, eps) ->
                   normalize_mbp model
                   @@ (if Stdlib.(glb_eps = eps) || glb_eps (*ToDo*) then
                         T_real.mk_rgeq
                       else T_real.mk_rgt)
                        glb t))
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
          let data =
            match Evaluator.eval_term term with
            | Value.Bool b -> T_bool.make b
            | Value.Int n -> T_int.mk_int n
            | Value.Real _ -> failwith "LIA: real not supported"
            | Value.BV _ -> failwith "LIA: bitvector not supported"
            | Value.Arr _ -> failwith "LIA: array not supported"
            | Value.TupleCons _ -> failwith "LIA: tuple not supported"
            | Value.DTCons _ -> failwith "LIA: datatype not supported"
          in
          Map.Poly.add_exn model ~key:tvar ~data)

  let is_pdiv tvar = function
    | Atom.App (Predicate.Psym (T_int.(PDiv | NotPDiv) as psym), [ d; t ], _) as
      atm -> (
        match
          AffineTerm.find_var_monomial (Term.mk_var tvar T_int.SInt)
          @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) t
        with
        | Some (c, rest) ->
            if occur tvar rest then raise NotNormalized;
            First (psym, Evaluator.eval_term d, c, rest)
        | None -> Second atm)
    | atm -> Second atm

  let rm_pdiv ~print pdivs model tvar =
    let lcm =
      Set.fold pdivs ~init:Z.one ~f:(fun d1 -> function
        | _, Value.Int d2, _, _ -> Z.lcm d1 d2
        | _ -> d1)
    in
    print @@ lazy ("[mbp lia] lcm: " ^ Z.to_string lcm);
    let varmodel = Term.subst model (Term.mk_var tvar T_int.SInt) in
    let u_val =
      Evaluator.eval_term
      @@ T_int.mk_rem Value.Euclidean varmodel (T_int.mk_int lcm)
    in
    let u = Term.of_value (get_dtenv ()) u_val in
    let newtvar = Ident.mk_fresh_tvar () in
    let newterm =
      T_int.(mk_add u (mk_mul (mk_int lcm) (Term.mk_var newtvar SInt)))
    in
    let newmodel =
      if true then model
      else
        let newvalue =
          Term.of_value (get_dtenv ())
          @@ Evaluator.eval_term
          @@ T_int.(mk_div Value.Euclidean (mk_sub varmodel u) (mk_int lcm))
        in
        print
        @@ lazy
             (sprintf "[mbp lia] newvar: %s |-> %s"
                (Ident.name_of_tvar newtvar)
                (Term.str_of newvalue));
        Map.Poly.add_exn model ~key:newtvar ~data:newvalue
    in
    let pdivs =
      Set.Poly.map pdivs ~f:(function
        | T_int.PDiv, d, c, t ->
            Normalizer.normalize_atom
            @@ Atom.mk_app (Predicate.Psym T_int.PDiv)
                 [
                   Term.of_value (get_dtenv ()) d;
                   T_int.mk_add
                     (T_int.mk_int
                        Z.(mul (Value.int_of c) (Value.int_of u_val)))
                     (AffineTerm.mk_int_term t);
                 ]
        | psym, _, _, _ ->
            failwith
            @@ sprintf "[rm_pdiv] %s not supported" (Predicate.str_of_psym psym))
    in
    (newmodel, newtvar, newterm, pdivs)

  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; _ ], _) as atm -> (
        match
          AffineTerm.find_var_monomial (Term.mk_var tvar T_int.SInt)
          @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) t
        with
        | Some (c, rest) ->
            if occur tvar rest then raise NotNormalized;
            if
              Map.Poly.for_all rest ~f:(fun v ->
                  Z.Compare.(Value.(int_of @@ rem Euclidean v c = Z.zero)))
            then
              Some
                ( Z.one,
                  AffineTerm.mk_int_term
                  @@ Map.Poly.map rest
                       ~f:(Fn.flip (Value.div Value.Euclidean) (Value.neg c)),
                  atm )
            else if Z.Compare.(Value.int_of c > Z.zero) then
              Some
                ( Value.int_of c,
                  AffineTerm.mk_int_term
                  @@ Map.Poly.map rest ~f:(Fn.flip Value.mul (Int Z.minus_one)),
                  atm )
            else Some (Z.(-Value.int_of c), AffineTerm.mk_int_term rest, atm)
        | _ -> None)
    | _ -> None

  let neq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; _ ], _) as atm -> (
        match
          AffineTerm.find_var_monomial (Term.mk_var tvar T_int.SInt)
          @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) t
        with
        | Some (c, rest) ->
            if occur tvar rest then raise NotNormalized;
            if
              Map.Poly.for_all rest ~f:(fun v ->
                  Z.Compare.(Value.(int_of @@ rem Euclidean v c = Z.zero)))
            then
              First
                ( Z.one,
                  AffineTerm.mk_int_term
                  @@ Map.Poly.map rest
                       ~f:(Fn.flip (Value.div Value.Euclidean) (Value.neg c)) )
            else if Z.Compare.(Value.int_of c > Z.zero) then
              First
                ( Value.int_of c,
                  AffineTerm.mk_int_term
                  @@ Map.Poly.map rest ~f:(Fn.flip Value.mul (Int Z.minus_one))
                )
            else First (Z.(-Value.int_of c), AffineTerm.mk_int_term rest)
        | None -> Second atm)
    | atm -> Second atm

  let ub_and_lb tvar =
    Set.fold ~init:(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
      ~f:(fun (ub, lb, others) -> function
      | Atom.App (Predicate.Psym T_int.Geq, [ t; _ ], _) as atom -> (
          match
            AffineTerm.find_var_monomial (Term.mk_var tvar T_int.SInt)
            @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) t
          with
          | Some (Int n, rest) ->
              if occur tvar rest then raise NotNormalized;
              if Z.Compare.(n < Z.zero) then
                (Set.add ub (Z.(-n), AffineTerm.mk_int_term rest), lb, others)
              else if Z.Compare.(n > Z.zero) then
                ( ub,
                  Set.add lb
                    ( n,
                      AffineTerm.mk_int_term
                      @@ Map.Poly.map rest
                           ~f:(Fn.flip Value.mul (Int Z.minus_one)) ),
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

  (* resolve(M, ax <= t, bx >= s) *)
  let resolve model av t bv s =
    let tv = Value.int_of @@ Evaluator.eval_term (Term.subst model t) in
    let sv = Value.int_of @@ Evaluator.eval_term (Term.subst model s) in
    let btt = T_int.mk_mul (T_int.mk_int bv) t in
    let ast = T_int.mk_mul (T_int.mk_int av) s in
    let a_1b_1 = Z.((av - one) * (bv - one)) in
    let bt_as = Z.((bv * tv) - (av * sv)) in
    if Z.Compare.(a_1b_1 <= bt_as) then
      Set.Poly.singleton
      @@ T_int.mk_leq (T_int.mk_add ast (T_int.mk_int a_1b_1)) btt
    else if Z.Compare.(av >= bv) then
      let d = Z.erem (Z.neg sv) bv in
      let sd = T_int.mk_add s (T_int.mk_int d) in
      Set.Poly.of_list
        [
          T_int.mk_leq ast btt;
          T_int.mk_pdiv (T_int.mk_int bv) sd;
          T_int.(mk_leq (mk_mul (mk_int av) sd) btt);
        ]
    else
      let d = Z.erem tv av in
      let td = T_int.mk_sub t (T_int.mk_int d) in
      Set.Poly.of_list
        [
          T_int.mk_leq ast btt;
          T_int.mk_pdiv (T_int.mk_int av) td;
          T_int.(mk_leq ast (mk_mul (mk_int bv) td));
        ]

  let model_based_projection_aux ~print model tvar atoms =
    let ub, lb, rest = ub_and_lb tvar atoms in
    print
    @@ lazy
         ("[mbp lia] ub: "
         ^ List.to_string
             ~f:(fun (t1, t2) -> Z.to_string t1 ^ "," ^ Term.str_of t2)
             (Set.to_list ub));
    print
    @@ lazy
         ("[mbp lia] lb: "
         ^ List.to_string
             ~f:(fun (t1, t2) -> Z.to_string t1 ^ "," ^ Term.str_of t2)
             (Set.to_list lb));
    print
    @@ lazy
         ("[mbp lia] rest: " ^ List.to_string ~f:Atom.str_of (Set.to_list rest));
    (* if Set.mem (Set.concat_map ~f:Formula.fvs_of rest) tvar then
       let sub = Map.Poly.singleton tvar (Map.Poly.find_exn model tvar) in
       Set.concat_map atoms ~f:(Atom.subst sub >> Formula.mk_atom)
       else *)
    match (lub model ub, glb model lb) with
    | Some (cub, tub), Some (clb, tlb) ->
        let lbformulas =
          Set.Poly.map lb ~f:(fun (c, t) ->
              T_int.mk_leq
                (T_int.mk_mul t @@ T_int.mk_int clb)
                (T_int.mk_mul tlb @@ T_int.mk_int c))
        in
        let ubformulas =
          Set.concat_map ub ~f:(fun (c, t) -> resolve model c t clb tlb)
        in
        let rest =
          let sub =
            let glb = T_int.mk_div Value.Euclidean tlb @@ T_int.mk_int clb in
            let lub =
              T_int.(mk_add (mk_div Value.Euclidean tub @@ mk_int cub) (one ()))
            in
            Map.Poly.singleton tvar
              T_int.(mk_div Value.Euclidean (mk_add glb lub) (from_int 2))
          in
          if true then rest else Set.Poly.map rest ~f:(Atom.subst sub)
        in
        print
        @@ lazy
             ("[mbp lia] lbformulas: "
             ^ String.concat_map_set ~sep:", " ~f:Atom.str_of lbformulas);
        print
        @@ lazy
             ("[mbp lia] ubformulas: "
             ^ String.concat_map_set ~sep:", " ~f:Atom.str_of ubformulas);
        Set.concat_map ~f:(normalize_mbp model)
        @@ Set.Poly.union_list [ lbformulas; ubformulas; rest ]
    | Some (cub, tub), None ->
        let ubformulas =
          Set.Poly.map ub ~f:(fun (c, t) ->
              T_int.mk_leq
                (T_int.mk_mul tub @@ T_int.mk_int c)
                (T_int.mk_mul t @@ T_int.mk_int cub))
        in
        let rest =
          let sub =
            Map.Poly.singleton tvar
            @@ T_int.mk_div Value.Euclidean tub
            @@ T_int.mk_int cub
          in
          if true then rest else Set.Poly.map rest ~f:(Atom.subst sub)
        in
        Set.concat_map ~f:(normalize_mbp model)
        @@ Set.Poly.union_list [ ubformulas; rest ]
    | None, Some (clb, tlb) ->
        let lbformulas =
          Set.Poly.map lb ~f:(fun (c, t) ->
              T_int.mk_leq
                (T_int.mk_mul t @@ T_int.mk_int clb)
                (T_int.mk_mul tlb @@ T_int.mk_int c))
        in
        let rest =
          let sub =
            Map.Poly.singleton tvar
            @@ T_int.mk_add
                 (T_int.mk_div Value.Euclidean tlb @@ T_int.mk_int clb)
                 (T_int.one ())
          in
          if true then rest else Set.Poly.map rest ~f:(Atom.subst sub)
        in
        Set.concat_map ~f:(normalize_mbp model)
        @@ Set.Poly.union_list [ lbformulas; rest ]
    | None, None ->
        if Set.exists rest ~f:(fun atom -> Set.mem (Atom.fvs_of atom) tvar) then
          raise NotNormalized
          (*failwith @@ "no constraint on " ^ Ident.name_of_tvar tvar*)
        else rest (* reachable here when simplification eliminated tvar *)

  let rec model_based_projection ~print model tvar atoms =
    match Set.find_map atoms ~f:(eq_atom tvar) with
    | Some (c, t, atom) ->
        if Z.Compare.(c = Z.one) then
          let sub = Map.Poly.singleton tvar t in
          Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
        else
          let cx = T_int.(mk_mul (mk_int c) @@ Term.mk_var tvar SInt) in
          model_based_projection ~print model tvar
          @@ Set.union (Set.remove atoms atom)
          @@ Set.concat_map ~f:(normalize_mbp model)
          @@ Set.Poly.of_list [ T_int.mk_geq t cx; T_int.mk_geq cx t ]
    | None ->
        let atoms =
          Set.Poly.map atoms
            ~f:
              ( neq_atom tvar >> function
                | First (c, t) ->
                    let cx =
                      T_int.(mk_mul (mk_int c) @@ Term.mk_var tvar SInt)
                    in
                    Normalizer.normalize_atom
                    @@
                    let lhs = Evaluator.eval_term @@ Term.subst model cx in
                    let rhs = Evaluator.eval_term @@ Term.subst model t in
                    if Value.compare true Z.Compare.( > ) Q.( > ) lhs rhs then
                      T_int.mk_gt cx t
                    else if Value.compare true Z.Compare.( < ) Q.( < ) lhs rhs
                    then T_int.mk_gt t cx
                    else failwith "elim_neq"
                | Second atm -> atm )
        in
        let pdivs, rest = Set.partition_map atoms ~f:(is_pdiv tvar) in
        if Set.is_empty pdivs then
          model_based_projection_aux ~print model tvar rest
        else
          let newmodel, newtvar, newterm, pdivs =
            rm_pdiv ~print pdivs model tvar
          in
          print
          @@ lazy
               (sprintf "[mbp lia] newterm: %s -> %s" (Ident.name_of_tvar tvar)
                  (Term.str_of newterm));
          print
          @@ lazy (sprintf "[mbp lia] newmodel: %s" (TermSubst.str_of newmodel));
          Set.union (Set.concat_map pdivs ~f:(normalize_mbp model))
          @@ model_based_projection ~print newmodel newtvar
          @@
          let sub = Map.Poly.singleton tvar newterm in
          Set.concat_map rest ~f:(Atom.subst sub >> normalize_mbp model)
end

module Boolean = struct
  let let_sort names =
    Map.Poly.fold ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term model ->
        if Set.mem names (Ident.name_of_tvar tvar) then model (*ToDo*)
        else
          let data =
            match Evaluator.eval_term term with
            | Value.Bool b -> T_bool.make b
            | Value.Int _ -> failwith "Boolean: int not supported"
            | Value.Real _ -> failwith "Boolean: real not supported"
            | Value.BV _ -> failwith "Boolean: bitvector not supported"
            | Value.Arr _ -> failwith "Boolean: array not supported"
            | Value.TupleCons _ -> failwith "Boolean: tuple not supported"
            | Value.DTCons _ -> failwith "Boolean: datatype not supported"
          in
          Map.Poly.add_exn model ~key:tvar ~data)

  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Neq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some (Evaluator.simplify_term @@ T_bool.negate t)
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some (Evaluator.simplify_term @@ T_bool.negate t)
    | _ -> None

  let model_based_projection ~print:_ model tvar atoms =
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
