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
                    let tx = Term.mk_var tvar T_real.SReal in
                    Normalizer.normalize_atom
                    @@
                    let lhs =
                      Evaluator.eval_term @@ Map.Poly.find_exn model tvar
                    in
                    let rhs = Evaluator.eval_term @@ Term.subst model t in
                    if Value.gt lhs rhs then T_real.mk_rgt tx t
                    else if Value.lt lhs rhs then T_real.mk_rgt t tx
                    else failwith "elim_neq"
                | Second atm -> atm )
        in
        let ub, lb, rest = ub_and_lb tvar atoms in
        let lub = lub model ub in
        let glb = glb model lb in
        print
        @@ lazy
             (sprintf "[mbp lra] lb: %s"
             @@ String.concat_map_set ~sep:", " lb ~f:(fun (t, eps) ->
                 sprintf "%s %s %s" (Term.str_of t)
                   (if eps then "<" else "<=")
                   (Ident.name_of_tvar tvar)));
        print
        @@ lazy
             (sprintf "[mbp lra] ub: %s"
             @@ String.concat_map_set ~sep:", " ub ~f:(fun (t, eps) ->
                 sprintf "%s %s %s" (Term.str_of t)
                   (if eps then ">" else ">=")
                   (Ident.name_of_tvar tvar)));
        (match glb with
        | None -> ()
        | Some (t, eps) ->
            print
            @@ lazy
                 (sprintf "[mbp lra] glb: %s %s %s" (Term.str_of t)
                    (if eps then "<" else "<=")
                    (Ident.name_of_tvar tvar)));
        (match lub with
        | None -> ()
        | Some (t, eps) ->
            print
            @@ lazy
                 (sprintf "[mbp lra] lub: %s %s %s" (Term.str_of t)
                    (if eps then ">" else ">=")
                    (Ident.name_of_tvar tvar)));
        print
        @@ lazy
             (sprintf "[mbp lra] rest: %s"
             @@ String.concat_map_set ~sep:", " rest ~f:(fun atm ->
                 sprintf "%s" (Atom.str_of atm)));
        match (lub, glb) with
        | Some (lub, _), Some (glb, glb_eps) ->
            Set.Poly.union_list
              [
                (let sub =
                   Map.Poly.singleton tvar
                   @@ T_real.mk_rmul (T_real.mk_radd lub glb)
                        (T_real.mk_real (Q.of_float 0.5))
                 in
                 Set.Poly.map rest ~f:(Atom.subst sub));
                Set.concat_map lb ~f:(fun (t, eps) ->
                    normalize_mbp model
                    @@
                    if Stdlib.(glb_eps = eps) || glb_eps (*ToDo*) then
                      T_real.mk_rgeq glb t
                    else T_real.mk_rgt glb t);
                Set.concat_map ub ~f:(fun (t, eps) ->
                    normalize_mbp model
                    @@
                    if (not glb_eps) && not eps then T_real.mk_rgeq t glb
                    else T_real.mk_rgt t glb);
              ]
        | Some (lub, lub_eps), None ->
            Set.union
              (let sub =
                 Map.Poly.singleton tvar @@ T_real.mk_rsub lub (T_real.rone ())
               in
               Set.Poly.map rest ~f:(Atom.subst sub))
              (Set.concat_map ub ~f:(fun (t, eps) ->
                   normalize_mbp model
                   @@
                   if Stdlib.(lub_eps = eps) || lub_eps (*ToDo*) then
                     T_real.mk_rgeq t lub
                   else T_real.mk_rgt t lub))
        | None, Some (glb, glb_eps) ->
            Set.union
              (let sub =
                 Map.Poly.singleton tvar @@ T_real.mk_radd glb (T_real.rone ())
               in
               Set.Poly.map rest ~f:(Atom.subst sub))
              (Set.concat_map lb ~f:(fun (t, eps) ->
                   normalize_mbp model
                   @@
                   if Stdlib.(glb_eps = eps) || glb_eps (*ToDo*) then
                     T_real.mk_rgeq glb t
                   else T_real.mk_rgt glb t))
        | None, None ->
            let sub = Map.Poly.singleton tvar @@ Term.mk_dummy T_real.SReal in
            Set.Poly.map rest ~f:(Atom.subst sub))
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
          Set.Poly.map rest ~f:(Atom.subst sub)
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
          Set.Poly.map rest ~f:(Atom.subst sub)
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
          Set.Poly.map rest ~f:(Atom.subst sub)
        in
        Set.concat_map ~f:(normalize_mbp model)
        @@ Set.Poly.union_list [ lbformulas; rest ]
    | None, None ->
        let sub = Map.Poly.singleton tvar @@ Term.mk_dummy T_int.SInt in
        Set.Poly.map rest ~f:(Atom.subst sub)

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
                    if Value.gt lhs rhs then T_int.mk_gt cx t
                    else if Value.lt lhs rhs then T_int.mk_gt t cx
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

module ADT = struct
  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | _ -> None

  (* TODO now, only check eq_atom *)
  let model_based_projection ~print:_ model tvar atoms =
    match Set.find_map atoms ~f:(eq_atom tvar) with
    | Some t ->
        let sub = Map.Poly.singleton tvar t in
        Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
    | None -> (
        match Map.Poly.find model tvar with
        | Some value ->
            let sub = Map.Poly.singleton tvar value in
            Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
        | None -> atoms)
end

module SAtom = struct
  type t = Atom.t * Term.t Set.Poly.t

  let get_atom (atom, _) = atom
  let get_set (_, s) = s
  let of_atom ?(s = Set.Poly.empty) atom = (atom, s)
end

module ARR = struct
  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | _ -> None

  let neq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | _ -> None

  let triv_eq satoms =
    let term_equal t1 t2 =
      match (t1, t2) with
      | Term.Var (v1, _, _), Term.Var (v2, _, _) -> Ident.tvar_equal v1 v2
      | _ -> false
      (*TODO Other terms*)
    in

    let is_triv_eq_atom atom =
      match atom with
      | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) ->
          if term_equal t1 t2 then true else false
      | _ -> false
    in
    Set.filter satoms ~f:(fun (atom, _) -> not (is_triv_eq_atom atom))

  let is_store = function
    | Term.FunApp (T_array.AStore _, _, _) -> true
    | _ -> false

  let symm satoms =
    let is_symm_target atom =
      match atom with
      | Atom.App (_, [ t1; t2 ], _) -> (not (is_store t1)) && is_store t2
      | _ -> false
    in

    Set.Poly.map satoms ~f:(fun (atom, set) ->
        if is_symm_target atom then
          match atom with
          | Atom.App (pred, [ t1; t2 ], info) ->
              SAtom.of_atom ~s:set (Atom.App (pred, [ t2; t1 ], info))
          | _ -> SAtom.of_atom ~s:set atom
        else SAtom.of_atom ~s:set atom)

  let rec eval_satom model (atom, set) =
    match atom with
    | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], info) -> (
        match t1 with
        | Term.FunApp (T_array.AStore (idx_s, elem_s), _, _) ->
            let tmp_t1 =
              Set.fold set ~init:t1 ~f:(fun acc i ->
                  T_array.mk_store idx_s elem_s acc i
                    (T_array.mk_select idx_s elem_s t2 i))
            in
            Evaluator.eval_atom
            @@ Atom.subst model
                 (Atom.mk_app (Predicate.Psym T_bool.Eq) [ tmp_t1; t2 ] ~info)
        | _ -> Evaluator.eval_atom @@ Atom.subst model atom)
    | Atom.App (Predicate.Psym T_bool.Neq, args, info) ->
        not
          (eval_satom model
             (Atom.mk_app ~info (Predicate.Psym T_bool.Eq) args, set))
    | Atom.App (_, _, _) -> Evaluator.eval_atom @@ Atom.subst model atom
    | Atom.True _ -> true
    | Atom.False _ -> false

  let mem_by_model model i set =
    let i_v = Evaluator.eval_term @@ Term.subst model i in
    Set.find set ~f:(fun t ->
        Value.eq i_v @@ Evaluator.eval_term @@ Term.subst model t)

  let mbp_disjunction model satom1 satom2 =
    if eval_satom model satom1 then Some satom1
    else if eval_satom model satom2 then Some satom2
    else None

  let rec aux_elim_wr_rd model term =
    match term with
    | Term.FunApp
        ( T_array.ASelect (idx_s, elemm_s),
          [ Term.FunApp (T_array.AStore (_, _), [ t; i; v ], _); j ],
          _ ) ->
        if
          Value.eq
            (Evaluator.eval_term @@ Term.subst model i)
            (Evaluator.eval_term @@ Term.subst model j)
        then
          let extra, new_v = aux_elim_wr_rd model v in
          ( Set.add extra
              (Atom.mk_app (Predicate.Psym T_bool.Eq) [ i; j ], Set.Poly.empty),
            new_v )
        else
          let extra_t, new_t = aux_elim_wr_rd model t in
          let extra_j, new_j = aux_elim_wr_rd model j in
          let extra_t_j = Set.union extra_t extra_j in
          ( Set.add extra_t_j
              (Atom.mk_app (Predicate.Psym T_bool.Neq) [ i; j ], Set.Poly.empty),
            T_array.mk_select idx_s elemm_s new_t new_j )
    | Term.FunApp (fun_sym, args, info) ->
        let extra_atoms, new_args =
          List.fold_map args ~init:Set.Poly.empty ~f:(fun acc arg ->
              let extra, new_arg = aux_elim_wr_rd model arg in
              (Set.union acc extra, new_arg))
        in
        (extra_atoms, Term.mk_fsym_app fun_sym new_args ~info)
    | Term.LetTerm (tvar, sort, t1, t2, info) ->
        let extra1, new_t1 = aux_elim_wr_rd model t1 in
        let extra2, new_t2 = aux_elim_wr_rd model t2 in
        (Set.union extra1 extra2, Term.mk_let_term tvar sort new_t1 new_t2 ~info)
    | _ -> (Set.Poly.empty, term)

  let elim_wr_rd model satoms =
    Set.concat_map satoms ~f:(fun (atom, set) ->
        match atom with
        | Atom.App (pred, args, info) ->
            let extra_atoms, new_args =
              List.fold_map args ~init:Set.Poly.empty ~f:(fun acc arg ->
                  let extra, new_arg = aux_elim_wr_rd model arg in
                  (Set.union acc extra, new_arg))
            in
            Set.add extra_atoms (Atom.mk_app pred new_args ~info, set)
        | _ -> Set.Poly.singleton (atom, set))

  let elim_wr_eq_satom model (atom, set) =
    match atom with
    | Atom.App (_, args, info) -> (
        match args with
        | [ wrt; t2 ] -> (
            match wrt with
            | Term.FunApp (T_array.AStore (idx_s, val_s), [ t1; j; v ], _) -> (
                match mem_by_model model j set with
                | Some t ->
                    let eq1 =
                      let atm1 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Eq) [ t1; t2 ]
                      in
                      SAtom.of_atom ~s:set atm1
                    in
                    let eq2 =
                      let atm2 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Eq) [ j; t ]
                      in
                      SAtom.of_atom atm2
                    in
                    Set.Poly.of_list [ eq1; eq2 ]
                | None ->
                    let eq1 =
                      let atm1 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Eq) [ t1; t2 ]
                      in
                      let set1 = Set.add set j in
                      SAtom.of_atom ~s:set1 atm1
                    in
                    let eq2 =
                      let rdt = T_array.mk_select idx_s val_s t2 j in
                      let atm2 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Eq) [ v; rdt ]
                      in
                      SAtom.of_atom atm2
                    in
                    let neq_set =
                      Set.Poly.map set ~f:(fun t ->
                          ( Atom.mk_app ~info (Predicate.Psym T_bool.Neq)
                              [ j; t ],
                            Set.Poly.empty ))
                    in
                    Set.union neq_set (Set.Poly.of_list [ eq1; eq2 ]))
            | _ -> failwith "elim_wr_eq: not a write term")
        | _ -> failwith "elim_wr_eq: not a binary predicate")
    | _ -> failwith "elim_wr_eq: not apply"

  let elim_wr_eq model satoms =
    Set.concat_map satoms ~f:(fun satom ->
        let atom = SAtom.get_atom satom in
        match atom with
        | Atom.App (Predicate.Psym T_bool.Eq, [ t1; _ ], _) when is_store t1 ->
            elim_wr_eq_satom model satom
        | _ -> Set.Poly.singleton satom)

  let elim_wr_neq_satom model (atom, set) =
    match atom with
    | Atom.App (_, args, info) -> (
        match args with
        | [ wrt; t2 ] -> (
            match wrt with
            | Term.FunApp (T_array.AStore (idx_s, elem_s), [ t1; j; v ], _) -> (
                match mem_by_model model j set with
                | Some t ->
                    let neq =
                      let atm1 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Neq) [ t1; t2 ]
                      in
                      SAtom.of_atom ~s:set atm1
                    in
                    let eq =
                      let atm2 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Eq) [ j; t ]
                      in
                      SAtom.of_atom atm2
                    in
                    Set.Poly.of_list [ neq; eq ]
                | None -> (
                    let neq1 =
                      let atm1 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Neq) [ t1; t2 ]
                      in
                      let set1 = Set.add set j in
                      SAtom.of_atom ~s:set1 atm1
                    in
                    let neq2 =
                      let rdt = T_array.mk_select idx_s elem_s t2 j in
                      let atm2 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Neq) [ v; rdt ]
                      in
                      SAtom.of_atom atm2
                    in
                    let neq_set =
                      Set.Poly.map set ~f:(fun t ->
                          ( Atom.mk_app ~info (Predicate.Psym T_bool.Neq)
                              [ j; t ],
                            Set.Poly.empty ))
                    in
                    match mbp_disjunction model neq1 neq2 with
                    | Some atm -> Set.add neq_set atm
                    | None ->
                        Set.Poly.singleton (Atom.mk_false (), Set.Poly.empty)))
            | _ -> failwith "elim_wr_neq: not a write term")
        | _ -> failwith "elim_wr_neq: not a binary predicate")
    | _ -> failwith "elim_wr_neq: not apply"

  let elim_wr_neq model satoms =
    Set.concat_map satoms ~f:(fun satom ->
        let atom = SAtom.get_atom satom in
        match atom with
        | Atom.App (Predicate.Psym T_bool.Neq, [ t1; _ ], _) when is_store t1 ->
            elim_wr_neq_satom model satom
        | _ -> Set.Poly.singleton satom)

  let rec aux_elim_write model satoms =
    let rec exist_write_term = function
      | Term.FunApp (T_array.AStore (_, _), _, _) -> true
      | Term.FunApp (T_array.ASelect (_, _), [ arr; ind ], _) ->
          exist_write_term arr || exist_write_term ind
      | Term.FunApp (T_array.AConst (_, _), [ value ], _) ->
          exist_write_term value
      | _ -> false
    in

    let exist_write =
      Set.exists satoms ~f:(fun (atm, _) ->
          match atm with
          | Atom.App (_, args, _) -> List.exists args ~f:exist_write_term
          | _ -> false)
    in

    if exist_write then
      satoms |> symm |> triv_eq |> elim_wr_rd model |> elim_wr_eq model
      |> elim_wr_neq model |> aux_elim_write model
    else satoms

  let elim_write model satoms = aux_elim_write model satoms |> triv_eq

  let rec aux_factor_out model tvar term =
    match term with
    | Term.FunApp (T_array.ASelect (idx_s, elemm_s), [ t1; t2 ], _) -> (
        let extra2, new_t2 = aux_factor_out model tvar t2 in
        match t1 with
        | Term.Var (x, sort, info) when Ident.tvar_equal tvar x ->
            let s = Term.mk_fresh_var elemm_s in
            let new_read =
              T_array.mk_select idx_s elemm_s
                (Term.mk_var tvar sort ~info)
                new_t2
            in
            ( Set.Poly.singleton
                ( Atom.mk_app (Predicate.Psym T_bool.Eq) [ s; new_read ],
                  Set.Poly.empty ),
              s )
        | _ ->
            let extra1, new_t1 = aux_factor_out model tvar t1 in
            ( Set.union extra1 extra2,
              T_array.mk_select idx_s elemm_s new_t1 new_t2 ))
    | Term.FunApp (fun_sym, args, info) ->
        let extra_satoms, new_args =
          List.fold args ~init:(Set.Poly.empty, [])
            ~f:(fun (acc_atoms, acc_args) arg ->
              let atom, new_arg = aux_factor_out model tvar arg in
              (Set.union acc_atoms atom, new_arg :: acc_args))
          |> fun (res_atoms, res_args) -> (res_atoms, List.rev res_args)
        in
        (extra_satoms, Term.mk_fsym_app ~info fun_sym new_args)
    | Term.LetTerm (tvar, sort, t1, t2, info) ->
        let extra1, new_t1 = aux_factor_out model tvar t1 in
        let extra2, new_t2 = aux_factor_out model tvar t2 in
        (Set.union extra1 extra2, Term.mk_let_term ~info tvar sort new_t1 new_t2)
    | _ -> (Set.Poly.empty, term)

  let factor_out model tvar satoms =
    (*CaseSplitEq*)
    (* We don't have to implement since in this point, we think only atomic formulas*)
    (*FactorRd*)
    Set.concat_map satoms ~f:(fun (atom, set) ->
        match atom with
        | Atom.App (pred, args, info) ->
            let extra_satoms, new_args =
              List.fold args ~init:(Set.Poly.empty, [])
                ~f:(fun (acc_atoms, acc_args) arg ->
                  let atom, new_arg = aux_factor_out model tvar arg in
                  (Set.union acc_atoms atom, new_arg :: acc_args))
              |> fun (res_atoms, res_args) -> (res_atoms, List.rev res_args)
            in
            Set.add extra_satoms (Atom.mk_app pred new_args ~info, set)
        | _ -> Set.Poly.singleton (atom, set))

  let elim_eq _model tvar satoms =
    match
      Set.find_map satoms ~f:(fun (atom, set) ->
          match eq_atom tvar atom with Some t -> Some (t, set) | None -> None)
    with
    | Some (t, set) -> (
        match Term.sort_of t with
        | T_array.SArray (idx_s, elem_s) ->
            let updated_t =
              Set.fold set ~init:t ~f:(fun acc i ->
                  let fresh_var = Term.mk_fresh_var elem_s in
                  T_array.mk_store idx_s elem_s acc i fresh_var)
            in
            let sub = Map.Poly.singleton tvar updated_t in
            Some
              (Set.Poly.map satoms ~f:(fun (atom, set) ->
                   (Atom.subst sub atom, set)))
        | _ -> failwith "elim_eq: tvar not array")
    | None -> None

  let elim_neq _model tvar satoms =
    Set.filter satoms ~f:(fun (atom, _) ->
        match neq_atom tvar atom with Some _ -> false | None -> true)

  let ackermann model tvar satoms =
    let reads, other_satoms =
      Set.fold satoms ~init:([], Set.Poly.empty)
        ~f:(fun (pairs, others) (atom, set) ->
          match atom with
          | Atom.App
              ( Predicate.Psym T_bool.Eq,
                [
                  s;
                  Term.FunApp
                    (T_array.ASelect (_, _), [ Term.Var (a, _, _); t ], _);
                ],
                _ )
          | Atom.App
              ( Predicate.Psym T_bool.Eq,
                [
                  Term.FunApp
                    (T_array.ASelect (_, _), [ Term.Var (a, _, _); t ], _);
                  s;
                ],
                _ ) ->
              if Ident.tvar_equal a tvar then ((t, s) :: pairs, others)
              else (pairs, Set.add others (atom, set))
          | _ -> (pairs, Set.add others (atom, set)))
    in
    let reads_with_values =
      List.map reads ~f:(fun (t, s) ->
          let v = Evaluator.eval_term (Term.subst model t) in
          (v, (t, s)))
    in

    let sorted_reads =
      List.sort reads_with_values ~compare:(fun (v1, _) (v2, _) ->
          if Value.eq v1 v2 then 0 else if Value.geq v1 v2 then 1 else -1)
    in
    let groups =
      List.group sorted_reads ~break:(fun (v1, _) (v2, _) -> Value.neq v1 v2)
    in

    let equivalence_class_atoms =
      Set.Poly.of_list
      @@ List.concat_map groups ~f:(fun group ->
          match List.map group ~f:snd with
          | (t_rep, s_rep) :: others ->
              List.concat_map others ~f:(fun (t_nrep, s_nrep) ->
                  [
                    ( Atom.mk_app (Predicate.Psym T_bool.Eq) [ t_rep; t_nrep ],
                      Set.Poly.empty );
                    ( Atom.mk_app (Predicate.Psym T_bool.Eq) [ s_rep; s_nrep ],
                      Set.Poly.empty );
                  ])
          | _ -> [])
    in

    let representatives =
      List.filter_map groups ~f:(fun group ->
          Option.map (List.hd group) ~f:(fun (_, ts) -> ts))
    in

    let rec inter_constraints = function
      | (t1, _) :: (t2, s2) :: rest ->
          (Atom.mk_app (Predicate.Psym T_int.Lt) [ t1; t2 ], Set.Poly.empty)
          :: inter_constraints ((t2, s2) :: rest)
      | _ -> []
    in

    let inter_atoms = Set.Poly.of_list @@ inter_constraints representatives in

    Set.Poly.union_list [ other_satoms; equivalence_class_atoms; inter_atoms ]

  let target_var_elim model tvar satoms =
    match elim_eq model tvar satoms with
    | Some satoms -> satoms
    | None -> satoms |> elim_neq model tvar |> ackermann model tvar

  let diseq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | _ -> None

  let model_based_projection ~print:_ model tvar atoms =
    (*
    let () =
      Stdlib.print_endline "--------------------------------------------------";
      Stdlib.print_endline ("::: [Array MBP] Target TVar (x): " ^ Ident.name_of_tvar tvar);
      let model_str = String.concat_map_list ~sep:", " (Map.Poly.to_alist model)
          ~f:(fun (Ident.Tvar v, value) -> Printf.sprintf "%s |-> %s" v (Term.str_of value)) in
      Stdlib.print_endline ("::: [Array MBP] Full Model: [" ^ model_str ^ "]");
      let atoms_str = String.concat ~sep:", " (List.map (Set.to_list atoms) ~f:Atom.str_of) in
      Stdlib.print_endline ("::: [Array MBP] Atoms: {" ^ atoms_str ^ "}");
      Stdlib.print_endline "--------------------------------------------------";
      Stdlib.flush Stdlib.stdout
    in
    *)
    match Set.find_map atoms ~f:(eq_atom tvar) with
    | Some t ->
        let sub = Map.Poly.singleton tvar t in
        Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
    | None ->
        (*TODO: Implement for constant arrays*)
        (*In the current implementation, if a constant is present, *)
        (*we give up on model-based projection and directly substitute.*)
        (*Warning: Inparticular, the situation changes if there is a constant around NEQ*)
        let rec contains_aconst t =
          match t with
          | Term.Var (_, _, _) -> false
          | Term.FunApp (sym, args, _) -> (
              match sym with
              | T_array.AConst (_, _) -> true
              | _ -> List.exists ~f:contains_aconst args)
          | Term.LetTerm (_, _, t1, t2, _) ->
              contains_aconst t1 || contains_aconst t2
        in

        if
          Set.exists atoms ~f:(fun atom ->
              match atom with
              | Atom.App (_, [ t1; t2 ], _) ->
                  contains_aconst t1 || contains_aconst t2
              | _ -> false)
        then
          match Map.Poly.find model tvar with
          | Some value ->
              let sub = Map.Poly.singleton tvar value in
              Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
          | None -> atoms
        else
          (*Equality with Sets*)
          let satoms = Set.Poly.map atoms ~f:(fun atom -> SAtom.of_atom atom) in
          (*
        let() =
          Stdlib.print_endline "--------------------------------------------------";
          let atoms = Set.Poly.map(satoms) ~f: (fun (atom, _) -> atom) in
          let atoms_str = String.concat ~sep:", " (List.map (Set.to_list atoms) ~f:Atom.str_of) in
          Stdlib.print_endline ("::: [Start Atoms] Atoms: {" ^ atoms_str ^ "}");
          Stdlib.flush Stdlib.stdout
        in
        *)

          (*Elim Write*)
          let elim_write_atoms = elim_write model satoms in
          (*
        let() =
          let atoms = Set.Poly.map(elim_write_atoms) ~f: (fun (atom, _) -> atom) in
          let atoms_str = String.concat ~sep:", " (List.map (Set.to_list atoms) ~f:Atom.str_of) in
          Stdlib.print_endline ("::: [Elim Write] Atoms: {" ^ atoms_str ^ "}");
          Stdlib.flush Stdlib.stdout
        in
        *)

          (*Factor out qualities and read terms*)
          let factor_out_atoms = factor_out model tvar elim_write_atoms in

          (*LiftEqDiseqRd*)
          (*We don't have to implement since we think formulas as a set of atomic formulas*)

          (*Target Variables Elimination*)
          let target_var_elim_atoms =
            target_var_elim model tvar factor_out_atoms
          in
          (*
        let() =
          let atoms = Set.Poly.map(target_var_elim_atoms) ~f: (fun (atom, _) -> atom) in
          let atoms_str = String.concat ~sep:", " (List.map (Set.to_list atoms) ~f:Atom.str_of) in
          Stdlib.print_endline ("::: [Target Variables Elimination] Atoms: {" ^ atoms_str ^ "}");
          Stdlib.flush Stdlib.stdout
        in
        *)

          (*Output*)
          let out_atoms =
            Set.concat_map target_var_elim_atoms ~f:(fun (atom, set) ->
                let updated_atom =
                  if Set.is_empty set then atom
                  else
                    match atom with
                    | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], info) -> (
                        match t1 with
                        | Term.FunApp (T_array.AStore (idx_s, elem_s), _, _) ->
                            let new_t1 =
                              Set.fold set ~init:t1 ~f:(fun acc i ->
                                  let v = T_array.mk_select idx_s elem_s t2 i in
                                  T_array.mk_store idx_s elem_s acc i v)
                            in
                            Atom.mk_app (Predicate.Psym T_bool.Eq)
                              [ new_t1; t2 ] ~info
                        | _ -> atom)
                    | _ -> atom
                in
                normalize_mbp model updated_atom)
          in
          (*
        let() =
          let atoms_str = String.concat ~sep:", " (List.map (Set.to_list out_atoms) ~f:Atom.str_of) in
          Stdlib.print_endline ("::: [Output] Atoms: {" ^ atoms_str ^ "}");
          Stdlib.print_endline "--------------------------------------------------";
          Stdlib.flush Stdlib.stdout
        in
        *)
          out_atoms
end
