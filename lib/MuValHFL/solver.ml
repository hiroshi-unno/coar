(* MuValHFL: HFL(Z) validity checking by refinement typing.

   Reads an HES ([.in], [.hfl], in the configured dialect) or an OCaml file in
   RCaml's Boolean HFL mode, and answers one line, [valid], [invalid] or
   [unknown], followed by the iterations of the solver that decided it.

   Refused by name on the route through RCaml (an [Or_error], never an
   answer): an alternating HES (one
   lambda-HFL model has one fixpoint kind); an existential quantifier in a
   greatest-fixpoint equation or a universal one in a least-fixpoint equation
   (not continuous in that order: the typing rule for fixed points reasons
   about the Kleene limit, which can then differ from the fixed point); a main
   equation with a non-integer parameter.

   Answers, and why each is sound:
   - an order-1 HES goes to MuVal when [order1_backend] names a
     configuration, and MuVal's answer is passed on (the HES is the muCLP);
   - otherwise a greatest-fixpoint HES is translated to OCaml and RCaml types
     the main equation as [{ v : prop | v }] in the Boolean mode, whose
     admissible refinements make a typing a proof of validity: [sat] answers
     [valid].  A least-fixpoint HES is dualised first (its dual is a
     greatest-fixpoint HES that is valid exactly when it is not), and a typing
     of the dual answers [invalid];
   - any other RCaml outcome answers [unknown]: an untypable formula is not
     thereby refuted, because the type system is incomplete;
   - with [refute_by_unfolding], an [unknown] greatest-fixpoint HES is
     unfolded k times for k = 1 .. [unfolding_depth], every equation's k-th
     approximant from above replacing it (each starts from [true]); the main
     formula's approximant is first-order after beta-reduction, and if it is
     quantifier-free and not valid for some value of the main equation's
     parameters, neither is the formula ([invalid]), since a greatest fixed
     point lies below each of its approximants from above.  For a
     least-fixpoint HES the same refutation of its dual answers [valid]. *)

open Core
open Common
open HFL
open HflSyntax

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_module_name "MuValHFL"

  let refused fmt = ksprintf (fun s -> Or_error.error_string ("refused: " ^ s)) fmt

  let read filename =
    match snd (Filename.split_extension filename) with
    | Some "ml" -> (
        try Ok (HflOfOCaml.from_file filename)
        with HflOfOCaml.Refused msg -> refused "%s" msg)
    | _ -> (
        match dialect_of_string config.dialect with
        | None -> Or_error.errorf "unknown HFL dialect %S" config.dialect
        | Some dialect -> (
            try Ok (HflReader.from_file ~dialect filename)
            with HflReader.Refused msg -> refused "%s" msg))

  let check_solvable hes =
    if is_alternating hes then
      refused
        "an alternating HES (greatest and least fixed points together) is \
         not supported"
    else
      match discontinuous_quantifier hes with
      | Some (name, q, fix) ->
          refused
            "%s inside the %s fixed point %s (not continuous in that order; \
             no sound typing rule is known)"
            q
            (match fix with Nu -> "greatest" | Mu -> "least")
            name
      | None -> (
          match hes.eqns with
          | main :: _
            when List.for_all main.params ~f:(fun (_, ty) ->
                     match ty with Some TInt -> true | _ -> false) ->
              Ok ()
          | _ -> refused "the main equation has a non-integer parameter")

  (* [valid] answers by typing a greatest-fixpoint HES *)
  let type_nu ~filename nu_hes =
    let text = HflToOCaml.print nu_hes in
    Debug.print @@ lazy ("[MuValHFL] the OCaml representation:\n" ^ text);
    (* made here, not at functor application: the MuVal-only use of this
       module has no instantiated RCaml configuration *)
    let module RCamlSolver = RCaml.Solver.Make (struct
      let config = config.rcaml
    end) in
    match RCamlSolver.solutions_of_ml_string ~filename text with
    | Error e ->
        Debug.print @@ lazy ("[MuValHFL] RCaml: " ^ Error.to_string_hum e);
        Error e
    | Ok sols -> (
        let asserts =
          List.filter_map sols ~f:(function
            | RCaml.Problem.AssertSol (_, sol, iter) -> Some (sol, iter)
            | RCaml.Problem.OptimizeSol _ -> None)
        in
        match asserts with
        | [ (PCSP.Problem.Sat _, iter) ] -> Ok (true, iter)
        | [ (_, iter) ] -> Ok (false, iter)
        | _ -> Or_error.error_string "the OCaml representation has no single assertion")

  (* The k-th approximant from above of every equation of a greatest-fixpoint
     HES, applied to the main equation's parameters and beta-reduced. *)
  let approximant hes k =
    let lam e body =
      List.fold_right e.params ~init:body ~f:(fun (x, ty) b -> Abs (x, ty, b))
    in
    let top e = lam e (Bool true) in
    let rec level k =
      if k = 0 then List.map hes.eqns ~f:(fun e -> (e.name, top e))
      else
        let prev = level (k - 1) in
        List.map hes.eqns ~f:(fun e ->
            ( e.name,
              lam e
                (List.fold prev ~init:e.body ~f:(fun b (x, s) -> subst x s b))
            ))
    in
    let defs = level k in
    let main = List.hd_exn hes.eqns in
    beta
      (apps
         (List.Assoc.find_exn defs main.name ~equal:String.equal)
         (List.map main.params ~f:(fun (x, _) -> Var x)))

  let rec quantifier_free = function
    | Forall _ | Exists _ | Abs _ | App _ -> false
    | Var _ | Int _ | Bool _ -> true
    | Neg a -> quantifier_free a
    | Op (_, a, b) | Pred (_, a, b) | And (a, b) | Or (a, b) ->
        quantifier_free a && quantifier_free b

  (* [true] when some unfolding is shown not valid *)
  let refute_nu nu_hes =
    let main = List.hd_exn nu_hes.eqns in
    let rec go k =
      if k > config.unfolding_depth then false
      else
        (* a leading universal quantifier is the same question with its
           variable free (validity is the universal closure), unless the
           variable is a parameter's name, which would merge the two *)
        let rec strip = function
          | Forall (x, a)
            when not (List.Assoc.mem main.params x ~equal:String.equal) ->
              strip a
          | t -> t
        in
        let phi = strip (approximant nu_hes k) in
        if not (quantifier_free phi) then false
        else
          let fvs =
            List.dedup_and_sort ~compare:String.compare
              (free_vars String.Set.empty phi)
          in
          let fml =
            HflToMuCLP.formula_of ~arity:(fun _ -> None) phi |> fun body ->
            match fvs with
            | [] -> body
            | xs ->
                Ast.LogicOld.Formula.mk_forall
                  (List.map xs ~f:(fun x ->
                       (Ast.Ident.Tvar x, Ast.LogicOld.T_int.SInt)))
                  body
          in
          match
            Z3Smt.Z3interface.decide_valid ~id:None (Ast.LogicOld.get_fenv ())
              fml
          with
          | `Invalid ->
              Debug.print
              @@ lazy (sprintf "[MuValHFL] unfolding %d is not valid" k);
              true
          | _ -> go (k + 1)
    in
    go 1

  let answer ~filename hes =
    let open Or_error.Monad_infix in
    let to_muval =
      match config.order1_backend with
      | Some (Util.ExtFile.Instance cfg) when is_order1 hes -> Some cfg
      | _ -> None
    in
    match to_muval with
    | Some cfg ->
        (* MuVal decides a muCLP with both fixpoint kinds and quantifiers
           anywhere, so neither alternation nor a quantifier is refused on
           this route *)
        let muclp = HflToMuCLP.to_problem hes in
        let module MuValSolver = MuVal.Solver.Make (struct
          let config = cfg
        end) in
        MuValSolver.solve ~print_sol:false muclp >>| fun (sol, str_info, _) ->
        (sol, str_info)
    | None ->
        check_solvable hes >>= fun () ->
        let kind = match fix_kinds hes with [ k ] -> k | _ -> Nu in
        let nu_hes = match kind with Nu -> hes | Mu -> dual_hes hes in
        let flip v = match kind with Nu -> v | Mu -> Verdict.flip v in
        type_nu ~filename nu_hes >>| fun (typed, iter) ->
        let iter = Int.to_string iter in
        if typed then (flip Verdict.Valid, iter)
        else if config.refute_by_unfolding && refute_nu nu_hes then
          (flip Verdict.Invalid, iter)
        else (Verdict.Unknown, iter)

  (* MuVal's reading of an HES: an order-1 HES is a muCLP, any other is
     refused by name *)
  let solve_order1_from_file filename =
    let open Or_error.Monad_infix in
    read filename >>= fun hes ->
    if not (is_order1 hes) then
      refused
        "MuVal reads an HES only at order 1 (as a muCLP); this one has order \
         %d.  Use MuValHFL."
        (order hes)
    else answer ~filename hes >>| fun (verdict, iter) ->
    print_endline (sprintf "%s,%s" (Verdict.str_of verdict) iter)

  let solve_from_file filename =
    let open Or_error.Monad_infix in
    read filename >>= fun hes ->
    answer ~filename hes >>| fun (verdict, iter) ->
    print_endline (sprintf "%s,%s" (Verdict.str_of verdict) iter)
end
