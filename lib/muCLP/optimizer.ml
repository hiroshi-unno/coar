open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld

module Config = struct
  type t = { enable : bool; erase_quantifiers : bool; verbose : bool }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid Optimizer Configuration (%s): %s" filename msg)
end

module type OptimizerType = sig
  val f :
    ?id:int option ->
    ?elim_forall:bool ->
    ?elim_exists:bool ->
    ?elim_pvar_args:bool ->
    Problem.t ->
    Problem.t
end

module Make (Config : Config.ConfigType) = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  module EraseUnreachedPredicates : sig
    val optimize : Problem.t -> Problem.t
  end = struct
    (* 0: query, n: n-th pvar from toplevel *)
    let pvargraph_of_muclp muclp =
      let pvar_to_id = Hashtbl.Poly.create ~size:1234 () in
      (* initialize pvar_to_id *)
      List.iteri muclp.Problem.preds ~f:(fun i pred ->
          if false then
            Debug.print @@ lazy ("adding: " ^ Ident.name_of_pvar @@ pred.name);
          Hashtbl.Poly.set pvar_to_id ~key:pred.name ~data:(i + 1));
      muclp.Problem.query
      :: List.map ~f:(fun pred -> pred.body) muclp.Problem.preds
      |> List.map
           ~f:
             (Formula.pvs_of
             >> Set.Poly.map ~f:(fun pvar ->
                    try Hashtbl.Poly.find_exn pvar_to_id pvar
                    with _ ->
                      failwith @@ "not found: " ^ Ident.name_of_pvar pvar)
             >> Set.to_list)
      |> Array.of_list

    let reachable_from starting_node_id graph =
      let res = Array.init (Array.length graph) ~f:(fun _ -> false) in
      let queue = Queue.create () in
      res.(starting_node_id) <- true;
      Queue.enqueue queue starting_node_id;
      while Fn.non Queue.is_empty queue do
        let node_id = Queue.dequeue_exn queue in
        List.iter graph.(node_id) ~f:(fun nxt_node_id ->
            if not res.(nxt_node_id) then (
              res.(nxt_node_id) <- true;
              Queue.enqueue queue nxt_node_id))
      done;
      res

    let optimize muclp =
      let reachable =
        Array.to_list @@ reachable_from 0 @@ pvargraph_of_muclp muclp
      in
      let preds =
        List.zip_exn muclp.Problem.preds (List.tl_exn reachable)
        |> List.filter_map ~f:(fun (p, r) -> if r then Some p else None)
      in
      Problem.make preds muclp.Problem.query
  end

  (* inline extension

     if a predicate P1 is called from only one predicate P2
     and depth(P1) > depth(P2)
     then P1 is eliminated by inline extension *)
  module InlineExtension : sig
    val optimize : Problem.t -> Problem.t
  end = struct
    (* let update_called_counts_in_fml called_counts fml =
       if Formula.is_atom fml then
       let atom, _ = Formula.let_atom fml in
       update_called_counts_in_atom called_counts atom
       else if Formula.is_unop fml then
       let _, fml, _ = Formula.let_unop fml in
       update_called_counts_in_fml called_counts fml
       else if Formula.is_binop fml then
       let _, fml1, fml2, _ = Formula.let_binop fml in
       update_called_counts_in_fml called_counts fml1;
       update_called_counts_in_fml called_counts fml2
       else if Formula.is_bind fml then
       let _, fml, _ = Formula.let_bind fml in
       update_called_counts_in_fml called_counts fml
       else
       failwith @@ sprintf "InlineExtension.update_called_counts_in_fml: not implemented for: %s" (Convert.PrinterHum.str_of_formula fml) *)
    let get_pvar_called_counts pvar_to_id preds query =
      let res = Array.init (List.length preds) ~f:(fun _ -> 0) in
      List.iter
        (query :: List.map preds ~f:(fun pred -> pred.Pred.body))
        ~f:
          (Formula.iter_atom ~f:(function
            | Atom.App (Predicate.Var (pvar, _), _, _) ->
                let pvar_id = pvar_to_id pvar in
                res.(pvar_id) <- res.(pvar_id) + 1
            | _ -> ()));
      res

    let optimize muclp =
      let n = List.length muclp.Problem.preds in
      (* pvar -> depth *)
      let pvar_to_id = Hashtbl.Poly.find_exn @@ Problem.get_depth_ht muclp in
      let called_counts =
        get_pvar_called_counts pvar_to_id muclp.Problem.preds
          muclp.Problem.query
      in
      let expanded = Array.init n ~f:(fun _ -> false) in
      let preds = Array.of_list muclp.Problem.preds in
      List.iteri (List.rev muclp.Problem.preds) ~f:(fun i pred ->
          let pred_id = n - i - 1 in
          let body =
            Formula.map_atom pred.Pred.body ~f:(function
              | Atom.App (Predicate.Var (pvar, _), args, _) as atm ->
                  let pred_id' = pvar_to_id pvar in
                  if called_counts.(pred_id') = 1 && pred_id' > pred_id then (
                    expanded.(pred_id') <- true;
                    assert (Stdlib.(pvar = preds.(pred_id').name));
                    let tsub =
                      Map.Poly.of_alist_exn
                      @@ List.zip_exn
                           (List.map ~f:fst preds.(pred_id').args)
                           args
                    in
                    Formula.subst tsub
                    @@ (* avoid variable capture *)
                    Formula.aconv_tvar preds.(pred_id').body)
                  else Formula.mk_atom atm
              | atm -> Formula.mk_atom atm)
          in
          preds.(pred_id) <- { pred with body });
      let preds =
        List.filter (Array.to_list preds) ~f:(fun pred ->
            not expanded.(pvar_to_id pred.Pred.name))
      in
      Problem.make preds muclp.Problem.query
  end

  module EraseQuantifiers : sig
    val optimize :
      ?elim_forall:bool -> ?elim_exists:bool -> Problem.t -> Problem.t
  end = struct
    let seed = 1007

    (* AV(a+1) = {a}
       AV(a*2) = {}
       AV(a + a + b) = {b}
       AV(a + b + c) = {a, b, c}
       AV(1) = {} *)
    let rec adj_vars_of_term = function
      | Term.Var (tvar, _, _) ->
          (* AV(a) = {a} *)
          Set.Poly.singleton tvar
      | FunApp ((T_int.Add | T_int.Sub), [ a; b ], _) ->
          (* AV(a + b) = AV(a - b) = AV(a) + AV(b) - (AV(a) and AV(b))
             AV(a * b) = AV(a / b) = AV(a % b) = {}
             AV(-a) = AV(a) *)
          let av1 = adj_vars_of_term a in
          let av2 = adj_vars_of_term b in
          Set.diff (Set.union av1 av2) (Set.inter av1 av2)
      | FunApp ((T_int.Mul | T_int.Div _ | T_int.Rem _), [ _; _ ], _)
      | FunApp
          ( ( T_int.Int _
            | T_bool.Formula (Formula.Atom (Atom.(True _ | False _), _)) ),
            [],
            _ ) ->
          Set.Poly.empty
      | FunApp (T_int.Neg, [ a ], _) -> adj_vars_of_term a
      | term ->
          if true then (*ToDo*) Set.Poly.empty
          else failwith @@ sprintf "unknown operation: %s" (Term.str_of term)

    let check_separatable avfvs =
      let avfvs = Array.of_list avfvs in
      (* multiset of fv1 U fv2 U ... U fvN *)
      let fv_count : (Ident.tvar, int) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      (* x in fv1 iff 1 in indexes_of_ftv[x] *)
      let indexes_of_ftv : (Ident.tvar, int list) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      Array.iteri avfvs ~f:(fun idx ->
          snd >> Set.to_list
          >> List.iter ~f:(fun tvar ->
                 let current_count =
                   match Hashtbl.Poly.find fv_count tvar with
                   | None -> 0
                   | Some x -> x
                 in
                 Hashtbl.Poly.set fv_count ~key:tvar ~data:(current_count + 1);
                 Hashtbl.Poly.add_multi indexes_of_ftv ~key:tvar ~data:idx));
      let tvars = Hashtbl.Poly.keys fv_count in
      let is_assigned = Array.init (Array.length avfvs) ~f:(fun _ -> false) in
      let queue = Queue.create () in
      List.iter tvars ~f:(fun tvar ->
          if Hashtbl.Poly.find_exn fv_count tvar = 1 then
            Queue.enqueue queue tvar);
      while Fn.non Queue.is_empty queue do
        let tvar = Queue.dequeue_exn queue in
        if Hashtbl.Poly.find_exn fv_count tvar = 1 then
          Hashtbl.find_multi indexes_of_ftv tvar
          |> List.iter ~f:(fun idx ->
                 if (not is_assigned.(idx)) && Set.mem (fst avfvs.(idx)) tvar
                 then (
                   is_assigned.(idx) <- true;
                   Set.iter
                     (snd avfvs.(idx))
                     ~f:(fun tvar' ->
                       let nxt_count =
                         Hashtbl.Poly.find_exn fv_count tvar' - 1
                       in
                       Hashtbl.Poly.set fv_count ~key:tvar' ~data:nxt_count;
                       if nxt_count = 1 then Queue.enqueue queue tvar')))
      done;
      Array.for_all ~f:Fn.id is_assigned

    let str_of_tvarset s =
      sprintf "{%s}" @@ String.concat_map_set s ~sep:", " ~f:Ident.name_of_tvar

    let bound_flags_of_app_opt bounds args =
      (* let args = List.map Term.simplify args in *)
      let bounds = Set.Poly.of_list @@ List.map ~f:fst bounds in
      let avs = List.map args ~f:(adj_vars_of_term >> Set.inter bounds) in
      let fvs = List.map args ~f:(Term.tvs_of >> Set.inter bounds) in
      let avfvs = List.zip_exn avs fvs in
      if false then
        printf "[%s]: %s\n"
          (String.concat_map_list ~sep:"; " ~f:Term.str_of args)
          (String.concat_map_list ~sep:" "
             ~f:(fun (av, fv) ->
               String.paren
               @@ sprintf "%s, %s" (str_of_tvarset av) (str_of_tvarset fv))
             avfvs);
      if
        List.exists avfvs ~f:(fun (av, fv) ->
            Fn.non Set.is_empty fv && Set.is_empty av)
      then
        (* if FV(t) and bounds != {} /\ AV(t) and bounds = {} for some arg t *)
        None
      else if
        check_separatable (List.filter avfvs ~f:(snd >> Fn.non Set.is_empty))
      then
        (* exists x, y. F x (x + y) -> exists x, y. F x y
           exists x, y. F (x + y) (x + y) -> exists x, y. F (x + y) (x + y) *)
        Some (List.map avs ~f:(Fn.non Set.is_empty))
      else None

    let create_initial_pvar_to_xpvar bounds pvar =
      let res = Hashtbl.Poly.create ~size:seed () in
      Hashtbl.Poly.set res ~key:(List.map ~f:(fun _ -> false) bounds) ~data:pvar;
      res

    let let_if_opt fml =
      if Fn.non SimpleFormula.is_branch fml then None
      else
        let outer_op, fmls = SimpleFormula.let_branch fml in
        match fmls with
        | [ fml1; fml2 ] ->
            let inner_op = Formula.flip_binop outer_op in
            let get_formulas op fml =
              (* for fmls: atom *)
              if SimpleFormula.is_branch fml then
                let op', fmls = SimpleFormula.let_branch fml in
                if Stdlib.(op' = op) then fmls else [ fml ]
              else [ fml ]
            in
            let ht_of_formulas fmls =
              let ht = Hashtbl.Poly.create ~size:1234 () in
              List.iteri fmls ~f:(fun i fml ->
                  Hashtbl.Poly.set ht ~key:fml ~data:i);
              ht
            in
            let search_for_dual_formulas fmls ht =
              List.fold_left ~init:None (List.zip_index fmls)
                ~f:(fun res (fml, i) ->
                  if Option.is_none res then
                    if Set.is_empty @@ SimpleFormula.get_fpv fml then
                      (* TODO: to be more efficient *)
                      let fmls =
                        get_formulas inner_op @@ SimpleFormula.neg fml
                      in
                      if List.for_all ~f:(Hashtbl.Poly.mem ht) fmls then
                        Some ([ i ], List.map ~f:(Hashtbl.Poly.find_exn ht) fmls)
                      else None
                    else None
                  else res)
            in
            let fmls1 = get_formulas inner_op fml1 in
            let fmls2 = get_formulas inner_op fml2 in
            let ht1 = ht_of_formulas fmls1 in
            let ht2 = ht_of_formulas fmls2 in
            let result =
              match search_for_dual_formulas fmls1 ht2 with
              | Some result -> Some result
              | None -> (
                  match search_for_dual_formulas fmls2 ht1 with
                  | Some (pos2, pos1) -> Some (pos1, pos2)
                  | None -> None)
            in
            if Option.is_none result then None
            else
              let pos1, pos2 = Option.value_exn result in
              let set_pos1 = Set.Poly.of_list pos1 in
              let set_pos2 = Set.Poly.of_list pos2 in
              let cond_fml =
                List.zip_index fmls1
                |> List.filter ~f:(snd >> Set.mem set_pos1)
                |> List.map ~f:fst
                |> SimpleFormula.mk_branch_with_simplification_one inner_op
              in
              (* TODO: O(nlogn) -> O(n) *)
              let fml1 =
                List.zip_index fmls1
                |> List.filter ~f:(snd >> Set.mem set_pos1 >> not)
                |> List.map ~f:fst
                |> SimpleFormula.mk_branch_with_simplification_one inner_op
              in
              let fml2 =
                List.zip_index fmls2
                |> List.filter ~f:(snd >> Set.mem set_pos2 >> not)
                |> List.map ~f:fst
                |> SimpleFormula.mk_branch_with_simplification_one inner_op
              in
              Some (outer_op, cond_fml, fml1, fml2)
        | _ -> None

    let let_if fml =
      match let_if_opt fml with Some res -> res | None -> assert false

    let is_from_if fml =
      match let_if_opt fml with Some _ -> true | None -> false

    let optimize ?(elim_forall = true) ?(elim_exists = true) muclp =
      let preds = Array.of_list muclp.Problem.preds in
      let pvar_to_pred : (Ident.pvar, Pred.t) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      let pvar_to_nxtpvar : (Ident.pvar, Ident.pvar) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      let pvar_to_epvar :
          (Ident.pvar, (bool list, Ident.pvar) Hashtbl.t) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      let pvar_to_fpvar :
          (Ident.pvar, (bool list, Ident.pvar) Hashtbl.t) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      let endpvar = Ident.mk_fresh_pvar () in
      let startpvar =
        if Array.is_empty preds then endpvar else preds.(0).name
      in
      let ht_of_binder = function
        | Formula.Forall -> pvar_to_fpvar
        | Exists -> pvar_to_epvar
        | _ -> assert false
      in
      (* init pvar_to_pred, pvar_to_nxtpvar, pvar_to_epvar, pvar_to_fpvar *)
      Array.iteri preds ~f:(fun i pred ->
          let nxtpvar =
            if i = Array.length preds - 1 then endpvar else preds.(i + 1).name
          in
          Hashtbl.Poly.set pvar_to_nxtpvar ~key:pred.name ~data:nxtpvar;
          Hashtbl.Poly.set pvar_to_pred ~key:pred.name ~data:pred;
          Hashtbl.Poly.set pvar_to_epvar ~key:pred.name
            ~data:(create_initial_pvar_to_xpvar pred.args pred.name);
          Hashtbl.Poly.set pvar_to_fpvar ~key:pred.name
            ~data:(create_initial_pvar_to_xpvar pred.args pred.name));
      (* queue for erase_quantifiers_rep *)
      let queue = Queue.create () in
      (* add exists/forall pred of [pvar] pred and return the pvar of it *)
      let add_pred binder bound_flags pvar =
        (* construct new function *)
        let pvar, pred =
          let pred' = Hashtbl.find_exn pvar_to_pred pvar in
          let pvar' = Ident.mk_fresh_pvar () in
          (* TODO *)
          Debug.print
          @@ lazy
               (sprintf "add_pred (pvar): %s. %s"
                  (Formula.str_of_binder binder)
                  (Ident.name_of_pvar pvar'));
          let qbounds, args =
            List.partition_map (List.zip_exn pred'.args bound_flags)
              ~f:(fun (b, f) -> if f then First b else Second b)
          in
          ( pred'.name,
            {
              pred' with
              name = pvar';
              args;
              body = Formula.mk_bind_if_bounded binder qbounds pred'.body;
            } )
        in
        (* update pvar_to_nxtpvar: insert the pred just after [pvar] *)
        let nxtpvar = Hashtbl.Poly.find_exn pvar_to_nxtpvar pvar in
        Hashtbl.Poly.set pvar_to_nxtpvar ~key:pvar ~data:pred.name;
        Hashtbl.Poly.set pvar_to_nxtpvar ~key:pred.name ~data:nxtpvar;
        (* update pvar_to_pred *)
        Hashtbl.Poly.set pvar_to_pred ~key:pred.name ~data:pred;
        (* update pvar_to_fpvar, pvar_to_epvar *)
        Hashtbl.Poly.set
          (Hashtbl.find_exn (ht_of_binder binder) pvar)
          ~key:bound_flags ~data:pred.name;
        Hashtbl.Poly.set (ht_of_binder binder) ~key:pred.name
          ~data:(Hashtbl.Poly.create ~size:seed ());
        (* push to the queue for erase_quantifiers_rep *)
        Queue.enqueue queue pred.name;
        (* return new pvar *)
        pred.name
      in
      let get_or_add_pred binder bound_flags pvar =
        Debug.print
        @@ lazy
             (sprintf "get_or_add_pred: %s. %s"
                (Formula.str_of_binder binder)
                (Ident.name_of_pvar pvar));
        let ht' =
          let ht = ht_of_binder binder in
          Hashtbl.Poly.find_or_add
            ~default:(fun _ -> Hashtbl.Poly.create ())
            ht pvar
        in
        if not (Hashtbl.Poly.mem ht' bound_flags) then
          ignore (add_pred binder bound_flags pvar : Ident.pvar);
        Hashtbl.find_exn ht' bound_flags
      in
      let binder_of_op = function
        | Formula.Forall -> Formula.And
        | Formula.Exists -> Formula.Or
        | _ -> assert false
      in
      (* erase quantifiers in [binder] [bounds]. [fml] *)
      let rec erase_quantifiers_rep_bind binder bounds fml =
        let ftv = SimpleFormula.get_ftv fml in
        let bounds = List.filter ~f:(fst >> Set.mem ftv) bounds in
        if List.is_empty bounds then erase_quantifiers_rep fml
        else if SimpleFormula.is_branch fml then (
          (* exists a. P(a) \/ P(b) -> (exists a. P(a)) \/ (exists a. P(b))
             exists a. P(a) /\ Q -> (exists a. P(a)) /\ Q *)
          let op, fmls = SimpleFormula.let_branch fml in
          if Stdlib.(binder_of_op binder = op) then
            (* exists a. P(a) \/ P(b) -> (exists a. P(a)) \/ (exists a. P(b)) *)
            SimpleFormula.mk_branch op
            @@ List.map ~f:(erase_quantifiers_rep_bind binder bounds) fmls
          else if is_from_if fml then (
            (* forall x. (P /\ Q) \/ (not P /\ R)
               -> forall x. (P => Q) /\ (not P => R)
               -> (forall x. not P \/ Q) /\ (forall x. P \/ R)

               exists x. (P \/ Q) /\ (not P \/ R)
               -> exists x. (not P => Q) /\ (P => R)
               -> exists x. (not P /\ Q) \/ (P /\ R)
               -> (exists x. not P /\ Q) \/ (exists x. P /\ R) *)
            let op', cond_fml, fml1, fml2 = let_if fml in
            assert (Stdlib.(op' = op));
            let fml1 =
              SimpleFormula.mk_branch_with_simplification_one op
                [ SimpleFormula.neg cond_fml; fml1 ]
              |> erase_quantifiers_rep_bind binder bounds
            in
            let fml2 =
              SimpleFormula.mk_branch_with_simplification_one op
                [ cond_fml; fml2 ]
              |> erase_quantifiers_rep_bind binder bounds
            in
            SimpleFormula.mk_branch_with_simplification_one
              (Formula.flip_binop op) [ fml1; fml2 ])
          else
            (* exists a. P(a) /\ Q
                 -> (exists a. P(a)) /\ Q

               [exists a, b, c. P1(a, b) /\ P2(a) /\ P3(c)]
                 -> [exists a, b, c. P1(a, b) /\ P2(a)] /\ [exists a, b, c. P3(c)]
                 with UnionFind *)
            let bounds_tvar_set = Set.Poly.of_list @@ List.map ~f:fst bounds in
            let ht = Hashtbl.Poly.create ~size:seed () in
            List.iteri fmls ~f:(fun i fml ->
                Set.iter (SimpleFormula.get_ftv fml) ~f:(fun tvar ->
                    if Set.mem bounds_tvar_set tvar then
                      let ids =
                        match Hashtbl.Poly.find ht tvar with
                        | Some ids -> ids
                        | None -> []
                      in
                      Hashtbl.Poly.set ht ~key:tvar ~data:(i :: ids)));
            let n = List.length fmls in
            if false then
              printf "%s\n\n"
                (String.concat_map_list ~sep:"\n" ~f:SimpleFormula.string_of
                   fmls);
            assert (n >= 2);
            (* because of simplification *)
            (* construct uf *)
            let uf = UnionFind.mk_size_uf ~size:n in
            Hashtbl.Poly.iter ht ~f:(fun ids ->
                let ids = Array.of_list ids in
                Array.iteri ids ~f:(fun i _ ->
                    if i + 1 < Array.length ids then
                      UnionFind.unite ids.(i) ids.(i + 1) uf));
            (* reconstruct the branch *)
            let fmls = Array.of_list fmls in
            UnionFind.get_groups uf
            |> List.map ~f:(fun ids ->
                   let fmls' = List.map ~f:(fun id -> fmls.(id)) ids in
                   match fmls' with
                   | [ fml' ] -> erase_quantifiers_rep_bind binder bounds fml'
                   (* try let_if *)
                   | [ _; _ ] ->
                       (* TODO *)
                       let fml' =
                         SimpleFormula.mk_branch_with_simplification_one op
                           fmls'
                       in
                       if is_from_if fml' then
                         erase_quantifiers_rep_bind binder bounds fml'
                       else
                         List.map ~f:erase_quantifiers_rep fmls'
                         |> SimpleFormula.mk_branch_with_simplification_one op
                         |> SimpleFormula.mk_bind_with_filter binder bounds
                   | _ ->
                       (* List.length fmls >= 2 *)
                       List.map ~f:erase_quantifiers_rep fmls'
                       |> SimpleFormula.mk_branch_with_simplification_one op
                       |> SimpleFormula.mk_bind_with_filter binder bounds)
            |> SimpleFormula.mk_branch_with_simplification_one op)
        else if SimpleFormula.is_bind fml then
          let binder', bounds', fml' = SimpleFormula.let_bind fml in
          (* forall x. forall y. P -> forall x, y. P *)
          if Stdlib.(binder = binder') then
            (* bounds, bounds' must be distinct *)
            (*let new_bounds = bounds @ bounds' in
              assert (Stdlib.(SimpleFormula.update_bounds bounds bounds' = new_bounds));*)
            let new_bounds = SimpleFormula.update_bounds bounds bounds' in
            erase_quantifiers_rep_bind binder new_bounds fml'
          else
            (* forall x. exists y. P
               1. process [exists y. P]
               2. if it's still of the form [forall x. exists y. P] then give up erasing (to avoid an infinite-loop)
               3. otherwise, continue to process erase_quantifiers_rep_bind *)
            let fml = erase_quantifiers_rep_bind binder' bounds' fml' in
            if SimpleFormula.is_bind fml then
              let binder', _, _ = SimpleFormula.let_bind fml in
              if Stdlib.(binder <> binder') then
                SimpleFormula.mk_bind_with_filter binder bounds fml
              else erase_quantifiers_rep_bind binder bounds fml
            else erase_quantifiers_rep_bind binder bounds fml
        else if SimpleFormula.is_app fml then (
          let pvar, args = SimpleFormula.let_app fml in
          Debug.print
          @@ lazy
               (sprintf "erase_quantifiers_rep_bind(is_app): "
               ^ SimpleFormula.string_of fml);
          match bound_flags_of_app_opt bounds args with
          | Some bound_flags ->
              SimpleFormula.mk_app (get_or_add_pred binder bound_flags pvar)
              @@ List.map ~f:fst
              @@ List.filter ~f:(snd >> not)
              @@ List.zip_exn args bound_flags
          | None -> SimpleFormula.mk_bind_with_filter binder bounds fml)
        else if SimpleFormula.is_cond fml then
          SimpleFormula.mk_bind_with_filter binder bounds fml
        else assert false
      and erase_quantifiers_rep fml =
        if SimpleFormula.is_and fml then
          SimpleFormula.let_and fml
          |> List.map ~f:erase_quantifiers_rep
          |> SimpleFormula.mk_and
        else if SimpleFormula.is_or fml then
          SimpleFormula.let_or fml
          |> List.map ~f:erase_quantifiers_rep
          |> SimpleFormula.mk_or
        else if SimpleFormula.is_bind fml then
          let binder, bounds, fml' = SimpleFormula.let_bind fml in
          if
            Stdlib.(
              (elim_forall && binder = Formula.Forall)
              || (elim_exists && binder = Formula.Exists))
          then erase_quantifiers_rep_bind binder bounds fml'
          else fml
        else if SimpleFormula.is_atom fml then fml
        else assert false
      in
      let erase_quantifiers fml =
        try
          Debug.print
          @@ lazy (sprintf "erase_quantifiers before: " ^ Formula.str_of fml);
          let fml = SimpleFormula.of_formula @@ Formula.nnf_of fml in
          Debug.print
          @@ lazy
               (sprintf "erase_quantifiers after: "
               ^ SimpleFormula.string_of fml);
          SimpleFormula.formula_of @@ erase_quantifiers_rep fml
        with _ -> fml
      in
      (* init queue *)
      Array.iter preds ~f:(fun pred -> Queue.enqueue queue pred.name);
      let query = erase_quantifiers muclp.Problem.query in
      while Fn.non Queue.is_empty queue do
        let pvar = Queue.dequeue_exn queue in
        let pred = Hashtbl.Poly.find_exn pvar_to_pred pvar in
        assert (Stdlib.( = ) pvar pred.name);
        Debug.print @@ lazy (sprintf "%s: " (Ident.name_of_pvar pvar));
        Hashtbl.Poly.set pvar_to_pred ~key:pvar
          ~data:{ pred with body = erase_quantifiers pred.body }
      done;
      (* reconstruct preds from startpvar, endpvar, pvar_to_nxtpvar, pvar_to_pred, processed_pvars(reached) *)
      let preds_queue = Queue.create () in
      let current_pvar = ref startpvar in
      while Stdlib.(!current_pvar <> endpvar) do
        Queue.enqueue preds_queue
        @@ Hashtbl.Poly.find_exn pvar_to_pred !current_pvar;
        current_pvar := Hashtbl.Poly.find_exn pvar_to_nxtpvar !current_pvar
      done;
      Problem.make ((*ToDo*) Queue.to_list preds_queue) query
  end

  (* exists x. 0 <= x /\ x <= 100 -> true *)
  module CheckAndReplaceToTopOrBot : sig
    val optimize : id:int option -> Problem.t -> Problem.t
  end = struct
    let bind_free_tvas_with_forall fml =
      let bounds = Set.to_list @@ Formula.term_sort_env_of fml in
      Formula.mk_forall_if_bounded bounds fml ~info:Dummy

    let gen_smt_solver timeout_milliseconds =
      let ctx =
        Z3.mk_context [ ("timeout", string_of_int timeout_milliseconds) ]
      in
      (Z3.Solver.mk_simple_solver ctx, ctx)

    let check_always_true ~id ?(timeout_milliseconds = 1000) fml =
      if Fn.non Set.is_empty @@ Formula.pvs_of fml then false
      else (
        Debug.print @@ lazy "\n[optimize][check_always_true]";
        Debug.print @@ lazy (sprintf "input: %s" (Formula.str_of fml));
        (* x >= 10 -> forall (x: int). x >= 10 *)
        let fml = bind_free_tvas_with_forall fml in
        (* to smt format and solve it with z3 *)
        let solver, ctx = gen_smt_solver timeout_milliseconds in
        let fenv =
          Map.Poly.empty
          (*ToDo*)
          (*PCSP.Problem.fenv_of APCSP.problem*)
        in
        let dtenv =
          Set.Poly.empty
          (*ToDo*)
          (*Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx (PCSP.Problem.dtenv_of APCSP.problem)*)
        in
        let expr = Z3Smt.Z3interface.of_formula ~id ctx [] [] fenv dtenv fml in
        Debug.print @@ lazy (sprintf "expr: %s" (Z3.Expr.to_string expr));
        try
          let z3result = Z3.Solver.check solver [ expr ] in
          Debug.print
          @@ lazy (sprintf "Z3: %s\n" (Z3.Solver.string_of_status z3result));
          match z3result with Z3.Solver.SATISFIABLE -> true | _ -> false
        with Z3.Error reason ->
          (* timeout *)
          Debug.print @@ lazy (sprintf "Z3 Error: %s" reason);
          false)

    let rec replace_to_topbot ~id = function
      | Formula.BinaryOp (op, phi1, phi2, info) ->
          Formula.mk_binop ~info op
            (replace_to_topbot ~id phi1)
            (replace_to_topbot ~id phi2)
      | Formula.UnaryOp (op, phi1, info) ->
          Formula.mk_unop ~info op (replace_to_topbot ~id phi1)
      | Formula.Atom (_, _) as phi -> phi
      | Formula.Bind (binder, bounds, fml, info) as phi ->
          if check_always_true ~id phi then Formula.mk_true ()
          else if check_always_true ~id (Evaluator.simplify_neg phi) then
            Formula.mk_false ()
          else Formula.mk_bind binder bounds ~info @@ replace_to_topbot ~id fml
      | _ -> failwith "replace_to_topbot"

    let optimize ~id = Problem.map_formula (replace_to_topbot ~id)
  end

  module EraseConstVariables : sig
    val optimize : Problem.t -> Problem.t
  end = struct
    type vartype =
      | UnReached
      | ConstInt of Z.t
      | ConstReal of Q.t
      | ConstBool of bool
      | NonConst

    let merge_vt vt1 vt2 =
      match (vt1, vt2) with
      | UnReached, vt | vt, UnReached -> vt
      | ConstInt x, ConstInt y -> if Z.(equal x y) then ConstInt x else NonConst
      | ConstReal x, ConstReal y ->
          if Q.(equal x y) then ConstReal x else NonConst
      | ConstBool x, ConstBool y ->
          if Stdlib.(x = y) then ConstBool x else NonConst
      | _ -> NonConst

    let is_const = function
      | ConstInt _ -> true
      | ConstReal _ -> true
      | ConstBool _ -> true
      | _ -> false

    let string_of_vt = function
      | UnReached -> "unreached"
      | NonConst -> "nonconst"
      | ConstInt x -> sprintf "const %s" (Z.to_string x)
      | ConstReal x -> sprintf "const %s" (Q.to_string x)
      | ConstBool x -> sprintf "const %s" (Bool.to_string x)

    let seed = 1007

    let vt_of_pt ht_vt (pvar, tvar) =
      Hashtbl.Poly.(find_exn (find_exn ht_vt pvar) tvar)

    let init_ht_vt muclp =
      let ht_vt : (Ident.pvar, (Ident.tvar, vartype) Hashtbl.t) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      List.iter muclp.Problem.preds ~f:(fun pred ->
          let ht = Hashtbl.Poly.create ~size:seed () in
          List.iter pred.args ~f:(fun (tvar, _) ->
              Hashtbl.Poly.set ht ~key:tvar ~data:UnReached);
          Hashtbl.Poly.set ht_vt ~key:pred.name ~data:ht);
      ht_vt

    let rec nonconst_update ht_vt graph pt =
      let pvar, tvar = pt in
      Hashtbl.Poly.set
        (Hashtbl.Poly.find_exn ht_vt pvar)
        ~key:tvar ~data:NonConst;
      Hashtbl.Poly.find_exn graph pt
      |> List.iter ~f:(fun (nxt_pvar, nxt_tvar, _) ->
             let nxt_pt = (nxt_pvar, nxt_tvar) in
             let env = Hashtbl.Poly.find_exn ht_vt nxt_pvar in
             if Stdlib.( <> ) (Hashtbl.Poly.find_exn env nxt_tvar) NonConst then
               nonconst_update ht_vt graph nxt_pt)

    let rec vt_of_term env = function
      | Term.Var (tvar, _, _) ->
          if Hashtbl.Poly.mem env tvar then Hashtbl.Poly.find_exn env tvar
          else NonConst
      | Term.FunApp (funsym, args, _) -> (
          let arg_vts = List.map ~f:(vt_of_term env) args in
          if List.exists ~f:(Stdlib.( = ) NonConst) arg_vts then NonConst
          else if List.exists ~f:(Stdlib.( = ) UnReached) arg_vts then UnReached
          else
            match (funsym, arg_vts) with
            | T_bool.Formula (Formula.Atom (Atom.True _, _)), [] ->
                ConstBool true
            | T_bool.Formula (Formula.Atom (Atom.False _, _)), [] ->
                ConstBool false
            | T_int.Int x, [] -> ConstInt x
            | T_int.Neg, [ ConstInt x ] -> ConstInt (Z.neg x)
            | T_int.Nop, [ ConstInt x ] -> ConstInt x
            | T_int.Abs, [ ConstInt x ] -> ConstInt (Z.abs x)
            | T_int.Add, [ ConstInt x; ConstInt y ] -> ConstInt (Z.( + ) x y)
            | T_int.Sub, [ ConstInt x; ConstInt y ] -> ConstInt (Z.( - ) x y)
            | T_int.Mul, [ ConstInt x; ConstInt y ] -> ConstInt (Z.( * ) x y)
            | T_int.Div m, [ ConstInt x; ConstInt y ] ->
                ConstInt (Value.div_of m x y)
            | T_int.Rem m, [ ConstInt x; ConstInt y ] ->
                ConstInt (Value.rem_of m x y)
            | T_int.Power, [ ConstInt x; ConstInt y ] ->
                ConstInt (Z.pow x (Z.to_int (*ToDo*) y))
            | T_real.Real x, [] -> ConstReal x
            | T_real.RNeg, [ ConstReal x ] -> ConstReal (Q.neg x)
            | T_real.RAbs, [ ConstReal x ] -> ConstReal (Q.abs x)
            | T_real.RAdd, [ ConstReal x; ConstReal y ] ->
                ConstReal (Q.( + ) x y)
            | T_real.RSub, [ ConstReal x; ConstReal y ] ->
                ConstReal (Q.( - ) x y)
            | T_real.RMul, [ ConstReal x; ConstReal y ] ->
                ConstReal (Q.( * ) x y)
            | T_real.RDiv, [ ConstReal x; ConstReal y ] ->
                ConstReal (Q.( / ) x y)
            | T_bv.BVNum (_, _), []
            | T_bv.(BVNeg _ | BVSEXT _ | BVZEXT _), [ _ ]
            | ( T_bv.(
                  ( BVAdd _ | BVSub _ | BVMul _ | BVDiv _ | BVRem _ | BVSHL _
                  | BVLSHR _ | BVASHR _ | BVOr _ | BVAnd _ )),
                [ _; _ ] ) ->
                NonConst (*ToDo*)
            | _ ->
                failwith @@ "EraseConstVariables.vt_of_term: illegal funapp "
                ^ Term.str_of_funsym funsym)
      | _ -> failwith "vt_of_term"

    let value_of_const_term term =
      match vt_of_term (Hashtbl.Poly.create ~size:seed ()) term with
      | ConstInt x -> ConstInt x
      | ConstReal x -> ConstReal x
      | ConstBool x -> ConstBool x
      | _ -> assert false

    let rec get_vargraph_rep (tvars_of_pvar : Ident.pvar -> Ident.tvar list)
        (pvar : Ident.pvar) arg_tvars consts nonconsts graph = function
      | Formula.UnaryOp (_, fml, _) ->
          get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph
            fml
      | Formula.BinaryOp (_, fml1, fml2, _) ->
          let consts, nonconsts =
            get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph
              fml1
          in
          get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph
            fml2
      | Formula.Atom (Atom.App (Predicate.Var (pvar', _), args, _), _) ->
          List.zip_exn args (tvars_of_pvar pvar')
          |> List.fold_left ~init:(consts, nonconsts)
               ~f:(fun (consts, nonconsts) (arg, tvar') ->
                 let ftv = Term.tvs_of arg in
                 if Set.is_empty ftv then
                   try
                     ( (pvar', tvar', value_of_const_term arg) :: consts,
                       nonconsts )
                   with _ -> (*ToDo*) (consts, nonconsts)
                 else if Set.is_empty @@ Set.diff ftv arg_tvars then (
                   Set.iter (Set.inter ftv arg_tvars) ~f:(fun tvar ->
                       let pt = (pvar, tvar) in
                       let edges = Hashtbl.Poly.find_exn graph pt in
                       Hashtbl.Poly.set graph ~key:pt
                         ~data:((pvar', tvar', arg) :: edges));
                   (consts, nonconsts))
                 else (consts, (pvar', tvar') :: nonconsts))
      | Formula.Atom (_, _) -> (consts, nonconsts)
      | Formula.Bind (_, bounds, fml, _) ->
          let arg_tvars =
            Set.diff arg_tvars @@ Set.Poly.of_list @@ List.map ~f:fst bounds
          in
          get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph
            fml
      | _ -> failwith "get_vargraph_rep"

    let tvars_of_pvar_of_muclp muclp =
      let tvars_of_pvar_ht = Hashtbl.Poly.create ~size:seed () in
      List.iter muclp.Problem.preds ~f:(fun pred ->
          Hashtbl.Poly.set tvars_of_pvar_ht ~key:pred.name
            ~data:(List.map ~f:fst pred.args));
      fun pvar -> Hashtbl.find_exn tvars_of_pvar_ht pvar

    let get_vargraph muclp =
      let dummy_pvar = Ident.Pvar "dummy" in
      let consts : (Ident.pvar * Ident.tvar * vartype) list = [] in
      let nonconsts : (Ident.pvar * Ident.tvar) list = [] in
      let graph :
          ( Ident.pvar * Ident.tvar,
            (Ident.pvar * Ident.tvar * Term.t) list )
          Hashtbl.Poly.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      let tvars_of_pvar = tvars_of_pvar_of_muclp muclp in
      List.iter (Pred.pvars_of_list muclp.Problem.preds) ~f:(fun pvar ->
          List.iter (tvars_of_pvar pvar) ~f:(fun tvar ->
              Hashtbl.Poly.set graph ~key:(pvar, tvar) ~data:[]));
      let consts, nonconsts =
        List.fold_left muclp.Problem.preds
          ~init:
            (get_vargraph_rep tvars_of_pvar dummy_pvar Set.Poly.empty consts
               nonconsts graph muclp.Problem.query)
          ~f:(fun (consts, nonconsts) pred ->
            let arg_tvars = Set.Poly.of_list @@ List.map ~f:fst pred.args in
            get_vargraph_rep tvars_of_pvar pred.name arg_tvars consts nonconsts
              graph pred.body)
      in
      (consts, nonconsts, graph)

    let gen_ht_vt muclp =
      let ht_vt = init_ht_vt muclp in
      let consts, nonconsts, graph = get_vargraph muclp in
      if false then
        printf "nonconsts: %s\n"
          (String.concat_map_list ~sep:" "
             ~f:(fun (pvar, tvar) ->
               sprintf "(%s, %s)" (Ident.name_of_pvar pvar)
                 (Ident.name_of_tvar tvar))
             nonconsts);
      List.iter nonconsts ~f:(nonconst_update ht_vt graph);
      let queue = Queue.create () in
      let update_ht_vt pt const =
        let current_vt = vt_of_pt ht_vt pt in
        if Stdlib.(current_vt <> NonConst) then
          let new_vt = merge_vt current_vt const in
          if Stdlib.(new_vt <> current_vt) then (
            let pvar, tvar = pt in
            Hashtbl.Poly.set
              (Hashtbl.find_exn ht_vt pvar)
              ~key:tvar ~data:new_vt;
            if Stdlib.(new_vt = NonConst) then nonconst_update ht_vt graph pt
            else Queue.enqueue queue pt)
      in
      List.iter consts ~f:(fun (pvar, tvar, value) ->
          update_ht_vt (pvar, tvar) value);
      while Fn.non Queue.is_empty queue do
        let pt = Queue.dequeue_exn queue in
        let pvar, tvar = pt in
        if false then (
          printf "%s, %s: %s\n" (Ident.name_of_pvar pvar)
            (Ident.name_of_tvar tvar)
            (string_of_vt (vt_of_pt ht_vt pt));
          Out_channel.flush stdout);
        if Stdlib.(vt_of_pt ht_vt pt <> NonConst) then
          List.iter (Hashtbl.Poly.find_exn graph pt)
            ~f:(fun (nxt_pvar, nxt_tvar, term) ->
              let nxt_pt = (nxt_pvar, nxt_tvar) in
              let current_vt = vt_of_pt ht_vt nxt_pt in
              if Stdlib.(current_vt <> NonConst) then
                let env = Hashtbl.Poly.find_exn ht_vt pvar in
                (* it's ok *)
                match vt_of_term env term with
                | NonConst -> nonconst_update ht_vt graph nxt_pt
                | (ConstBool _ | ConstInt _ | ConstReal _) as con ->
                    update_ht_vt nxt_pt con
                | UnReached -> ())
      done;
      ht_vt

    let filter_nonconst_args tvars_of_pvar ht_vt =
      Formula.map_atom ~f:(function
        | Atom.App (Predicate.Var (pvar, sorts), args, info) ->
            let ht_vt_of_tvar = Hashtbl.Poly.find_exn ht_vt pvar in
            let args, sorts =
              List.zip_exn (List.zip_exn args sorts) (tvars_of_pvar pvar)
              |> List.filter
                   ~f:
                     (snd
                     >> Hashtbl.Poly.find_exn ht_vt_of_tvar
                     >> is_const >> not)
              |> List.map ~f:fst |> List.unzip
            in
            Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts args ~info
        | atm -> Formula.mk_atom atm)

    let optimize muclp =
      if false then (
        printf "[ReplaceConstVariables]\n";
        printf "Input: %s\n\n" (Problem.str_of muclp));
      let ht_vt = gen_ht_vt muclp in
      let tvars_of_pvar = tvars_of_pvar_of_muclp muclp in
      let query =
        filter_nonconst_args tvars_of_pvar ht_vt muclp.Problem.query
      in
      let preds =
        List.map muclp.Problem.preds ~f:(fun pred ->
            let ht_vt_of_tvar = Hashtbl.Poly.find_exn ht_vt pred.name in
            let subst =
              List.fold_left pred.args ~init:Map.Poly.empty
                ~f:(fun tsub (tvar, _) ->
                  match Hashtbl.Poly.find_exn ht_vt_of_tvar tvar with
                  | ConstBool x ->
                      Map.Poly.set tsub ~key:tvar ~data:(T_bool.make x)
                  | ConstInt x ->
                      Map.Poly.set tsub ~key:tvar ~data:(T_int.mk_int x)
                  | ConstReal x ->
                      Map.Poly.set tsub ~key:tvar ~data:(T_real.mk_real x)
                  | _ -> tsub)
            in
            {
              pred with
              args =
                List.filter pred.args
                  ~f:
                    (fst
                    >> Hashtbl.Poly.find_exn ht_vt_of_tvar
                    >> is_const >> not);
              body =
                filter_nonconst_args tvars_of_pvar ht_vt
                @@ Formula.subst subst pred.body;
            })
      in
      Problem.make preds query
  end

  let print_log = true

  let f ?(id = None) ?(elim_forall = true) ?(elim_exists = true)
      ?(elim_pvar_args = true) muclp =
    let simplify =
      Problem.map_formula Formula.(elim_unused_bounds >> elim_let (*ToDo*))
    in
    Debug.set_id id;
    if config.enable then
      muclp |> simplify
      |> (fun muclp ->
           if print_log then
             Debug.print @@ lazy ("simplified: " ^ Problem.str_of muclp);
           muclp)
      |> InlineExtension.optimize
      |> (fun muclp ->
           if print_log then
             Debug.print @@ lazy ("\ninlined: " ^ Problem.str_of muclp);
           muclp)
      |> (if config.erase_quantifiers then
            EraseQuantifiers.optimize ~elim_forall ~elim_exists
          else Fn.id)
      |> (fun muclp ->
           if print_log then
             Debug.print
             @@ lazy ("\nquantifiers eliminated: " ^ Problem.str_of muclp);
           muclp)
      |> EraseUnreachedPredicates.optimize
      |> (if elim_pvar_args then EraseConstVariables.optimize else Fn.id)
      |> CheckAndReplaceToTopOrBot.optimize ~id
      |> Problem.simplify |> InlineExtension.optimize
    else muclp |> simplify
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : OptimizerType)
