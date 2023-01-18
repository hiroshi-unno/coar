open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld

module Config = struct
  type t = {
    enable : bool;
    verbose : bool
  } [@@deriving yojson]

  module type ConfigType = sig val config : t end

  let load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> Ok (ExtFile.Instance x)
        | Error msg ->
          error_string @@ Printf.sprintf
            "Invalid Optimizer Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)
end

module type OptimizerType = sig
  val optimize: ?is_print_for_debug:bool -> Problem.t -> Problem.t
end

module Make (Config: Config.ConfigType) = struct
  let config = Config.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))

  let get_pvar_called_counts pvar_to_id preds =
    let n = List.length preds in
    let res = Array.init n ~f:(fun _ -> 0) in
    List.iter preds ~f:(fun (_, _, _, body) ->
        Formula.iter_pred_app ~f:(fun pvar _ ->
            let pvar_id = pvar_to_id pvar in
            res.(pvar_id) <- res.(pvar_id) + 1) body);
    res

  (* 0: query, n: n-th pvar from toplevel *)
  let pvargraph_of_muclp muclp =
    let preds, query = Problem.let_muclp muclp in
    let pvar_to_id = Hashtbl.Poly.create ~size:1234 () in
    (* initialize pvar_to_id *)
    List.iteri ~f:(fun i pred -> Hashtbl.Poly.set pvar_to_id ~key:(Pred.pvar_of pred) ~data:(i+1)) preds;
    query :: List.map ~f:(fun pred -> Pred.body_of pred) preds
    |> List.map ~f:(fun body ->
        Pred.get_next_list body
        |> List.map ~f:(fun nxt_pvar -> Hashtbl.Poly.find_exn pvar_to_id nxt_pvar))
    |> Array.of_list

  let reachable_from starting_node_id graph =
    let n = Array.length graph in
    let res = Array.init n ~f:(fun _ -> false) in
    let queue = Queue.create () in
    res.(starting_node_id) <- true;
    Queue.enqueue queue starting_node_id;
    while Fn.non Queue.is_empty queue do
      let node_id = Queue.dequeue_exn queue in
      List.iter graph.(node_id) ~f:(fun nxt_node_id ->
          if not res.(nxt_node_id) then begin
            res.(nxt_node_id) <- true;
            Queue.enqueue queue nxt_node_id
          end)
    done;
    res

  module EraseUnreachedPredicates : sig
    val optimize: Problem.t -> Problem.t
  end = struct
    let optimize muclp =
      let graph = pvargraph_of_muclp muclp in
      let reachable = reachable_from 0 graph |> Array.to_list in
      let preds, query = Problem.let_muclp muclp in
      let preds =
        List.zip_exn preds (List.tl_exn reachable)
        |> List.filter ~f:snd
        |> List.map ~f:fst
      in
      Problem.make preds query
  end


(*
  inline extension

  if a predicate P1 is called from only one predicate P2
  and depth(P1) > depth(P2)
  then P1 is eliminated by inline extension
*)

  module InlineExtension : sig
    val optimize: Problem.t -> Problem.t
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
        failwith @@ Printf.sprintf "InlineExtension.update_called_counts_in_fml: not implemented for: %s" (Convert.PrinterHum.str_of_formula fml) *)
    let optimize muclp =
      let preds_list, query = Problem.let_muclp muclp in
      let n = List.length preds_list in
      (* pvar -> depth *)
      let depth_ht = Problem.get_depth_ht muclp in
      let pvar_to_id = (fun pvar -> Hashtbl.Poly.find_exn depth_ht pvar) in
      let called_counts = get_pvar_called_counts pvar_to_id preds_list in
      let expanded = Array.init n ~f:(fun _ -> false) in
      let preds = Array.of_list preds_list in
      List.rev preds_list
      |> List.iteri ~f:(fun i pred ->
          let pred_id = n - i - 1 in
          let fix, pvar, args, body = Pred.let_ pred in
          let body =
            Pred.replace_app (fun fml ->
                let atom, _ = Formula.let_atom fml in
                let pred, args, _ = Atom.let_app atom in
                let pvar, _ = Predicate.let_var pred in
                let pred_id' = pvar_to_id pvar in
                if called_counts.(pred_id') = 1 && pred_id' > pred_id then begin
                  expanded.(pred_id') <- true;
                  let _, pvar', args', body = Pred.let_ preds.(pred_id') in
                  assert (Stdlib.(pvar = pvar'));
                  let subst =
                    List.zip_exn (List.map ~f:fst args') args
                    |> Map.Poly.of_alist_exn
                  in
                  Formula.subst subst body
                end else fml) body
          in
          preds.(pred_id) <- Pred.make fix pvar args body);
      let preds =
        Array.to_list preds
        |> List.filter ~f:(fun pred -> let pvar = Pred.pvar_of pred in not expanded.(pvar_to_id pvar))
      in
      Problem.make preds query
  end

  module EraseQuantifiers : sig
    val optimize: Problem.t -> Problem.t
  end = struct
    let seed = 1007

  (*
    AV(a+1) = {a}
    AV(a*2) = {}
    AV(a + a + b) = {b}
    AV(a + b + c) = {a, b, c}
    AV(1) = {}
  *)
    let rec adj_vars_of_term term =
      if Term.is_var term then
        (* AV(a) = {a} *)
        let (tvar, _), _ = Term.let_var term in
        Set.Poly.of_list [tvar]
      else if Term.is_app term then
        let funsym, args, _ = Term.let_app term in
      (*
        AV(a + b) = AV(a - b) = AV(a) + AV(b) - (AV(a) and AV(b))
        AV(a * b) = AV(a / b) = {}
        AV(-a) = AV(a)
      *)
        match funsym, args with
        | (T_int.Add, [a; b]) | (T_int.Sub, [a; b]) ->
          let av1 = adj_vars_of_term a in
          let av2 = adj_vars_of_term b in
          Set.Poly.diff (Set.Poly.union av1 av2) (Set.Poly.inter av1 av2)
        | (T_int.Mult, [_; _]) | (T_int.Div, [_; _])
        | (T_int.Int _, []) -> Set.Poly.empty
        | (T_int.Neg, [a]) -> adj_vars_of_term a
        | _ -> failwith @@ Printf.sprintf "unknown operation: %s" (Term.str_of term)
      else assert false

    let check_separatable avfvs =
      let avfvs = Array.of_list avfvs in
      (* multiset of fv1 U fv2 U ... U fvN *)
      let fv_count: (Ident.tvar, int) Hashtbl.t = Hashtbl.Poly.create ~size:seed () in
      (* x in fv1 iff 1 in indexes_of_ftv[x] *)
      let indexes_of_ftv: (Ident.tvar, int list) Hashtbl.t = Hashtbl.Poly.create ~size:seed () in
      Array.iteri avfvs ~f:(fun idx (_, fv) ->
          Set.Poly.to_list fv
          |> List.iter ~f:(fun tvar ->
              let current_count = match Hashtbl.Poly.find fv_count tvar with None -> 0 | Some x -> x in
              Hashtbl.Poly.set fv_count ~key:tvar ~data:(current_count + 1);
              Hashtbl.Poly.add_multi indexes_of_ftv ~key:tvar ~data:idx));
      let tvars = Hashtbl.Poly.keys fv_count in
      let n = Array.length avfvs in
      let is_assigned = Array.init n ~f:(fun _ -> false) in
      let queue = Queue.create () in
      List.iter tvars ~f:(fun tvar ->
          if Hashtbl.Poly.find_exn fv_count tvar = 1 then
            Queue.enqueue queue tvar);
      while Fn.non Queue.is_empty queue do
        let tvar = Queue.dequeue_exn queue in
        if Hashtbl.Poly.find_exn fv_count tvar = 1 then
          Hashtbl.find_multi indexes_of_ftv tvar
          |> List.iter ~f:(fun idx ->
              if not is_assigned.(idx) && Set.Poly.mem (fst avfvs.(idx)) tvar then begin
                is_assigned.(idx) <- true;
                Set.Poly.iter (snd avfvs.(idx)) ~f:(fun tvar' ->
                    let nxt_count = Hashtbl.Poly.find_exn fv_count tvar' - 1 in
                    Hashtbl.Poly.set fv_count ~key:tvar' ~data:nxt_count;
                    if nxt_count = 1 then Queue.enqueue queue tvar')
              end)
      done;
      Array.for_all ~f:Fn.id is_assigned

    (* let str_of_tvarset s =
       |> Set.Poly.map s ~f: Ident.name_of_tvar
       |> String.concat_set ", "
       |> Printf.sprintf "{%s}" *)

    let bound_flags_of_app_opt bounds args =
      (* let args = List.map Term.simplify args in *)
      let bounds = List.map ~f:fst bounds |> Set.Poly.of_list in
      let avs = List.map ~f:adj_vars_of_term args |> List.map ~f:(Set.Poly.inter bounds) in
      let fvs = List.map ~f:Term.tvs_of args |> List.map ~f:(Set.Poly.inter bounds) in
      let avfvs = List.zip_exn avs fvs in
      (* Printf.printf "[%s]: %s\n"
         (String.concat_map_list ~sep:"; " ~f:PrinterHum.str_of_term args)
         (String.concat_map_list ~sep:" " ~f:(fun (av, fv) -> Printf.sprintf "(%s, %s)" (str_of_tvarset av) (str_of_tvarset fv)) avfvs); *)
      if List.exists ~f:(fun (av, fv) -> Fn.non Set.Poly.is_empty fv && Set.Poly.is_empty av) avfvs then
        (* if FV(t) and bounds != {} /\ AV(t) and bounds = {} for some arg t *)
        None
      else if check_separatable (List.filter ~f:(fun (_, fv) -> Fn.non Set.Poly.is_empty fv) avfvs) then
      (*
        exists x, y. F x (x + y) -> exists x, y. F x y
        exists x, y. F (x + y) (x + y) -> exists x, y. F (x + y) (x + y)
      *)
        Some (List.map ~f:(fun av -> Set.Poly.is_empty av |> not) avs)
      else
        None

    let create_initial_pvar_to_xpvar bounds pvar =
      let res = Hashtbl.Poly.create ~size:seed () in
      Hashtbl.Poly.set res ~key:(List.map ~f:(fun _ -> false) bounds) ~data:pvar;
      res

    let flip_op = function Formula.And -> Formula.Or | Formula.Or -> Formula.And | _ -> assert false

    let let_if_opt fml =
      if Fn.non SimpleFormula.is_branch fml then None
      else
        let outer_op, fmls = SimpleFormula.let_branch fml in
        match fmls with
        | [fml1; fml2] ->
          let inner_op = flip_op outer_op in
          let get_formulas op fml =
            (* for fmls: atom *)
            if SimpleFormula.is_branch fml then
              let op', fmls = SimpleFormula.let_branch fml in
              if Stdlib.(op' = op) then fmls else [fml]
            else [fml]
          in
          let ht_of_formulas fmls =
            let ht = Hashtbl.Poly.create ~size:1234 () in
            List.iteri fmls ~f:(fun i fml -> Hashtbl.Poly.set ht ~key:fml ~data:i);
            ht
          in
          let search_for_dual_formulas fmls ht =
            List.fold_left ~init:None (List.zip_index fmls) ~f:(fun res (fml, i) ->
                if Option.is_none res then
                  if SimpleFormula.get_fpv fml |> Set.Poly.is_empty then (* TODO: to be more efficient *)
                    let fml = SimpleFormula.neg fml in
                    let fmls = get_formulas inner_op fml in
                    if List.for_all ~f:(Hashtbl.Poly.mem ht) fmls then
                      Some ([i], List.map ~f:(Hashtbl.Poly.find_exn ht) fmls)
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
            | None ->
              match search_for_dual_formulas fmls2 ht1 with
              | Some (pos2, pos1) -> Some (pos1, pos2)
              | None -> None
          in
          if Option.is_none result then None
          else
            let pos1, pos2 = Option.value_exn result in
            let set_pos1 = Set.Poly.of_list pos1 in
            let set_pos2 = Set.Poly.of_list pos2 in
            let cond_fml =
              List.filter ~f:(fun (_, i) -> Set.Poly.mem set_pos1 i) (List.zip_index fmls1)
              |> List.map ~f:fst
              |> SimpleFormula.mk_branch_with_simplification_one inner_op
            in
            (* TODO: O(nlogn) -> O(n) *)
            let fml1 =
              List.zip_index fmls1
              |> List.filter ~f:(fun (_, i) -> Set.Poly.mem set_pos1 i |> not)
              |> List.map ~f:fst
              |> SimpleFormula.mk_branch_with_simplification_one inner_op
            in
            let fml2 =
              List.zip_index fmls2
              |> List.filter ~f:(fun (_, i) -> Set.Poly.mem set_pos2 i |> not)
              |> List.map ~f:fst
              |> SimpleFormula.mk_branch_with_simplification_one inner_op
            in
            Some (outer_op, cond_fml, fml1, fml2)
        | _ -> None

    let let_if fml = match let_if_opt fml with Some res -> res | None -> assert false
    let is_from_if fml = match let_if_opt fml with Some _ -> true | None -> false

    let optimize muclp =
      let preds, query = Problem.let_muclp muclp in
      let preds = Array.of_list preds in
      let pvar_to_pred: (Ident.pvar, Pred.t) Hashtbl.t = Hashtbl.Poly.create ~size:seed () in
      let pvar_to_nxtpvar: (Ident.pvar, Ident.pvar) Hashtbl.t = Hashtbl.Poly.create ~size:seed () in
      let pvar_to_epvar: (Ident.pvar, (bool list, Ident.pvar) Hashtbl.t) Hashtbl.t = Hashtbl.Poly.create ~size:seed () in
      let pvar_to_fpvar: (Ident.pvar, (bool list, Ident.pvar) Hashtbl.t) Hashtbl.t = Hashtbl.Poly.create ~size:seed () in
      let endpvar = Ident.mk_fresh_pvar () in
      let startpvar =
        if Array.length preds = 0 then endpvar
        else preds.(0) |> Pred.pvar_of
      in
      let ht_of_binder = function Formula.Forall -> pvar_to_fpvar | Formula.Exists -> pvar_to_epvar | _ -> assert false in
      (* init pvar_to_pred, pvar_to_nxtpvar, pvar_to_epvar, pvar_to_fpvar *)
      Array.iteri preds ~f:(fun i pred ->
          let _, pvar, bounds, _ = Pred.let_ pred in
          let nxtpvar =
            if i = Array.length preds - 1 then endpvar
            else Pred.pvar_of preds.(i+1)
          in
          Hashtbl.Poly.set pvar_to_nxtpvar ~key:pvar ~data:nxtpvar;
          Hashtbl.Poly.set pvar_to_pred ~key:pvar ~data:pred;
          Hashtbl.Poly.set pvar_to_epvar ~key:pvar ~data:(create_initial_pvar_to_xpvar bounds pvar);
          Hashtbl.Poly.set pvar_to_fpvar ~key:pvar ~data:(create_initial_pvar_to_xpvar bounds pvar));
      (* queue for erase_quantifiers_rep *)
      let queue = Queue.create () in
      (* add exists/forall pred of [pvar] pred and return the pvar of it *)
      let add_pred binder bound_flags pvar =
        (* construct new function *)
        let pred = Hashtbl.find_exn pvar_to_pred pvar in
        let fix, pvar, bounds, body = Pred.let_ pred in
        let pvar' = Ident.mk_fresh_pvar () in (* TODO *)
        Debug.print @@ lazy (sprintf "add_pred (pvar): %s. %s" (Formula.str_of_binder binder) (Ident.name_of_pvar pvar'));
        let bounds' =
          List.zip_exn bounds bound_flags
          |> List.filter ~f:(fun (_, bf) -> not bf)
          |> List.map ~f:fst
        in
        let qbounds =
          List.zip_exn bounds bound_flags
          |> List.filter ~f:snd
          |> List.map ~f:fst
        in
        let body' = Formula.mk_bind_if_bounded binder qbounds body ~info:Dummy in
        let pred = Pred.make fix pvar' bounds' body' in
        (* update pvar_to_nxtpvar: insert the pred just after [pvar] *)
        let nxtpvar = Hashtbl.Poly.find_exn pvar_to_nxtpvar pvar in
        Hashtbl.Poly.set pvar_to_nxtpvar ~key:pvar ~data:pvar';
        Hashtbl.Poly.set pvar_to_nxtpvar ~key:pvar' ~data:nxtpvar;
        (* update pvar_to_pred *)
        Hashtbl.Poly.set pvar_to_pred ~key:pvar' ~data:pred;
        (* update pvar_to_fpvar, pvar_to_epvar *)
        Hashtbl.Poly.set (Hashtbl.find_exn (ht_of_binder binder) pvar) ~key:bound_flags ~data:pvar';
        Hashtbl.Poly.set (ht_of_binder binder) ~key:pvar' ~data:(Hashtbl.Poly.create ~size:seed ());
        (* push to the queue for erase_quantifiers_rep *)
        Queue.enqueue queue pvar';
        (* return new pvar *)
        pvar'
      in
      let get_or_add_pred binder bound_flags pvar =
        Debug.print @@ lazy (sprintf "get_or_add_pred: %s. %s" (Formula.str_of_binder binder) (Ident.name_of_pvar pvar));
        let ht = ht_of_binder binder in
        let ht' = Hashtbl.Poly.find_or_add ~default:(fun _ -> Hashtbl.Poly.create ()) ht pvar in
        if not (Hashtbl.Poly.mem ht' bound_flags) then
          (add_pred binder bound_flags pvar: Ident.pvar) |> ignore;
        Hashtbl.find_exn ht' bound_flags
      in
      let binder_of_op = function Formula.Forall -> Formula.And | Formula.Exists -> Formula.Or | _ -> assert false in
      (* erase quantifiers in [binder] [bounds]. [fml] *)
      let rec erase_quantifiers_rep_bind binder bounds fml =
        let ftv = SimpleFormula.get_ftv fml in
        let bounds = List.filter ~f:(fun (tvar, _) -> Set.Poly.mem ftv tvar) bounds in
        if List.is_empty bounds then erase_quantifiers_rep fml
        else if SimpleFormula.is_branch fml then
        (*
          exists a. P(a) \/ P(b) -> (exists a. P(a)) \/ (exists a. P(b))
          exists a. P(a) /\ Q -> (exists a. P(a)) /\ Q
        *)
          let op, fmls = SimpleFormula.let_branch fml in
          if Stdlib.(binder_of_op binder = op) then
            (* exists a. P(a) \/ P(b) -> (exists a. P(a)) \/ (exists a. P(b)) *)
            SimpleFormula.mk_branch op @@
            List.map ~f:(erase_quantifiers_rep_bind binder bounds) fmls
          else if is_from_if fml then
          (*
            forall x. (P /\ Q) \/ (not P /\ R)
            -> forall x. (P => Q) /\ (not P => R)
            -> (forall x. not P \/ Q) /\ (forall x. P \/ R)

            exists x. (P \/ Q) /\ (not P \/ R)
            -> exists x. (not P => Q) /\ (P => R)
            -> exists x. (not P /\ Q) \/ (P /\ R)
            -> (exists x. not P /\ Q) \/ (exists x. P /\ R)
          *)
            let op', cond_fml, fml1, fml2 = let_if fml in
            assert (Stdlib.(op' = op));
            let fml1 =
              SimpleFormula.mk_branch_with_simplification_one op [SimpleFormula.neg cond_fml; fml1]
              |> erase_quantifiers_rep_bind binder bounds
            in
            let fml2 =
              SimpleFormula.mk_branch_with_simplification_one op [cond_fml; fml2]
              |> erase_quantifiers_rep_bind binder bounds
            in
            SimpleFormula.mk_branch_with_simplification_one (flip_op op) [fml1; fml2]
          else
          (*
            exists a. P(a) /\ Q
              -> (exists a. P(a)) /\ Q

            [exists a, b, c. P1(a, b) /\ P2(a) /\ P3(c)]
              -> [exists a, b, c. P1(a, b) /\ P2(a)] /\ [exists a, b, c. P3(c)]
              with UnionFind
          *)
            let bounds_tvar_set = List.map ~f:fst bounds |> Set.Poly.of_list in
            let ht = Hashtbl.Poly.create ~size:seed () in
            List.iteri fmls ~f:(fun i fml ->
                SimpleFormula.get_ftv fml
                |> Set.Poly.iter ~f:(fun tvar ->
                    if Set.Poly.mem bounds_tvar_set tvar then
                      let ids =
                        match Hashtbl.Poly.find ht tvar with
                        | Some ids -> ids
                        | None -> []
                      in
                      Hashtbl.Poly.set ht ~key:tvar ~data:(i :: ids)));
            let n = List.length fmls in
            (* Printf.printf "%s\n\n" (String.concat_map_list ~sep:"\n" ~f:(SimpleFormula.string_of) fmls); *)
            assert (n >= 2); (* because of simplification *)
            (* construct uf *)
            let uf = UnionFind.mk_size_uf ~size:n in
            Hashtbl.Poly.iter ht ~f:(fun ids ->
                let ids = Array.of_list ids in
                Array.iteri ids ~f:(fun i _ ->
                    if i+1 < Array.length ids then
                      UnionFind.unite ids.(i) ids.(i+1) uf));
            (* reconstruct the branch *)
            let fmls = Array.of_list fmls in
            UnionFind.get_groups uf
            |> List.map ~f:(fun ids ->
                let fmls' = List.map ~f:(fun id -> fmls.(id)) ids in
                match fmls' with
                | [fml'] -> erase_quantifiers_rep_bind binder bounds fml'
                (* try let_if *)
                | [_; _] ->
                  (* TODO *)
                  let fml' = SimpleFormula.mk_branch_with_simplification_one op fmls' in
                  if is_from_if fml' then erase_quantifiers_rep_bind binder bounds fml'
                  else
                    List.map ~f:erase_quantifiers_rep fmls'
                    |> SimpleFormula.mk_branch_with_simplification_one op
                    |> SimpleFormula.mk_bind_with_filter binder bounds
                | _ -> (* List.length fmls >= 2 *)
                  List.map ~f:erase_quantifiers_rep fmls'
                  |> SimpleFormula.mk_branch_with_simplification_one op
                  |> SimpleFormula.mk_bind_with_filter binder bounds)
            |> SimpleFormula.mk_branch_with_simplification_one op
        else if SimpleFormula.is_bind fml then
          let binder', bounds', fml' = SimpleFormula.let_bind fml in
          (* forall x. forall y. P -> forall x, y. P *)
          if Stdlib.(binder = binder') then (
            (* bounds, bounds' must be distinct *)
            (*let new_bounds = bounds @ bounds' in
              assert (Stdlib.(SimpleFormula.update_bounds bounds bounds' = new_bounds));*)
            let new_bounds = SimpleFormula.update_bounds bounds bounds' in
            erase_quantifiers_rep_bind binder new_bounds fml')
          else
          (*
            forall x. exists y. P
            1. process [exists y. P]
            2. if it's still of the form [forall x. exists y. P] then give up erasing (to avoid an infinite-loop)
            3. otherwise, continue to process erase_quantifiers_rep_bind
          *)
            let fml = erase_quantifiers_rep_bind binder' bounds' fml' in
            if SimpleFormula.is_bind fml then
              let binder', _, _ = SimpleFormula.let_bind fml in
              if Stdlib.(binder <> binder') then
                SimpleFormula.mk_bind_with_filter binder bounds fml
              else erase_quantifiers_rep_bind binder bounds fml
            else erase_quantifiers_rep_bind binder bounds fml
        else if SimpleFormula.is_app fml then
          let pvar, args = SimpleFormula.let_app fml in
          Debug.print @@ lazy (sprintf "erase_quantifiers_rep_bind(is_app):" ^ SimpleFormula.string_of fml);
          match bound_flags_of_app_opt bounds args with
          | Some bound_flags ->
            let pvar' = get_or_add_pred binder bound_flags pvar in
            let args =
              List.zip_exn args bound_flags
              |> List.filter ~f:(fun (_, bf) -> not bf)
              |> List.map ~f:fst
            in
            SimpleFormula.mk_app pvar' args
          | None -> SimpleFormula.mk_bind_with_filter binder bounds fml
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
          let binder, bounds, fml = SimpleFormula.let_bind fml in
          erase_quantifiers_rep_bind binder bounds fml
        else if SimpleFormula.is_atom fml then fml
        else assert false
      in
      let erase_quantifiers fml =
        let fml = SimpleFormula.of_formula fml in
        Debug.print @@ lazy (sprintf "erase_quantifiers: " ^ SimpleFormula.string_of fml);
        erase_quantifiers_rep fml |> SimpleFormula.formula_of
      in
      (* init queue *)
      Array.iter preds ~f:(fun pred ->
          let pvar = Pred.pvar_of pred in
          Queue.enqueue queue pvar);
      let query = erase_quantifiers query in
      while Fn.non Queue.is_empty queue do
        let pvar = Queue.dequeue_exn queue in
        let fix, pvar_confirm, bounds, body = Hashtbl.Poly.find_exn pvar_to_pred pvar |> Pred.let_ in
        assert (Stdlib.(pvar = pvar_confirm));
        Debug.print @@ lazy (sprintf "%s: " (Ident.name_of_pvar pvar));
        let body = erase_quantifiers body in
        let pred = Pred.make fix pvar bounds body in
        Hashtbl.Poly.set pvar_to_pred ~key:pvar ~data:pred
      done;
      (* reconstruct preds from startpvar, endpvar, pvar_to_nxtpvar, pvar_to_pred, processed_pvars(reached) *)
      let preds_queue = Queue.create () in
      let current_pvar = ref startpvar in
      while Stdlib.(!current_pvar <> endpvar) do
        let pred = Hashtbl.Poly.find_exn pvar_to_pred !current_pvar in
        Queue.enqueue preds_queue pred;
        current_pvar := Hashtbl.Poly.find_exn pvar_to_nxtpvar !current_pvar
      done;
      let preds = (*ToDo*)Queue.to_list preds_queue in
      Problem.make preds query
  end

  (* exists x. 0 <= x /\ x <= 100 -> true *)
  module CheckAndReplaceToTopOrBot : sig
    val optimize: is_print_for_debug:bool -> Problem.t -> Problem.t
  end = struct
    let bind_free_tvas_with_forall fml =
      let ftv = Formula.tvs_of fml in
      let bounds =
        ftv
        |> Set.Poly.map ~f:(fun tvar -> tvar, T_int.SInt) (* TODO *)
        |> Set.Poly.to_list
      in
      Formula.mk_forall_if_bounded bounds fml ~info:Dummy

    let gen_smt_solver timeout_milliseconds =
      let options = ["timeout", string_of_int timeout_milliseconds] in
      let ctx = Z3.mk_context options in
      let solver = Z3.Solver.mk_simple_solver ctx in
      solver, ctx

    let check_always_true ?(timeout_milliseconds=1000) ~is_print_for_debug fml =
      let fpv = Formula.pvs_of fml in
      if Fn.non Set.Poly.is_empty fpv then
        false
      else (
        if is_print_for_debug then (
          Debug.print @@ lazy "";
          Debug.print @@ lazy "[optimize][check_always_true]";
          Debug.print @@ lazy (Printf.sprintf "input: %s" (Formula.str_of fml));
        );
        (* x >= 10 -> forall (x: int). x >= 10 *)
        let fml = bind_free_tvas_with_forall fml in
        (* to smt format and solve it with z3 *)
        let solver, ctx = gen_smt_solver timeout_milliseconds in
        let fenv = Map.Poly.empty(*ToDo*)(*PCSP.Problem.fenv_of APCSP.problem*) in
        let dtenv = Set.Poly.empty(*ToDo*)(*Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx (PCSP.Problem.dtenv_of APCSP.problem)*) in
        let expr = Z3Smt.Z3interface.of_formula ctx [] [] fenv dtenv fml in
        if is_print_for_debug then
          Debug.print @@ lazy (Printf.sprintf "expr: %s" (Z3.Expr.to_string expr));
        try let z3result = Z3.Solver.check solver [expr] in
          if is_print_for_debug then
            (Debug.print @@ lazy (Printf.sprintf "Z3: %s" (Z3.Solver.string_of_status z3result));
             Debug.print @@ lazy "");
          match z3result with
          | Z3.Solver.SATISFIABLE -> true
          | _ -> false
        with
        | Z3.Error reason ->
          if is_print_for_debug then
            (Debug.print @@ lazy (Printf.sprintf "Z3: %s" reason);
             Debug.print @@ lazy "");
          (* timeout *)
          if is_print_for_debug then
            Debug.print @@ lazy (Printf.sprintf "Z3 Error: %s" reason);
          Out_channel.flush stderr;
          false)

    let rec replace_to_topbot ~is_print_for_debug fml =
      if Formula.is_binop fml then
        let binop, fml1, fml2, info = Formula.let_binop fml in
        let fml1 = replace_to_topbot ~is_print_for_debug fml1 in
        let fml2 = replace_to_topbot ~is_print_for_debug fml2 in
        Formula.mk_binop binop fml1 fml2 ~info
      else if Formula.is_unop fml then
        let unop, fml, info = Formula.let_unop fml in
        let fml = replace_to_topbot ~is_print_for_debug fml in
        Formula.mk_unop unop fml ~info
      else if Formula.is_atom fml then fml
      else if Formula.is_bind fml then
        if check_always_true ~is_print_for_debug fml then
          Formula.mk_atom (Atom.mk_true () ~info:Dummy) ~info:Dummy
        else if check_always_true ~is_print_for_debug (Evaluator.simplify_neg fml) then
          Formula.mk_atom (Atom.mk_false () ~info:Dummy) ~info:Dummy
        else
          let binder, bounds, fml, info = Formula.let_bind fml in
          let fml = replace_to_topbot ~is_print_for_debug fml in
          Formula.mk_bind binder bounds fml ~info
      else assert false

    let optimize ~is_print_for_debug muclp =
      let preds, query = Problem.let_muclp muclp in
      let query = replace_to_topbot ~is_print_for_debug query in
      let preds =
        List.map preds ~f:(fun pred ->
            let fix, pvar, args, body = Pred.let_ pred in
            let body = replace_to_topbot ~is_print_for_debug body in
            Pred.make fix pvar args body)
      in
      Problem.make preds query
  end

  module EraseConstVariables : sig
    val optimize: Problem.t -> Problem.t
  end = struct
    type vartype =
      | UnReached
      | Const of Z.t
      | NonConst

    let merge_vt vt1 vt2 =
      match (vt1, vt2) with
      | (UnReached, vt) | (vt, UnReached) -> vt
      | (NonConst, _) | (_, NonConst) -> NonConst
      | (Const x, Const y) ->
        if Z.(equal x y) then Const x else NonConst

    let is_const = function
      | Const _ -> true
      | _ -> false

    (* let string_of_vt = function
       | UnReached -> "unreached"
       | NonConst -> "nonconst"
       | Const x -> Printf.sprintf "const %s" (Z.to_string x) *)

    let seed = 1007

    let vt_of_pt ht_vt (pvar, tvar) =
      Hashtbl.Poly.find_exn (Hashtbl.Poly.find_exn ht_vt pvar) tvar

    let init_ht_vt muclp =
      let preds = Problem.preds_of muclp in
      let ht_vt: (Ident.pvar, (Ident.tvar, vartype) Hashtbl.t) Hashtbl.t = Hashtbl.Poly.create ~size:seed () in
      List.iter preds ~f:(fun pred ->
          let _, pvar, bounds, _ = Pred.let_ pred in
          let ht = Hashtbl.Poly.create ~size:seed () in
          List.iter ~f:(fun (tvar, _) -> Hashtbl.Poly.set ht ~key:tvar ~data:UnReached) bounds;
          Hashtbl.Poly.set ht_vt ~key:pvar ~data:ht);
      ht_vt

    let rec nonconst_update ht_vt graph pt =
      let pvar, tvar = pt in
      Hashtbl.Poly.set (Hashtbl.Poly.find_exn ht_vt pvar) ~key:tvar ~data:NonConst;
      Hashtbl.Poly.find_exn graph pt
      |> List.iter ~f:(fun (nxt_pvar, nxt_tvar, _) ->
          let nxt_pt = (nxt_pvar, nxt_tvar) in
          let env = Hashtbl.Poly.find_exn ht_vt nxt_pvar in
          if Stdlib.(<>) (Hashtbl.Poly.find_exn env nxt_tvar) NonConst
          then nonconst_update ht_vt graph nxt_pt)

    let rec vt_of_term env term =
      if Term.is_var term then
        let (tvar, _), _ = Term.let_var term in
        if Hashtbl.Poly.mem env tvar then Hashtbl.Poly.find_exn env tvar else NonConst
      else if Term.is_app term then
        let funsym, args, _ = Term.let_app term in
        let arg_vts = List.map ~f:(vt_of_term env) args in
        if List.exists ~f:(Stdlib.(=) NonConst) arg_vts then NonConst
        else if List.exists ~f:(Stdlib.(=) UnReached) arg_vts then UnReached
        else
          match funsym, arg_vts with
          | (T_int.Int x, []) -> Const x
          | (T_int.Add, [Const x; Const y]) -> Const (Z.(+) x y)
          | (T_int.Sub, [Const x; Const y]) -> Const (Z.(-) x y)
          | (T_int.Mult, [Const x; Const y]) -> Const (Z.( * ) x y)
          | (T_int.Neg, [Const x]) -> Const (Z.neg x)
          | _ -> failwith "EraseConstVariables.vt_of_term: illegal funapp"
      else assert false

    let value_of_const_term term =
      let dummy_ht = Hashtbl.Poly.create ~size:seed () in
      match vt_of_term dummy_ht term with
      | Const x -> x
      | _ -> assert false

    let rec get_vargraph_rep (tvars_of_pvar: Ident.pvar -> Ident.tvar list) (pvar: Ident.pvar) arg_tvars consts nonconsts graph fml =
      if Formula.is_unop fml then
        let _, fml, _ = Formula.let_unop fml in
        get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph fml
      else if Formula.is_binop fml then
        let _, fml1, fml2, _ = Formula.let_binop fml in
        let consts, nonconsts = get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph fml1 in
        get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph fml2
      else if Formula.is_atom fml then
        let atom, _ = Formula.let_atom fml in
        if Atom.is_pvar_app atom then
          let pvar', _, args, _ = Atom.let_pvar_app atom in
          let tvars = tvars_of_pvar pvar' in
          List.zip_exn args tvars
          |> List.fold_left ~init:(consts, nonconsts) ~f:(fun (consts, nonconsts) (arg, tvar') ->
              let ftv = Term.tvs_of arg in
              if Set.Poly.is_empty ftv then
                let value = value_of_const_term arg in
                (pvar', tvar', value) :: consts, nonconsts
              else if Set.Poly.diff ftv arg_tvars |> Set.Poly.is_empty then (
                Set.Poly.inter ftv arg_tvars
                |> Set.Poly.to_list
                |> List.iter ~f:(fun tvar ->
                    let pt = (pvar, tvar) in
                    let edges = Hashtbl.Poly.find_exn graph pt in
                    Hashtbl.Poly.set graph ~key:pt ~data:((pvar', tvar', arg) :: edges));
                consts, nonconsts)
              else consts, (pvar', tvar') :: nonconsts)
        else consts, nonconsts
      else if Formula.is_bind fml then
        let _, bounds, fml, _ = Formula.let_bind fml in
        let bound_tvars = List.map ~f:fst bounds |> Set.Poly.of_list in
        let arg_tvars = Set.Poly.diff arg_tvars bound_tvars in
        get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph fml
      else assert false

    let tvars_of_pvar_of_muclp muclp =
      let preds, _ = Problem.let_muclp muclp in
      let tvars_of_pvar_ht = Hashtbl.Poly.create ~size:seed () in
      List.iter preds ~f:(fun pred ->
          let _, pvar, bounds, _ = Pred.let_ pred in
          let tvars = List.map ~f:fst bounds in
          Hashtbl.Poly.set tvars_of_pvar_ht ~key:pvar ~data:tvars);
      fun pvar -> Hashtbl.find_exn tvars_of_pvar_ht pvar

    let get_vargraph muclp =
      let preds, query = Problem.let_muclp muclp in
      let dummy_pvar = Ident.Pvar "dummy" in
      let consts: (Ident.pvar * Ident.tvar * Z.t) list = [] in
      let nonconsts: (Ident.pvar * Ident.tvar) list = [] in
      let graph: (Ident.pvar * Ident.tvar, (Ident.pvar * Ident.tvar * Term.t) list) Hashtbl.Poly.t = Hashtbl.Poly.create ~size:seed () in
      let tvars_of_pvar = tvars_of_pvar_of_muclp muclp in
      List.iter ~f:(fun pvar ->
          List.iter ~f:(fun tvar ->
              Hashtbl.Poly.set graph ~key:(pvar, tvar) ~data:[])
            (tvars_of_pvar pvar))
        (Pred.pvars_of_list preds);
      let consts, nonconsts =
        List.fold_left preds
          ~init:(get_vargraph_rep tvars_of_pvar dummy_pvar Set.Poly.empty consts nonconsts graph query)
          ~f:(fun (consts, nonconsts) pred ->
              let _, pvar, bounds, body = Pred.let_ pred in
              let arg_tvars = List.map ~f:fst bounds |> Set.Poly.of_list in
              get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph body)
      in
      consts, nonconsts, graph

    let gen_ht_vt muclp =
      let ht_vt = init_ht_vt muclp in
      let consts, nonconsts, graph = get_vargraph muclp in
      (* Printf.printf "nonconsts: %s\n" (String.concat_map_list ~sep:" " ~f:(fun (pvar, tvar) -> Printf.sprintf "(%s, %s)" (Ident.name_of_pvar pvar) (Ident.name_of_tvar tvar)) nonconsts); *)
      List.iter ~f:(fun pt -> nonconst_update ht_vt graph pt) nonconsts;
      let queue = Queue.create () in
      let update_ht_vt pt value =
        let current_vt = vt_of_pt ht_vt pt in
        if Stdlib.(current_vt <> NonConst) then
          let new_vt = merge_vt current_vt (Const value) in
          if Stdlib.(new_vt <> current_vt) then (
            let pvar, tvar = pt in
            Hashtbl.Poly.set (Hashtbl.find_exn ht_vt pvar) ~key:tvar ~data:new_vt;
            if Stdlib.(new_vt = NonConst) then nonconst_update ht_vt graph pt
            else Queue.enqueue queue pt
          )
      in
      List.iter ~f:(fun (pvar, tvar, value) -> update_ht_vt (pvar, tvar) value) consts;
      while Fn.non Queue.is_empty queue do
        let pt = Queue.dequeue_exn queue in
        let pvar, _ = pt in
        (* Printf.printf "%s, %s: %s\n" (Ident.name_of_pvar pvar) (Ident.name_of_tvar tvar) (string_of_vt (vt_of_pt ht_vt pt)); flush stdout; *)
        if Stdlib.(vt_of_pt ht_vt pt <> NonConst) then
          Hashtbl.Poly.find_exn graph pt
          |> List.iter ~f:(fun (nxt_pvar, nxt_tvar, term) ->
              let nxt_pt = (nxt_pvar, nxt_tvar) in
              let current_vt = vt_of_pt ht_vt nxt_pt in
              if Stdlib.(current_vt <> NonConst) then
                let env = Hashtbl.Poly.find_exn ht_vt pvar in
                (* it's ok *)
                let vt = vt_of_term env term in
                match vt with
                | NonConst -> nonconst_update ht_vt graph nxt_pt
                | Const value -> update_ht_vt nxt_pt value
                | UnReached -> ());
      done;
      ht_vt

    let filter_nonconst_args tvars_of_pvar ht_vt fml =
      Pred.replace_app (fun fml ->
          let atom, info = Formula.let_atom fml in
          let pvar, _, args, info' = Atom.let_pvar_app atom in
          let ht_vt_of_tvar = Hashtbl.Poly.find_exn ht_vt pvar in
          let tvars = tvars_of_pvar pvar in
          let args =
            List.zip_exn args tvars
            |> List.filter ~f:(fun (_, tvar) -> Hashtbl.Poly.find_exn ht_vt_of_tvar tvar |> is_const |> not)
            |> List.map ~f:fst
          in
          Formula.mk_atom (Atom.mk_pvar_app pvar (List.map ~f:(fun _ -> T_int.SInt) args(* TODO *)) args ~info:info') ~info)
        fml

    let optimize muclp =
      (* Printf.printf "[ReplaceConstVariables]\n";
         Printf.printf "Input: %s\n\n" (Hesutil.str_of_muclp muclp); *)
      let ht_vt = gen_ht_vt muclp in
      let preds, query = Problem.let_muclp muclp in
      let tvars_of_pvar = tvars_of_pvar_of_muclp muclp in
      let query = filter_nonconst_args tvars_of_pvar ht_vt query in
      let preds =
        List.map preds ~f:(fun pred ->
            let fix, pvar, bounds, fml = Pred.let_ pred in
            let ht_vt_of_tvar = Hashtbl.Poly.find_exn ht_vt pvar in
            let subst =
              List.fold_left bounds ~init:Map.Poly.empty ~f:(fun subst (tvar, _) ->
                  match Hashtbl.Poly.find_exn ht_vt_of_tvar tvar with
                  | Const x -> Map.Poly.set subst ~key:tvar ~data:(T_int.mk_int x ~info:Dummy)
                  | _ -> subst)
            in
            let fml =
              Formula.subst subst fml
              |> filter_nonconst_args tvars_of_pvar ht_vt
            in
            let bounds =
              List.filter ~f:(fun (tvar, _) -> Hashtbl.Poly.find_exn ht_vt_of_tvar tvar |> is_const |> not) bounds
            in
            Pred.make fix pvar bounds fml)
      in
      Problem.make preds query
  end

  let optimize_formula muclp =
    let preds, query = Problem.let_muclp muclp in
    let preds =
      List.map preds ~f:(fun pred ->
          let fix, pvar, bounds, body = Pred.let_ pred in
          let body = Formula.elim_unused_bounds body in
          Pred.make fix pvar bounds body)
    in
    let query = Formula.elim_unused_bounds query in
    Problem.make preds query

  let optimize ?(is_print_for_debug=false) muclp =
    if config.enable then
      muclp
      |> optimize_formula
      |> InlineExtension.optimize
      |> EraseQuantifiers.optimize
      |> EraseUnreachedPredicates.optimize
      |> EraseConstVariables.optimize
      |> CheckAndReplaceToTopOrBot.optimize ~is_print_for_debug
      |> Problem.simplify
      |> InlineExtension.optimize
    else muclp |> optimize_formula
end

let make (config : Config.t) =
  (module Make (struct let config = config end) : OptimizerType)
