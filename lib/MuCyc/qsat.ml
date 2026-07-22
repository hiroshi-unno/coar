open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

type theory = QBF | LRA | LIA | PLRA | PLIA
type player = SAT | UNSAT

let decide_theory quantifiers =
  let sortlist =
    List.fold quantifiers ~init:[] ~f:(fun l (_binder, sortenv) ->
        let _, sort = List.unzip sortenv in
        l @ sort)
  in
  let rec loop theory = function
    | [] -> theory
    | T_bool.SBool :: tl -> loop theory tl
    | T_int.SInt :: tl -> (
        match theory with QBF | LIA -> loop LIA tl | _ -> assert false)
    | T_real.SReal :: tl -> (
        match theory with QBF | LRA -> loop LRA tl | _ -> assert false)
    | _ -> assert false
  in
  let theory = loop QBF sortlist in
  if List.exists quantifiers ~f:(fst >> Formula.is_random) then
    match theory with LRA -> PLRA | LIA -> PLIA | _ -> assert false
  else theory

let level_exists atom vlevel =
  Set.fold ~init:Z.zero (Atom.fvs_of atom) ~f:(fun level tvar ->
      match Map.Poly.find vlevel tvar with
      | Some (l, _) -> if Z.is_odd l then Z.max level l else level
      | None -> level)

let level_forall atom vlevel =
  Set.fold ~init:Z.zero (Atom.fvs_of atom) ~f:(fun level tvar ->
      match Map.Poly.find vlevel tvar with
      | Some (l, _) -> if Z.is_even l then Z.max level l else level
      | None -> level)

let level_j j = if Z.is_odd j then level_exists else level_forall

let rec level_j_atom j vlevel = function
  | Formula.Atom (a, _) -> level_j j a vlevel
  | UnaryOp (Not, phi, _) -> level_j_atom j vlevel phi
  | _ -> assert false

let strategy ~print model j atoms vlevel =
  if Map.Poly.is_empty model then Set.Poly.singleton @@ Formula.mk_true ()
  else
    Set.filter atoms ~f:(fun a ->
        Z.Compare.(level_j j a vlevel <= Z.(j - Z.of_int 2)))
    |> Set.Poly.map ~f:(Mbp.sign ~print model)

module type MBP_TYPE = sig
  val let_sort : string Set.Poly.t -> TermSubst.t -> TermSubst.t

  val model_based_projection :
    print:(string lazy_t -> unit) ->
    TermSubst.t ->
    Ident.tvar ->
    Atom.t Set.Poly.t ->
    Atom.t Set.Poly.t
end

let rec bool_var_atom = function
  | Formula.UnaryOp (Not, UnaryOp (Not, phi, _), _) -> bool_var_atom phi
  | Atom (App (Predicate.Var (x, _), [], _), _) ->
      First (Atom.of_bool_var (Ident.pvar_to_tvar x))
  | UnaryOp (Not, Atom (App (Predicate.Var (x, _), [], _), _), _) ->
      First (Atom.of_neg_bool_var (Ident.pvar_to_tvar x))
  | Atom ((App (Predicate.Psym T_bool.(Eq | Neq), [ t1; _t2 ], _) as atm), _)
    when T_bool.is_sbool t1 ->
      First atm
  | Atom (atm, _) -> Second atm
  | UnaryOp (Not, Atom (atm, _), _) ->
      Second
        (match Atom.negate atm with
        | None -> failwith "[bool_var_atom]"
        | Some neg_atm -> neg_atm)
  | _ -> assert false

(*This QSAT supports bool, LIA and LRA.*)
module QSAT (A : MBP_TYPE) = struct
  let rec level_of level = function
    | [] -> Map.Poly.empty
    | (Formula.Exists, sortenv) :: tl ->
        let level = if Z.is_odd level then level else Z.succ level in
        let map =
          Map.Poly.map (Map.Poly.of_alist_exn sortenv) ~f:(fun s -> (level, s))
        in
        Map.force_merge map (level_of level tl)
    | (Forall, sortenv) :: tl ->
        let level = if Z.is_even level then level else Z.succ level in
        let map =
          Map.Poly.map (Map.Poly.of_alist_exn sortenv) ~f:(fun s -> (level, s))
        in
        Map.force_merge map (level_of level tl)
    | (Random _, _) :: _ -> assert false

  let rec mbp ~print ~config model j vlevel fmls =
    let mbp_main vs fmls =
      let non_bool_atms, bool_atms =
        Set.fold fmls ~init:(Set.Poly.empty, Set.Poly.empty)
          ~f:(fun (c, bc) phi ->
            match bool_var_atom phi with
            | First bool_atm -> (c, Set.add bc bool_atm)
            | Second non_bool_atm -> (Set.add c non_bool_atm, bc))
      in
      print
      @@ lazy
           (sprintf "[mbp_main] vs: %s"
           @@ String.concat_map_list ~sep:", " ~f:Ident.name_of_tvar
           @@ Map.Poly.keys vs);
      print @@ lazy (sprintf "[mbp_main] j: %s" (Z.to_string j));
      print
      @@ lazy
           (sprintf "[mbp_main] non_bool_atms: %s"
           @@ String.concat_map_set ~sep:", " ~f:Atom.str_of non_bool_atms);
      print
      @@ lazy
           (sprintf "[mbp_main] bool_atms: %s"
           @@ String.concat_map_set ~sep:", " ~f:Atom.str_of bool_atms);
      print @@ lazy "";
      let non_bool_atms, bool_atms =
        Map.Poly.fold vs ~init:(non_bool_atms, bool_atms)
          ~f:(fun ~key:tvar ~data:(_, sort) (non_bool_atms, bool_atms) ->
            if Term.is_bool_sort sort then
              ( non_bool_atms,
                Mbp.Boolean.model_based_projection ~print model tvar bool_atms
              )
            else
              ( A.model_based_projection ~print model tvar non_bool_atms,
                bool_atms ))
      in
      Set.Poly.map ~f:Evaluator.simplify_atom
      @@ Set.union non_bool_atms bool_atms
    in
    let jformulas =
      let vs_tail =
        Map.Poly.filter vlevel ~f:(fun (level, _) ->
            Z.Compare.(level >= Z.(j - Z.one)))
      in
      mbp_main vs_tail fmls
    in
    let index =
      Set.fold jformulas
        ~init:(if Z.is_odd j then Z.one else Z.of_int 2)
        ~f:(fun i jformula -> Z.max i (level_j_atom j vlevel jformula))
    in
    let jformula = Formula.and_of @@ Set.to_list jformulas in
    match config.Config.backtrack_strategy with
    | Original -> (jformula, index)
    | Chronological -> (jformula, Z.(j - Z.of_int 2))
    | NonChronological ->
        if Z.Compare.(index = Z.(j - Z.of_int 2)) then (jformula, index)
        else
          let vs =
            Map.Poly.filter vlevel ~f:(fun (level, _) ->
                Z.Compare.(level >= Z.(index + Z.one)))
          in
          (Formula.and_of @@ Set.to_list @@ mbp_main vs jformulas, index)
    | NonChronologicalRec ->
        if Z.Compare.(index = Z.(j - Z.of_int 2)) then (jformula, index)
        else mbp ~print ~config model Z.(index + Z.of_int 2) vlevel jformulas

  let add_atoms atoms1 atoms2 =
    let neg_atoms1 =
      Set.Poly.filter_map atoms1 ~f:(fun atm ->
          Option.(Atom.negate atm >>= (Normalizer.normalize_atom >> return)))
    in
    Set.union atoms1
    @@ Set.filter ~f:(Set.mem neg_atoms1 >> not)
    @@ Set.Poly.map ~f:Normalizer.normalize_atom atoms2

  let update_frames ~config frames atoms j jformula =
    let newframes =
      if config.Config.update_all_frames_j_and_after then
        Map.Poly.mapi frames ~f:(fun ~key ~data ->
            if Z.Compare.(key < j) then data
            else if Z.(is_even (key - j)) then
              Formula.(mk_and data (negate jformula))
            else data)
      else
        Map.Poly.update frames j ~f:(function
          | Some frame -> Formula.(mk_and frame (negate jformula))
          | None -> assert false)
    in
    let newatoms =
      let jatoms =
        let pos, neg = Formula.atoms_of jformula in
        Set.union pos neg
      in
      Map.Poly.mapi atoms ~f:(fun ~key ~data ->
          if
            (not config.Config.update_only_atoms_j_and_before)
            || Z.Compare.(key <= j)
          then add_atoms data jatoms
          else data)
    in
    (newframes, newatoms)

  let solve ~print ~config quantifiers f =
    print
    @@ lazy
         (String.concat_map_list ~sep:" " quantifiers ~f:(fun (binder, senv) ->
              Formula.str_of_binder binder
              ^ str_of_sort_env_list Term.str_of_sort senv));
    print @@ lazy "";
    print @@ lazy (Formula.str_of f);
    let vlevel = level_of Z.one quantifiers in
    let names = Set.Poly.singleton "main" in
    let frames =
      Map.Poly.add_exn ~key:(Z.of_int 2) ~data:(Formula.negate f)
        (Map.Poly.singleton Z.one f)
    in
    let atoms0 =
      let pos, neg = Formula.atoms_of f in
      add_atoms Set.Poly.empty (Set.union pos neg)
    in
    let atoms =
      Map.Poly.add_exn ~key:(Z.of_int 2) ~data:atoms0
        (Map.Poly.singleton Z.one atoms0)
    in
    let fenv = (*TODO: generate fenv*) Map.Poly.empty in
    let rec loop model j frames atoms names =
      let frame_j = Map.Poly.find_exn frames j in
      print
      @@ lazy
           (sprintf "\n[solve] current frame @ %s: %s" (Z.to_string j)
              (Formula.str_of frame_j));
      let strat_j =
        strategy ~print model j (Map.Poly.find_exn atoms j) vlevel
      in
      print
      @@ lazy
           (sprintf "[solve] strategy @ %s: %s" (Z.to_string j)
              (String.concat_map_set ~sep:", " ~f:Formula.str_of strat_j));
      let pvar_clause_map, names =
        List.foldi (Set.to_list strat_j)
          ~init:(Map.Poly.singleton "main" frame_j, names)
          ~f:(fun i (map, names) fml ->
            let name = sprintf "|#S_%s|" (string_of_int i) in
            (Map.Poly.add_exn map ~key:name ~data:fml, Set.add names name))
      in
      match
        Z3Smt.Z3interface.check_sat_unsat_core ~id:None fenv pvar_clause_map
      with
      | `Unsat core ->
          if Z.Compare.(j = Z.one) then UNSAT
          else if Z.Compare.(j = Z.of_int 2) then SAT
          else
            let core =
              List.filter_opt
              @@ List.map core ~f:(function
                   | "main" -> None
                   | v -> Map.Poly.find pvar_clause_map v)
            in
            print
            @@ lazy
                 (sprintf "[solve] unsat core: %s"
                 @@ String.concat_map_list ~sep:", " ~f:Formula.str_of core);
            print @@ lazy (sprintf "[solve] model: %s" (TermSubst.str_of model));
            let jformula, j =
              mbp ~print ~config model j vlevel (Set.Poly.of_list core)
            in
            let jformula =
              Evaluator.simplify @@ Normalizer.normalize jformula
            in
            print
            @@ lazy
                 (sprintf "[solve] jformula: %s @ %s" (Formula.str_of jformula)
                    (Z.to_string j));
            let frames, atoms = update_frames ~config frames atoms j jformula in
            loop Map.Poly.empty j frames atoms names
      | `Sat model ->
          let model =
            let model =
              A.let_sort names @@ Map.Poly.of_alist_exn @@ remove_dontcare model
            in
            Map.Poly.fold vlevel ~init:model
              ~f:(fun ~key ~data:(_, sort) model ->
                match Map.Poly.find model key with
                | Some _ -> model
                | None -> Map.Poly.add_exn model ~key ~data:(Term.mk_dummy sort))
          in
          print
          @@ lazy (sprintf "[solve] new model: %s" (TermSubst.str_of model));
          let frames =
            Map.Poly.update frames (Z.succ j) ~f:(function
              | Some frame -> frame
              | None ->
                  if config.Config.reuse_prev_frame then
                    Map.Poly.find_exn frames (Z.pred j)
                  else if Z.is_odd (Z.succ j) then f
                  else Formula.negate f)
          in
          let atoms =
            Map.Poly.update atoms (Z.succ j) ~f:(function
              | Some atoms -> atoms
              | None ->
                  if config.Config.update_only_atoms_j_and_before then atoms0
                  else Map.Poly.find_exn atoms j)
          in
          loop model (Z.succ j) frames atoms names
      | _ -> assert false
    in
    loop Map.Poly.empty Z.one frames atoms names
end
