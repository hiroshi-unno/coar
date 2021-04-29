open Core
open LogicOld


(** ToDo: this seems not capture avoiding *)
(*val move_quantifiers_to_front: Formula.t -> Formula.t*)
let move_quantifiers_to_front fml =
  let rec rename_in_formula used_names replace_env fml =
    if Formula.is_atom fml then
      let atom, info = Formula.let_atom fml in
      let atom = rename_in_atom replace_env atom in
      Formula.mk_atom atom ~info, used_names, replace_env
    else if Formula.is_binop fml then
      let binop, left, right, info = Formula.let_binop fml in
      let left, used_names, replace_env = rename_in_formula used_names replace_env left in
      let right, used_names, replace_env = rename_in_formula used_names replace_env right in
      Formula.mk_binop binop left right ~info, used_names, replace_env
    else if Formula.is_unop fml then
      let unop, body, info = Formula.let_unop fml in
      let body, used_names, replace_env = rename_in_formula used_names replace_env body in
      Formula.mk_unop unop body ~info, used_names, replace_env
    else if Formula.is_bind fml then
      let binder, bounds, body, info = Formula.let_bind fml in
      let new_bounds = SortEnv.map bounds
          ~f:(fun (tvar, sort) ->
              let var_name = ref (Ident.name_of_tvar tvar) in
              while Env.has !var_name used_names do
                var_name := !var_name ^ "'"
              done;
              Ident.Tvar !var_name, sort)
      in
      let new_bound_tvars, _ = Core.List.unzip new_bounds in
      let bound_tvars = SortEnv.args_of bounds in
      let used_names = Env.update (List.map ~f:(fun tvar -> Ident.name_of_tvar tvar, ()) bound_tvars) used_names in
      let replace_env = Env.update (Core.List.zip_exn bound_tvars new_bound_tvars) replace_env in
      let body, used_names, replace_env = rename_in_formula used_names replace_env body in
      Formula.mk_bind binder (SortEnv.of_list new_bounds) body ~info, used_names, replace_env
    else
      assert false
  and rename_in_atom replace_env atom =
    if Atom.is_true atom || Atom.is_false atom then
      atom
    else if Atom.is_app atom then
      let pred, args, info = Atom.let_app atom in
      let pred = rename_in_predicate pred in
      let args = List.map ~f:(rename_in_term replace_env) args in
      Atom.mk_app pred args ~info
    else
      assert false
  and rename_in_predicate pred =
    if Predicate.is_fix pred then
      let fix, pvar, args, body = Predicate.let_fix pred in
      let body = rename body in
      Predicate.mk_fix fix pvar args body
    else if Predicate.is_psym pred || Predicate.is_var pred then
      pred
    else
      assert false
  and rename_in_term replace_env term =
    if Term.is_var term then
      let tvar, sort, info = Term.let_var term in
      Term.mk_var (Env.lookup_exn tvar replace_env) sort ~info
    else if Term.is_app term then
      let funsym, args, info = Term.let_app term in
      Term.mk_fsym_app funsym (List.map ~f:(rename_in_term replace_env) args) ~info
    else
      assert false
  and rename fml =
    let fv = Formula.tvs_of fml |> Core.Set.Poly.to_list in
    let fv_names = Env.update (List.map ~f:(fun tvar -> (Ident.name_of_tvar tvar, ())) fv) Env.empty in
    let fml, _, _ = rename_in_formula fv_names (Core.List.zip_exn fv fv) fml in
    fml
  in
  let mk_bind binder bounds fml = if SortEnv.is_empty bounds then fml else Formula.mk_bind binder bounds fml
  in
  let rec move_to_front_in_formula fml =
    if Formula.is_atom fml then
      let atom, info = Formula.let_atom fml in
      Formula.mk_atom (move_to_front_in_atom atom) ~info, SortEnv.empty, SortEnv.empty
    else if Formula.is_neg fml then
      let negop, fml, info = Formula.let_unop fml in
      let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
      Formula.mk_unop negop fml ~info, exists_bounds, forall_bounds
    else if Formula.is_imply fml then
      (* TODO *)
      failwith (Formula.str_of fml ^ " not supported\n")
    else if Formula.is_iff fml then
      (* TODO *)
      failwith (Formula.str_of fml ^ " not supported\n")
    else if Formula.is_and fml || Formula.is_or fml then
      let binop, left_fml, right_fml, info = Formula.let_binop fml in
      let left_fml, left_forall_bounds, left_exists_bounds = move_to_front_in_formula left_fml in
      let right_fml, right_forall_bounds, right_exists_bounds = move_to_front_in_formula right_fml in
      Formula.mk_binop binop left_fml right_fml ~info,
      SortEnv.append left_forall_bounds right_forall_bounds,
      SortEnv.append left_exists_bounds right_exists_bounds
    else if Formula.is_bind fml then
      let binder, bounds, fml, _ = Formula.let_bind fml in
      let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
      let binder_bounds, another_bounds =
        match binder with
        | Formula.Forall -> forall_bounds, exists_bounds
        | Formula.Exists -> exists_bounds, forall_bounds
        | Formula.Random _ -> assert false
      in
      let fml = mk_bind (Formula.flip_quantifier binder) another_bounds fml in
      let another_bounds = SortEnv.empty in
      let binder_bounds = SortEnv.append bounds binder_bounds in
      let forall_bounds, exists_bounds =
        match binder with
        | Formula.Forall -> binder_bounds, another_bounds
        | Formula.Exists -> another_bounds, binder_bounds
        | Formula.Random _ -> assert false
      in
      fml, forall_bounds, exists_bounds
    else
      assert false
  and move_to_front_in_atom atom =
    if Atom.is_app atom then
      let pred, args, info = Atom.let_app atom in
      Atom.mk_app (move_to_front_in_predicate pred) args ~info
    else if Atom.is_true atom || Atom.is_false atom then
      atom
    else
      assert false
  and move_to_front_in_predicate pred =
    if Predicate.is_fix pred then
      let fix, pvar, arg_sorts, body = Predicate.let_fix pred in
      Predicate.mk_fix fix pvar arg_sorts (move_to_front body)
    else if Predicate.is_psym pred || Predicate.is_var pred then
      pred
    else
      assert false
  and move_to_front fml =
    let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
    mk_bind Formula.Forall forall_bounds
    @@ mk_bind Formula.Exists exists_bounds fml
  in
  move_to_front @@ rename fml

let rec remove_unused_bounds fml =
  if Formula.is_atom fml then
    fml (* TODO *)
  else if Formula.is_and fml then
    let fml1, fml2, info = Formula.let_and fml in
    Formula.mk_and
      (remove_unused_bounds fml1)
      (remove_unused_bounds fml2)
      ~info
  else if Formula.is_or fml then
    let fml1, fml2, info = Formula.let_or fml in
    Formula.mk_or
      (remove_unused_bounds fml1)
      (remove_unused_bounds fml2)
      ~info
  else if Formula.is_bind fml then
    let binder, bounds, fml, info = Formula.let_bind fml in
    let fml = remove_unused_bounds fml in
    Formula.bind binder bounds fml ~info
  else
    failwith (Formula.str_of fml ^ " not supported\n")
