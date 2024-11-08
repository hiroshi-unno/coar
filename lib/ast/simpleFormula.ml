open Core
open Common.Ext
open Common.Combinator
open LogicOld

type t =
  | ForallNode of sort_env_list * t
  | ExistsNode of sort_env_list * t
  | AndNode of t list
  | OrNode of t list
  | TopNode of unit
  | BotNode of unit
  | CondNode of pred_sym * Term.t list
  | AppNode of Ident.pvar * Term.t list

let mk_and fmls = AndNode fmls
let mk_or fmls = OrNode fmls
let mk_forall bounds fml = ForallNode (bounds, fml)
let mk_exists bounds fml = ExistsNode (bounds, fml)
let mk_top () = TopNode ()
let mk_bot () = BotNode ()
let mk_cond psym args = CondNode (psym, args)
let mk_app pvar args = AppNode (pvar, args)

let mk_branch binop fmls =
  match binop with
  | Formula.And -> mk_and fmls
  | Formula.Or -> mk_or fmls
  | _ -> failwith @@ "SimpleFormula.mk_binop: invalid binop"

let mk_bind binder bounds fml =
  match binder with
  | Formula.Forall -> mk_forall bounds fml
  | Formula.Exists -> mk_exists bounds fml
  | _ -> assert false

let is_and = function AndNode _ -> true | _ -> false
let is_or = function OrNode _ -> true | _ -> false
let is_forall = function ForallNode _ -> true | _ -> false
let is_exists = function ExistsNode _ -> true | _ -> false
let is_top = function TopNode _ -> true | _ -> false
let is_bot = function BotNode _ -> true | _ -> false
let is_cond = function CondNode _ -> true | _ -> false
let is_app = function AppNode _ -> true | _ -> false
let is_branch = function AndNode _ | OrNode _ -> true | _ -> false
let is_bind = function ForallNode _ | ExistsNode _ -> true | _ -> false

let is_atom = function
  | TopNode _ | BotNode _ | CondNode _ | AppNode _ -> true
  | _ -> false

let let_and = function AndNode fmls -> fmls | _ -> assert false
let let_or = function OrNode fmls -> fmls | _ -> assert false

let let_forall = function
  | ForallNode (bounds, fml) -> (bounds, fml)
  | _ -> assert false

let let_exists = function
  | ExistsNode (bounds, fml) -> (bounds, fml)
  | _ -> assert false

let let_cond = function
  | CondNode (psym, args) -> (psym, args)
  | _ -> assert false

let let_app = function
  | AppNode (pvar, args) -> (pvar, args)
  | _ -> assert false

let is_certain_branch op = function
  | AndNode _ -> Stdlib.(op = Formula.And)
  | OrNode _ -> Stdlib.(op = Formula.Or)
  | _ -> false

let let_branch = function
  | AndNode fmls -> (Formula.And, fmls)
  | OrNode fmls -> (Formula.Or, fmls)
  | _ -> assert false

let let_bind = function
  | ForallNode (args, fml) -> (Formula.Forall, args, fml)
  | ExistsNode (args, fml) -> (Formula.Exists, args, fml)
  | _ -> assert false

let rec get_ftv = function
  | AndNode fmls | OrNode fmls ->
      List.map ~f:get_ftv fmls
      |> List.fold_left ~f:Set.union ~init:Set.Poly.empty
  | ForallNode (bounds, fml) | ExistsNode (bounds, fml) ->
      Set.diff (get_ftv fml) (List.map ~f:fst bounds |> Set.Poly.of_list)
  | CondNode (_, args) | AppNode (_, args) ->
      List.map ~f:Term.tvs_of args
      |> List.fold_left ~f:Set.union ~init:Set.Poly.empty
  | TopNode () | BotNode () -> Set.Poly.empty

let rec get_fpv = function
  | AndNode fmls | OrNode fmls ->
      List.map ~f:get_fpv fmls
      |> List.fold_left ~f:Set.union ~init:Set.Poly.empty
  | ForallNode (_, fml) | ExistsNode (_, fml) -> get_fpv fml
  | AppNode (pvar, _) -> Set.Poly.of_list [ pvar ]
  | CondNode _ | TopNode () | BotNode () -> Set.Poly.empty

let mk_branch_with_simplification_one op fmls =
  let f =
    match op with
    | Formula.And -> is_top
    | Formula.Or -> is_bot
    | _ -> assert false
  in
  let fmls = List.filter ~f:(f >> not) fmls in
  if
    List.exists
      ~f:
        (match op with
        | Formula.And -> is_bot
        | Formula.Or -> is_top
        | _ -> assert false)
      fmls
  then
    match op with
    | Formula.And -> BotNode ()
    | Formula.Or -> TopNode ()
    | _ -> assert false
  else
    match fmls with
    | [] -> (
        match op with
        | Formula.And -> TopNode ()
        | Formula.Or -> BotNode ()
        | _ -> assert false)
    | [ fml ] -> fml
    | fmls ->
        List.fold_left
          ~f:(fun fmls fml ->
            if is_certain_branch op fml then
              let _, fmls' = let_branch fml in
              List.rev_append fmls' fmls
            else fml :: fmls)
          ~init:[] fmls
        |> List.rev |> mk_branch op

let mk_bind_with_filter binder bounds fml =
  let ftv = get_ftv fml in
  let bounds = List.filter ~f:(fun (tvar, _) -> Set.mem ftv tvar) bounds in
  mk_bind binder bounds fml

(*
  (a: int, b: int) @ (a: bool, c: int) -> (a: bool, b: int, c: int)
*)
let update_bounds bounds bounds' =
  let ht = Hashtbl.Poly.create ~size:1234 () in
  List.iter
    ~f:(fun (tvar, sort) -> Hashtbl.Poly.add_exn ht ~key:tvar ~data:sort)
    (bounds @ bounds');
  Hashtbl.Poly.to_alist ht

(*
  forall x, forall y -> forall x, y
  exists x, exists y -> exists x, y
  top /\ P -> P
  bot /\ P -> bot
  top \/ P -> top
  bot \/ P -> P
  (P /\ Q) /\ R -> (P /\ Q /\ R)
  (/\ [empty]) -> top
  (\/ [empty]) -> bot
*)
let rec simplify = function
  | (ForallNode _ | ExistsNode _) as phi ->
      let binder, bounds, fml = let_bind phi in
      let fml = simplify fml in
      if is_bind fml then
        let binder', bounds', fml' = let_bind fml in
        if Stdlib.(binder = binder') then
          mk_bind binder (update_bounds bounds bounds') fml'
        else mk_bind binder bounds fml
      else mk_bind binder bounds fml
  | AndNode fmls -> (
      let fmls = List.map ~f:simplify fmls in
      if List.exists ~f:is_bot fmls then mk_bot ()
      else
        let fmls = List.filter ~f:(is_top >> not) fmls in
        match fmls with
        | [] -> mk_top ()
        | [ fml ] -> fml
        | _ -> mk_branch_with_simplification_one Formula.And fmls)
  | OrNode fmls -> (
      let fmls = List.map ~f:simplify fmls in
      if List.exists ~f:is_top fmls then mk_top ()
      else
        let fmls = List.filter ~f:(is_bot >> not) fmls in
        match fmls with
        | [] -> mk_bot ()
        | [ fml ] -> fml
        | _ -> mk_branch_with_simplification_one Formula.Or fmls)
  | (AppNode _ | CondNode _ | TopNode () | BotNode ()) as phi -> phi

let of_atom atom =
  if Atom.is_true atom then mk_top ()
  else if Atom.is_false atom then mk_bot ()
  else if Atom.is_psym_app atom then
    let psym, args, _ = Atom.let_psym_app atom in
    mk_cond psym args
  else if Atom.is_pvar_app atom then
    let pvar, _, args, _ = Atom.let_pvar_app atom in
    mk_app pvar args
  else failwith @@ sprintf "SimpleFormula.of_atom: unsupported atom"

let rec of_formula_rep = function
  | Formula.Atom (atom, _) -> of_atom atom
  | UnaryOp (_op, _phi, _) ->
      failwith @@ sprintf "[SimpleFormula.of_formula_rep] UnaryOp not supported"
  | BinaryOp (op, phi1, phi2, _) ->
      mk_branch op [ of_formula_rep phi1; of_formula_rep phi2 ]
  | Bind (binder, bounds, phi, _) -> mk_bind binder bounds @@ of_formula_rep phi
  | LetRec (_funcs, _phi, _info) ->
      failwith @@ sprintf "[SimpleFormula.of_formula_rep] LetRec not supported"
  | LetFormula (_var, _sort, _def, _body, _info) ->
      failwith
      @@ sprintf "[SimpleFormula.of_formula_rep] LetFormula not supported"

let of_formula fml = of_formula_rep fml |> simplify

let rec formula_of = function
  | AndNode fmls -> Formula.and_of (List.map ~f:formula_of fmls)
  | OrNode fmls -> Formula.or_of (List.map ~f:formula_of fmls)
  | ForallNode (bounds, fml) ->
      Formula.mk_forall_if_bounded bounds @@ formula_of fml
  | ExistsNode (bounds, fml) ->
      Formula.mk_exists_if_bounded bounds @@ formula_of fml
  | TopNode () -> Formula.mk_true ()
  | BotNode () -> Formula.mk_false ()
  | CondNode (psym, args) -> Formula.mk_atom @@ Atom.mk_psym_app psym args
  | AppNode (pvar, args) ->
      let sorts = List.map args ~f:Term.sort_of in
      Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts args

let rec neg = function
  | AndNode fmls -> OrNode (List.map ~f:neg fmls)
  | OrNode fmls -> AndNode (List.map ~f:neg fmls)
  | ForallNode (bounds, fml) -> ExistsNode (bounds, neg fml)
  | ExistsNode (bounds, fml) -> ForallNode (bounds, neg fml)
  | TopNode () -> BotNode ()
  | BotNode () -> TopNode ()
  | CondNode (psym, args) ->
      let psym =
        Evaluator.simplify_pred_neg (Predicate.mk_psym psym)
        |> Predicate.let_psym
      in
      CondNode (psym, args)
  | AppNode _ -> raise (Invalid_argument "pvar is included")

let rec string_of fml =
  if is_and fml then
    let fmls = let_and fml in
    sprintf "/\\[%s]" (String.concat_map_list ~sep:"; " ~f:string_of fmls)
  else if is_or fml then
    let fmls = let_or fml in
    sprintf "\\/[%s]" (String.concat_map_list ~sep:"; " ~f:string_of fmls)
  else if is_forall fml then
    let bounds, fml = let_forall fml in
    sprintf "forall %s. %s"
      (str_of_sort_env_list Term.str_of_sort bounds)
      (string_of fml)
  else if is_exists fml then
    let bounds, fml = let_exists fml in
    sprintf "exists %s. %s"
      (str_of_sort_env_list Term.str_of_sort bounds)
      (string_of fml)
  else if is_top fml then "true"
  else if is_bot fml then "false"
  else if is_app fml then
    let pvar, args = let_app fml in
    sprintf "%s(%s)" (Ident.name_of_pvar pvar)
      (String.concat_map_list ~sep:"," ~f:Term.str_of args)
  else if is_cond fml then Formula.str_of (formula_of fml)
  else assert false
