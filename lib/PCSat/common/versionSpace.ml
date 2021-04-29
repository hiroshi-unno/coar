open Core
open Common.Util
open Ast
open Ast.LogicOld

type examples = ExClauseSet.t * ExClauseSet.t * ExClauseSet.t
type components = (Ident.tvar, int * SortEnv.t * Formula.t Set.Poly.t * Term.t Set.Poly.t) Hashtbl.Poly.t
type truth_table = TruthTable.t
type labeling = (Ident.pvar, (int, int) Map.Poly.t) Map.Poly.t
type fenv = (Ident.tvar * (Ident.tvar * LogicOld.Sort.t) list * LogicOld.Sort.t * LogicOld.Term.t * (LogicOld.Formula.t Set.Poly.t)) Set.Poly.t
type t = {
  examples    : examples;
  components  : components;
  truth_table : truth_table;
  labelings   : labeling list;
  fenv        : fenv
}

let init () = {
  examples = Set.Poly.(empty, empty, empty);
  components = Hashtbl.Poly.create ();
  truth_table = TruthTable.create ();
  labelings = [Map.Poly.empty];
  fenv = Set.Poly.empty
}

let examples_of t = t.examples
let components_of t = t.components
let truth_table_of t = t.truth_table
let labelings_of t = t.labelings
let fenv_of t = t.fenv

let components_of_pvar (Ident.Pvar name) t =
  let components = components_of t in
  match Hashtbl.Poly.find components (Ident.Tvar name) with
  | None ->
    let new_cs = (-1, SortEnv.empty, Set.Poly.empty, Set.Poly.empty) in
    Hashtbl.Poly.add_exn components ~key:(Ident.Tvar name) ~data:new_cs;
    new_cs
  | Some cs -> cs
let depth_of_components (depth, _, _, _) = depth
let params_of_components (_, params, _, _) = params
let quals_of_components (_, _, quals, _) = quals
let terms_of_components (_, _, _, terms) = terms
let terms_of_pvar pvar t = terms_of_components @@ components_of_pvar pvar t
let reduced_terms_of_pvar pvar t = (*ToDo*)terms_of_components @@ components_of_pvar pvar t
let quals_of t = TruthTable.qualifiers_of (truth_table_of t)
let reduced_quals_of t = TruthTable.qualifiers_of (Hashtbl.Poly.map ~f:TruthTable.reduce_qualifiers @@ truth_table_of t)

let set_examples examples t = { t with examples = examples }
let set_labelings labelings t = { t with labelings = labelings }
let set_label t label labeling atom =
  match ExAtom.pvar_of atom with
  | None -> labeling
  | Some pvar ->
    let ai = TruthTable.index_of_atom (TruthTable.get_table (truth_table_of t) pvar) (fenv_of t) atom in
    match Map.Poly.find labeling pvar with
    | None -> Map.Poly.add_exn labeling ~key:pvar ~data:(Map.Poly.singleton ai label)
    | Some l -> Map.Poly.set labeling ~key:pvar ~data:(Map.Poly.set l ~key:ai ~data:label)
let set_fenv fenv t  = {t with fenv = fenv}

let update_components pvar (depth, params, quals, terms) t =
  let components = components_of t in
  match Hashtbl.Poly.find components pvar with
  | None ->
    Hashtbl.Poly.add_exn components ~key:pvar ~data:(depth, params, quals, terms)
  | Some (_, _, quals', terms') ->
    Hashtbl.Poly.set components ~key:pvar
      ~data:(depth, params, (Set.Poly.union quals quals'), (Set.Poly.union terms terms'))
let update_truth_table t =
  Hashtbl.Poly.iteri (components_of t) ~f:(fun ~key:(Ident.Tvar name) ~data:(_, env, quals, _) ->
      TruthTable.update_map_with_qualifiers (truth_table_of t) (fenv_of t) ((*ToDo*)Ident.Pvar name) (env, quals));
  let pos, neg, und = examples_of t in
  TruthTable.update_map_with_examples (truth_table_of t) (fenv_of t) (Set.Poly.union_list [pos; neg; und])

let map ~f vs =
  let examples', labelings' = f ~examples:(examples_of vs) ~labelings:(labelings_of vs) in
  vs |> set_examples examples' |> set_labelings labelings'

let str_of_components name (depth, params, quals, terms) =
  sprintf "[%s](%s)\ndepth: %d\nqualifiers: %s\nterms: %s"
    name
    (SortEnv.str_of (Term.str_of_sort) params)
    depth
    (String.concat ~sep:"\n" @@ Set.Poly.to_list @@ Set.Poly.map quals ~f:Formula.str_of)
    (String.concat ~sep:"\n" @@ Set.Poly.to_list @@ Set.Poly.map terms ~f:Term.str_of)
let str_of_examples (decided_pos, decided_neg, undecided) =
  "********* given example instances *********\n"
  ^ (Printf.sprintf "*** decided positive (%d): [\n" @@ Set.Poly.length decided_pos)
  ^ (ExClauseSet.str_of decided_pos)
  ^ (Printf.sprintf "]\n*** decided negative (%d): [\n" @@ Set.Poly.length decided_neg)
  ^ (ExClauseSet.str_of decided_neg)
  ^ (Printf.sprintf "]\n*** undecided (%d): [\n" @@ Set.Poly.length undecided)
  ^ (ExClauseSet.str_of undecided)
  ^ "]\n"
let str_of_number_of_examples (decided_pos, decided_neg, undecided) =
  let dp, dn, u =
    Set.Poly.length decided_pos,
    Set.Poly.length decided_neg,
    Set.Poly.length undecided
  in
  Printf.sprintf "#decided_positive: %d, #decided_negative: %d, #undecided: %d" dp dn u
