open Core
open Common.Util
open Ast
open Ast.LogicOld

type table = {
  mutable table  : (int, Bigarray.int_elt, Bigarray.c_layout) IncrBigArray2.t;
  mutable qarr   : Formula.t IncrArray.t;
  mutable aarr   : ExAtom.t IncrArray.t;
  qenv           : (Formula.t, int) Hashtbl.Poly.t;
  aenv           : (ExAtom.t,  int) Hashtbl.Poly.t;
  mutable params : SortEnv.t;
  mutable qlist  : int list;
  mutable alist  : (int , int) Map.Poly.t
}

type t = (Ident.pvar, table) Hashtbl.Poly.t
let create_table ?(def_length=16) () = {
  table = IncrBigArray2.create (Bigarray.int) (Bigarray.c_layout) def_length def_length;
  qarr = Array.create ~len:def_length (Formula.mk_true ());
  aarr = Array.create ~len:def_length (ExAtom.mk_true ());
  qenv = Hashtbl.Poly.create ();
  aenv = Hashtbl.Poly.create ();
  params = SortEnv.empty;
  qlist = [];
  alist = Map.Poly.empty;
}
let create () = Hashtbl.Poly.create ()
let get_table t pvar =
  match Hashtbl.Poly.find t pvar with
  | Some table -> table
  | None -> (*if no table for pvar exists, create and return a new one *)
    let table = create_table () in
    Hashtbl.Poly.add_exn ~key:pvar ~data:table t;
    table

let name_of_qual qi = Printf.sprintf "#qual_%d" qi
let qual_of_name name k = Scanf.sscanf name "#qual_%d" k
let length_of_quals table = Hashtbl.Poly.length table.qenv
let length_of_atoms table = Hashtbl.Poly.length table.aenv

let update_map t pvar table = Hashtbl.Poly.set t ~key:pvar ~data:table

let eval_qual fenv (params, qual) (_param_senv, cond, _sorts, args) =
  (* print_endline ("evaluating " ^ Formula.str_of qual ^ " with (" ^ (Formula.str_of cond) ^ "=>"^ (String.concat ~sep:"," @@ List.map ~f:Term.str_of args) ^ ")"); *)
  let phi =
    let sub = Map.Poly.of_alist_exn @@ List.zip_exn (List.map ~f:fst @@ LogicOld.SortEnv.list_of params) args in
    Formula.subst sub qual in
  match Evaluator.check ~cond (Z3Smt.Z3interface.is_valid fenv) phi with
  | Some true -> 1
  | Some false -> -1
  | _ -> 0

(* assume atom is papp or ppapp*)
let check_ex_atom fenv (params, qual) = function
  | ExAtom.PApp ((_pvar, sorts), args) ->
    eval_qual fenv (params, qual) (Map.Poly.empty, Formula.mk_true (), sorts, args)
  | ExAtom.PPApp ((param_senv, cond), ((_pvar, sorts), args)) ->
    eval_qual fenv (params, qual) (param_senv, cond, sorts, args)
  | _ -> assert false
let update_with_atom (table:table) fenv atom =
  if Hashtbl.Poly.mem table.aenv atom then ()
  else begin
    let ai = length_of_atoms table in
    table.aarr <- IncrArray.auto_set table.aarr ai atom;
    Hashtbl.Poly.add_exn table.aenv ~key:atom ~data:ai;
    for qi = 0 to (length_of_quals table) - 1 do
      table.table <- IncrBigArray2.auto_set table.table qi ai (check_ex_atom fenv (table.params, table.qarr.(qi)) atom)
    done
  end
let update_map_with_atom t fenv atom =
  match ExAtom.pvar_of atom with
  | None -> ()
  | Some pvar -> update_with_atom (get_table t pvar) fenv atom
let update_map_with_atoms t fenv = Set.Poly.iter ~f:(update_map_with_atom t fenv)
let update_map_with_example t fenv example =
  Set.Poly.iter example.ExClause.negative ~f:(update_map_with_atom t fenv);
  Set.Poly.iter example.ExClause.positive ~f:(update_map_with_atom t fenv)
let update_map_with_examples t fenv = Set.Poly.iter ~f:(update_map_with_example t fenv)

let update_with_qualifier (table:table) fenv qual =
  if Hashtbl.Poly.mem table.qenv qual then ()
  else begin
    let qi = length_of_quals table in
    Hashtbl.Poly.add_exn table.qenv ~key:qual ~data:qi;
    table.qarr <- IncrArray.auto_set table.qarr qi qual;
    table.qlist <- qi::table.qlist;
    for ai = 0 to length_of_atoms table - 1 do
      table.table <- IncrBigArray2.auto_set table.table qi ai
          (check_ex_atom fenv (table.params, qual) @@ table.aarr.(ai))
    done
  end
let update_map_with_qualifiers t fenv pvar (params, qualifiers) =
  let table = get_table t pvar in
  table.params <- params;
  update_map t pvar table;
  if (length_of_quals table) < Set.Poly.length qualifiers then
    Set.iter qualifiers ~f:(update_with_qualifier table fenv)

let set_alist (t:table) alist = { t with alist = alist }
let set_qlist (t:table) qlist = { t with qlist = qlist }

(* this may update truth table *)
let index_of_atom table fenv atom =
  match Hashtbl.Poly.find table.aenv atom with
  | Some ai -> ai
  | None ->
    (*print_endline ("adding atom: " ^ ExAtom.str_of atom);*)
    let ai = length_of_atoms table in
    update_with_atom table fenv atom; ai
(* this may update truth table *)
let index_of_qual table fenv qual =
  match Hashtbl.Poly.find table.qenv qual with
  | Some qi -> qi
  | None ->
    (*print_endline (" adding qual: " ^ Formula.str_of qual);*)
    let qi = length_of_quals table in
    update_with_qualifier table fenv qual; qi

let label_pos = 1
let label_neg = -1
let num_pos_neg_labeled_atoms t =
  let pelist, nelist = Map.Poly.partition_tf t.alist ~f:((=) label_pos(*ToDo*)) in
  Map.Poly.length pelist, Map.Poly.length nelist
let num_pos_labeled_atoms t =
  Map.Poly.length @@ Map.Poly.filter t.alist ~f:((=) label_pos)
let num_neg_labeled_atoms t =
  Map.Poly.length @@ Map.Poly.filter t.alist ~f:((=) label_neg)
let num_atoms t = Map.Poly.length t.alist
let divide q (t: table) =
  let qlist' = List.filter ~f:((<>) q) t.qlist in
  let palist, nalist = Map.Poly.fold t.alist ~init:(Map.Poly.empty, Map.Poly.empty) ~f:(
      fun ~key:ai ~data:l (palist, nalist) ->
        if t.table.{q, ai} = label_pos then
          (Map.Poly.add_exn ~key:ai ~data:l palist, nalist)
        else if t.table.{q, ai} = label_neg then
          (palist, Map.Poly.add_exn ~key:ai ~data:l nalist)
        else (palist, nalist)) in
  { t with qlist = qlist'; alist = palist },
  { t with qlist = qlist'; alist = nalist }
(* return npapps, nppapps, ppapps, pppapps *)
let papps_of table =
  Map.Poly.fold table.alist
    ~init:(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
    ~f:(fun ~key ~data (npapps, nppapps, ppapps, pppapps) ->
        match table.aarr.(key) with
        | ExAtom.PApp atom ->
          if data = label_pos then (npapps, nppapps, Set.Poly.add ppapps atom, pppapps)
          else if data = label_neg then (Set.Poly.add npapps atom, nppapps, ppapps, pppapps)
          else assert false
        | ExAtom.PPApp atom ->
          if data = label_pos then (npapps, nppapps, ppapps, Set.Poly.add pppapps atom)
          else if data = label_neg then (npapps, Set.Poly.add nppapps atom, ppapps, pppapps)
          else assert false
        | _ -> (npapps, nppapps, ppapps, pppapps))
let pos_neg_atoms_of table =
  Map.Poly.fold table.alist ~init:(Set.Poly.empty, Set.Poly.empty) ~f:(fun ~key ~data (pos, neg) ->
      let atom = table.aarr.(key) in
      if data = label_pos then (Set.Poly.add pos atom, neg)
      else if data = label_neg then (pos, Set.Poly.add neg atom)
      else assert false)
let labeled_atoms_of table =
  Map.Poly.fold table.alist ~init:Set.Poly.empty ~f:(fun ~key ~data atoms ->
      Set.Poly.add atoms @@ (table.aarr.(key), data))

let num_quals tt = List.length tt.qlist
let qualifiers table =
  Set.Poly.of_list @@ List.map table.qlist ~f:(IncrArray.get table.qarr)
let qualifiers_of = Hashtbl.Poly.map ~f:qualifiers
let qualifiers_of_pvar t pvar = qualifiers (get_table t pvar)

let reduced_alist_of (t: table) =
  let qlist = t.qlist in
  let _, alist =
    Map.Poly.fold t.alist ~init:(Set.Poly.empty, Map.Poly.empty) ~f:(
      fun ~key:ai ~data:l (memo, alist)->
        let example = l, List.map qlist ~f:(fun qi -> t.table.{qi, ai}) in
        if Set.Poly.mem memo example then (memo, alist)
        else (Set.Poly.add memo example, Map.Poly.add_exn alist ~key:ai ~data:l)) in
  alist
(** remove redundant atoms *)
let reduce_atoms (t: table) = { t with alist = reduced_alist_of t }

let reduced_qlist_of (t: table) =
  let atoms_length = length_of_atoms t in
  let alist = Map.Poly.to_alist t.alist in
  let neg_of qualifier =
    let neg_qualifier = Bigarray.Array1.create Bigarray.Int Bigarray.C_layout (Bigarray.Array1.dim qualifier) in
    Bigarray.Array1.blit qualifier neg_qualifier;
    for i = 0 to Bigarray.Array1.dim neg_qualifier - 1 do
      neg_qualifier.{i} <- 0 - neg_qualifier.{i}
    done;
    neg_qualifier
  in
  let rec inner memo = function
    | [] -> List.dedup_and_sort ~compare:Int.compare @@ Map.Poly.data memo
    | idx :: qlist ->
      let qualifier =
        if atoms_length = 0 then
          Bigarray.Array1.create Bigarray.Int Bigarray.C_layout 0
        else if List.is_empty alist then
          Bigarray.Array1.sub (Bigarray.Array2.slice_left t.table idx) 0 atoms_length
        else
          Bigarray.Array1.of_array Bigarray.Int Bigarray.c_layout @@ Array.of_list @@
          List.map alist ~f:(fun (ai, _) -> t.table.{idx, ai})
      in
      match Map.Poly.find memo qualifier with
      | Some qi when Rank.compare (Rank.rank_of t.qarr.(idx)) (Rank.rank_of t.qarr.(qi)) >= 0 ->
        inner memo qlist
      | _ ->
        inner
          (Map.Poly.set (Map.Poly.set memo ~key:qualifier ~data:idx)
             ~key:(neg_of qualifier) ~data:idx)
          qlist
  in
  inner Map.Poly.empty t.qlist
(** remove redundant qualifiers *)
let reduce_qualifiers t = { t with qlist = reduced_qlist_of t }

let concretize_bf quals phi =
  let rec inner = function
    | PropLogic.Formula.True _  ->
      LogicOld.Formula.mk_atom (LogicOld.Atom.mk_true ())
    | False _ ->
      LogicOld.Formula.mk_atom (LogicOld.Atom.mk_false ())
    | Atom (name, _) ->
      qual_of_name name (fun qi -> quals.(qi))
    | UnaryOp (PropLogic.Formula.Neg, phi, _) ->
      LogicOld.Formula.mk_neg (inner phi)
    | BinaryOp (PropLogic.Formula.And, phi1, phi2, _) ->
      LogicOld.Formula.mk_binop LogicOld.Formula.And (inner phi1) (inner phi2)
    | BinaryOp (PropLogic.Formula.Or, phi1, phi2, _) ->
      LogicOld.Formula.mk_binop LogicOld.Formula.Or (inner phi1) (inner phi2)
  in inner phi

let str_of_quals ?(qlist = None) t =
  let qlist = match qlist with None -> List.sort t.qlist ~compare:Int.compare | Some qlist -> qlist in
  String.concat ~sep:"\n" @@
  List.map qlist ~f:(fun qi ->
      let phi = t.qarr.(qi) in
      let rank = Rank.rank_of phi in
      sprintf "%d %s: %s" qi (Rank.str_of rank) (Formula.str_of phi))
let str_of_atoms ?(alist = None) t =
  let alist = match alist with None -> List.sort (Map.Poly.to_alist t.alist) ~compare:(fun (x, _) (y, _) -> Int.compare x y) | Some alist -> alist in
  String.concat ~sep:"\n" @@
  List.map alist ~f:(fun (ai, label) ->
      let atom = t.aarr.(ai) in sprintf "%d (%d): %s" ai label (ExAtom.str_of atom))
let str_of_table ?(qlist = None) ?(alist = None) t =
  let qlist = match qlist with None -> List.sort t.qlist ~compare:Int.compare | Some qlist -> qlist in
  let alist = match alist with None -> List.sort (Map.Poly.to_alist t.alist) ~compare:(fun (x, _) (y, _) -> Int.compare x y) | Some alist -> alist in
  if List.is_empty alist then ""
  else
    String.concat ~sep:"\n" @@
    List.map qlist ~f:(fun qi ->
        String.concat
          (List.map alist ~f:(fun (ai, _) ->
               match t.table.{qi, ai} with
               | 1 -> "T" | -1 -> "F" | 0 -> "_"
               | _ -> assert false)))
let str_of_table_transposed ?(qlist = None) ?(alist = None) t =
  let qlist = match qlist with None -> List.sort t.qlist ~compare:Int.compare | Some qlist -> qlist in
  let alist = match alist with None -> List.sort (Map.Poly.to_alist t.alist) ~compare:(fun (x, _) (y, _) -> Int.compare x y) | Some alist -> alist in
  if List.is_empty alist then ""
  else
    String.concat ~sep:"\n" @@
    List.map alist ~f:(fun (ai, _) ->
        String.concat
          (List.map qlist ~f:(fun qi ->
               match t.table.{qi, ai} with
               | 1 -> "T" | -1 -> "F" | 0 -> "_"
               | _ -> assert false)))
let str_of ?(qlist = None) ?(alist = None) (Ident.Pvar name, t) =
  let qlist = match qlist with None -> List.sort t.qlist ~compare:Int.compare | Some qlist -> qlist in
  let alist = match alist with None -> List.sort (Map.Poly.to_alist t.alist) ~compare:(fun (x, _) (y, _) -> Int.compare x y) | Some alist -> alist in
  (*let reduced_qlist = reduced_qlist_of table in*)
  sprintf "===== %s =====\n" name ^
  sprintf "qualifiers (%d):\n%s\n" (List.length qlist) (str_of_quals ~qlist:(Some qlist) t) ^
  sprintf "atoms (%d):\n%s\n" (List.length alist) (str_of_atoms ~alist:(Some alist) t) ^
  sprintf "table:\n%s\n" (str_of_table ~qlist:(Some qlist) ~alist:(Some alist) t)
(*^ sprintf "reduced qualifiers (%d):\n%s\n" (List.length @@ reduced_qlist) (str_of_quals table reduced_qlist)*)
let str_of_map t =
  Hashtbl.Poly.fold t ~init:"" ~f:(fun ~key ~data ret -> ret ^ "\n" ^ str_of (key, data))
