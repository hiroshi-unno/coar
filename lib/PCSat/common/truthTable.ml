open Core
open Common.Ext
open Ast
open Ast.LogicOld
open HypSpace

type table = {
  mutable table : (int, Bigarray.int_elt, Bigarray.c_layout) IncrBigArray2.t;
  mutable qarr : Formula.t IncrArray.t;
  mutable aarr : ExAtom.t IncrArray.t;
  qenv : (Formula.t, int) Hashtbl.Poly.t;
  aenv : (ExAtom.t, int) Hashtbl.Poly.t;
  mutable params : sort_env_list;
}
(** truth table *)

let res_valid = 1
let res_invalid = -1
let res_unknown = 0

let res_encode = function
  | Some true -> res_valid
  | Some false -> res_invalid
  | None -> res_unknown

let str_of_res r =
  if r = res_valid then "T"
  else if r = res_invalid then "F"
  else if r = res_unknown then "_"
  else failwith ""

let create_table ?(def_length = 16) () =
  {
    table =
      IncrBigArray2.create Bigarray.int Bigarray.c_layout def_length def_length;
    qarr = Array.create ~len:def_length (Formula.mk_true ());
    aarr = Array.create ~len:def_length (ExAtom.mk_true ());
    qenv = Hashtbl.Poly.create ();
    aenv = Hashtbl.Poly.create ();
    params = [];
  }

let clone_table t =
  {
    params = t.params;
    aenv = Hashtbl.Poly.copy t.aenv;
    qenv = Hashtbl.Poly.copy t.qenv;
    qarr = t.qarr;
    aarr = t.aarr;
    table = t.table;
  }

let length_of_quals table = Hashtbl.Poly.length table.qenv
let length_of_atoms table = Hashtbl.Poly.length table.aenv

let update_with_atom ~id (table : table) fenv qdeps atom =
  if Hashtbl.Poly.mem table.aenv atom then ()
  else
    let ai = length_of_atoms table in
    table.aarr <- IncrArray.auto_set table.aarr ai atom;
    Hashtbl.Poly.add_exn table.aenv ~key:atom ~data:ai;
    for qi = 0 to length_of_quals table - 1 do
      table.table <-
        IncrBigArray2.auto_set table.table qi ai
          (res_encode
          @@ ExAtom.eval_pred ~id fenv qdeps
               (table.params, table.qarr.(qi))
               atom)
    done

let update_with_qualifier ~id (table : table) fenv qdeps qual =
  if Hashtbl.Poly.mem table.qenv qual then ()
  else
    let qi = length_of_quals table in
    Hashtbl.Poly.add_exn table.qenv ~key:qual ~data:qi;
    table.qarr <- IncrArray.auto_set table.qarr qi qual;
    for ai = 0 to length_of_atoms table - 1 do
      table.table <-
        IncrBigArray2.auto_set table.table qi ai
          (res_encode
          @@ ExAtom.eval_pred ~id fenv qdeps (table.params, qual)
          @@ table.aarr.(ai))
    done

type t = (Ident.pvar, table) Hashtbl.Poly.t
(** map from pvar to table *)

let create () = Hashtbl.Poly.create ()

let clone t =
  Hashtbl.Poly.fold t ~init:(create ()) ~f:(fun ~key ~data acc ->
      Hashtbl.Poly.add_exn ~key ~data:(clone_table data) acc;
      acc)

let update_map t pvar table = Hashtbl.Poly.set t ~key:pvar ~data:table

let get_table t pvar =
  match Hashtbl.Poly.find t pvar with
  | Some table -> table
  | None ->
      (*if no table for pvar exists, create and return a new one *)
      let table = create_table () in
      Hashtbl.Poly.add_exn ~key:pvar ~data:table t;
      update_map t pvar table;
      table

let update_map_with_atom ~id t fenv hspaces atom =
  match ExAtom.pvar_of atom with
  | None -> ()
  | Some pvar ->
      let hspace = Hashtbl.Poly.find_exn hspaces (Ident.pvar_to_tvar pvar) in
      update_with_atom ~id (get_table t pvar) fenv hspace.qdeps atom

let update_map_with_atoms ~id t qdeps fenv =
  Set.iter ~f:(update_map_with_atom ~id t fenv qdeps)

let update_map_with_example ~id t fenv hspaces example =
  Set.iter example.ExClause.negative
    ~f:(update_map_with_atom ~id t fenv hspaces);
  Set.iter example.ExClause.positive
    ~f:(update_map_with_atom ~id t fenv hspaces)

let update_map_with_examples ~id t fenv hspaces =
  Set.iter ~f:(update_map_with_example ~id t fenv hspaces)

let update_map_with_qualifiers ~id t fenv qdeps pvar (params, qualifiers) =
  let table = get_table t pvar in
  table.params <- params;
  Set.iter qualifiers ~f:(update_with_qualifier ~id table fenv qdeps)

(* this may update truth table *)
let index_of_atom ~id table fenv qdeps atom =
  match Hashtbl.Poly.find table.aenv atom with
  | Some ai -> ai
  | None ->
      (*print_endline ("adding atom: " ^ ExAtom.str_of atom);*)
      let ai = length_of_atoms table in
      update_with_atom ~id table fenv qdeps atom;
      ai

(* this may update truth table *)
let index_of_qual ~id table fenv qdeps qual =
  match Hashtbl.Poly.find table.qenv qual with
  | Some qi -> qi
  | None ->
      (*print_endline (" adding qual: " ^ Formula.str_of qual);*)
      let qi = length_of_quals table in
      update_with_qualifier ~id table fenv qdeps qual;
      qi

(** qlist and alist *)

type qlist = int list
type alist = (int, int) Map.Poly.t
(* qlist = []; alist = Map.Poly.empty *)

let label_pos = 1
let label_neg = -1

let num_pos_neg_labeled_atoms alist =
  let pelist, nelist =
    Map.Poly.partition_tf alist ~f:(( = ) label_pos (*ToDo*))
  in
  (Map.Poly.length pelist, Map.Poly.length nelist)

let num_pos_labeled_atoms alist =
  Map.Poly.length @@ Map.Poly.filter alist ~f:(( = ) label_pos)

let num_neg_labeled_atoms alist =
  Map.Poly.length @@ Map.Poly.filter alist ~f:(( = ) label_neg)

let num_atoms alist = Map.Poly.length alist
let num_quals qlist = List.length qlist

(* return npapps, nppapps, ppapps, pppapps *)
let papps_of table alist =
  Map.Poly.fold alist
    ~init:(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
    ~f:(fun ~key ~data (npapps, nppapps, ppapps, pppapps) ->
      match table.aarr.(key) with
      | ExAtom.PApp atom ->
          if data = label_pos then
            (npapps, nppapps, Set.add ppapps atom, pppapps)
          else if data = label_neg then
            (Set.add npapps atom, nppapps, ppapps, pppapps)
          else assert false
      | ExAtom.PPApp atom ->
          if data = label_pos then
            (npapps, nppapps, ppapps, Set.add pppapps atom)
          else if data = label_neg then
            (npapps, Set.add nppapps atom, ppapps, pppapps)
          else assert false
      | _ -> (npapps, nppapps, ppapps, pppapps))

let pos_neg_atoms_of table =
  Map.Poly.fold ~init:(Set.Poly.empty, Set.Poly.empty)
    ~f:(fun ~key ~data (pos, neg) ->
      let atom = table.aarr.(key) in
      if data = label_pos then (Set.add pos atom, neg)
      else if data = label_neg then (pos, Set.add neg atom)
      else assert false)

let labeled_atoms_of table =
  Map.Poly.fold ~init:Set.Poly.empty ~f:(fun ~key ~data atoms ->
      Set.add atoms @@ (table.aarr.(key), data))

(** remove redundant atoms *)
let reduced_alist_of (t : table) (qlist, alist) =
  snd
  @@ Map.Poly.fold alist ~init:(Set.Poly.empty, Map.Poly.empty)
       ~f:(fun ~key:ai ~data:l (memo, alist) ->
         let example = (l, List.map qlist ~f:(fun qi -> t.table.{qi, ai})) in
         if Set.mem memo example then (memo, alist)
         else (Set.add memo example, Map.Poly.add_exn alist ~key:ai ~data:l))

(** remove redundant qualifiers
    the prior qualifier in [qlist] is adopted if there are multiple indistinguishable qualifiers *)
let reduced_qlist_of (t : table) (qlist, alist) =
  let atoms_length = length_of_atoms t in
  let alist = Map.Poly.to_alist alist in
  let neg_of qualifier =
    let neg_qualifier =
      Bigarray.Array1.create Bigarray.Int Bigarray.C_layout
        (Bigarray.Array1.dim qualifier)
    in
    Bigarray.Array1.blit qualifier neg_qualifier;
    for i = 0 to Bigarray.Array1.dim neg_qualifier - 1 do
      neg_qualifier.{i} <- 0 - neg_qualifier.{i}
    done;
    neg_qualifier
  in
  let rec inner memo = function
    | [] -> []
    | idx :: qlist ->
        let qualifier =
          if atoms_length = 0 then
            Bigarray.Array1.create Bigarray.Int Bigarray.C_layout 0
          else if List.is_empty alist then
            Bigarray.Array1.sub
              (Bigarray.Array2.slice_left t.table idx)
              0 atoms_length
          else
            Bigarray.Array1.of_array Bigarray.Int Bigarray.c_layout
            @@ Array.of_list
            @@ List.map alist ~f:(fun (ai, _) -> t.table.{idx, ai})
        in
        if Set.mem memo qualifier then inner memo qlist
        else
          let memo' = Set.add (Set.add memo qualifier) (neg_of qualifier) in
          idx :: inner memo' qlist
  in
  inner Set.Poly.empty qlist

(** printers *)

let str_of_quals t qlist =
  let qlist = List.sort qlist ~compare:Int.compare in
  String.concat_map_list ~sep:"\n" qlist ~f:(fun qi ->
      let phi = t.qarr.(qi) in
      let rank = Rank.rank_of phi in
      sprintf "%d %s: %s" qi (Rank.str_of rank) (Formula.str_of phi))

let str_of_atoms t alist =
  let alist =
    List.sort (Map.Poly.to_alist alist) ~compare:(fun (x, _) (y, _) ->
        Int.compare x y)
  in
  String.concat_map_list ~sep:"\n" alist ~f:(fun (ai, label) ->
      let atom = t.aarr.(ai) in
      sprintf "%d (%d): %s" ai label (ExAtom.str_of atom))

let str_of_table t (qlist, alist) =
  let qlist = List.sort qlist ~compare:Int.compare in
  let alist =
    List.sort (Map.Poly.to_alist alist) ~compare:(fun (x, _) (y, _) ->
        Int.compare x y)
  in
  if List.is_empty alist then ""
  else
    String.concat_map_list ~sep:"\n" qlist ~f:(fun qi ->
        String.concat_map_list alist ~f:(fun (ai, _) ->
            str_of_res t.table.{qi, ai}))

let str_of_table_transposed t (qlist, alist) =
  let qlist = List.sort qlist ~compare:Int.compare in
  let alist =
    List.sort (Map.Poly.to_alist alist) ~compare:(fun (x, _) (y, _) ->
        Int.compare x y)
  in
  if List.is_empty alist then ""
  else
    String.concat_map_list ~sep:"\n" alist ~f:(fun (ai, _) ->
        String.concat_map_list qlist ~f:(fun qi -> str_of_res t.table.{qi, ai}))

let str_of (Ident.Pvar name, t) (qlist, alist) =
  let reduced_qlist = reduced_qlist_of t (qlist, alist) in
  sprintf "===== %s =====\n" name
  ^ sprintf "qualifiers (%d):\n%s\n" (List.length qlist) (str_of_quals t qlist)
  ^ sprintf "atoms (%d):\n%s\n" (Map.Poly.length alist) (str_of_atoms t alist)
  ^ sprintf "table:\n%s\n" (str_of_table t (qlist, alist))
  ^
  if List.length reduced_qlist = List.length qlist then ""
  else
    sprintf "reduced qualifiers (%d):\n%s\n"
      (List.length @@ reduced_qlist)
      (str_of_quals t reduced_qlist)

let str_of_map t (qlist, alist) =
  Hashtbl.Poly.fold t ~init:"" ~f:(fun ~key ~data ret ->
      ret ^ "\n" ^ str_of (key, data) (qlist, alist))
