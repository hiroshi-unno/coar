open Core
open Common
open Util
open Ast
open LogicOld


let split_sels dt sels =
  List.partition_tf sels ~f:(
    fun sel -> match sel with
      | Datatype.Sel _ -> true
      | Datatype.InSel (_, dt_name, dt_args) -> 
        not @@ Stdlib.(=) dt_name (Datatype.name_of dt) || not @@ Stdlib.(=) dt_args (Datatype.args_of dt)
  )

let update_term_map ?(d=0) sort terms term_map = 
  if d = 0 then term_map 
  else
    match sort with
    | T_dt.SDT dt ->
      Set.Poly.fold terms ~init:term_map ~f:(
        fun term_map term -> 
          let sels = Datatype.sels_of dt in
          let sels, insels  = split_sels dt sels in
          let in_terms = List.map insels ~f:(fun sel -> T_dt.mk_sel dt (Datatype.name_of_sel sel) term) in
          let sel_terms = in_terms @ (List.concat @@ List.map sels ~f:(fun sel -> List.map [term] ~f:(fun t -> T_dt.mk_sel dt (Datatype.name_of_sel sel) t))) in
          List.fold_left sel_terms ~init:term_map ~f:(
            fun term_map sel_term -> 
              let sel_sort = Term.sort_of sel_term in 
              match Map.Poly.find term_map sel_sort  with
              | Some(group) -> Map.Poly.set ~key:sel_sort ~data:(Set.Poly.add group sel_term) term_map
              | None -> Map.Poly.add_exn ~key:sel_sort ~data:(Set.Poly.singleton sel_term) term_map
          )
      )
    | _ -> term_map

let qualifiers_of sort terms =
  (match sort with
   | T_dt.SDT dt -> 
     let conses = Datatype.conses_of dt in
     List.fold_left conses ~init:Set.Poly.empty ~f:(fun ret cons -> 
         Set.Poly.map terms ~f:(fun t -> T_dt.mk_is_cons dt cons t) |> Set.Poly.union ret) 
     |> Set.Poly.union (Set.Poly.of_list @@ T_bool.mk_eqs (Set.Poly.to_list @@ Set.Poly.filter terms ~f:(Term.is_var)))
   | _ -> Set.Poly.empty)
  |> Set.Poly.map ~f:(Formula.mk_atom)