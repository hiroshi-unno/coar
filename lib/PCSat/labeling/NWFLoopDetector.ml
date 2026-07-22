(* TODO: Functorize this module and implement configurable loop-detection
   options, including verbosity, whether to use Johnson's algorithm, and so on. *)

open Core
open Ast

let find_cycle graph vertiecs =
  (* graph must be strongly connected *)
  let open Graph in
  let open Pack.Digraph in
  let rec inner stack visited ver =
    if Set.mem visited ver then
      match List.findi stack ~f:(fun _ v -> Stdlib.(v = ver)) with
      | Some (i, _) -> ver :: List.take stack (i + 1) |> List.rev
      | None -> assert false
    else
      inner (ver :: stack) (Set.add visited ver) (List.hd_exn (succ graph ver))
  in
  let start = Set.choose_exn vertiecs in
  inner [] Set.Poly.empty start

(* ToDo: implement Johnson algorithm to find all cycle *)
let find_cycles graph vertiecs = [ find_cycle graph vertiecs ]

let term_map m examples =
  (* size of examples is more than 0 *)
  let open Graph in
  let open Pack.Digraph in
  let cnt = ref 0 in
  let map =
    Set.fold ~init:Map.Poly.empty examples ~f:(fun map -> function
      | _, (idl, idr), terms ->
          let _, sorts_shared, sorts_l, sorts_r =
            Map.Poly.find_exn m (idl, idr)
          in
          let size_shared = List.length sorts_shared in
          let size_l = List.length sorts_l in
          let size_r = List.length sorts_r in
          let params, terms = List.split_n terms size_shared in
          let t1, t2 = List.split_n terms size_l in
          assert (List.length t2 = size_r);
          let set term map =
            Map.Poly.update map term ~f:(function
              | None ->
                  incr cnt;
                  V.create !cnt
              | Some n -> n)
          in
          map |> set (params @ t1, idl) |> set (params @ t2, idr))
  in
  let rmap =
    Map.Poly.fold ~init:Map.Poly.empty map ~f:(fun ~key:k ~data:v ->
        Map.Poly.add_exn ~key:v ~data:k)
  in
  (map, rmap, !cnt)

let gen_graph m sample =
  let open Graph in
  let open Pack.Digraph in
  let node_map, node_map_rev, n = term_map m sample in
  let graph = create ~size:n () in
  Set.iter sample ~f:(fun (_, (idl, idr), terms) ->
      let _, sorts_shared, sorts_l, sorts_r = Map.Poly.find_exn m (idl, idr) in
      let size_shared = List.length sorts_shared in
      let size_l = List.length sorts_l in
      let size_r = List.length sorts_r in
      let params, terms = List.split_n terms size_shared in
      let t1, t2 = List.split_n terms size_l in
      assert (List.length t2 = size_r);
      add_edge graph
        (Map.Poly.find_exn node_map (params @ t1, idl))
        (Map.Poly.find_exn node_map (params @ t2, idr)));
  (graph, node_map_rev)

let rec get_papps_nwf ~print name m node_map_rev acc = function
  | v1 :: v2 :: tl ->
      let t1, idl = Map.Poly.find_exn node_map_rev v1 in
      let t2, idr = Map.Poly.find_exn node_map_rev v2 in
      let _, sorts_shared, sorts_l, sorts_r = Map.Poly.find_exn m (idl, idr) in
      let papp =
        ExAtom.PApp
          ( ( Ident.tvar_to_pvar @@ Kind.nwf_tvar_of_nwf name idl idr,
              sorts_shared @ sorts_l @ sorts_r ),
            t1 @ List.drop t2 (List.length sorts_shared) )
      in
      print @@ lazy (ExAtom.str_of papp ^ ",");
      get_papps_nwf ~print name m node_map_rev (papp :: acc) (v2 :: tl)
  | _ -> acc

let detect_nwf ~print name m (graph, components, node_map_rev) res =
  let open Graph in
  let open Pack.Digraph in
  List.fold ~init:res components ~f:(fun acc component ->
      if List.length component <= 1 then acc
      else
        let subgraph = create ~size:(List.length component) () in
        let component = Set.Poly.of_list component in
        Set.iter component ~f:(fun v ->
            List.iter (succ graph v) ~f:(fun s ->
                if Set.mem component s then add_edge subgraph v s else ()));
        List.fold ~init:acc (find_cycles subgraph component)
          ~f:(fun acc cycle ->
            print @@ lazy "A non-NWF cycle found: [";
            let papps = get_papps_nwf ~print name m node_map_rev [] cycle in
            print @@ lazy "]\n";
            Set.add acc
              ExClause.
                { positive = Set.Poly.empty; negative = Set.Poly.of_list papps }))

let is_sat_parity_cond m node_map_rev = function
  | v1 :: v2 :: tl ->
      let _, idl = Map.Poly.find_exn node_map_rev v1 in
      let _, idr = Map.Poly.find_exn node_map_rev v2 in
      let nwf, _, _, _ = Map.Poly.find_exn m (idl, idr) in
      let min =
        List.fold_left ~init:(Map.Poly.find_exn nwf.Kind.sigma idl) (v2 :: tl)
          ~f:(fun m v ->
            let _, id = Map.Poly.find_exn node_map_rev v in
            min m (Map.Poly.find_exn nwf.Kind.sigma id))
      in
      Set.mem nwf.Kind.acc_set min
  | _ -> assert false

let rec get_papps_parity ~print m node_map_rev acc = function
  | v1 :: v2 :: tl ->
      let t1, idl = Map.Poly.find_exn node_map_rev v1 in
      let t2, idr = Map.Poly.find_exn node_map_rev v2 in
      let nwf, sorts_shared, sorts_l, sorts_r =
        Map.Poly.find_exn m (idl, idr)
      in
      let papp =
        ExAtom.PApp
          ( ( Ident.tvar_to_pvar @@ Kind.parity_tvar_of_nwf nwf idl idr,
              sorts_shared @ sorts_l @ sorts_r ),
            t1 @ List.drop t2 (List.length sorts_shared) )
      in
      print @@ lazy (ExAtom.str_of papp ^ ",");
      get_papps_parity ~print m node_map_rev (papp :: acc) (v2 :: tl)
  | _ -> acc

let detect_parity ~print m (graph, components, node_map_rev) res =
  let open Graph in
  let open Pack.Digraph in
  List.fold ~init:res components ~f:(fun acc component ->
      if List.length component <= 1 then acc
      else
        let subgraph = create ~size:(List.length component) () in
        let component = Set.Poly.of_list component in
        Set.iter component ~f:(fun v ->
            List.iter (succ graph v) ~f:(fun s ->
                if Set.mem component s then add_edge subgraph v s else ()));
        List.fold ~init:acc (find_cycles subgraph component)
          ~f:(fun acc cycle ->
            if is_sat_parity_cond m node_map_rev cycle then acc
            else (
              print @@ lazy "A non-parity cycle found: [";
              let papps = get_papps_parity ~print m node_map_rev [] cycle in
              print @@ lazy "]\n";
              Set.add acc
                ExClause.
                  {
                    positive = Set.Poly.empty;
                    negative = Set.Poly.of_list papps;
                  })))
