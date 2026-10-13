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
            (* canonicalised: a [Set.Poly] orders by the shape of the tree it
               was built as, so one clause built in two orders is two elements *)
            Set.add acc @@ ExClause.canon
            @@ ExClause.
                 { positive = Set.Poly.empty; negative = Set.Poly.of_list papps }))

(* The parity condition: an infinite chain is allowed exactly when the least
   priority it visits infinitely often is accepting.  [priority_of] raises on a
   tag the family's priority function does not map, so it must be given the
   family's real record, never a placeholder. *)
let priority_of (nwf : Kind.nwf) tag = Map.Poly.find_exn nwf.Kind.sigma tag
let is_accepting_priority (nwf : Kind.nwf) pri = Set.mem nwf.Kind.acc_set pri

(* A self-loop among the sample: an atom over a diagonal tag pair (t, t) whose
   left and right node, after the shared arguments, are equal.  It is caught
   before the graph is built and refuted by a unit negative lemma.  [allowed nwf
   t] says the family permits an infinite chain staying at tag [t]; the first
   self-loop in the sample's order that is not allowed is returned. *)
let find_self_loop ~allowed m sample =
  Set.find_map sample ~f:(fun (pv, (idl, idr), terms) ->
      if Ident.tvar_equal idl idr then
        let nwf, sorts_shared, _, _ = Map.Poly.find_exn m (idl, idr) in
        if
          (not (allowed nwf idl))
          && ExClause.has_self_loop
               ~drop:(Some (List.length sorts_shared))
               terms
        then Some (ExClause.mk_unit_neg (ExAtom.PApp (pv, terms)))
        else None
      else None)

(* Non-well-foundedness forbids every infinite chain, so every self-loop is a
   violation.  The family record in [m] is not read, which is what lets the
   labeler pass a placeholder there. *)
let nwf_self_loop m sample = find_self_loop ~allowed:(fun _ _ -> false) m sample

(* A self-loop is an infinite chain visiting one priority, so under the parity
   condition it is a violation only when that priority is rejecting. *)
let parity_self_loop m sample =
  find_self_loop m sample ~allowed:(fun nwf tag ->
      is_accepting_priority nwf (priority_of nwf tag))

let is_sat_parity_cond m node_map_rev = function
  | v1 :: v2 :: tl ->
      let _, idl = Map.Poly.find_exn node_map_rev v1 in
      let _, idr = Map.Poly.find_exn node_map_rev v2 in
      let nwf, _, _, _ = Map.Poly.find_exn m (idl, idr) in
      let min =
        List.fold_left ~init:(priority_of nwf idl) (v2 :: tl) ~f:(fun m v ->
            let _, id = Map.Poly.find_exn node_map_rev v in
            min m (priority_of nwf id))
      in
      is_accepting_priority nwf min
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
              Set.add acc @@ ExClause.canon
              @@ ExClause.
                   {
                     positive = Set.Poly.empty;
                     negative = Set.Poly.of_list papps;
                   })))
