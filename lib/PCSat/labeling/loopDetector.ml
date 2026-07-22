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

let term_map examples =
  (* size of examples is more than 0 *)
  let open Graph in
  let open Pack.Digraph in
  let cnt = ref 0 in
  let size =
    match Set.find_exn examples ~f:(fun _ -> true) with
    | (_, _), terms ->
        let l = List.length terms in
        if l mod 2 = 1 then assert false else l / 2
  in
  let map =
    Set.fold ~init:Map.Poly.empty examples ~f:(fun map -> function
      | (_, _), terms ->
          let t1, t2 = List.split_n terms size in
          let set term map =
            Map.Poly.update map term ~f:(function
              | None ->
                  incr cnt;
                  V.create !cnt
              | Some n -> n)
          in
          map |> set t1 |> set t2)
  in
  let rmap =
    Map.Poly.fold ~init:Map.Poly.empty map ~f:(fun ~key:k ~data:v ->
        Map.Poly.add_exn ~key:v ~data:k)
  in
  (map, rmap, !cnt, size)

let gen_graph sample =
  let open Graph in
  let open Pack.Digraph in
  let node_map, node_map_rev, n, size = term_map sample in
  let graph = create ~size:n () in
  Set.iter sample ~f:(fun (_, terms) ->
      let t1, t2 = List.split_n terms size in
      add_edge graph
        (Map.Poly.find_exn node_map t1)
        (Map.Poly.find_exn node_map t2));
  (graph, node_map_rev)

let detect ~print pvar sorts (graph, components, node_map_rev) res =
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
            let rec get_papps acc = function
              | v1 :: v2 :: tl ->
                  let t1 = Map.Poly.find_exn node_map_rev v1 in
                  let t2 = Map.Poly.find_exn node_map_rev v2 in
                  let papp = ExAtom.PApp ((pvar, sorts), t1 @ t2) in
                  print @@ lazy (ExAtom.str_of papp ^ ",");
                  get_papps (papp :: acc) (v2 :: tl)
              | _ -> acc
            in
            print @@ lazy "A non-WF cycle found: [";
            let papps = get_papps [] cycle in
            print @@ lazy "]\n";
            Set.add acc
              ExClause.
                { positive = Set.Poly.empty; negative = Set.Poly.of_list papps }))
