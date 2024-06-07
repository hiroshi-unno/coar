(* TODO: Functorize this module and implemente configurations of
   loop detection including verbose, whether use Jhonson's algorithms, and so on. *)

open Core
open PCSatCommon

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
      let visited = Set.add visited ver in
      let nexts = succ graph ver in
      let next = List.hd_exn nexts in
      inner (ver :: stack) visited next
  in
  let start = Set.choose_exn vertiecs in
  inner [] Set.Poly.empty start

(* ToDo: implement Johnson algorithm to find all cycle *)
let find_cycles graph vertiecs = [ find_cycle graph vertiecs ]

let term_map (sorts, sorts_l, _sorts_r) examples =
  (* size of examples is more than 0 *)
  let open Graph in
  let open Pack.Digraph in
  let cnt = ref 0 in
  let size_param = List.length sorts in
  let size_l = List.length sorts_l in
  let map =
    Set.fold
      ~f:(fun map -> function
        | (_, _), terms ->
            let params = List.take terms size_param in
            let terms = List.drop terms size_param in
            let t1 = params @ List.take terms size_l in
            let t2 = params @ List.drop terms size_l in
            let set term map =
              Map.Poly.update map term ~f:(function
                | None ->
                    incr cnt;
                    V.create !cnt
                | Some n -> n)
            in
            set t2 @@ set t1 map)
      ~init:Map.Poly.empty examples
  in
  let rmap =
    Map.Poly.fold
      ~f:(fun ~key:k ~data:v acc -> Map.Poly.add_exn acc ~key:v ~data:k)
      ~init:Map.Poly.empty map
  in
  (map, rmap, !cnt, (size_param, size_l))

let gen_graph (sorts, sorts_l, sorts_r) sample =
  let open Graph in
  let open Pack.Digraph in
  let node_map, node_map_rev, n, (size_param, size_l) =
    term_map (sorts, sorts_l, sorts_r) sample
  in
  let graph = create ~size:n () in
  Set.iter sample ~f:(fun ((_, _), terms) ->
      let params = List.take terms size_param in
      let terms = List.drop terms size_param in
      let t1 = params @ List.take terms size_l in
      let t2 = params @ List.drop terms size_l in
      let e1 = Map.Poly.find_exn node_map t1 in
      let e2 = Map.Poly.find_exn node_map t2 in
      add_edge graph e1 e2);
  (graph, node_map_rev)

let detect ~print res pvar (sorts, sorts_l, sorts_r)
    (graph, components, node_map_rev) =
  let open Graph in
  let open Pack.Digraph in
  List.fold components ~init:res ~f:(fun acc component ->
      if List.length component <= 1 then acc
      else
        let subgraph = create ~size:(List.length component) () in
        let component = Set.Poly.of_list component in
        Set.iter component ~f:(fun v ->
            List.iter (succ graph v) ~f:(fun s ->
                if Set.mem component s then add_edge subgraph v s else ()));
        find_cycles subgraph component
        |> List.fold ~init:acc ~f:(fun acc cycle ->
               let rec get_papps acc = function
                 | v1 :: v2 :: tl ->
                     let t1, t2 =
                       Map.Poly.
                         (find_exn node_map_rev v1, find_exn node_map_rev v2)
                     in
                     let t2 = List.drop t2 (List.length sorts) in
                     let papp =
                       ExAtom.PApp ((pvar, sorts @ sorts_l @ sorts_r), t1 @ t2)
                     in
                     print @@ lazy (ExAtom.str_of papp ^ ",");
                     let acc' = papp :: acc in
                     get_papps acc' (v2 :: tl)
                 | _ -> acc
               in
               print @@ lazy "find a cycle:[";
               let papps = get_papps [] cycle in
               print @@ lazy "]\n";
               Set.add acc
               @@ ExClause.
                    {
                      positive = Set.Poly.empty;
                      negative = Set.Poly.of_list papps;
                    }))
