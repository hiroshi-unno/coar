(* TODO: Functorize this module and implemente configurations of
   loop detection including verbose, whether use Jhonson's algorithms, and so on. *)

open Core

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
    Set.fold
      ~f:(fun map -> function
        | (_, _), terms ->
            let t1 = List.take terms size in
            let t2 = List.drop terms size in
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
  (map, rmap, !cnt, size)

let gen_graph sample =
  let open Graph in
  let open Pack.Digraph in
  let node_map, node_map_rev, n, size = term_map sample in
  let graph = create ~size:n () in
  Set.iter sample ~f:(fun ((_, _), terms) ->
      let t1 = List.take terms size in
      let t2 = List.drop terms size in
      let e1 = Map.Poly.find_exn node_map t1 in
      let e2 = Map.Poly.find_exn node_map t2 in
      add_edge graph e1 e2);
  (graph, node_map_rev)

let detect res pvar sorts (graph, components, node_map_rev) =
  let open Graph in
  let open Pack.Digraph in
  List.fold ~init:res
    ~f:(fun acc component ->
      if List.length component <= 1 then acc
      else
        let subgraph = create ~size:(List.length component) () in
        let component = Set.Poly.of_list component in
        Set.iter
          ~f:(fun v ->
            List.iter ~f:(fun s ->
                if Set.mem component s then add_edge subgraph v s else ())
            @@ succ graph v)
          component;
        find_cycles subgraph component
        |> List.fold
             ~f:(fun acc cycle ->
               let rec get_papps acc = function
                 | v1 :: v2 :: tl ->
                     let t1, t2 =
                       Map.Poly.
                         (find_exn node_map_rev v1, find_exn node_map_rev v2)
                     in
                     let papp =
                       PCSatCommon.ExAtom.PApp ((pvar, sorts), t1 @ t2)
                     in
                     (* Debug.print ~id @@ lazy (str_of_example papp ^ ","); *)
                     let acc' = papp :: acc in
                     get_papps acc' (v2 :: tl)
                 | _ -> acc
               in
               (* Debug.print ~id @@ lazy "find a cycle:["; *)
               let papps = get_papps [] cycle in
               (* Debug.print ~id @@ lazy "]\n"; *)
               let neg_examples = Set.Poly.of_list papps in
               let clause =
                 PCSatCommon.ExClause.
                   { positive = Set.Poly.empty; negative = neg_examples }
               in
               Set.add acc clause)
             ~init:acc)
    components
