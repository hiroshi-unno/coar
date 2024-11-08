open Core

(* parents, heights, data *)
type 'a t = UF of int array * int array * 'a array * ('a -> 'a -> 'a)

let mk_uf ~initial_data ~merge =
  let n = Array.length initial_data in
  let parent = Array.init n ~f:Fn.id in
  let height = Array.init n ~f:(Fn.const 0) in
  UF (parent, height, initial_data, merge)

let mk_unit_uf ~size =
  let initial_data = Array.init size ~f:(Fn.const ()) in
  mk_uf ~initial_data ~merge:(Fn.const (Fn.const ()))

let mk_size_uf ~size =
  let initial_data = Array.init size ~f:(Fn.const 1) in
  mk_uf ~initial_data ~merge:( + )

let rec find node_id = function
  | UF (parent, _, _, _) as uf ->
      let parent_id = parent.(node_id) in
      if parent_id = node_id then parent_id
      else
        let res = find parent_id uf in
        parent.(node_id) <- res;
        res

let unite node_id1 node_id2 = function
  | UF (parent, height, data, merge) as uf ->
      let node_id1 = find node_id1 uf in
      let node_id2 = find node_id2 uf in
      if node_id1 = node_id2 then ()
      else
        let new_node_id =
          if height.(node_id1) < height.(node_id2) then (
            parent.(node_id1) <- node_id2;
            node_id2)
          else (
            parent.(node_id2) <- node_id1;
            if height.(node_id1) <> height.(node_id2) then
              height.(node_id1) <- height.(node_id1) + 1;
            node_id1)
        in
        data.(new_node_id) <- merge data.(node_id1) data.(node_id2)

let is_united node_id1 node_id2 uf = find node_id1 uf = find node_id2 uf

let get_data node_id = function
  | UF (_, _, data, _) as uf -> data.(find node_id uf)

let size = function UF (parent, _, _, _) -> Array.length parent

let get_groups uf =
  let n = size uf in
  let res = Array.init n ~f:(Fn.const []) in
  List.iter (List.init n ~f:Fn.id) ~f:(fun i ->
      let gid = find i uf in
      res.(gid) <- i :: res.(gid));
  Array.to_list res
  |> List.filter ~f:(Fn.non List.is_empty)
  |> List.map ~f:List.rev (* to be sorted *)
