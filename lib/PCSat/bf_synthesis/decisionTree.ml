open Core
open Common.Ext
open PCSatCommon

type 'a dtree =
  | Leaf of bool
  | Node of int * 'a dtree * 'a dtree
  | Select of ('a (* score *) * int (* #visited *) * 'a dtree) list
      (** for MCTS *)

let divide q (t : TruthTable.table) (qlist, alist) =
  let palist, nalist =
    Map.Poly.fold alist ~init:(Map.Poly.empty, Map.Poly.empty)
      ~f:(fun ~key:ai ~data:l (palist, nalist) ->
        if t.table.{q, ai} = TruthTable.label_pos then
          (Map.Poly.add_exn ~key:ai ~data:l palist, nalist)
        else if t.table.{q, ai} = TruthTable.label_neg then
          (palist, Map.Poly.add_exn ~key:ai ~data:l nalist)
        else (palist, nalist))
  in
  (List.filter ~f:(( <> ) q) qlist, palist, nalist)

let entropy alist =
  let d_pos, d_neg = TruthTable.num_pos_neg_labeled_atoms alist in
  let p, n = (float_of_int d_pos, float_of_int d_neg) in
  let l =
    if Float.(p > 0.) then
      let x = p /. (p +. n) in
      x *. Float.log2 x
    else 0.
  in
  let r =
    if Float.(n > 0.) then
      let x = n /. (p +. n) in
      x *. Float.log2 x
    else 0.
  in
  let res = -1. *. (l +. r) in
  assert (Float.(res >= 0. && res <= 1.));
  res

let info_gain (d : TruthTable.table) (qlist, alist) q =
  let qlist', palist, nalist = divide q d (qlist, alist) in
  let size_d_q = float_of_int @@ TruthTable.num_atoms palist in
  let size_d_nq = float_of_int @@ TruthTable.num_atoms nalist in
  let size_d = float_of_int @@ TruthTable.num_atoms alist in
  let weighted_entropy_q = entropy palist *. size_d_q /. size_d in
  let weighted_entropy_nq = entropy nalist *. size_d_nq /. size_d in
  ( entropy alist -. (weighted_entropy_q +. weighted_entropy_nq),
    (q, qlist', palist, nalist) )

let choose_qualifier (d : TruthTable.table) (qlist, alist) =
  if Map.is_empty alist then Or_error.error_string "There is no example"
  else if List.is_empty qlist then Or_error.error_string "There is no qualifier"
  else
    Ok
      (List.optimize qlist
         ~f:(info_gain d (qlist, alist))
         ~ord:(fun (ig1, _) (ig2, _) -> Float.(ig1 > ig2)))

let rec build_tree (d : TruthTable.table) (qlist, alist) =
  let d_pos, d_neg = TruthTable.num_pos_neg_labeled_atoms alist in
  if d_neg = 0 then Ok (Leaf true)
  else if d_pos = 0 then Ok (Leaf false)
  else
    let open Or_error in
    choose_qualifier d (qlist, alist)
    >>= fun (_, (q, qlist', palist, nalist)) ->
    build_tree d (qlist', palist) >>= fun t_q ->
    build_tree d (qlist', nalist) >>= fun t_nq -> Ok (Node (q, t_q, t_nq))

let select d (qlist, alist) total_num_visited (coeff, bias) ts =
  let igs =
    List.map qlist ~f:(fun q ->
        let ig, (q, _, _, _) = info_gain d (qlist, alist) q in
        (ig, q))
  in
  if total_num_visited = 0 then
    snd
    @@ List.optimize igs ~f:Fn.id ~ord:(fun (ig1, _) (ig2, _) ->
           Float.(ig1 > ig2))
  else
    let tmp = sqrt Float.(coeff * log (float_of_int total_num_visited)) in
    snd
    @@ List.argmax igs ~f:(fun (ig, q) ->
           let score, num_visited =
             match
               List.find_map ts ~f:(function
                 | score, num_visited, Node (q', _, _) when q = q' ->
                     Some (score, num_visited)
                 | _ -> None)
             with
             | Some (score, num_visited) -> (score, num_visited)
             | None -> (0. (*dummy score*), 0)
           in
           (* UCT-like but the information gain is used as a weight *)
           Float.(
             score + (ig * tmp / sqrt (float_of_int Int.(num_visited + bias)))))

let rec mcts (d : TruthTable.table) (qlist, alist) total_num_visited
    (coeff, bias (* > 0*)) = function
  | Leaf _ -> assert false
  | Node (_, _, _) -> assert false
  | Select ts ->
      let d_pos, d_neg = TruthTable.num_pos_neg_labeled_atoms alist in
      if d_neg = 0 then choose_leaf true ts
      else if d_pos = 0 then choose_leaf false ts
      else if Map.is_empty alist then
        Or_error.error_string "There is no example"
      else if List.is_empty qlist then
        Or_error.error_string "There is no qualifier"
      else
        choose_node d (qlist, alist) total_num_visited (coeff, bias)
          (select d (qlist, alist) total_num_visited (coeff, bias) ts)
          ts

and choose_leaf b ts =
  match
    List.partition_tf ts ~f:(function _, _, Leaf _ -> true | _ -> false)
  with
  | [], ts ->
      (* first visit *) Ok (Select ((0. (*dummy score*), 1, Leaf b) :: ts))
  | [ (score, num_visited, Leaf _) ], ts ->
      Ok (Select ((score, num_visited + 1, Leaf b) :: ts))
  | _, _ -> assert false

and choose_node d (qlist, alist) total_num_visited (coeff, bias) q ts =
  match
    List.partition_tf ts ~f:(function
      | _, _, Node (q', _, _) -> q = q'
      | _ -> false)
  with
  | [], ts ->
      (* first visit *)
      let qlist', palist, nalist = divide q d (qlist, alist) in
      let open Or_error in
      mcts d (qlist', palist) total_num_visited (coeff, bias) (Select [])
      >>= fun t_q ->
      mcts d (qlist', nalist) total_num_visited (coeff, bias) (Select [])
      >>= fun t_nq ->
      Ok (Select ((0. (*dummy score*), 1, Node (q, t_q, t_nq)) :: ts))
  | [ (score, num_visited, Node (_, t_q, t_nq)) ], ts ->
      let qlist', palist, nalist = divide q d (qlist, alist) in
      let open Or_error in
      mcts d (qlist', palist) total_num_visited (coeff, bias) t_q
      >>= fun t_q' ->
      mcts d (qlist', nalist) total_num_visited (coeff, bias) t_nq
      >>= fun t_nq' ->
      Ok (Select ((score, num_visited + 1, Node (q, t_q', t_nq')) :: ts))
  | _, _ -> assert false
