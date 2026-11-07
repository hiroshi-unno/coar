(* Thinning the demands a ranking key's re-synthesis states over a long play.

   A counter-play visits a ranked predicate at states [s_0, s_1, .., s_k]
   along a chain segment, and every ordered pair [(s_i, s_j)], [i < j], is a
   chain pair: the ranking must contain it.  The pairs are quadratic in the
   length of the segment, and so is the work of stating each pair as a region
   (one model-based projection per pair).  Two reductions keep that work
   linear-ish, and they differ in what they cost.

   Every instance of the ranking template is transitive (over integer and
   real states).  An instance is
     W(x, y) = (OR_j D_j(y)) /\ OR_i [ D_i(x) /\ AND_j (D_j(y) => ldec(i, j)) ]
   and [ldec(i, j)] holds exactly when the clamped component vectors
   [max(r_i(x), -1)] and [max(r_j(y), -1)] are in the bounded lexicographic
   order [a > b] (some component [k] has [a_k >= 0], [a_k >= b_k + 1], and
   every earlier one [a_l >= b_l]), which is transitive.  Given [W(x, y)] by a
   piece [i] of [x] and [W(y, z)] by a piece [i'] of [y]: [i'] is one of the
   pieces holding at [y], so [r_i(x) > r_i'(y)], and [r_i'(y) > r_k(z)] for
   every piece [k] holding at [z]; hence [r_i(x) > r_k(z)] for each such [k],
   and some piece holds at [z] because [W(y, z)] says so.  So [W(x, z)].

   Consequently a template instance contains a set of ground pairs exactly
   when it contains a transitive reduction of it ([transitive_reduction]):
   dropping a pair implied by transitivity loses no constraint on the
   template's hypothesis space.  Regions are different: a region of a long
   segment is a cube projected at the play's point, and the composition of
   the cubes of its sub-segments need not contain it, so asking regions only
   for visits a bounded number apart ([window_ancestors]) gives the
   synthesiser a weaker demand.  Neither reduction can make an answer
   unsound: a ranking only proposes a strategy, and an answer still comes
   from a won strategy check. *)

open Core

(* A census line on stderr per use of the region construction and of the
   reduction, only when the environment variable
   [COAR_MUSTRAT_LONGPLAY_CENSUS] is set: a measurement instrument that tells
   where the reductions act and what the construction costs, without the
   verbose trace whose printing changes a run's timing.  Nothing is printed
   otherwise. *)
(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let log_enabled =
  Lazy.from_val (Option.is_some (Sys.getenv "COAR_MUSTRAT_LONGPLAY_CENSUS"))

let log msg =
  if Lazy.force log_enabled then (
    Out_channel.output_string stderr ("LONGPLAY " ^ msg ^ "\n");
    Out_channel.flush stderr)

(* [window_ancestors ~window ~equal st ancestors]: the earlier visits of a
   segment that the visit at [st] is paired with when chain pairs become
   regions, [ancestors] being the earlier visits nearest first.  Pre: none.
   Post: the visits whose state differs from [st] (a pair of equal states is
   a revisit, which no ranking contains), all of them when [window <= 0], and
   otherwise the nearest [window] of them, in the input's order.  Skipping
   the equal ones before counting keeps a stutter (a visit repeating the
   previous state) from breaking the chain of nearest pairs. *)
let window_ancestors ~window ~equal st ancestors =
  if window <= 0 then List.filter ancestors ~f:(fun a -> not (equal a st))
  else
    (* stop at the [window]-th distinct one: reading the whole list made a
       long segment's walk quadratic in its visits *)
    let rec take n acc = function
      | [] -> List.rev acc
      | a :: rest ->
          if n <= 0 then List.rev acc
          else if equal a st then take n acc rest
          else take (n - 1) (a :: acc) rest
    in
    take window [] ancestors

(* [effective_window ~window ~min_pairs ~pairs]: the window a play is
   paired with, [pairs] being the number of distinct chain pairs the play
   asks without a window (forced only when needed).  Pre: none.  Post:
   [window] when [window <= 0] or [min_pairs <= 0] or the play asks more
   than [min_pairs] pairs; 0 (every pair a region) otherwise.  A short
   play's regions are cheap, and the long segments' regions the window
   would drop are a demand the composition of the short ones does not
   imply. *)
let effective_window ~window ~min_pairs ~pairs =
  if window > 0 && min_pairs > 0 && Lazy.force pairs <= min_pairs then 0
  else window

(* [dedup_and_sort pairs]: [List.dedup_and_sort ~compare:Stdlib.compare
   pairs], returning a list already strictly sorted as it is.  Pre: none.
   Post: the same list as [List.dedup_and_sort] (a strictly sorted list is
   its own deduplicated sort).  Why: a play's pairs are sorted once where
   they are read off the play and then pass through several such calls,
   each a full merge sort of a list that is quadratic in a segment's length
   (1.1 million pairs, about 2 s a sort with structural comparison of the
   states), where the check is one comparison per pair. *)
let dedup_and_sort pairs =
  if List.is_sorted_strictly pairs ~compare:Stdlib.compare then pairs
  else List.dedup_and_sort ~compare:Stdlib.compare pairs

(* [transitive_reduction pairs]: the pairs of the directed graph [pairs]
   that no path of two or more edges of the graph joins, states compared
   structurally.  Pre: none.  Post: when the graph is acyclic, the result is
   a subset of [pairs] (deduplicated, sorted) whose transitive closure is the
   closure of [pairs] (an edge [a -> b] is dropped only when some other
   successor [c] of [a] reaches [b], and that path is kept by induction on the
   length of the longest path from [a]); so every transitive relation
   contains the result exactly when it contains [pairs].  When the graph has
   a cycle (a self-loop included), [pairs] deduplicated and sorted, unchanged
   otherwise: no well-founded relation contains it either way.

   How, and why this way.  The states are numbered once (a table hashing
   deep into the state, equality [Stdlib.compare = 0], the equality the
   deduplication uses), and a depth-first search gives a topological order
   or finds a cycle.  Then, successors before predecessors, each state [a]
   takes its successors in topological order, nearest first, with a set
   [covered] of the states some earlier successor reaches: a successor in
   [covered] is reached through another successor (one that reaches it
   precedes it in topological order) and its edge is dropped; otherwise the
   edge is kept and [covered] grows by the successor and what it reaches.
   A dropped successor's reach is inside [covered] already, so [covered] is
   in the end everything [a] reaches.  Only kept edges cost a set union, so
   a play's long chain segment -- a visit sequence of length [n] gives all
   [n (n - 1) / 2] ordered pairs, of which the [n - 1] adjacent ones are
   kept -- costs one membership test per pair and one union per adjacent
   pair.  Computing every state's reach as the union over ALL its
   successors, comparing states structurally inside the sets, was cubic on
   such a segment: about 80 s for 1500 visits (1.1 million pairs) of a
   deterministic counter-play. *)
let rec transitive_reduction pairs =
  match reduce_if_acyclic pairs with
  | Some reduced -> reduced
  | None -> dedup_and_sort pairs

(* [reduce_if_acyclic pairs]: [Some (transitive_reduction pairs)] when the
   graph [pairs] is acyclic, [None] when it has a cycle (a self-loop
   included), states compared structurally; so [Option.is_none] of it is
   whether the graph has a cycle, as a depth-first colouring of the states
   decides it.  Pre: none.  One numbering of the states serves both
   questions. *)
and reduce_if_acyclic pairs =
  let pairs = dedup_and_sort pairs in
  let ids = Common.Ext.Hashtbl.PolyDeep.create () in
  let n = ref 0 in
  let id s =
    match Hashtbl.find ids s with
    | Some i -> i
    | None ->
        let i = !n in
        incr n;
        Hashtbl.set ids ~key:s ~data:i;
        i
  in
  (* the pairs are sorted, so a run of pairs shares its first state *)
  let last = ref None in
  let edges =
    List.map pairs ~f:(fun (a, b) ->
        let ia =
          match !last with
          | Some (a', i) when phys_equal a a' -> i
          | _ ->
              let i = id a in
              last := Some (a, i);
              i
        in
        (ia, id b))
  in
  let n = !n in
  let succs = Array.create ~len:n [] in
  List.iter edges ~f:(fun (a, b) -> succs.(a) <- b :: succs.(a));
  (* depth-first: [post] lists the states finished last first, which is a
     topological order when no cycle is met; 1 on the path, 2 finished *)
  let colour = Array.create ~len:n 0 in
  let post = ref [] in
  let exception Cyclic in
  let rec visit a =
    match colour.(a) with
    | 1 -> raise Cyclic
    | 2 -> ()
    | _ ->
        colour.(a) <- 1;
        List.iter succs.(a) ~f:visit;
        colour.(a) <- 2;
        post := a :: !post
  in
  match
    for a = 0 to n - 1 do
      visit a
    done
  with
  | exception Cyclic -> None
  | () ->
      let topo = Array.of_list !post in
      let pos = Array.create ~len:n 0 in
      Array.iteri topo ~f:(fun i a -> pos.(a) <- i);
      let reach = Array.create ~len:n Int.Set.empty in
      let dropped = Hash_set.Poly.create () in
      for i = n - 1 downto 0 do
        let a = topo.(i) in
        let ordered =
          List.sort succs.(a) ~compare:(fun b c -> Int.compare pos.(b) pos.(c))
        in
        reach.(a) <-
          List.fold ordered ~init:Int.Set.empty ~f:(fun covered c ->
              if Set.mem covered c then (
                Hash_set.add dropped (a, c);
                covered)
              else Set.union (Set.add covered c) reach.(c))
      done;
      Some
        (List.filter_map (List.zip_exn pairs edges) ~f:(fun (p, e) ->
             if Hash_set.mem dropped e then None else Some p))

(* Reading chain pairs off a play that shares nodes.

   A play is a derivation whose nodes may be shared: a node used by several
   parents is one node (the ground split keeps one node per ground atom, and
   the play is built once per distinct step).  The chain pairs are defined on
   the play read as a tree, path by path from the root: walking down a path,
   each visit of the ranked predicate at a state [st] is paired with the
   earlier visits of the path's current segment ([ancestors], nearest first),
   and a node of a predicate ranked below the ranked one ([resets]) ends the
   segment.  Read path by path, a play of a few thousand nodes can have
   trillions of paths.

   The ORDER of the tree reading: a node's own pairs (in the order of its
   ancestors), then its children's subtrees left to right.  The walks below
   visit an occurrence of a node only when no occurrence met earlier by the
   walk had the same node and the same list of ancestor states, and that is
   exact:
   - what is emitted within the subtree of an occurrence -- which pairs, how
     many, in which order -- is a function of the node and of the ancestor
     states alone ([state_of] and [resets] read the node, the pairing reads
     the states, never the depths);
   - two occurrences of one node are not ancestor and descendant (the play is
     acyclic), so their subtrees are disjoint intervals of the order, and the
     walk finishes the one it enters first before it enters the other;
   - hence a pruned occurrence emits only pairs the kept one emitted.
   [pairs] reads the pairs as a set, so any order serves.  [pair_segments]
   keeps, per pair, the segment of the LAST occurrence in the tree order (the
   reader it replaces sorted stably by pair and kept the last of each run).
   So it walks the reverse order -- children right to left, then the node's
   own pairs in reverse -- and keeps the first per pair: the reverse of an
   interval order is again one with every subtree an interval, so the
   pruning argument holds as stated, and the first occurrence in the reverse
   order is the last in the tree order.  The property test compares both
   readings on random shared plays.
   Cost: one visit per pair of a node and an ancestor-state list met at it,
   which on a tree is one visit per node, as before. *)

(* [pairs ?nearest_only ~children ~hash ~state_of ~resets root]: every chain
   pair [(a, b)] of the play [root] read path by path, [a] the earlier visit's
   state, deduplicated, sorted, and with the revisits [a = b] removed.  [hash]
   is a hash of a node consistent with physical equality, which is how nodes
   are told apart.  States are compared structurally.

   [~nearest_only:true]: each visit is paired only with the nearest earlier
   visit of its segment (and the pair dropped when the two states are equal).
   Post: the result is a subset of the full one with the same transitive
   closure -- every full pair [(a_k, b)] is joined by the chain of
   consecutive visits [a_k, .., a_1, b] of its segment, each link of which is
   either kept or a revisit, whose two equal states merge.  So whatever is
   invariant under the closure (a transitive relation's containing the pairs,
   their transitive reduction when acyclic, whether they contain a cycle)
   reads the same off either.  The cost is one visit per node and nearest
   state, linear on a long chain, where the full set is quadratic in the
   number of visits of a segment: a single path through a loop run 5,000
   times asks about 12.5 million pairs, whose construction and sorting did
   not finish in 300 s. *)
let pairs (type n s) ?(nearest_only = false) ~(children : n -> n list)
    ~(hash : n -> int) ~(state_of : n -> s option) ~(resets : n -> bool)
    (root : n) : (s * s) list =
  let module NT = Stdlib.Hashtbl.Make (struct
    type t = n

    let equal = phys_equal
    let hash = hash
  end) in
  (* ancestor states by their numbers below: two lists of numbers are equal
     exactly when the lists of states are *)
  let module CT = Stdlib.Hashtbl.Make (struct
    type t = int list

    let equal = List.equal Int.equal
    let hash = Stdlib.Hashtbl.hash_param 100 1000
  end) in
  (* Each distinct state is numbered once, at the visit that meets it
     (equality [Stdlib.compare = 0], the comparison the result is sorted
     by), so the pairs are collected, sorted and deduplicated as pairs of
     numbers.  Why: a segment of [n] visits emits [n (n - 1) / 2] pairs, and
     sorting 1.1 million pairs of states (lists of terms) by structural
     comparison took seconds, where the states are 1,500. *)
  let ids = Common.Ext.Hashtbl.PolyDeep.create () in
  let states = ref [] in
  let count = ref 0 in
  let number st =
    match Hashtbl.find ids st with
    | Some i -> i
    | None ->
        let i = !count in
        incr count;
        Hashtbl.set ids ~key:st ~data:i;
        states := st :: !states;
        i
  in
  let seen = NT.create 256 in
  let acc = ref [] in
  let rec go ancestors node =
    let ctxs =
      match NT.find_opt seen node with
      | Some c -> c
      | None ->
          let c = CT.create 4 in
          NT.replace seen node c;
          c
    in
    if not (CT.mem ctxs ancestors) then (
      CT.replace ctxs ancestors ();
      let ancestors' =
        match state_of node with
        | Some st ->
            let i = number st in
            List.iter ancestors ~f:(fun a -> acc := (a, i) :: !acc);
            if nearest_only then [ i ] else i :: ancestors
        | None -> if resets node then [] else ancestors
      in
      List.iter (children node) ~f:(go ancestors'))
  in
  go [] root;
  (* the numbers renumbered by the states' order, so that pairs of numbers
     sort as the pairs of states do *)
  let by_number = Array.of_list (List.rev !states) in
  let order =
    Array.init (Array.length by_number) ~f:Fn.id
    |> Array.to_list
    |> List.sort ~compare:(fun i j ->
           Stdlib.compare by_number.(i) by_number.(j))
    |> Array.of_list
  in
  let rank = Array.create ~len:(Array.length order) 0 in
  Array.iteri order ~f:(fun r i -> rank.(i) <- r);
  List.map !acc ~f:(fun (a, b) -> (rank.(a), rank.(b)))
  |> List.dedup_and_sort ~compare:(fun (a1, b1) (a2, b2) ->
         match Int.compare a1 a2 with 0 -> Int.compare b1 b2 | c -> c)
  |> List.filter_map ~f:(fun (a, b) ->
         if a = b then None
         else Some (by_number.(order.(a)), by_number.(order.(b))))

(* [pair_segments ~window ~children ~hash ~state_of ~resets root]: per chain
   pair [(a, b)] of the play [root] read path by path, with [a <> b], the
   path segment of its last occurrence in the tree order (see above): the
   nodes from the visit at [a] down to the visit at [b], each with its index
   among its parent's children ([-1] for the root), so that the step from a
   node to the next is known even when a node has two equal children.
   Sorted by pair.  Above 0, [window] pairs each visit only with the
   [window] nearest earlier visits of a different state
   ([window_ancestors]).  Also returns the number of pairs the window
   dropped, counted over the occurrences visited (a census figure; read path
   by path it counted every occurrence).

   [~window_key:true] (read only with [window] above 0) prunes an occurrence
   on its node and the shortest prefix of its ancestor states, nearest
   first, that holds [window + 1] distinct states ([window_prefix]), instead
   of the whole list.  Same result: what a subtree emits is a function of the
   node and that prefix, since every visit below pairs with its nearest
   [window] earlier visits of a state other than its own, read first from
   the visits between and then from the ancestors, and any [window + 1]
   distinct states hold [window] that differ from a given one; the pruning
   argument above then holds as stated with the prefix in place of the list.
   Only the census count of dropped pairs, taken over the occurrences
   visited, is smaller.  Why: on a play that shares nodes, the occurrences
   of a node reached along different paths carry different whole lists of
   ancestor states, so the walk visited a node once per path through the
   segment, and on plays of a few hundred visits it did not finish in 290 s
   (polymorphic equality of the long lists in the pruning table was all of
   its time), where the prefixes are few. *)
let window_prefix ~window ~equal key =
  if window <= 0 then key
  else
    let rec take distinct n acc = function
      | [] -> List.rev acc
      | a :: rest ->
          let distinct, n =
            if List.exists distinct ~f:(equal a) then (distinct, n)
            else (a :: distinct, n + 1)
          in
          if n > window then List.rev (a :: acc)
          else take distinct n (a :: acc) rest
    in
    take [] 0 [] key

let pair_segments (type n s) ?(window_key = false) ~window
    ~(children : n -> n list)
    ~(hash : n -> int) ~(state_of : n -> s option) ~(resets : n -> bool)
    (root : n) : ((s * s) * (n * int) list) list * int =
  let module NT = Stdlib.Hashtbl.Make (struct
    type t = n

    let equal = phys_equal
    let hash = hash
  end) in
  let module CT = Stdlib.Hashtbl.Make (struct
    type t = s list

    let equal = Stdlib.( = )
    let hash = Stdlib.Hashtbl.hash_param 100 1000
  end) in
  let seen = NT.create 256 in
  let skipped = ref 0 in
  (* census only: occurrences entered and pruned *)
  let entered = ref 0 and pruned = ref 0 in
  let prefix_key = window_key && window > 0 in
  (* the emissions in the reverse tree order, latest first *)
  let acc = ref [] in
  let equal (a, _) st = Stdlib.( = ) a st in
  (* The segment's earlier visits as [ancestors] (state and depth, nearest
     first) together with what the walk would otherwise recompute from them
     at every visit, which made a segment of [n] visits cost [n^2]: [key],
     the states alone (the pruning key); [n_anc], the length of
     [ancestors]; [mult], how many of [ancestors] hold each state, so that
     the census count of the distinct ones is [n_anc - mult(st)] (the
     states are compared structurally, as [equal] does). *)
  let empty = ([], [], 0, Map.Poly.empty) in
  let rec go path_rev len_rev (ancestors, key, n_anc, mult) (node, idx) =
    let ctxs =
      match NT.find_opt seen node with
      | Some c -> c
      | None ->
          let c = CT.create 4 in
          NT.replace seen node c;
          c
    in
    if CT.mem ctxs key then incr pruned
    else (
      CT.replace ctxs key ();
      incr entered;
      if !entered land 0xFFFFF = 0 then
        log
          (sprintf "segwalk progress entered=%d pruned=%d nodes=%d" !entered
             !pruned (NT.length seen));
      let path_rev' = (node, idx) :: path_rev in
      let len = len_rev + 1 in
      let here, segment' =
        match state_of node with
        | Some st ->
            let paired = window_ancestors ~window ~equal st ancestors in
            if window > 0 then
              skipped :=
                !skipped + n_anc
                - Option.value ~default:0 (Map.Poly.find mult st)
                - List.length paired;
            ( List.map paired ~f:(fun (a, depth) ->
                  ((a, st), List.rev (List.take path_rev' (len - depth)))),
              ( (st, len_rev) :: ancestors,
                (if prefix_key then
                   window_prefix ~window ~equal:Stdlib.( = ) (st :: key)
                 else st :: key),
                n_anc + 1,
                Map.Poly.update mult st ~f:(function
                  | None -> 1
                  | Some k -> k + 1) ) )
        | None ->
            ([], if resets node then empty else (ancestors, key, n_anc, mult))
      in
      let kids = List.mapi (children node) ~f:(fun i c -> (c, i)) in
      List.iter (List.rev kids) ~f:(go path_rev' len segment');
      List.iter (List.rev here) ~f:(fun e -> acc := e :: !acc))
  in
  go [] 0 empty (root, -1);
  log
    (sprintf "segwalk window=%d window_key=%b entered=%d pruned=%d nodes=%d"
       window prefix_key !entered !pruned (NT.length seen));
  let segments =
    List.rev !acc
    |> List.filter ~f:(fun ((a, b), _) -> not (Stdlib.( = ) a b))
    |> List.stable_sort ~compare:(fun (p1, _) (p2, _) -> Stdlib.compare p1 p2)
    |> List.remove_consecutive_duplicates ~which_to_keep:`First
         ~equal:(fun (p1, _) (p2, _) -> Stdlib.( = ) p1 p2)
  in
  (segments, !skipped)
