(* A memo keyed by node address, for the passes that rebuild a formula node
   by node and would otherwise turn a shared value into a tree.

   A table maps a node (compared by physical identity, hashed by address) to
   the result computed for it under a context of at most two values, which
   are compared by physical identity too; a lookup under a different context
   misses.  Because the key and the context are compared by identity, a hit
   returns the result of the same computation on the same arguments: for a
   function of its node and its context (and of global state the caller
   promises does not change while the table lives), the result it would
   compute again.  A node that moved in the heap (a promotion, a
   compaction) only misses, since the address picks the bucket and identity
   decides.

   [memo tbl node c1 c2 compute] stores the result only when [compute ()]
   drew no fresh name ([Ident.fresh_stamp] unchanged), so that standing in
   for it later changes neither the value nor the names that later draws
   give: a computation that drew names is redone each time, as without the
   memo.  So a pass wrapped this way returns, value for value and draw for
   draw, what it returns without the memo; only the sharing differs.

   A table is not safe to share between domains; callers keep one per
   domain. *)

module Tbl = Stdlib.Hashtbl.Make (struct
  type t = Stdlib.Obj.t

  let equal = ( == )
  let hash = Common.Ext.Hashtbl.phys_hash
end)

(* each entry: (context 1, context 2, result).  The table is untyped: each
   one must be used by one function only, so that a hit returns a value of
   the type that function computes. *)
type t = (Stdlib.Obj.t * Stdlib.Obj.t * Stdlib.Obj.t) Tbl.t

let create () : t = Tbl.create 1024

let memo (tbl : t) (node : 'k) (c1 : 'a) (c2 : 'b)
    (compute : unit -> 'v) : 'v =
  let key = Stdlib.Obj.repr node in
  let o1 = Stdlib.Obj.repr c1 and o2 = Stdlib.Obj.repr c2 in
  match Tbl.find_opt tbl key with
  | Some (e1, e2, v) when e1 == o1 && e2 == o2 -> Stdlib.Obj.obj v
  | _ ->
      let stamp = Ident.fresh_stamp () in
      let v = compute () in
      if Ident.fresh_stamp () = stamp then
        Tbl.replace tbl key (o1, o2, Stdlib.Obj.repr v);
      v
