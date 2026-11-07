(* Maximal sharing of an immutable value: [share v] returns a value
   structurally equal to [v] in which every two structurally equal subvalues
   are one block, so a value that a pass has turned from a graph into a tree
   (a substitution that rebuilds the term it substitutes at every occurrence)
   is a graph again, of the size of its distinct subvalues.

   Contract.  [v] is immutable: no block reachable from it is ever written
   after the call, since two equal blocks become one and a write to one would
   then be seen through the other.  Under that premise [share v] and [v] are
   indistinguishable to any function that does not test physical identity:
   [Stdlib.compare (share v) v = 0], every constructor and field is the same,
   and the closures, custom blocks (big integers among them), lazy values,
   objects and extension constructors (the identity of an extensible
   variant's constructor is the block it points to) of [v] are kept as the
   same blocks, never copied and never entered.  A function that does test
   identity (an address-keyed memo) sees more hits; the memos in this tree
   store a result only when computing it drew no fresh name, so they return
   the same values and draw the same names with or without the sharing.
   Strings are shared by content, which is exact as long as no string
   reachable from [v] is mutated (bytes are not used in terms).  A cyclic
   value is not supported (it would not terminate).

   Cost: one table entry per reachable block of [v] and one per distinct
   block, and a copy of the distinct blocks only.  The walk forces a full
   major collection first, after which every block of [v] is in the major
   heap, where OCaml 5 moves a block only in an explicit compaction, so a
   block's address names it for the whole walk (the new blocks are never
   looked up by address). *)

let address = DagCensus.address

let share (v : 'a) : 'a =
  let root = Obj.repr v in
  Gc.full_major ();
  (* old block (by address) -> (id, canonical value) *)
  let seen : (int, int * Obj.t) Hashtbl.t = Hashtbl.create 1_000_000 in
  (* canonical key -> (id, canonical value) *)
  let canon : (int array, int * Obj.t) Hashtbl.t = Hashtbl.create 100_000 in
  let strings : (string, int * Obj.t) Hashtbl.t = Hashtbl.create 10_000 in
  let next_id = ref 0 in
  let fresh () =
    incr next_id;
    !next_id
  in
  (* Each field has a kind slot (immediate or block) and a value slot,
     so the full range of immediate integers is represented without overflow. *)
  let rec go (o : Obj.t) : int * Obj.t =
    let key = address o in
    match Hashtbl.find_opt seen key with
    | Some r -> r
    | None ->
        let tag = Obj.tag o in
        let r =
          if tag = Obj.string_tag then (
            let s : string = Obj.obj o in
            match Hashtbl.find_opt strings s with
            | Some r -> r
            | None ->
                let r = (fresh (), o) in
                Hashtbl.replace strings s r;
                r)
          else if tag >= Obj.cont_tag then
            (* a continuation, lazy value, closure, object or extension
               constructor, forward pointer, or a block of raw data (custom,
               abstract, float, float array): kept as it is, by identity *)
            (fresh (), o)
          else
            let size = Obj.size o in
            let fields = Array.make size (Obj.repr 0) in
            let k = Array.make ((2 * size) + 2) 0 in
            k.(0) <- tag;
            k.(1) <- size;
            for i = 0 to size - 1 do
              let f = Obj.field o i in
              if Obj.is_int f then (
                fields.(i) <- f;
                k.((2 * i) + 2) <- 0;
                k.((2 * i) + 3) <- (Obj.obj f : int))
              else
                let id, c = go f in
                fields.(i) <- c;
                k.((2 * i) + 2) <- 1;
                k.((2 * i) + 3) <- id
            done;
            match Hashtbl.find_opt canon k with
            | Some r -> r
            | None ->
                (* a block equal to an earlier one would have been found, so
                   this one is new: reuse [o] itself when its fields are
                   already the canonical ones, else copy it *)
                let same = ref true in
                for i = 0 to size - 1 do
                  if not (fields.(i) == Obj.field o i) then same := false
                done;
                let c =
                  if !same then o
                  else
                    let b = Obj.new_block tag size in
                    Array.iteri (fun i f -> Obj.set_field b i f) fields;
                    b
                in
                let r = (fresh (), c) in
                Hashtbl.replace canon k r;
                r
        in
        Hashtbl.replace seen key r;
        r
  in
  if Obj.is_int root then v else Obj.obj (snd (go root))
