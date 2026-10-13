(* A census of a value's heap graph, for instruments that ask whether a pass
   kept the sharing of its input.

   [count v] walks [v] as the directed acyclic graph it is in memory and
   returns [(phys, distinct)]: [phys] is the number of physically distinct
   blocks reachable from [v], and [distinct] the number of structurally
   distinct ones (blocks whose contents, read recursively, differ).  So
   [phys = distinct] means every two equal subvalues are one block, and
   [phys / distinct] is how many copies an equal subvalue has on average.

   Contract: [v] holds no abstract or out-of-heap block other than strings,
   floats, custom blocks (hashed by their serialisation) and closures (each
   counted as one constant, as the comparators Base's sets and maps carry
   are the same functions on both sides of a comparison).  A cyclic value is
   not supported (it would not terminate).  The walk forces a full major
   collection first, after which every block is in the major heap, and OCaml
   5 moves a major-heap block only in an explicit compaction, so an address
   names one block for the whole walk; the walk itself allocates only in its
   own tables and never compacts.  Two different structures get the same
   digest with probability about 2^-62, so [distinct] may undercount by such
   collisions.  It costs two table entries per reachable block. *)

let address (o : Obj.t) : int = (Obj.magic o : int) lsr 1

let count (v : 'a) : int * int =
  let root = Obj.repr v in
  Gc.full_major ();
  let memo : (int, int) Hashtbl.t = Hashtbl.create 1_000_000 in
  let digests : (int, unit) Hashtbl.t = Hashtbl.create 1_000_000 in
  let mix h x = ((h * 1_000_003) lxor x) land max_int in
  (* recursive: OCaml 5 grows the stack on the heap, so a deep spine needs
     only memory *)
  let rec go (o : Obj.t) =
    if Obj.is_int o then mix 17 (Obj.obj o : int)
    else
      let key = address o in
      match Hashtbl.find_opt memo key with
      | Some h -> h
      | None ->
          let tag = Obj.tag o in
          let h =
            if tag = Obj.string_tag then Hashtbl.hash (Obj.obj o : string)
            else if tag = Obj.double_tag then Hashtbl.hash (Obj.obj o : float)
            else if tag = Obj.double_array_tag then
              Hashtbl.hash (Marshal.to_string o [])
            else if tag = Obj.custom_tag then
              Hashtbl.hash (Marshal.to_string o [])
            else if tag = Obj.closure_tag || tag = Obj.infix_tag then 7
            else if tag = Obj.forward_tag then go (Obj.field o 0)
            else if tag >= Obj.no_scan_tag then
              failwith (Printf.sprintf "DagCensus.count: a block of tag %d" tag)
            else
              let h = ref (mix tag (Obj.size o)) in
              for i = 0 to Obj.size o - 1 do
                h := mix !h (go (Obj.field o i))
              done;
              !h
          in
          Hashtbl.replace memo key h;
          Hashtbl.replace digests h ();
          h
  in
  ignore (go root : int);
  (Hashtbl.length memo, Hashtbl.length digests)

(* The instrument built on [count]: with COAR_SHARE_CENSUS set in the
   environment, [report label v] prints [count v] with the heap size on
   stderr, as one [share-census] line; unset, it does nothing and walks
   nothing.  It decides nothing.  The variable is read once, at start-up,
   and not through a [lazy]: [report] runs in every solver domain, and a
   [lazy] forced by two domains at once raises [Lazy.Undefined]. *)
let enabled = Option.is_some (Sys.getenv_opt "COAR_SHARE_CENSUS")

let report ?(items = -1) label v =
  if enabled then (
    let t0 = Unix.gettimeofday () in
    let phys, distinct = count v in
    let heap = (Gc.quick_stat ()).Gc.heap_words * 8 / 1_000_000 in
    Printf.eprintf
      "[share-census] %s: items=%d phys=%d distinct=%d ratio=%.2f heap_mb=%d \
       census_s=%.1f\n\
       %!"
      label items phys distinct
      (float_of_int phys /. float_of_int (max 1 distinct))
      heap
      (Unix.gettimeofday () -. t0))
