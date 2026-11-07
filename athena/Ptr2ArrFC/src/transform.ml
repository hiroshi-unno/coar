(* The pointer-replacing transformation.

   Every region K becomes a global array [p2a_memK], and a pointer value
   becomes an index into the array of the region it points into, 0 being
   NULL. A typed region's array holds cells of its cell type and is indexed by
   cell; a byte region's array holds unsigned chars and is indexed by byte, in
   the layout of the translated types (pointers become int), and its scalars
   are read and written by generated functions that assemble and split the
   bytes (little-endian, as on the x86 machines the front end describes,
   32-bit and 64-bit alike).

   The rules, one per rule of the definition:

   - types: a pointer type becomes int, everywhere (variables, parameters,
     results, fields, typedefs, casts, sizeof operands);
   - objects: a variable whose address is taken lives in its region. A global
     or static one, or a string literal, has a fixed index; a local one gets a
     fresh block each time its declaring block is entered, and a parameter one
     each time its function is entered, its value copied in from the renamed
     parameter;
   - left values: a variable that is not an object stays a variable; an object
     [v off] or a dereference [*e off] is at index i = base + [off] (array
     indices scaled to cells or bytes; in a byte region field offsets too). In
     a typed region it becomes [p2a_memK[i] fs], fs the field path left inside
     the cell; in a byte region a read is a call of the load function before
     the instruction and a write a call of the store function, a structure
     being read and written scalar by scalar;
   - expressions: an address is its index; pointer arithmetic is index
     arithmetic scaled by the size of the pointed-to type; pointers into one
     region compare as indices; [==] between pointers into different regions
     holds exactly when both are NULL (they cannot point to the same object);
   - allocation: a fresh block from the region's bump allocator, of as many
     cells as the requested bytes hold (a byte region's cells are bytes);
     release does nothing;
   - initialisation: the cells of the static objects are written at the start
     of main (zero, then the initialiser), so the arrays' own initial contents
     never matter.

   In the two safety modes, every pointer location also holds the shadow of
   its value: the first index and the length of the block the value was
   derived from. A pointer variable has two companion variables, a pointer
   parameter two companion parameters, a function returning a pointer a pair
   of globals written before each return, a pointer field two companion
   fields in its structure (so that copying a structure copies the shadows),
   and a region cell holding a pointer directly a place in two parallel
   arrays. The shadow of a value follows the value: it is the block's for an
   address or an allocation, it is not moved by pointer arithmetic or casts,
   and it is (0, 0) for NULL. Before every access through a pointer the index
   is checked against the shadow and the block against the released ones; a
   subscript of an array that is not in a region is checked against the
   array's length. Release checks that the pointer is the start of a live
   block an allocator returned and marks it released, and a local object is
   marked released when its block is left. The two modes check the same
   things and differ only in what a violation does: --assume-safety ends the
   execution normally, so that it stops every execution at its first
   violation; --memory-safety calls a marker. With the split markers (the
   default) the marker names the property violated, in SV-COMP's terms:
   __p2a_violation_valid_deref() for an access or a subscript and
   __p2a_violation_valid_free() for a release, each defined in the output
   as a noreturn function ending the execution with status 77 and 78, and
   only those used are written; the input's own reach_error is then an
   ordinary function of the program. With the reach-error markers every
   violation calls reach_error(), declared only, as consumers that predate
   the split expect; the input's own reach_error is renamed, so that the
   output calls reach_error() for violations alone.

   The safety modes keep a block table per region: at each block's first
   index its kind (static, local, alloca or heap), the cells it occupies (at
   least one, so that two blocks never share a first index) and whether it
   is released. The allocator writes it, main's prelude writes it for the
   static objects, a function that allocates alloca blocks releases them
   when it returns, and a variable-length array is released at the end of
   its scope. Release checks the kind (a heap block).

   --memory-cleanup checks valid-deref and valid-free as --memory-safety
   does, and both check the ends of the execution, when the program
   allocates a heap block: the return from main (the input's main is renamed
   __p2a_main and a new main calls it), exit, and the calls that end the
   execution at once (abort, _Exit, __assert_fail, and reach_error and
   __VERIFIER_error when the program does not define them), except a call
   in the then-branch of a null test of a fresh allocation, which no
   execution reaches since allocation does not fail. At an end,
   --memory-cleanup reports valid-memcleanup when a heap block is not
   released (__p2a_violation_valid_memcleanup(), status 80), and
   --memory-safety reports valid-memtrack when such a block is not tracked
   (__p2a_violation_valid_memtrack(), status 79): no pointer held in a root
   points to it, nor any pointer held in a tracked block. A pointer points
   to the block its shadow names when its value lies in the block or right
   after it. The roots are the globals, the live blocks that are not heap
   blocks, and the variables of the frame the end is in, written to a
   table before the check. The variables holding pointers of the callers of
   a function with an end, which C does not let the check read, are made
   objects (local blocks) for this. Below an end only a halting execution
   is checked: a block lost by an execution that then runs for ever is not
   reported. The check is a fixpoint over the marks of the blocks, or (the
   default) a guessed set S of live heap blocks, drawn from a weak function
   a checking tool may replace, that is reported when it holds a block, no
   root points into it and no live block outside it does: some S passes
   exactly when a live heap block is not tracked. In --memory-safety a
   byte region's parallel shadow arrays say where its pointers are: a
   pointer field stored there has its shadow written to them too, and a
   scalar that is not a pointer clears the shadows of the bytes it
   overwrites. With --memtrack-nonterminating memtrack is also checked at
   every function's entry and every loop's head when a weak probe function
   chooses so, the execution ending there (__p2a_stop) unless the check
   reports; a block lost by an execution that runs for ever is then found
   too (in --memory-cleanup the report is valid-memcleanup).

   memset, memcpy, memmove, realloc, atexit and the string functions strlen,
   strcmp, strcpy, strncpy and strcat are modelled in every mode by
   generated functions that loop over the cells of a region; the safety
   modes check each range they read and write and copy (or clear) the
   shadows of the pointers they copy (or overwrite). atexit numbers the
   functions it registers in a table that exit and the return from main run
   in reverse.

   Contract: [run ()] works in the current project, which must be a copy of
   the input made for the output (see [Rewrite]); it analyses it and rewrites
   it in place. It raises [Unsupported] for a construct outside the fragment
   that only the regions reveal and [Not_implemented] for a construct the
   current stage does not handle; in both cases the project is left in an
   unspecified state and must not be printed. *)

open Cil_types

exception Unsupported of string
exception Not_implemented of string

let unsupported fmt = Format.kasprintf (fun s -> raise (Unsupported s)) fmt
let not_implemented fmt = Format.kasprintf (fun s -> raise (Not_implemented s)) fmt

type safety = Memory_safety | Memory_cleanup | Assume_safety

(* What a violation calls in --memory-safety and --memory-cleanup: one marker
   per property, or reach_error() for every property. *)
type markers = Split | Reach_error

(* How --memory-safety checks valid-memtrack at an end of the execution: by
   computing the tracked blocks (a fixpoint), or by guessing a set of blocks
   and checking in one pass that it is an untracked set holding a live heap
   block. *)
type memtrack_check = Guess | Fixpoint

(* The memory-safety properties a violation is reported as, named as in
   SV-COMP's MemSafety category. *)
type property = Valid_deref | Valid_free | Valid_memtrack | Valid_memcleanup | Uninit_read

let property_name = function
  | Valid_deref -> "valid-deref"
  | Valid_free -> "valid-free"
  | Valid_memtrack -> "valid-memtrack"
  | Valid_memcleanup -> "valid-memcleanup"
  | Uninit_read -> "uninit-read"

(* The split marker of a property: its name before renaming and the exit
   status its definition ends the execution with. *)
let marker_of = function
  | Valid_deref -> ("__p2a_violation_valid_deref", 77)
  | Valid_free -> ("__p2a_violation_valid_free", 78)
  | Valid_memtrack -> ("__p2a_violation_valid_memtrack", 79)
  | Valid_memcleanup -> ("__p2a_violation_valid_memcleanup", 80)
  | Uninit_read -> ("__p2a_violation_uninit_read", 82)

(* The status __p2a_region_exhausted() ends the execution with. *)
let exhausted_status = 81

(* The kinds of block the block table records at a block's first index. *)
let kind_static = 1
let kind_local = 2
let kind_alloca = 3
let kind_heap = 4

(* The kinds of end of the execution an end check is placed at. *)
type end_kind = Main_return | Exit | Abort

let end_kind_name = function Main_return -> "main-return" | Exit -> "exit" | Abort -> "abort"

(* The external functions whose call ends the execution, with the kind of
   end: exit (which runs the atexit functions) and the calls that end it
   without them. reach_error and __VERIFIER_error count only when the input
   does not define them; a defined reach_error ends the execution through
   the __assert_fail its body calls. *)
let end_function_kind name =
  match name with
  | "exit" -> Some Exit
  | "abort" | "_Exit" | "__assert_fail" | "reach_error" | "__VERIFIER_error" -> Some Abort
  | _ -> None

(* The allocators a null test right after the allocation guards: a call in
   the then-branch of such a test is not reached, since an allocation does
   not fail (SV-COMP's rules, and the output's bump allocator). *)
let failing_allocators = [ "malloc"; "calloc"; "realloc"; "alloca"; "__builtin_alloca" ]

(* The allocators of heap blocks, which free releases. *)
let heap_allocators = [ "malloc"; "calloc"; "realloc" ]

let ity = Cil_const.intType
let ulltype = Cil_const.ulongLongType
let lltype = Cil_const.longLongType
let loc0 = Fileloc.unknown
let mk ?(loc = loc0) node = Cil.new_exp ~loc node
let iconst ?(loc = loc0) n = Cil.integer ~loc n
let int_of e = Cil.mkCast ~newt:ity e
let copy = Cil.copy_exp

let add ?(loc = loc0) a b =
  if Cil.isZero b then a else mk ~loc (BinOp (PlusA, a, b, ity))

let scale ?(loc = loc0) e n =
  if n = 1 then e else mk ~loc (BinOp (Mult, e, iconst ~loc n, ity))

(* Type translation. Named and composite types are rewritten in place, once,
   at the end ([retype]); here they stay as they are. *)
let rec tr_type t =
  match t.tnode with
  | TPtr _ -> ity
  | TArray (t', len) -> Cil_const.mk_typ ~tattr:t.tattr (TArray (tr_type t', len))
  | TFun (r, args, va) ->
      Cil_const.mk_typ ~tattr:t.tattr
        (TFun
           ( tr_type r,
             Option.map (List.map (fun (n, t, a) -> (n, tr_type t, a))) args,
             va ))
  | _ -> t

(* The shape of a shadow: int where [t] has a pointer, with [t]'s array
   dimensions; [None] when [t] is not a pointer or an array of pointers. *)
let rec ptr_shape t =
  match Ast_types.unroll_node t with
  | TPtr _ -> Some ity
  | TArray (t', len) -> Option.map (fun s -> Cil_const.mk_tarray s len) (ptr_shape t')
  | _ -> None

type region_info = {
  reg : Regions.region;
  byte : bool;
  sigma : typ;  (** cell type, before translation (unsigned char for bytes) *)
  arr : varinfo;  (** p2a_memK *)
  free : varinfo;  (** p2a_memK_free: the next unused index *)
  alloc : fundec;  (** p2a_allocK (n): n fresh cells *)
  mutable alloc0 : fundec option;  (** the same, zeroed (calloc) *)
  mutable zero : varinfo option;  (** a zero cell, when sigma is a structure *)
  mutable next_static : int;
  access : (string, fundec * fundec) Hashtbl.t;
      (** byte region: load and store function for each scalar type *)
  mutable shadow_arrays : (varinfo * varinfo) option;
      (** safety: the shadows of the pointers held directly in cells *)
  mutable table : (varinfo * varinfo * varinfo) option;
      (** safety: the block table, per block start: its kind, its length in
          cells, released *)
  mutable check : fundec option;  (** safety: the access check *)
  mutable release : fundec option;  (** safety: the checked release *)
  mutable release_alloca : fundec option;
      (** safety: releases the alloca blocks from an index on *)
  mutable release_vla : fundec option;  (** safety: releases one block *)
  mutable flag_read : bool option;
      (** safety: whether anything reads the released flags, once computed
          ([released_flag_read]) *)
  mutable clear : fundec option;
      (** memtrack, byte region: clears the shadows at the bytes a scalar that
          is not a pointer overwrites *)
  mutable mark : varinfo option;
      (** memtrack: per block start, tracked (fixpoint) or guessed (guess) *)
  mutable point : fundec option;
      (** memtrack: what a pointer into this region does to the marks *)
}

(* A variable that starts uninitialised (--uninit), for the record: its
   name in the input, its function, its declaration, its scalar count (None
   for a variable-length array), where it is set to its starting state
   ("block-entry", "function-entry", "jump-source", "declaration") and, with
   --uninit=check, whether its reads are checked. *)
type uninit_target = {
  u_name : string;
  u_var : string;  (** its name in the normalised input (the front end renames a shadowing local) *)
  u_func : string;
  u_loc : Fileloc.t;
  u_leaves : int option;
  u_placed : string list;
  u_checked : bool option;
}

type ctx = {
  st : PointsTo.t;
  regs : Regions.t;
  size : int;  (** length of each region array *)
  unbounded : bool;
      (** --unbounded-regions: the arrays are read as having no length, and
          no index is compared with [size] *)
  safety : safety option;
  infos : (int, region_info) Hashtbl.t;  (** by region id *)
  static_index : (int, int) Hashtbl.t;  (** object variable id -> fixed index *)
  addr_var : (int, varinfo) Hashtbl.t;  (** object variable id -> its index variable *)
  names_used : (string, unit) Hashtbl.t;
  roles : (int, string) Hashtbl.t;
      (** variable id -> role in the record, for the names that are not
          [program]: index (was a pointer), addr (an object's index),
          generated, shadow *)
  mutable pointers : (string * string option * string * int option) list;
      (** the pointer locations of the input: name, function, kind, region *)
  layouts : (int, compinfo) Hashtbl.t;
      (** composite key -> a copy whose fields have the translated types, used
          only to compute the translated layout *)
  mutable pending : instr list;
      (** reversed: loads and checks the expression being translated needs
          first *)
  mutable cur_fd : fundec option;
  (* safety *)
  shadow_vars : (int, varinfo * varinfo) Hashtbl.t;
      (** pointer variable or parameter id -> its companions *)
  companions : (string, fieldinfo * fieldinfo) Hashtbl.t;
      (** "ckey.field" of a pointer field -> its companion fields *)
  companion_names : (string, unit) Hashtbl.t;  (** "ckey.field" of companions *)
  ret_shadow : (int, varinfo * varinfo) Hashtbl.t;
      (** function id -> the globals its pointer result's shadow is passed in *)
  orig_formals : (int, varinfo list) Hashtbl.t;  (** function id -> its parameters *)
  mutable helpers : global list;  (** reversed; placed before the first function *)
  markers : markers;
  mutable violation_fn : varinfo option;
      (** assume-safety: the function a violation calls; memory-safety with
          the reach-error markers: reach_error *)
  mutable marker_fns : (property * varinfo) list;
      (** memory-safety with the split markers: the markers made so far *)
  mutable violation_calls : (instr * property) list;
      (** memory safety and cleanup: every call of a marker a check makes,
          with the property it reports (the instruction itself, compared
          physically: with the reach-error markers one marker stands for
          every property, so the callee does not say which); not the
          reach_error() an exhausted region calls with those markers, which
          reports no violation *)
  mutable check_index : varinfo option;
  wrap : (int * bool -> varinfo) option;
      (** --wrap-integers: the reduction function of an integer kind (width,
          signed) *)
  (* the ends of the execution *)
  memtrack : memtrack_check option;
      (** memory safety: how valid-memtrack is checked at an end *)
  mutable end_check : fundec option;
      (** memory safety and cleanup: the check an end calls, when the program
          has a heap allocation (without one neither property can fail) *)
  mutable end_points : (int * end_kind) list;
      (** reversed: the output statement of each end check, with its kind *)
  unreached : (int, unit) Hashtbl.t;
      (** statement ids of the calls in the then-branch of a null test of a
          fresh allocation, which no execution reaches *)
  memtrack_roots : (int, unit) Hashtbl.t;
      (** ids of the variables made objects so that a check deeper in the call
          stack sees them as roots *)
  mutable site : (varinfo * varinfo * varinfo * varinfo) option;
      (** memtrack: the roots of the function the end is in, written before
          the check: values, shadow bases, regions, count *)
  mutable site_max : int;
  mutable guess_fn : varinfo option;
  nonterminating : bool;
      (** memtrack also where an execution that does not halt passes: at
          every function's entry and every loop's head, chosen
          nondeterministically *)
  mutable mt3_check : fundec option;
      (** the memtrack check at those places (the end check in
          --memory-safety; in --memory-cleanup one that reports
          valid-memcleanup) *)
  mutable mt3_points : (int * string) list;  (** reversed *)
  mutable probe_fn : varinfo option;
  mutable stop_fn : varinfo option;
  fns : (string, varinfo) Hashtbl.t;
      (** the generated functions of the block and string models, by kind
          and regions *)
  atexit_ids : (int, int) Hashtbl.t;
      (** the functions atexit registers, by id, numbered from 1 *)
  mutable atexit_targets : varinfo list;  (** in the order of their numbers *)
  mutable atexit_table : (varinfo * varinfo) option;  (** p2a_atexit_fn, p2a_atexit_n *)
  mutable run_atexit : fundec option;
  mutable exhausted_fn : varinfo option;
      (** safety: the stop at an allocation past the end of a region's array *)
  heap_released : (int, unit) Hashtbl.t;
      (** the ids of the regions a call of free or realloc may release a
          block of *)
  scalar_cells : (int, varinfo * instr) Hashtbl.t;
      (** region id -> the scalar global that holds the region's one cell,
          and the function that makes it arbitrary ([scalar_regions]) *)
  inner_locals : (int, unit) Hashtbl.t;
      (** the ids of the local variables declared in a block nested in their
          function's body, whose block is released when that block ends *)
  mutable overflow_marker : varinfo option;
      (** --check-overflow: the reach_error() the checks call, when the
          program has a signed operation to check (set after [run]) *)
  (* --uninit=check *)
  uninit_check : bool;
  init_vars : (int, varinfo) Hashtbl.t;
      (** the variables whose reads are checked, by id -> the variable that
          holds their state (a check target, a structure parameter that
          receives the state of its argument) *)
  check_targets : (int, unit) Hashtbl.t;  (** the check targets, by id *)
  init_formals : (int, unit) Hashtbl.t;
      (** the structure parameters that receive their argument's state *)
  ret_init : (int, varinfo) Hashtbl.t;
      (** function id -> the global its structure result's state is passed
          in *)
  init_comps : (int, compinfo) Hashtbl.t;  (** structure key -> its state structure *)
  mutable init_comptags : global list;  (** reversed *)
  mutable init_check : varinfo option;
  init_struct_checks : (int, varinfo) Hashtbl.t;  (** state structure key -> its check *)
  init_ones : (int, varinfo) Hashtbl.t;  (** state structure key -> all written *)
  mutable uninit_marker : varinfo option;  (** the normal mode's reach_error *)
  init_counters : (int * int, varinfo) Hashtbl.t;
      (** (function id, depth) -> the loop counter of the state writes *)
  elided : (int * int, unit) Hashtbl.t;
      (** (statement id, variable id): the reads of the variable in the
          statement need no check, every path having written it before *)
  mutable cur_sid : int;  (** the input statement being translated *)
  init_jumped : (int, unit) Hashtbl.t;
      (** the checked variables of a block a jump enters, set also at the
          function's start and before the jump *)
  mutable uninit_targets : uninit_target list;
  mutable uninit_elided : (string * Fileloc.t * string) list;
      (** --uninit=check: the reads left unchecked because every path writes
          them first: function, location, variable *)
  mutable uninit_parameters : (string * string) list;
      (** --uninit=check: the structure parameters that receive their
          argument's state: name, function *)
  mutable uninit_generators : (varinfo * string) list;
      (** --uninit=nondet: the functions that draw the starting values, with
          the kind of value each draws (set after [run]) *)
  bad_call : string option;
      (** the function a call through an invalid function pointer calls (see
          [Defunc]); the safety modes call their invalid-dereference marker
          instead *)
}

let is_object ctx vi = Hashtbl.mem ctx.st.address_taken vi.vid

let fresh_name ctx base =
  let rec go n =
    let cand = if n = 0 then base else Printf.sprintf "%s_%d" base n in
    if Hashtbl.mem ctx.names_used cand then go (n + 1)
    else (Hashtbl.add ctx.names_used cand (); cand)
  in
  go 0

let emit ctx i = ctx.pending <- i :: ctx.pending

let take_pending ctx =
  let l = List.rev ctx.pending in
  ctx.pending <- [];
  l

let temp ctx ty =
  match ctx.cur_fd with
  | Some fd ->
      (* a temporary is assigned, so it drops the qualifiers (const) of the
         left value it stands for *)
      let v = Cil.makeTempVar fd ~name:"p2a_t" (Ast_types.remove_qualifiers ty) in
      Hashtbl.replace ctx.roles v.vid "generated";
      v
  | None -> not_implemented "an access that needs a temporary outside a function"

let field_key ci f = Printf.sprintf "%d.%s" ci.ckey f.fname
let is_companion ctx f = Hashtbl.mem ctx.companion_names (field_key f.fcomp f)
let companions_of ctx f = Hashtbl.find_opt ctx.companions (field_key f.fcomp f)

(* The translated layout: sizes and offsets once pointers are ints, computed by
   the front end's layout rules (its machine description) on copies of the
   composite types whose fields have the translated types. *)
let rec layout_type_in layouts t =
  match Ast_types.unroll_node t with
  | TPtr _ -> ity
  | TArray (t', len) -> Cil_const.mk_tarray (layout_type_in layouts t') len
  | TComp ci -> Cil_const.mk_tcomp (layout_comp_in layouts ci)
  | _ -> Ast_types.unroll t

and layout_comp_in layouts ci =
  match Hashtbl.find_opt layouts ci.ckey with
  | Some c -> c
  | None ->
      let c = Cil_const.copyCompInfo ~fresh:true ci ("p2a_layout_" ^ ci.cname) in
      Hashtbl.add layouts ci.ckey c;
      Option.iter
        (List.iter (fun fi ->
             fi.ftype <- layout_type_in layouts fi.ftype;
             fi.fsize_in_bits <- None;
             fi.foffset_in_bits <- None))
        c.cfields;
      c

let layout_type ctx = layout_type_in ctx.layouts
let layout_comp ctx = layout_comp_in ctx.layouts

(* The byte offset, in the translated layout, of the member an offset [off]
   of an object of type [t] reaches: what offsetof(⟦t⟧, off) computes, and
   what a byte region adds for the same path (i ⊕ off).  [None] when an
   index of the path is not a constant.  For a bit-field, the byte holding
   its first bit. *)
let offset_bytes_in layouts t off =
  let rec go t off acc =
    match off with
    | NoOffset -> Some acc
    | Field (f, off') ->
        let c = layout_comp_in layouts f.fcomp in
        let g =
          match c.cfields with
          | Some fs -> List.find (fun g -> g.fname = f.fname) fs
          | None -> assert false
        in
        go f.ftype off' (acc + (fst (Cil.fieldBitsOffset g) / 8))
    | Index (i, off') -> (
        match (Ast_types.unroll_node t, Cil.constFoldToInt i) with
        | TArray (elt, _), Some k ->
            let w = Cil.bitsSizeOf (layout_type_in layouts elt) / 8 in
            go elt off' (acc + (Z.to_int k * w))
        | _ -> None)
  in
  go t off 0

(* The offsetof expressions of the input ([Offsetof]): each was replaced by a
   read of a placeholder variable, declared nowhere, which the translation of
   expressions turns into the offset in the translated layout of the program
   being written (in safety mode its structures hold the shadow fields, so
   the offset is known only here).  Keyed by the placeholder's vid: the type
   whose member is reached and the path. *)
let offsetof_placeholders : (int, typ * offset) Hashtbl.t = Hashtbl.create 8

let size_bytes ctx t =
  if Ast_types.is_void t then 1 else Cil.bitsSizeOf (layout_type ctx t) / 8

let field_offset ctx ci f =
  let c = layout_comp ctx ci in
  match c.cfields with
  | Some fs -> (
      match List.find_opt (fun g -> g.fname = f.fname) fs with
      | Some g -> fst (Cil.fieldBitsOffset g) / 8
      | None -> assert false)
  | None -> assert false

let info_of_region ctx reg = Hashtbl.find ctx.infos reg.Regions.rid

let info_of_node ctx n =
  match Regions.find ctx.regs n with
  | Some reg -> Some (info_of_region ctx reg)
  | None -> None

let info_of_exp ctx e = info_of_node ctx (PointsTo.ptee ctx.st e)

(* In a safety mode, the shadow of a pointer held in a byte region is in the
   region's parallel arrays, at the pointer's first byte: whether it is held
   directly or as a field of a structure, which a pointer to the field can
   reach either way. The companion fields of a structure stored in the
   region are written too and never read. A region whose pointers point
   nowhere needs none of this. *)
let byte_shadows ctx info =
  ctx.safety <> None && info.byte
  && Regions.find ctx.regs (PointsTo.pt ctx.st info.reg.rep) <> None

let info_of_var ctx vi =
  match info_of_node ctx (PointsTo.var_node ctx.st vi) with
  | Some i -> i
  | None -> assert false (* an object is in a region by construction *)

(* Cells a value of type [t] occupies: sigma cells in a typed region (t is
   sigma or an array of it), bytes of the translated layout in a byte region. *)
let units ctx info t =
  if info.byte then size_bytes ctx t
  else if Regions.same_type (Regions.elem t) info.sigma || Ast_types.is_void t then
    Regions.cells_of t
  else
    not_implemented "a %a in a region of %a cells" Cil_datatype.Typ.pretty t
      Cil_datatype.Typ.pretty info.sigma

(* Cells one step of pointer arithmetic on [e] moves. *)
let step ctx e =
  match (info_of_exp ctx e, Ast_types.unroll_node (Cil.typeOf e)) with
  | Some info, TPtr t -> units ctx info t
  | None, _ -> 1 (* a pointer that only ever holds NULL *)
  | Some _, _ -> assert false

let base_index ctx vi =
  match Hashtbl.find_opt ctx.static_index vi.vid with
  | Some n -> iconst n
  | None -> (
      match Hashtbl.find_opt ctx.addr_var vi.vid with
      | Some a -> Cil.evar a
      | None -> not_implemented "object %s has no index variable" vi.vname)

(* ---- generated globals of the safety modes ---- *)

(* The function named [name] in the output: one of the input, or one this
   transformation has already declared or defined. *)
let find_function ctx name =
  List.find_map
    (function
      | GFun (fd, _) when fd.svar.vname = name -> Some fd.svar
      | GFunDecl (_, vi, _) when vi.vname = name -> Some vi
      | _ -> None)
    ((Ast.get ()).globals @ ctx.helpers)
  |> function
  | Some vi -> vi
  | None -> raise Not_found

(* The function [name] of the output, declared with the given type and
   function-type attributes when there is none yet. *)
let declare_function ?(attrs = []) ctx name ret args =
  try find_function ctx name
  with Not_found ->
    let t =
      Cil_const.mk_tfun ~tattr:attrs ret
        (Some (List.map (fun (n, t) -> (n, t, [])) args))
        false
    in
    let vi = Cil.makeGlobalVar name t in
    Cil.setFormalsDecl vi t;
    Hashtbl.replace ctx.names_used name ();
    ctx.helpers <- GFunDecl (Cil.empty_funspec (), vi, loc0) :: ctx.helpers;
    vi

let add_helper ctx fd =
  Hashtbl.replace ctx.roles fd.svar.vid "generated";
  List.iter (fun v -> Hashtbl.replace ctx.roles v.vid "generated") (fd.sformals @ fd.slocals);
  ctx.helpers <- GFun (fd, loc0) :: ctx.helpers

(* A local of the generated function [fd] with a name no other variable has:
   the end check reads the program's globals, which a local of the same name
   would hide. *)
let fresh_local ctx fd base ty =
  let v = Cil.makeLocalVar fd (fresh_name ctx base) ty in
  Hashtbl.replace ctx.roles v.vid "generated";
  v

let stmt i = Cil.mkStmtOneInstr ~valid_sid:true i
let if_stmt c th el = Cil.mkStmt ~valid_sid:true (If (c, Cil.mkBlock th, Cil.mkBlock el, loc0))

(* [if (c1) s; else if (c2) s; ... else rest]: a disjunction written as
   nested conditionals, the form the front end normalises [||] into, so that
   the output reads back unchanged. *)
let rec if_any conds then_ rest =
  match conds with
  | [] -> rest
  | c :: cs -> [ if_stmt c (then_ ()) (if_any cs then_ rest) ]

let noreturn = [ ("noreturn", []) ]

(* _Exit, which a violation calls to end the execution: the input's when it
   declares it as the C library does (a void function of one integer, or of
   unspecified parameters), declared otherwise. An input that defines _Exit
   or gives the name to anything else would change what a violation does,
   and is refused. *)
let exit_function ?attrs ctx =
  let refuse () =
    unsupported "the name _Exit, which the output calls when a violation ends the execution, is defined or declared otherwise by the input"
  in
  List.iter
    (function
      | GFun (fd, _) when fd.svar.vname = "_Exit" -> refuse ()
      | (GVar (vi, _, _) | GVarDecl (vi, _)) when vi.vname = "_Exit" && not (Ast_types.is_fun vi.vtype) ->
          refuse ()
      | GFunDecl (_, vi, _) when vi.vname = "_Exit" -> (
          match Ast_types.unroll_node vi.vtype with
          | TFun (r, None, _) when Ast_types.is_void r -> ()
          | TFun (r, Some [ (_, t, _) ], false)
            when Ast_types.is_void r && Ast_types.is_integral t -> ()
          | _ -> refuse ())
      | GType (ti, _) when ti.tname = "_Exit" -> refuse ()
      | GEnumTag (ei, _) when List.exists (fun it -> it.einame = "_Exit") ei.eitems ->
          refuse ()
      | _ -> ())
    (Ast.get ()).globals;
  declare_function ?attrs ctx "_Exit" Cil_const.voidType [ ("status", ity) ]

(* The split marker of [prop], defined on first use as a noreturn function
   that ends the execution with the property's status. Its body ends with
   the return the front end gives every function body of type void, so that
   the output reads back unchanged. *)
let split_marker ctx prop =
  match List.assoc_opt prop ctx.marker_fns with
  | Some f -> f
  | None ->
      let name, status = marker_of prop in
      let exit_f = exit_function ~attrs:noreturn ctx in
      let fd = Cil.emptyFunction (fresh_name ctx name) in
      Cil.update_var_type fd.svar
        (Cil_const.mk_tfun ~tattr:noreturn Cil_const.voidType (Some []) false);
      fd.sbody.bstmts <-
        [ stmt (Call (None, Var exit_f, [ iconst status ], loc0));
          Cil.mkStmt ~valid_sid:true (Return (None, loc0)) ];
      add_helper ctx fd;
      Hashtbl.replace ctx.roles fd.svar.vid "marker";
      ctx.marker_fns <- ctx.marker_fns @ [ (prop, fd.svar) ];
      fd.svar

(* The call a violation of [prop] makes, not recorded as one (see
   [violation]). *)
(* --assume-safety's cut, __ptr2arr_assume(c): the execution ends when c is
   0. llvm2lts reads a call of it as a guard on its transition, the
   argument a premise rather than a branch to the end. *)
let cut_fn ctx =
  match ctx.violation_fn with
  | Some f -> f
  | None ->
      let exit_f = exit_function ctx in
      let fd = Cil.emptyFunction (fresh_name ctx "__ptr2arr_assume") in
      Cil.setReturnType fd Cil_const.voidType;
      let c = Cil.makeFormalVar fd "c" ity in
      fd.sbody.bstmts <-
        [ if_stmt
            (mk (UnOp (LNot, Cil.evar c, ity)))
            [ stmt (Call (None, Var exit_f, [ iconst 0 ], loc0)) ]
            [] ];
      add_helper ctx fd;
      ctx.violation_fn <- Some fd.svar;
      fd.svar

let violation_call ctx prop loc =
  match ctx.safety with
  | Some Assume_safety -> Call (None, Var (cut_fn ctx), [ iconst 0 ], loc)
  | Some (Memory_safety | Memory_cleanup) -> (
      match ctx.markers with
      | Split -> Call (None, Var (split_marker ctx prop), [], loc)
      | Reach_error ->
          (* the input's own reach_error was renamed (see [run]), so this
             declares a new one *)
          let f =
            match ctx.violation_fn with
            | Some f -> f
            | None ->
                let f = declare_function ctx "reach_error" Cil_const.voidType [] in
                Hashtbl.replace ctx.roles f.vid "marker";
                ctx.violation_fn <- Some f;
                f
          in
          Call (None, Var f, [], loc))
  | None -> assert false

(* The call a violation of [prop] makes, recorded in [violation_calls] in
   the modes that report violations. *)
let violation ctx prop loc =
  let i = violation_call ctx prop loc in
  (match ctx.safety with
   | Some (Memory_safety | Memory_cleanup) ->
       ctx.violation_calls <- (i, prop) :: ctx.violation_calls
   | Some Assume_safety | None -> ());
  i

(* The negation of a violation condition, as a cut's argument: a comparison
   with its predicate flipped, anything else compared with 0. *)
let negate_cond c =
  let flip op =
    match op with
    | Lt -> Some Ge | Ge -> Some Lt | Gt -> Some Le | Le -> Some Gt
    | Eq -> Some Ne | Ne -> Some Eq
    | _ -> None
  in
  match c.enode with
  | BinOp (op, a, b, t) when flip op <> None -> (
      match flip op with Some op' -> mk (BinOp (op', a, b, t)) | None -> assert false)
  | _ -> mk (BinOp (Eq, c, iconst 0, ity))

(* [rest] when none of [conds] holds, and a violation of [prop] at the first
   that does, the conditions tried in order. In --assume-safety the
   violation ends the execution, so the conditions become one cut each,
   __ptr2arr_assume(!c), in the same order: the same executions end at the
   same point, and the check has no branch, which a verifier reading the
   cut as a guard sees as premises of one transition. *)
let violation_if_any ctx prop conds rest =
  match ctx.safety with
  | Some Assume_safety ->
      List.map (fun c -> stmt (Call (None, Var (cut_fn ctx), [ negate_cond c ], loc0))) conds
      @ rest
  | _ -> if_any conds (fun () -> [ stmt (violation ctx prop loc0) ]) rest

(* An allocation past the end of a region's array: the output cannot
   represent the execution from there on, which says nothing about the
   input. With the split markers and in --assume-safety the execution stops
   at __p2a_region_exhausted(), defined as _Exit(81), which a consumer reads
   as "unknown" (neither a violation nor its absence); with the reach-error
   markers, whose consumers can express no "unknown", it calls reach_error()
   as any violation does, which over-reports and never under-reports. *)
let exhausted_call ctx loc =
  match (ctx.safety, ctx.markers) with
  | Some (Memory_safety | Memory_cleanup), Reach_error -> violation_call ctx Valid_deref loc
  | _ ->
      let f =
        match ctx.exhausted_fn with
        | Some f -> f
        | None ->
            let exit_f = exit_function ~attrs:noreturn ctx in
            let fd = Cil.emptyFunction (fresh_name ctx "__p2a_region_exhausted") in
            Cil.update_var_type fd.svar
              (Cil_const.mk_tfun ~tattr:noreturn Cil_const.voidType (Some []) false);
            fd.sbody.bstmts <-
              [ stmt (Call (None, Var exit_f, [ iconst exhausted_status ], loc0));
                Cil.mkStmt ~valid_sid:true (Return (None, loc0)) ];
            add_helper ctx fd;
            Hashtbl.replace ctx.roles fd.svar.vid "exhausted";
            ctx.exhausted_fn <- Some fd.svar;
            fd.svar
      in
      Call (None, Var f, [], loc)

(* ---- uninitialised reads (--uninit=check) ---- *)

(* The variable holding the state of a variable whose reads are checked. *)
let tracked ctx v = Hashtbl.find_opt ctx.init_vars v.vid

(* The state type of a value of type [t]: [t] with every scalar unsigned char
   (0 not written, 1 written); an array of states for an array, a structure
   of states for a structure. A companion field of the safety modes has no
   state: it is not a field of the program. *)
let rec init_type ctx t =
  match Ast_types.unroll_node t with
  | TArray (t', len) -> Cil_const.mk_tarray (init_type ctx t') len
  | TComp ci when ci.cstruct -> Cil_const.mk_tcomp (init_comp ctx ci)
  | _ -> Cil_const.ucharType

and init_comp ctx ci =
  match Hashtbl.find_opt ctx.init_comps ci.ckey with
  | Some c -> c
  | None ->
      let fields =
        List.filter_map
          (fun f ->
            if is_companion ctx f then None
            else Some (f.fname, init_type ctx f.ftype, None, None, [], loc0))
          (Option.value ~default:[] ci.cfields)
      in
      let c =
        Cil_const.mkCompInfo true (fresh_name ctx ("p2a_init_" ^ ci.cname)) (fun _ -> Some fields) []
      in
      Hashtbl.add ctx.init_comps ci.ckey c;
      ctx.init_comptags <- GCompTag (c, loc0) :: ctx.init_comptags;
      c

let init_field ctx (f : fieldinfo) =
  let c = init_comp ctx f.fcomp in
  match List.find_opt (fun g -> g.fname = f.fname) (Option.value ~default:[] c.cfields) with
  | Some g -> g
  | None -> assert false

(* The state offset of an output offset (its indices translated already). *)
let rec init_offset ctx = function
  | NoOffset -> NoOffset
  | Index (e, o) -> Index (copy e, init_offset ctx o)
  | Field (f, o) -> Field (init_field ctx f, init_offset ctx o)

(* The state of the left value [x off'] of a checked variable, [off'] an
   output offset. *)
let init_lval ctx sv off' = (Var sv, init_offset ctx off')

(* The call an uninitialised read makes: reach_error() in the normal mode
   (the input's own renamed, see [run]), otherwise the safety mode's
   violation of uninit-read (its split marker __p2a_violation_uninit_read,
   reach_error with the reach-error markers, the end of the execution in
   --assume-safety). *)
let uninit_violation ctx loc =
  match ctx.safety with
  | None ->
      let f =
        match ctx.uninit_marker with
        | Some f -> f
        | None ->
            let f = declare_function ctx "reach_error" Cil_const.voidType [] in
            Hashtbl.replace ctx.roles f.vid "marker";
            ctx.uninit_marker <- Some f;
            f
      in
      Call (None, Var f, [], loc)
  | Some _ -> violation ctx Uninit_read loc

(* The loop counter of state writes at [depth] in [fd]. *)
let init_counter ctx fd depth =
  match Hashtbl.find_opt ctx.init_counters (fd.svar.vid, depth) with
  | Some v -> v
  | None ->
      let v = fresh_local ctx fd "p2a_k" ity in
      Hashtbl.add ctx.init_counters (fd.svar.vid, depth) v;
      v

(* The statements that set every scalar of the state left value [lv] (of
   state type [t]) to [c]. *)
let rec init_fill ctx fd ?(depth = 0) lv t c =
  match Ast_types.unroll_node t with
  | TArray (t', len) ->
      let k = init_counter ctx fd depth in
      Cil.mkForIncr ~iter:k ~first:(iconst 0) ~stopat:(iconst (Cil.lenOfArray len))
        ~incr:(iconst 1)
        ~body:(init_fill ctx fd ~depth:(depth + 1) (Cil.addOffsetLval (Index (Cil.evar k, NoOffset)) lv) t' c)
        ()
  | TComp ci ->
      List.concat_map
        (fun f -> init_fill ctx fd ~depth (Cil.addOffsetLval (Field (f, NoOffset)) lv) f.ftype c)
        (Option.value ~default:[] ci.cfields)
  | _ -> [ stmt (Set (lv, Cil.mkCast ~newt:Cil_const.ucharType (iconst c), loc0)) ]

(* p2a_uninit_check(s): an uninitialised read when the state s is 0. *)
let init_check_fn ctx =
  match ctx.init_check with
  | Some f -> f
  | None ->
      let fd = Cil.emptyFunction (fresh_name ctx "p2a_uninit_check") in
      Cil.setReturnType fd Cil_const.voidType;
      let s = Cil.makeFormalVar fd "s" Cil_const.ucharType in
      fd.sbody.bstmts <-
        [ if_stmt (mk (BinOp (Eq, Cil.mkCast ~newt:ity (Cil.evar s), iconst 0, ity)))
            [ stmt (uninit_violation ctx loc0) ] [];
          Cil.mkStmt ~valid_sid:true (Return (None, loc0)) ];
      add_helper ctx fd;
      ctx.init_check <- Some fd.svar;
      fd.svar

(* p2a_uninit_check_S(v), for the state structure S of a structure read
   whole: an uninitialised read when no scalar of v is written. *)
(* The name of the structure a state structure is the state of. *)
let init_comp_base c =
  let p = "p2a_init_" in
  let n = String.length p in
  if String.length c.cname > n && String.sub c.cname 0 n = p then
    String.sub c.cname n (String.length c.cname - n)
  else c.cname

let init_struct_check_fn ctx c =
  match Hashtbl.find_opt ctx.init_struct_checks c.ckey with
  | Some f -> f
  | None ->
      let fd = Cil.emptyFunction (fresh_name ctx ("p2a_uninit_check_" ^ init_comp_base c)) in
      Cil.setReturnType fd Cil_const.voidType;
      let v = Cil.makeFormalVar fd "v" (Cil_const.mk_tcomp c) in
      (* w: some scalar is written; one return, the front end's normal form *)
      let w = fresh_local ctx fd "w" ity in
      let rec any lv t =
        match Ast_types.unroll_node t with
        | TArray (t', len) ->
            let k = fresh_local ctx fd "k" ity in
            Cil.mkForIncr ~iter:k ~first:(iconst 0) ~stopat:(iconst (Cil.lenOfArray len))
              ~incr:(iconst 1)
              ~body:(any (Cil.addOffsetLval (Index (Cil.evar k, NoOffset)) lv) t')
              ()
        | TComp ci ->
            List.concat_map
              (fun f -> any (Cil.addOffsetLval (Field (f, NoOffset)) lv) f.ftype)
              (Option.value ~default:[] ci.cfields)
        | _ -> [ if_stmt (Cil.mkCast ~newt:ity (mk (Lval lv))) [ stmt (Set (Cil.var w, iconst 1, loc0)) ] [] ]
      in
      fd.sbody.bstmts <-
        (stmt (Set (Cil.var w, iconst 0, loc0)) :: any (Cil.var v) (Cil_const.mk_tcomp c))
        @ [ if_stmt (mk (BinOp (Eq, Cil.evar w, iconst 0, ity))) [ stmt (uninit_violation ctx loc0) ] [];
            Cil.mkStmt ~valid_sid:true (Return (None, loc0)) ];
      add_helper ctx fd;
      Hashtbl.add ctx.init_struct_checks c.ckey fd.svar;
      fd.svar

(* p2a_init_ones_S(): the state of a structure every scalar of which is
   written (a value that comes from no checked variable). *)
let init_ones_fn ctx c =
  match Hashtbl.find_opt ctx.init_ones c.ckey with
  | Some f -> f
  | None ->
      let t = Cil_const.mk_tcomp c in
      let fd = Cil.emptyFunction (fresh_name ctx ("p2a_init_ones_" ^ init_comp_base c)) in
      Cil.setReturnType fd t;
      let r = fresh_local ctx fd "r" t in
      fd.sbody.bstmts <-
        init_fill ctx fd (Cil.var r) t 1
        @ [ Cil.mkStmt ~valid_sid:true (Return (Some (Cil.evar r), loc0)) ];
      add_helper ctx fd;
      Hashtbl.add ctx.init_ones c.ckey fd.svar;
      fd.svar

let byte_array ctx name =
  let v =
    Cil.makeGlobalVar (fresh_name ctx name)
      (Cil_const.mk_tarray Cil_const.ucharType (Some (iconst ctx.size)))
  in
  Hashtbl.replace ctx.roles v.vid "generated";
  ctx.helpers <- GVar (v, { init = None }, loc0) :: ctx.helpers;
  v

let int_array ctx name role =
  let v = Cil.makeGlobalVar (fresh_name ctx name) (Cil_const.mk_tarray ity (Some (iconst ctx.size))) in
  Hashtbl.replace ctx.roles v.vid role;
  ctx.helpers <- GVar (v, { init = None }, loc0) :: ctx.helpers;
  v

let shadow_arrays ctx info =
  match info.shadow_arrays with
  | Some p -> p
  | None ->
      let k = info.reg.rid in
      let p =
        ( int_array ctx (Printf.sprintf "p2a_mem%d__base" k) "shadow",
          int_array ctx (Printf.sprintf "p2a_mem%d__len" k) "shadow" )
      in
      info.shadow_arrays <- Some p;
      p

(* The block table of a region: at the first index of every block, its kind
   (kind_static .. kind_heap; 0 at every other index), the cells it occupies
   (at least one, so that blocks never share a first index) and whether it is
   released. The allocator writes the first two; the blocks lie one after the
   other from index 1, so the blocks below the next free index are
   enumerated by stepping by their lengths. *)
let block_table ctx info =
  match info.table with
  | Some p -> p
  | None ->
      let k = info.reg.rid in
      let p =
        ( byte_array ctx (Printf.sprintf "p2a_mem%d__kind" k),
          int_array ctx (Printf.sprintf "p2a_mem%d__blen" k) "generated",
          byte_array ctx (Printf.sprintf "p2a_mem%d__freed" k) )
      in
      info.table <- Some p;
      p

let freed_array ctx info =
  let _, _, f = block_table ctx info in
  f

let uchar_one = Cil.mkCast ~newt:Cil_const.ucharType (iconst 1)
let bin op a b = mk (BinOp (op, a, b, ity))
let aidx a i = (Var a, Index (i, NoOffset))
let rd a i = mk (Lval (aidx a i))

(* The comparisons of an index with the length N of a region's array (and of
   the atexit table, which has the same length). With --unbounded-regions an
   array has no length: every index is below it, so the comparison is not
   emitted. [below_size] is [None] for "always", [at_or_above_size] [None]
   for "never". *)
let below_size ctx e = if ctx.unbounded then None else Some (bin Lt e (iconst ctx.size))
let at_or_above_size ctx e = if ctx.unbounded then None else Some (bin Ge e (iconst ctx.size))

(* [th] when the index [e] is below the length. *)
let when_below ctx e th = match below_size ctx e with None -> th | Some c -> [ if_stmt c th [] ]

(* The loop over the blocks of a region below its next free index: [body b]
   for each block's first index b. The table never reaches past the array:
   the walk stops there (an allocation beyond it is caught at its first
   access); an unbounded array has no end to stop at. *)
let blocks_loop ?(from = iconst 1) ctx info fd body =
  let _, blen, _ = block_table ctx info in
  let b = fresh_local ctx fd "p2a_b" ity in
  Cil.mkFor
    ~start:[ stmt (Set (Cil.var b, from, loc0)) ]
    ~guard:(bin Lt (Cil.evar b) (Cil.evar info.free))
    ~next:[ stmt (Set (Cil.var b, bin PlusA (Cil.evar b) (rd blen (Cil.evar b)), loc0)) ]
    ~body:
      ((match at_or_above_size ctx (Cil.evar b) with
        | Some c -> [ if_stmt c [ Cil.mkStmt ~valid_sid:true (Break loc0) ] [] ]
        | None -> [])
       @ body (Cil.evar b))
    ()

(* p2a_release_allocaK(from): the alloca blocks (and variable-length
   arrays) from index [from] on are released, [from] being the next free index
   when the function that allocated them was entered: called as it returns,
   which ends their lifetime. *)
let release_alloca_fn ctx info =
  match info.release_alloca with
  | Some f -> f.svar
  | None ->
      let kind, _, freed = block_table ctx info in
      let fd =
        Cil.emptyFunction (fresh_name ctx (Printf.sprintf "p2a_release_alloca%d" info.reg.rid))
      in
      Cil.setReturnType fd Cil_const.voidType;
      let from = Cil.makeFormalVar fd "from" ity in
      fd.sbody.bstmts <-
        blocks_loop ~from:(Cil.evar from) ctx info fd (fun b ->
            [ if_stmt
                (bin Eq (Cil.mkCast ~newt:ity (rd kind b)) (iconst kind_alloca))
                [ stmt (Set (aidx freed (copy b), uchar_one, loc0)) ]
                [] ]);
      add_helper ctx fd;
      info.release_alloca <- Some fd;
      fd.svar

(* p2a_release_vlaK(i): the variable-length array whose block starts at i is
   released, at the end of its scope. *)
let release_vla_fn ctx info =
  match info.release_vla with
  | Some f -> f.svar
  | None ->
      let _, _, freed = block_table ctx info in
      let fd =
        Cil.emptyFunction (fresh_name ctx (Printf.sprintf "p2a_release_vla%d" info.reg.rid))
      in
      Cil.setReturnType fd Cil_const.voidType;
      let i = Cil.makeFormalVar fd "i" ity in
      fd.sbody.bstmts <-
        [ if_stmt (bin Gt (Cil.evar i) (iconst 0))
            (when_below ctx (Cil.evar i) [ stmt (Set (aidx freed (Cil.evar i), uchar_one, loc0)) ])
            [] ];
      add_helper ctx fd;
      info.release_vla <- Some fd;
      fd.svar

(* Can a block of the region be read after its release, so that an access
   must also check that its block is not released? A heap block that a call
   of free or realloc may release, a variable-length array and an
   address-taken local declared in a nested block (each at the end of its
   scope) are released while the function that holds the pointer still runs;
   a heap block no such call can reach is never released. An alloca block,
   and an address-taken local of the function's outermost block or a
   parameter, is released when the function returns, and a pointer to it
   outlives that function only
   when it is stored where the function's frame does not hold it: in a cell
   of any region (a pointer into the region in memory, which the region's
   class reaches as some region's successor), in a global variable, or as a
   function's result. When none of these holds, no execution reads a
   released block, and the check of the released flag can be left out: the
   flags are not read by an access (and under --assume-safety, where nothing
   else reads them, not written either: [released_flag_read]). The test is on
   the points-to classes, which over-approximate, so it errs towards keeping
   the check. *)
(* The regions a call of free or realloc may release a block of: those its
   pointer argument may point into. A heap block of any other region is never
   released. *)
let released_regions st regs file =
  let tbl = Hashtbl.create 8 in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vinst i =
        (match i with
         | Call (_, Var f, p :: _, _) | Local_init (_, ConsInit (f, p :: _, _), _)
           when List.mem f.vname [ "free"; "realloc" ] && not (PointsTo.is_defined f) -> (
             match Regions.find regs (PointsTo.ptee st p) with
             | Some reg -> Hashtbl.replace tbl reg.Regions.rid ()
             | None -> ())
         | _ -> ());
        Cil.SkipChildren
    end
  in
  Visitor.visitFramacFileSameGlobals v file;
  tbl

(* The local variables declared in a block nested in their function's body:
   an object among them has its block released when that block ends, while
   the function still runs. *)
let inner_scope_locals file =
  let tbl = Hashtbl.create 8 in
  let rec block ~top b =
    if not top then List.iter (fun v -> Hashtbl.replace tbl v.vid ()) b.blocals;
    List.iter
      (fun s ->
        match s.skind with
        | If (_, b1, b2, _) -> block ~top:false b1; block ~top:false b2
        | Loop (_, b', _, _, _) | Switch (_, b', _, _) | Block b' -> block ~top:false b'
        | _ -> ())
      b.bstmts
  in
  List.iter (function GFun (fd, _) -> block ~top:true fd.sbody | _ -> ()) file.globals;
  tbl

(* Can a pointer into region [reg] outlive the function that holds it: is
   one stored in a cell of any region (some region's successor is [reg]), in
   a global variable, or returned by a function? *)
let pointers_escape st (regs : Regions.t) file (reg : Regions.region) =
  let k = PointsTo.find reg.rep in
  let into n =
    match (PointsTo.find n).pt with Some p -> PointsTo.find p == k | None -> false
  in
  List.exists (fun (r : Regions.region) -> into r.rep) regs.list
  || Hashtbl.fold (fun _ n acc -> acc || into n) st.PointsTo.rets false
  || List.exists
       (function
         | GVar (vi, _, _) | GVarDecl (vi, _) -> (
             match Hashtbl.find_opt st.PointsTo.vars vi.vid with Some n -> into n | None -> false)
         | _ -> false)
       file.globals

let may_read_released ctx info =
  let released_in_scope =
    Hashtbl.mem ctx.heap_released info.reg.rid
    || List.exists
         (function
           | Regions.Alloc site -> site.PointsTo.allocator = "__fc_vla_alloc"
           | Regions.Var v -> Hashtbl.mem ctx.inner_locals v.vid)
         info.reg.objects
  in
  let released_at_return =
    List.exists
      (function
        | Regions.Alloc site -> List.mem site.PointsTo.allocator [ "alloca"; "__builtin_alloca" ]
        | Regions.Var v -> not v.vglob)
      info.reg.objects
  in
  released_in_scope
  || (released_at_return && pointers_escape ctx.st ctx.regs (Ast.get ()) info.reg)

(* Does anything read a released flag of the region? Writing one is otherwise
   a dead store, and the marking can be left out: the output then behaves as
   before at every step, since the flags enter no condition. In
   --assume-safety the readers are the access check, which reads them only
   under [may_read_released], and the checked release (free, realloc), whose
   regions [may_read_released] covers as released in scope; the end checks,
   which read every flag, exist only in --memory-safety and --memory-cleanup,
   where the flags are always kept. Leaving the marking out matters to a
   termination prover: releasing the alloca blocks as a function returns is a
   loop over the block table whose termination rests on every block length
   being positive, a fact about array contents that a function with no such
   loop never needs. *)
let released_flag_read ctx info =
  match info.flag_read with
  | Some r -> r
  | None ->
      let r = ctx.safety <> Some Assume_safety || may_read_released ctx info in
      info.flag_read <- Some r;
      r

(* p2a_checkK(i, w, base, len): the w cells at i lie in the block [base,
   base + len), and the block is not released (checked only where a block
   of the region may be read after its release, [may_read_released]). The
   block's first index is checked to be in the array before it is used. *)
let check_fn ctx info =
  match info.check with
  | Some f -> f.svar
  | None ->
      let fd = Cil.emptyFunction (fresh_name ctx (Printf.sprintf "p2a_check%d" info.reg.rid)) in
      Cil.setReturnType fd Cil_const.voidType;
      let i = Cil.makeFormalVar fd "i" ity in
      let w = Cil.makeFormalVar fd "w" ity in
      let b = Cil.makeFormalVar fd "base" ity in
      let l = Cil.makeFormalVar fd "len" ity in
      let v = Cil.evar in
      let bin op a b = mk (BinOp (op, a, b, ity)) in
      let off = bin MinusA (v i) (v b) in
      let conds =
        [ bin Lt (v b) (iconst 0) ]
        @ Option.to_list (at_or_above_size ctx (v b))
        @ [ bin Lt off (iconst 0);
          bin Gt (bin PlusA (bin MinusA (v i) (v b)) (v w)) (v l) ]
        @
        if may_read_released ctx info then
          [ mk (Lval (Var (freed_array ctx info), Index (v b, NoOffset))) ]
        else []
      in
      fd.sbody.bstmts <- violation_if_any ctx Valid_deref conds [];
      add_helper ctx fd;
      info.check <- Some fd;
      fd.svar

(* p2a_freeK(i, base): release of the block whose pointer is i, with shadow
   base. NULL is a no-op; otherwise i must be the start of a block an
   allocator returned that is not yet released. *)
let release_fn ctx info =
  match info.release with
  | Some f -> f.svar
  | None ->
      let kind, _, freed = block_table ctx info in
      let fd = Cil.emptyFunction (fresh_name ctx (Printf.sprintf "p2a_free%d" info.reg.rid)) in
      Cil.setReturnType fd Cil_const.voidType;
      let i = Cil.makeFormalVar fd "i" ity in
      let b = Cil.makeFormalVar fd "base" ity in
      let v = Cil.evar in
      let bin op a b = mk (BinOp (op, a, b, ity)) in
      let cell a = (Var a, Index (v b, NoOffset)) in
      let bad =
        [ bin Ne (v i) (v b); bin Lt (v b) (iconst 0) ]
        @ Option.to_list (at_or_above_size ctx (v b))
        @ [ bin Ne (Cil.mkCast ~newt:ity (mk (Lval (cell kind)))) (iconst kind_heap);
          mk (Lval (cell freed)) ]
      in
      fd.sbody.bstmts <-
        [ if_stmt (bin Ne (v i) (iconst 0))
            (violation_if_any ctx Valid_free bad
               [ stmt (Set (cell freed, Cil.mkCast ~newt:Cil_const.ucharType (iconst 1), loc0)) ])
            [] ];
      add_helper ctx fd;
      info.release <- Some fd;
      fd.svar

(* p2a_check_index(j, n): 0 <= j < n, for a subscript of an array that is not
   in a region. *)
let check_index_fn ctx =
  match ctx.check_index with
  | Some f -> f
  | None ->
      let fd = Cil.emptyFunction (fresh_name ctx "p2a_check_index") in
      Cil.setReturnType fd Cil_const.voidType;
      let j = Cil.makeFormalVar fd "j" lltype in
      let n = Cil.makeFormalVar fd "n" lltype in
      let bin op a b = mk (BinOp (op, a, b, ity)) in
      fd.sbody.bstmts <-
        violation_if_any ctx Valid_deref
          [ bin Lt (Cil.evar j) (Cil.kinteger ~loc:loc0 ILongLong 0);
            bin Ge (Cil.evar j) (Cil.evar n) ]
          [];
      add_helper ctx fd;
      ctx.check_index <- Some fd.svar;
      fd.svar

(* ---- byte regions ---- *)

(* Byte-region scalars: the type a scalar is read and written as. *)
let scalar_tag t =
  let of_ikind = function
    | IBool -> "bool" | IChar -> "char" | ISChar -> "schar" | IUChar -> "uchar"
    | IInt -> "int" | IUInt -> "uint" | IShort -> "short" | IUShort -> "ushort"
    | ILong -> "long" | IULong -> "ulong" | ILongLong -> "llong"
    | IULongLong -> "ullong"
    | IInt128 | IUInt128 -> not_implemented "a 128-bit integer in a byte region"
  in
  match Ast_types.unroll_node t with
  | TPtr _ -> Some ("int", ity)
  | TInt ik -> Some (of_ikind ik, Cil_const.mk_tint ik)
  | TEnum ei -> Some (of_ikind ei.ekind, Cil_const.mk_tint ei.ekind)
  | TFloat _ -> not_implemented "a floating-point value in a byte region"
  | _ -> None

(* The load and store functions of a byte region for scalar type [t]:
   [p2a_loadK_t(i)] assembles the value from the bytes at i, least significant
   first; [p2a_storeK_t(i, v)] splits it back. The bytes are combined in an
   unsigned long long, and the conversions between it and the scalar type are
   the C conversions: to an unsigned type modulo 2^w, to a signed type the
   two's-complement reinterpretation gcc defines. *)
let accessors ctx info t =
  let tag, ty =
    match scalar_tag t with Some p -> p | None -> assert false
  in
  match Hashtbl.find_opt info.access tag with
  | Some p -> p
  | None ->
      let k = info.reg.rid in
      let n = size_bytes ctx t in
      let c256 = Cil.kinteger ~loc:loc0 IULongLong 256 in
      let cell j i = (Var info.arr, Index (add (Cil.evar i) (iconst j), NoOffset)) in
      let ld = Cil.emptyFunction (fresh_name ctx (Printf.sprintf "p2a_load%d_%s" k tag)) in
      Cil.setReturnType ld ty;
      let i = Cil.makeFormalVar ld "i" ity in
      let u = Cil.makeLocalVar ld "u" ulltype in
      let body = ref [ stmt (Set (Cil.var u, Cil.kinteger ~loc:loc0 IULongLong 0, loc0)) ] in
      for j = n - 1 downto 0 do
        body :=
          stmt
            (Set
               ( Cil.var u,
                 mk
                   (BinOp
                      ( PlusA,
                        mk (BinOp (Mult, Cil.evar u, copy c256, ulltype)),
                        mk (CastE (ulltype, mk (Lval (cell j i)))),
                        ulltype )),
                 loc0 ))
          :: !body
      done;
      (* with --wrap-integers the conversions that are reductions are written
         as such, so that the functions also mean their C meaning when
         integers are read as mathematical integers *)
      let kind_of ty =
        match Ast_types.unroll_node ty with
        | TInt IBool -> None
        | TInt ik -> Some (Cil.bitsSizeOfInt ik, Cil.isSigned ik)
        | _ -> None
      in
      let result =
        match (ctx.wrap, kind_of ty) with
        | Some w, Some k ->
            let r = Cil.makeLocalVar ld "r" ty in
            [ stmt (Call (Some (Cil.var r), Var (w k), [ Cil.evar u ], loc0));
              Cil.mkStmt ~valid_sid:true (Return (Some (Cil.evar r), loc0)) ]
        | _ -> [ Cil.mkStmt ~valid_sid:true (Return (Some (mk (CastE (ty, Cil.evar u))), loc0)) ]
      in
      ld.sbody.bstmts <- List.rev !body @ result;
      let sf = Cil.emptyFunction (fresh_name ctx (Printf.sprintf "p2a_store%d_%s" k tag)) in
      Cil.setReturnType sf Cil_const.voidType;
      let i' = Cil.makeFormalVar sf "i" ity in
      let v = Cil.makeFormalVar sf "v" ty in
      let u' = Cil.makeLocalVar sf "u" ulltype in
      let first =
        match (ctx.wrap, kind_of ty) with
        | Some w, Some _ -> Call (Some (Cil.var u'), Var (w (64, false)), [ Cil.evar v ], loc0)
        | _ -> Set (Cil.var u', mk (CastE (ulltype, Cil.evar v)), loc0)
      in
      let body = ref [ stmt first ] in
      for j = 0 to n - 1 do
        body :=
          stmt (Set (Cil.var u', mk (BinOp (Div, Cil.evar u', copy c256, ulltype)), loc0))
          :: stmt
               (Set
                  ( cell j i',
                    mk
                      (CastE
                         ( Cil_const.ucharType,
                           mk (BinOp (Mod, Cil.evar u', copy c256, ulltype)) )),
                    loc0 ))
          :: !body
      done;
      sf.sbody.bstmts <- List.rev !body;
      List.iter
        (fun fd ->
          Hashtbl.replace ctx.roles fd.svar.vid "generated";
          List.iter
            (fun v -> Hashtbl.replace ctx.roles v.vid "generated")
            (fd.sformals @ fd.slocals))
        [ ld; sf ];
      Hashtbl.add info.access tag (ld, sf);
      (ld, sf)

(* A one-byte scalar of a byte region is its cell itself: the load and store
   functions would assemble it from that one byte and split it back into it,
   so its reads and writes go to the cell directly, with the C conversions
   between the scalar's type and unsigned char the functions make (an
   unsigned char goes through unsigned long long and back unchanged). Not
   with --wrap-integers, whose functions write the conversions that are
   reductions explicitly. *)
let direct_byte ctx t =
  ctx.wrap = None
  && match scalar_tag t with Some _ -> size_bytes ctx t = 1 | None -> false

let byte_cell info i = (Var info.arr, Index (i, NoOffset))

let read_byte info t i loc =
  match scalar_tag t with
  | Some (_, ty) -> mk ~loc (CastE (ty, mk ~loc (Lval (byte_cell info i))))
  | None -> assert false

let write_byte info i v loc = Set (byte_cell info i, mk ~loc (CastE (Cil_const.ucharType, v)), loc)

(* Bit-fields of a byte region.  A bit-field occupies [width] bits from bit
   [shift] of the byte its offset names, over [nb] bytes; the bytes are
   least significant first, as the load and store functions read them, so
   the field is the value of those bytes divided by 2^shift modulo 2^width
   (gcc's layout on the little-endian x86 machine descriptions).  Written
   with division and remainder by powers of two, not shifts and masks: the
   consumers read integers mathematically (llvm2lts's Int modes), where these
   are what the bit operations compute on non-negative values. *)
let bit_place ctx f =
  let c = layout_comp ctx f.fcomp in
  let g =
    match c.cfields with
    | Some fs -> List.find (fun g -> g.fname = f.fname) fs
    | None -> assert false
  in
  let off, width = Cil.fieldBitsOffset g in
  let shift = off mod 8 in
  (shift, width, (shift + width + 7) / 8)

let ull z = Cil.kinteger64 ~loc:loc0 ~kind:IULongLong z
let pow2 k = Z.shift_left Z.one k

(* The bit-field the last field of a left value is, if it is one. *)
let last_bitfield (_, off) =
  let rec last = function
    | Field (f, NoOffset) -> Some f
    | Field (_, o) | Index (_, o) -> last o
    | NoOffset -> None
  in
  match last off with Some f when f.fbitfield <> None -> Some f | _ -> None

(* [u := the nb bytes from i] *)
let gather_bytes info i nb u loc =
  Set (u, ull Z.zero, loc)
  :: List.init nb (fun k ->
         let j = nb - 1 - k in
         Set
           ( u,
             mk
               (BinOp
                  ( PlusA,
                    mk (BinOp (Mult, mk (Lval u), ull (Z.of_int 256), ulltype)),
                    mk (CastE (ulltype, mk (Lval (byte_cell info (add (copy i) (iconst j)))))),
                    ulltype )),
             loc ))

(* The instructions reading bit-field [f] at byte [i] into a temporary, and
   the value: the field's bits, sign-extended for a signed field. *)
let load_bitfield ctx info i f loc =
  let shift, width, nb = bit_place ctx f in
  let u = Cil.var (temp ctx ulltype) in
  let ins =
    gather_bytes info i nb u loc
    @ [ Set (u, mk (BinOp (Div, mk (Lval u), ull (pow2 shift), ulltype)), loc);
        Set (u, mk (BinOp (Mod, mk (Lval u), ull (pow2 width), ulltype)), loc) ]
  in
  let ft = Ast_types.unroll f.ftype in
  let signed = match Ast_types.unroll_node ft with TInt k -> Cil.isSigned k | TEnum ei -> Cil.isSigned ei.ekind | _ -> false in
  let ll = Cil_const.longLongType in
  let value =
    if signed then
      (* u - 2^width when the sign bit, bit width-1, is set *)
      mk ~loc
        (CastE
           ( ft,
             mk
               (BinOp
                  ( MinusA,
                    mk (CastE (ll, mk (Lval u))),
                    mk
                      (CastE
                         ( ll,
                           mk
                             (BinOp
                                ( Mult,
                                  mk (BinOp (Div, mk (Lval u), ull (pow2 (width - 1)), ulltype)),
                                  ull (pow2 width),
                                  ulltype )) )),
                    ll )) ))
    else mk ~loc (CastE (ft, mk (Lval u)))
  in
  (ins, value)

(* The output left value of the cell at index [i] (then [rest]) of a typed
   region: its array's element, or the scalar that holds the region's one
   cell (--scalar-cells, where every access is to that cell). *)
let cell_lval ctx info i rest =
  match Hashtbl.find_opt ctx.scalar_cells info.reg.rid with
  | Some (c, _) -> (Var c, rest)
  | None -> (Var info.arr, Index (i, rest))

(* ---- expressions and left values ---- *)

(* An expression of the input translated and made an int. The translation of a
   pointer is already an int; the type that decides whether a cast is needed
   is the input's, since the types of the variables are rewritten only at the
   end ([Cil.typeOf] on a translated expression would still see pointers). *)

(* --uninit=check: the check of a read of the input left value (host, off)
   whose output offset is [off']: the state of a scalar must be written,
   and a structure read whole must have some scalar written (C11 leaves the
   read of an uninitialised object undefined, and a structure is read as one
   object). Nothing for a variable that is not checked, or whose read every
   path writes before (see [elided]). *)
let init_read ctx (host, off) off' loc =
  match host with
  | Var v -> (
      match tracked ctx v with
      | Some _ when Hashtbl.mem ctx.elided (ctx.cur_sid, v.vid) ->
          ctx.uninit_elided <- (Option.fold ~none:"" ~some:(fun fd -> fd.svar.vname) ctx.cur_fd, loc, v.vname)
                               :: ctx.uninit_elided
      | Some sv -> (
          let state = mk ~loc (Lval (init_lval ctx sv off')) in
          match Ast_types.unroll_node (Cil.typeOfLval (host, off)) with
          | TComp ci when ci.cstruct ->
              emit ctx (Call (None, Var (init_struct_check_fn ctx (init_comp ctx ci)), [ state ], loc))
          | TArray _ -> ()
          | _ -> emit ctx (Call (None, Var (init_check_fn ctx), [ state ], loc)))
      | _ -> ())
  | Mem _ -> ()

let rec to_int ctx e =
  let e' = tr_exp ctx e in
  match Ast_types.unroll_node (Cil.typeOf e) with
  | TPtr _ | TArray _ | TInt IInt -> e'
  | _ -> mk ~loc:e.eloc (CastE (ity, e'))

and tr_offset ctx = function
  | NoOffset -> NoOffset
  | Field (f, off) -> Field (f, tr_offset ctx off)
  | Index (e, off) -> Index (tr_exp ctx e, tr_offset ctx off)

(* [base ⊕ off] for a value of type [t] at index [base]. In a typed region the
   array indices select a cell and what remains is the path inside the cell
   (returned translated and as in the input); in a byte region the whole
   offset is a byte displacement. *)
and linearize ctx info base t off =
  match (Ast_types.unroll_node t, off) with
  | _, NoOffset -> (base, NoOffset, NoOffset)
  | TArray (t', _), Index (j, off') ->
      let j = scale (to_int ctx j) (units ctx info t') in
      linearize ctx info (add base j) t' off'
  | TComp ci, Field (f, off') when info.byte ->
      linearize ctx info (add base (iconst (field_offset ctx ci f))) f.ftype off'
  | _, off ->
      if info.byte then assert false;
      (base, tr_offset ctx off, off)

(* The region, the index and the in-cell path of a left value that lies in a
   region; [None] for a variable that is not an object. *)
and address ctx (host, off) =
  match host with
  | Var vi when is_object ctx vi ->
      let info = info_of_var ctx vi in
      let i, rest, rest_in = linearize ctx info (base_index ctx vi) vi.vtype off in
      Some (info, i, rest, rest_in)
  | Var _ -> None
  | Mem e -> (
      match (info_of_exp ctx e, Ast_types.unroll_node (Cil.typeOf e)) with
      | Some info, TPtr t ->
          let i, rest, rest_in = linearize ctx info (to_int ctx e) t off in
          Some (info, i, rest, rest_in)
      | None, _ -> not_implemented "a dereference of a pointer that is always NULL"
      | Some _, _ -> assert false)

(* A left value that is a C left value of the output (a variable or a typed
   region's cell). *)
and tr_lval ctx ((host, off) as lv) =
  match address ctx lv with
  | Some (info, i, rest, _) ->
      if info.byte then assert false;
      cell_lval ctx info i rest
  | None -> (host, tr_offset ctx off)

(* The value of a left value of type [t] at byte index [i]: loaded into a
   temporary by instructions queued before the current one. *)
and load_bytes ctx info i t loc =
  match scalar_tag t with
  | Some _ when direct_byte ctx t -> read_byte info t i loc
  | Some (_, ty) ->
      let tmp = temp ctx ty in
      let ld, _ = accessors ctx info t in
      emit ctx (Call (Some (Cil.var tmp), Var ld.svar, [ i ], loc));
      mk ~loc (Lval (Cil.var tmp))
  | None ->
      let tmp = temp ctx (tr_type t) in
      List.iter (emit ctx) (copy_in ctx info i t (Cil.var tmp) loc);
      mk ~loc (Lval (Cil.var tmp))

(* Instructions that load an aggregate of type [t] at byte index [i] into the
   output left value [dst], scalar by scalar. *)
and copy_in ctx info i t dst loc =
  match Ast_types.unroll_node t with
  | TComp ci when ci.cstruct ->
      List.concat_map
        (fun f ->
          let i_f = add (copy i) (iconst (field_offset ctx ci f)) in
          if is_companion ctx f && byte_shadows ctx info then []
          else if f.fbitfield <> None && f.fname = Cil.missingFieldName then
            [] (* an unnamed bit-field is padding: no value to copy *)
          else if f.fbitfield <> None then begin
            let ins, v = load_bitfield ctx info i_f f loc in
            ins @ [ Set (Cil.addOffsetLval (Field (f, NoOffset)) dst, v, loc) ]
          end
          else
          copy_in ctx info i_f f.ftype (Cil.addOffsetLval (Field (f, NoOffset)) dst) loc
          @
          (* the shadows of a pointer field come from the parallel arrays,
             not from the companion bytes (see [byte_shadows]) *)
          match companions_of ctx f with
          | Some (fb, fl) when byte_shadows ctx info ->
              let rec reads i t cb cl =
                match Ast_types.unroll_node t with
                | TArray (t', len) ->
                    List.concat
                      (List.init (Cil.lenOfArray len) (fun j ->
                           let at o = Cil.addOffsetLval (Index (iconst j, NoOffset)) o in
                           reads (add (copy i) (iconst (j * size_bytes ctx t'))) t' (at cb) (at cl)))
                | _ ->
                    let sb, sl = shadow_arrays ctx info in
                    [ Set (cb, mk (Lval (Var sb, Index (copy i, NoOffset))), loc);
                      Set (cl, mk (Lval (Var sl, Index (copy i, NoOffset))), loc) ]
              in
              reads i_f f.ftype
                (Cil.addOffsetLval (Field (fb, NoOffset)) dst)
                (Cil.addOffsetLval (Field (fl, NoOffset)) dst)
          | _ -> [])
        (Option.value ~default:[] ci.cfields)
  | TArray (t', len) ->
      List.concat
        (List.init (Cil.lenOfArray len) (fun j ->
             copy_in ctx info
               (add (copy i) (iconst (j * size_bytes ctx t')))
               t'
               (Cil.addOffsetLval (Index (iconst j, NoOffset)) dst)
               loc))
  | _ -> (
      match scalar_tag t with
      | Some _ when direct_byte ctx t -> [ Set (dst, read_byte info t i loc, loc) ]
      | Some _ ->
          let ld, _ = accessors ctx info t in
          [ Call (Some dst, Var ld.svar, [ i ], loc) ]
      | None -> not_implemented "a %a in a byte region" Cil_datatype.Typ.pretty t)

(* Safety: the check before an access to [lv] at index [i] of [info]. *)
and access_check ctx lv info i rest_in loc =
  if ctx.safety <> None then begin
    let w = if info.byte then size_bytes ctx (Cil.typeOfLval lv) else 1 in
    let has_index = function
      | Index _ -> true
      | _ -> false
    in
    let rec any_index = function
      | NoOffset -> false
      | Index _ -> true
      | Field (_, o) -> any_index o
    in
    let shadow =
      match lv with
      | Mem e, _ -> Some (shadow_of ctx e)
      | Var v, off when any_index off || has_index off ->
          Some (base_index ctx v, iconst (units ctx (info_of_var ctx v) v.vtype))
      | Var _, _ -> None
    in
    Option.iter
      (fun (b, l) ->
        emit ctx (Call (None, Var (check_fn ctx info), [ copy i; iconst w; b; l ], loc)))
      shadow;
    if not info.byte then index_checks ctx info.sigma rest_in loc
  end

(* Safety: the subscripts of arrays that are not in a region, along [off]
   from type [t]. *)
and index_checks ctx t off loc =
  if ctx.safety <> None then
    match (Ast_types.unroll_node t, off) with
    | _, NoOffset -> ()
    | TArray (t', len), Index (j, off') ->
        (match len with
         | Some _ ->
             let n = Cil.lenOfArray len in
             emit ctx
               (Call
                  ( None,
                    Var (check_index_fn ctx),
                    [ mk ~loc (CastE (lltype, tr_exp ctx j));
                      Cil.kinteger ~loc ILongLong n ],
                    loc ))
         | None -> ());
        index_checks ctx t' off' loc
    | TComp _, Field (f, off') -> index_checks ctx f.ftype off' loc
    | _ -> ()

and read_lval ctx ?(check = true) lv loc =
  match address ctx lv with
  | Some (info, i, rest, rest_in) ->
      if check then begin
        access_check ctx lv info i rest_in loc;
        (* a checked variable in a region (a root of the end checks) *)
        match lv with
        | Var v, off when tracked ctx v <> None -> init_read ctx lv (tr_offset ctx off) loc
        | _ -> ()
      end;
      if info.byte then
        match last_bitfield lv with
        | Some f ->
            let ins, v = load_bitfield ctx info i f loc in
            List.iter (emit ctx) ins;
            v
        | None -> load_bytes ctx info i (Cil.typeOfLval lv) loc
      else mk ~loc (Lval (cell_lval ctx info i rest))
  | None ->
      let host, off = lv in
      (if check then
         match host with Var v -> index_checks ctx v.vtype off loc | Mem _ -> ());
      (* the subscripts' bounds are checked first: a read out of an array's
         bounds is reported as such, not as uninitialised *)
      let off' = tr_offset ctx off in
      if check then init_read ctx lv off' loc;
      mk ~loc (Lval (host, off'))

(* ---- shadows ---- *)

(* Where the shadow of the pointer held in the input left value [lv] lives:
   input left values (companion fields or companion variables), or the
   parallel arrays of a region at an index. *)
and shadow_place ctx ((host, off) as lv) =
  let rec split = function
    (* the last field of the offset, with what precedes and follows it *)
    | NoOffset -> None
    | Index (j, o) -> (
        match split o with
        | Some (pre, f, suf) -> Some (Index (j, pre), f, suf)
        | None -> None)
    | Field (f, o) -> (
        match split o with
        | Some (pre, g, suf) -> Some (Field (f, pre), g, suf)
        | None -> Some (NoOffset, f, o))
  in
  let with_field pre f suf = Cil.addOffset (Field (f, suf)) pre in
  let in_byte_region () =
    match host with
    | Var v when not (is_object ctx v) -> None
    | _ -> (
        match address ctx lv with
        | Some (info, i, _, _) when byte_shadows ctx info -> Some (`Cells (info, i))
        | _ -> None)
  in
  match split off with
  | Some (pre, f, suf) -> (
      match in_byte_region () with
      | Some c -> c
      | None -> (
          match companions_of ctx f with
          | Some (fb, fl) -> `Lvals ((host, with_field pre fb suf), (host, with_field pre fl suf))
          | None -> assert false))
  | None -> (
      match host with
      | Var v when not (is_object ctx v) -> (
          match Hashtbl.find_opt ctx.shadow_vars v.vid with
          | Some (vb, vl) -> `Lvals ((Var vb, off), (Var vl, off))
          | None -> not_implemented "pointer %s has no shadow" v.vname)
      | _ -> (
          match address ctx lv with
          | Some (info, i, _, _) -> `Cells (info, i)
          | None -> assert false))

and read_shadow ctx lv loc =
  match shadow_place ctx lv with
  | `Lvals (lb, ll) -> (read_lval ctx ~check:false lb loc, read_lval ctx ~check:false ll loc)
  | `Cells (info, i) ->
      let sb, sl = shadow_arrays ctx info in
      ( mk ~loc (Lval (Var sb, Index (i, NoOffset))),
        mk ~loc (Lval (Var sl, Index (copy i, NoOffset))) )

(* The shadow of a pointer value: the block the value was derived from. *)
and shadow_of ctx e =
  let loc = e.eloc in
  let none () = (iconst ~loc 0, iconst ~loc 0) in
  if Fragment.is_null_constant e then none ()
  else
    match e.enode with
    | Lval lv -> read_shadow ctx lv loc
    | CastE (_, e')
      when not (Ast_types.is_ptr (Cil.typeOf e') || Ast_types.is_array (Cil.typeOf e')) ->
      (* a function number converted to a data pointer: no block *)
      none ()
    | CastE (_, e') -> shadow_of ctx e'
    | BinOp ((PlusPI | MinusPI), p, _, _) -> shadow_of ctx p
    | (AddrOf _ | StartOf _) when Hashtbl.mem ctx.st.exempt e.eid -> none ()
    | AddrOf (Var v, _) | StartOf (Var v, _) when is_object ctx v ->
        (base_index ctx v, iconst ~loc (units ctx (info_of_var ctx v) v.vtype))
    | AddrOf (Mem e', _) | StartOf (Mem e', _) -> shadow_of ctx e'
    | _ -> none ()

and tr_exp ctx e =
  let loc = e.eloc in
  let m node = mk ~loc node in
  match e.enode with
  | Const _ -> e
  | Lval (Var v, NoOffset) when Hashtbl.mem offsetof_placeholders v.vid -> (
      let base, off = Hashtbl.find offsetof_placeholders v.vid in
      match (offset_bytes_in ctx.layouts base off, Ast_types.unroll_node v.vtype) with
      | Some k, TInt kind -> Cil.kinteger64 ~loc ~kind (Z.of_int k)
      | _ -> assert false (* [Offsetof] registers only paths it could lay out *))
  | Lval lv -> read_lval ctx lv loc
  | SizeOf t -> m (SizeOf (tr_type t))
  | SizeOfE e' -> m (SizeOf (tr_type (Cil.typeOf e')))
  | AlignOf (t, k) -> m (AlignOf (tr_type t, k))
  | AlignOfE (e', k) -> m (AlignOf (tr_type (Cil.typeOf e'), k))
  | UnOp (op, e', t) -> m (UnOp (op, tr_exp ctx e', tr_type t))
  | BinOp (((PlusPI | MinusPI) as op), p, k, _) ->
      let op = if op = PlusPI then PlusA else MinusA in
      let k = scale ~loc (to_int ctx k) (step ctx p) in
      m (BinOp (op, to_int ctx p, k, ity))
  | BinOp (MinusPP, a, b, t) ->
      let d = m (BinOp (MinusA, tr_exp ctx a, tr_exp ctx b, ity)) in
      let n = step ctx a in
      let d = if n = 1 then d else m (BinOp (Div, d, iconst ~loc n, ity)) in
      Cil.mkCast ~newt:(tr_type t) d
  | BinOp (((Lt | Gt | Le | Ge | Eq | Ne) as op), a, b, t)
    when Ast_types.is_ptr (Cil.typeOf a) ->
      compare_pointers ctx ~loc op a b t
  | BinOp (op, a, b, t) -> m (BinOp (op, tr_exp ctx a, tr_exp ctx b, tr_type t))
  | CastE (t, e')
    when Ast_types.is_ptr t
         && (Fragment.is_fnid (Cil.typeOf e') || Fragment.is_nonobj (Cil.typeOf e')) ->
      (* a function pointer converted to a data pointer: minus its number.
         A data pointer is an index, never negative, so a function never
         equals an object; NULL stays 0.  A number of a value that points to
         no object (a nondeterministic pointer) is read the same way: its
         numbers are above every function number *)
      m (UnOp (Neg, Cil.mkCast ~newt:ity (tr_exp ctx e'), ity))
  | CastE (t, e') when Fragment.is_fnid t && Ast_types.is_ptr (Cil.typeOf e') ->
      (* back: the number; an object's index gives a number no function has
         (0 or less), which a call through it treats as invalid *)
      Cil.mkCast ~newt:t (m (UnOp (Neg, to_int ctx e', ity)))
  | CastE (t, e') ->
      let src = Cil.typeOf e' in
      if Ast_types.is_ptr t then
        if Ast_types.is_ptr src || Ast_types.is_array src then tr_exp ctx e'
        else iconst ~loc 0 (* the fragment admits only the null constant *)
      else if Ast_types.is_ptr src then
        (* a pointer converted to _Bool is its comparison with NULL *)
        Cil.mkCast ~newt:t (m (BinOp (Ne, tr_exp ctx e', iconst ~loc 0, ity)))
      else m (CastE (tr_type t, tr_exp ctx e'))
  | (AddrOf _ | StartOf _) when Hashtbl.mem ctx.st.exempt e.eid -> e
  | AddrOf lv | StartOf lv -> (
      match address ctx lv with
      | Some (_, i, NoOffset, _) -> i
      | Some (_, _, _, _) ->
          (* a typed region has no pointer to a field of a cell, by the
             definition of typed regions *)
          assert false
      | None -> assert false (* an address is only taken of an object *))

and compare_pointers ctx ~loc op a b t =
  let m node = mk ~loc node in
  let ta = tr_exp ctx a and tb = tr_exp ctx b in
  let null e = Fragment.is_null_constant e in
  let same =
    null a || null b
    ||
    match (info_of_exp ctx a, info_of_exp ctx b) with
    | Some x, Some y -> x.reg.rid = y.reg.rid
    | None, None -> true
    | _ -> false
  in
  if same then m (BinOp (op, ta, tb, tr_type t))
  else
    match op with
    | Eq | Ne ->
        (* Pointers into different regions never point to the same object, so
           they are equal exactly when both are NULL. *)
        let z e = m (BinOp (Eq, e, iconst ~loc 0, ity)) in
        let both = m (BinOp (LAnd, z ta, z tb, ity)) in
        if op = Eq then both else m (UnOp (LNot, both, ity))
    | _ -> unsupported "an ordered comparison of pointers into different regions"

(* The parallel shadow arrays of a byte region say where its pointers are
   (see [byte_shadows], and memtrack reads them so): every pointer stored in
   the region (a pointer field of a structure included) has its shadow
   written there, and a scalar that is not a pointer clears the shadows at
   the bytes it overwrites (a pointer that is no longer there must not track
   a block). *)
let tracks_byte_pointers ctx info = byte_shadows ctx info

(* p2a_clearK(i, w): the shadows at the w bytes from i are those of no
   pointer. *)
let clear_fn ctx info =
  match info.clear with
  | Some f -> f.svar
  | None ->
      let sb, sl = shadow_arrays ctx info in
      let fd = Cil.emptyFunction (fresh_name ctx (Printf.sprintf "p2a_clear%d" info.reg.rid)) in
      Cil.setReturnType fd Cil_const.voidType;
      let i = Cil.makeFormalVar fd "i" ity in
      let w = Cil.makeFormalVar fd "w" ity in
      let j = Cil.makeLocalVar fd "j" ity in
      let at = bin PlusA (Cil.evar i) (Cil.evar j) in
      fd.sbody.bstmts <-
        Cil.mkForIncr ~iter:j ~first:(iconst 0) ~stopat:(Cil.evar w) ~incr:(iconst 1)
          ~body:
            [ if_stmt (bin Ge at (iconst 0))
                (when_below ctx (copy at)
                   [ stmt (Set (aidx sb (copy at), iconst 0, loc0));
                     stmt (Set (aidx sl (copy at), iconst 0, loc0)) ])
                [] ]
          ();
      add_helper ctx fd;
      info.clear <- Some fd;
      fd.svar

(* After a store of a scalar of input type [t] at byte [i]: the clearing of
   the shadows it overwrites, when it is not a pointer. *)
let clear_after ctx info i t loc =
  if tracks_byte_pointers ctx info && not (Ast_types.is_ptr t) then
    [ Call (None, Var (clear_fn ctx info), [ copy i; iconst (size_bytes ctx t) ], loc) ]
  else []

(* The instructions writing the output value [v] into bit-field [f] at byte
   [i]: its bytes read, the field's bits replaced by v modulo 2^width (C's
   conversion to the field's width), the bytes written back. *)
let store_bitfield ctx info i f v loc =
  let shift, width, nb = bit_place ctx f in
  let u = Cil.var (temp ctx ulltype) and nv = Cil.var (temp ctx ulltype) in
  let lu = mk (Lval u) in
  gather_bytes info i nb u loc
  @ [ Set
        ( nv,
          mk
            (BinOp
               ( Mult,
                 mk (BinOp (Mod, mk (CastE (ulltype, v)), ull (pow2 width), ulltype)),
                 ull (pow2 shift),
                 ulltype )),
          loc );
      Set
        ( u,
          mk
            (BinOp
               ( PlusA,
                 mk
                   (BinOp
                      ( MinusA,
                        lu,
                        mk
                          (BinOp
                             ( Mult,
                               mk
                                 (BinOp
                                    ( Mod,
                                      mk (BinOp (Div, mk (Lval u), ull (pow2 shift), ulltype)),
                                      ull (pow2 width),
                                      ulltype )),
                               ull (pow2 shift),
                               ulltype )),
                        ulltype )),
                 mk (Lval nv),
                 ulltype )),
          loc ) ]
  @ List.concat
      (List.init nb (fun j ->
           [ Set
               ( byte_cell info (add (copy i) (iconst j)),
                 mk (CastE (Cil_const.ucharType, mk (BinOp (Mod, mk (Lval u), ull (Z.of_int 256), ulltype)))),
                 loc );
             Set (u, mk (BinOp (Div, mk (Lval u), ull (Z.of_int 256), ulltype)), loc) ]))
  @
  if tracks_byte_pointers ctx info then
    [ Call (None, Var (clear_fn ctx info), [ copy i; iconst nb ], loc) ]
  else []

(* The shadows of the pointers of a field of shape [t] (a pointer, or an
   array of them) at byte [i], read from the companion left values [cb] and
   [cl], written to the parallel arrays. *)
let rec parallel_shadows ctx info i t cb cl loc =
  match Ast_types.unroll_node t with
  | TArray (t', len) ->
      List.concat
        (List.init (Cil.lenOfArray len) (fun j ->
             let at o = Cil.addOffsetLval (Index (iconst j, NoOffset)) o in
             parallel_shadows ctx info
               (add (copy i) (iconst (j * size_bytes ctx t')))
               t' (at cb) (at cl) loc))
  | _ ->
      let sb, sl = shadow_arrays ctx info in
      [ Set (aidx sb (copy i), mk (Lval cb), loc); Set (aidx sl (copy i), mk (Lval cl), loc) ]

(* Instructions that store the output value [v] (of input type [t]) at byte
   index [i]; an aggregate is stored scalar by scalar from a left value. *)
let rec copy_out ctx info i t src loc =
  match Ast_types.unroll_node t with
  | TComp ci when ci.cstruct ->
      List.concat_map
        (fun f ->
          let i_f = add (copy i) (iconst (field_offset ctx ci f)) in
          (if f.fbitfield <> None && f.fname = Cil.missingFieldName then []
           else if f.fbitfield <> None then
             store_bitfield ctx info i_f f
               (mk ~loc (Lval (Cil.addOffsetLval (Field (f, NoOffset)) src))) loc
           else copy_out ctx info i_f f.ftype (Cil.addOffsetLval (Field (f, NoOffset)) src) loc)
          @
          match companions_of ctx f with
          | Some (fb, fl) when tracks_byte_pointers ctx info ->
              parallel_shadows ctx info i_f f.ftype
                (Cil.addOffsetLval (Field (fb, NoOffset)) src)
                (Cil.addOffsetLval (Field (fl, NoOffset)) src)
                loc
          | _ -> [])
        (Option.value ~default:[] ci.cfields)
  | TArray (t', len) ->
      List.concat
        (List.init (Cil.lenOfArray len) (fun j ->
             copy_out ctx info
               (add (copy i) (iconst (j * size_bytes ctx t')))
               t'
               (Cil.addOffsetLval (Index (iconst j, NoOffset)) src)
               loc))
  | _ when direct_byte ctx t ->
      write_byte info i (mk ~loc (Lval src)) loc :: clear_after ctx info i t loc
  | _ ->
      let _, sf = accessors ctx info t in
      Call (None, Var sf.svar, [ i; mk ~loc (Lval src) ], loc) :: clear_after ctx info i t loc

let store_bytes ctx info i t v loc =
  match scalar_tag t with
  | Some _ when direct_byte ctx t -> write_byte info i v loc :: clear_after ctx info i t loc
  | Some _ ->
      let _, sf = accessors ctx info t in
      Call (None, Var sf.svar, [ i; v ], loc) :: clear_after ctx info i t loc
  | None -> (
      match v.enode with
      | Lval src -> copy_out ctx info i t src loc
      | _ ->
          let tmp = temp ctx (tr_type t) in
          Set (Cil.var tmp, v, loc) :: copy_out ctx info i t (Cil.var tmp) loc)

(* The instructions that write the output value [v] into the input left value
   [lv] (its checks and address loads are queued). *)
let write_lval ctx ?(check = true) lv v loc =
  match address ctx lv with
  | Some (info, i, rest, rest_in) ->
      if check then access_check ctx lv info i rest_in loc;
      if info.byte then
        match last_bitfield lv with
        | Some f -> store_bitfield ctx info i f v loc
        | None -> store_bytes ctx info i (Cil.typeOfLval lv) v loc
      else [ Set (cell_lval ctx info i rest, v, loc) ]
  | None ->
      let host, off = lv in
      (if check then
         match host with Var v -> index_checks ctx v.vtype off loc | Mem _ -> ());
      [ Set ((host, tr_offset ctx off), v, loc) ]

(* The region and the index of an input left value that lies in a region. *)
let lval_place ctx lv =
  match address ctx lv with Some (info, i, _, _) -> Some (info, i) | None -> None

let write_shadow ctx lv (b, l) loc =
  if ctx.safety = None then []
  else
    match shadow_place ctx lv with
    | `Lvals (lb, ll) ->
        let companions = write_lval ctx ~check:false lb b loc @ write_lval ctx ~check:false ll l loc in
        (* a pointer field in a byte region: its shadow in the parallel
           arrays too (see [tracks_byte_pointers]) *)
        let parallel =
          match lval_place ctx lv with
          | Some (info, i) when tracks_byte_pointers ctx info ->
              let sb, sl = shadow_arrays ctx info in
              [ Set (aidx sb i, copy b, loc); Set (aidx sl (copy i), copy l, loc) ]
          | _ -> []
        in
        companions @ parallel
    | `Cells (info, i) ->
        let sb, sl = shadow_arrays ctx info in
        [ Set ((Var sb, Index (i, NoOffset)), b, loc);
          Set ((Var sl, Index (copy i, NoOffset)), l, loc) ]

let is_pointer_lval lv = Ast_types.is_ptr (Cil.typeOfLval lv)

(* The shadow of [e], read into temporaries by queued instructions: the
   shadow is written after the value, and writing the value may change what
   the shadow's expression reads ([c = c->next] reads c's successor's shadow
   through c). *)
let captured_shadow ctx e loc =
  let b, l = shadow_of ctx e in
  let keep x =
    if Cil.isIntegerConstant x then x
    else begin
      let t = temp ctx ity in
      emit ctx (Set (Cil.var t, x, loc));
      Cil.evar t
    end
  in
  let b = keep b in
  let l = keep l in
  (b, l)

(* The region of the input left value [lv], without translating it. *)
let lval_info ctx (host, _) =
  match host with
  | Var v when is_object ctx v -> Some (info_of_var ctx v)
  | Var _ -> None
  | Mem e -> info_of_exp ctx e

let rec has_index = function
  | NoOffset -> false
  | Index _ -> true
  | Field (_, o) -> has_index o

(* A call whose result goes to the input left value [ret]. The result goes
   into a temporary first when its place is in a byte region (a store is a
   call), and in a safety mode whenever the place is checked: the store, and
   so the check, comes after the call returns, as in C, so that a violation
   is reported after what the call does (a nondeterministic draw, say). The
   instructions the arguments need come before the call, those of the place
   after it. *)
let call_into ctx ret mk_call loc =
  match ret with
  | None -> [ mk_call None ]
  | Some lv ->
      let info = lval_info ctx lv in
      let byte = match info with Some i -> i.byte | None -> false in
      let checked = ctx.safety <> None && (info <> None || has_index (snd lv)) in
      if byte || checked then begin
        let before = take_pending ctx in
        let tmp = temp ctx (tr_type (Cil.typeOfLval lv)) in
        let call = mk_call (Some (Cil.var tmp)) in
        let w = write_lval ctx lv (mk ~loc (Lval (Cil.var tmp))) loc in
        let after = take_pending ctx in
        before @ (call :: after) @ w
      end
      else
        match address ctx lv with
        | Some (info, i, rest, _) -> [ mk_call (Some (cell_lval ctx info i rest)) ]
        | None -> [ mk_call (Some (tr_lval ctx lv)) ]

(* --uninit=check: where the value written into a checked variable comes
   from, for its state. *)
type init_source =
  | Value of exp  (** an input expression *)
  | Result of varinfo  (** the result of a call of this function *)

(* The state instructions of a write into the input left value (host, off):
   a scalar is written; a structure written whole takes the state of the
   structure it is copied from when that is a checked variable (or the
   state a function passes its result's in), and is written whole
   otherwise. Placed before the write, so that the subscripts of the state
   are those of the left value before it changes. *)
let init_write ctx (host, off) src loc =
  match host with
  | Var v -> (
      match tracked ctx v with
      | None -> []
      | Some sv -> (
          let slv = init_lval ctx sv (tr_offset ctx off) in
          match Ast_types.unroll_node (Cil.typeOfLval (host, off)) with
          | TComp ci when ci.cstruct -> (
              let c = init_comp ctx ci in
              let ones () = Call (Some slv, Var (init_ones_fn ctx c), [], loc) in
              match src with
              | Value { enode = Lval ((Var y, offy) as ly); _ }
                when tracked ctx y <> None
                     && Ast_types.is_struct_or_union (Cil.typeOfLval ly) ->
                  let sy = Option.get (tracked ctx y) in
                  [ Set (slv, mk ~loc (Lval (init_lval ctx sy (tr_offset ctx offy))), loc) ]
              | Result f -> (
                  match Hashtbl.find_opt ctx.ret_init f.vid with
                  | Some g -> [ Set (slv, mk ~loc (Lval (Cil.var g)), loc) ]
                  | None -> [ ones () ])
              | Value _ -> [ ones () ])
          | TArray _ -> []
          | _ -> [ Set (slv, Cil.mkCast ~newt:Cil_const.ucharType (iconst 1), loc) ]))
  | Mem _ -> []

(* The state of the structure [e] a function returns, into the global [g]
   its callers read it from. *)
let init_write_global ctx g e loc =
  match e.enode with
  | Lval ((Var y, offy) as ly)
    when tracked ctx y <> None && Ast_types.is_struct_or_union (Cil.typeOfLval ly) ->
      let sy = Option.get (tracked ctx y) in
      [ Set (Cil.var g, mk ~loc (Lval (init_lval ctx sy (tr_offset ctx offy))), loc) ]
  | _ -> (
      match Ast_types.unroll_node g.vtype with
      | TComp c -> [ Call (Some (Cil.var g), Var (init_ones_fn ctx c), [], loc) ]
      | _ -> assert false)

(* The state arguments of a call of [f]: one per structure parameter that
   receives its argument's state, the state of a checked variable, or the
   state of a structure written whole for any other argument. *)
let init_args ctx f args loc =
  match Hashtbl.find_opt ctx.orig_formals f.vid with
  | None -> []
  | Some formals ->
      let rec go fs as_ =
        match (fs, as_) with
        | fv :: fs', a :: as' ->
            (if Hashtbl.mem ctx.init_formals fv.vid then
               let c =
                 match Ast_types.unroll_node fv.vtype with
                 | TComp ci -> init_comp ctx ci
                 | _ -> assert false
               in
               match a.enode with
               | Lval (Var y, offy) when tracked ctx y <> None ->
                   let sy = Option.get (tracked ctx y) in
                   [ mk ~loc (Lval (init_lval ctx sy (tr_offset ctx offy))) ]
               | _ ->
                   let t = temp ctx (Cil_const.mk_tcomp c) in
                   emit ctx (Call (Some (Cil.var t), Var (init_ones_fn ctx c), [], loc));
                   [ Cil.evar t ]
             else [])
            @ go fs' as'
        | _ -> []
      in
      go formals args

(* ---- initialisers ---- *)

let tr_init ctx i =
  let rec go = function
    | SingleInit e -> SingleInit (tr_exp ctx e)
    | CompoundInit (t, l) ->
        CompoundInit (tr_type t, List.map (fun (o, i) -> (tr_offset ctx o, go i)) l)
  in
  go i

(* Safety: the initialiser of a variable that is not an object, of input type
   [t], rebuilt so that every structure lists its companion fields, each
   initialised with the shadow of its pointer field's initialiser. CIL prints
   a structure's initialiser positionally, so the companions must be listed. *)
let rec tr_init_safe ctx t i =
  match (Ast_types.unroll_node t, i) with
  | TComp ci, CompoundInit (ct, l) when ci.cstruct ->
      let find f =
        List.find_map (function Field (g, NoOffset), i when g == f -> Some i | _ -> None) l
      in
      let entries =
        List.concat_map
          (fun f ->
            if is_companion ctx f then []
            else
              let fi = match find f with Some i -> i | None -> Cil.makeZeroInit ~loc:loc0 f.ftype in
              let own = (Field (f, NoOffset), tr_init_safe ctx f.ftype fi) in
              match companions_of ctx f with
              | Some (fb, fl) ->
                  let b, l = shadow_init ctx f.ftype fi in
                  [ own; (Field (fb, NoOffset), b); (Field (fl, NoOffset), l) ]
              | None -> [ own ])
          (Option.value ~default:[] ci.cfields)
      in
      CompoundInit (tr_type ct, entries)
  | TArray (t', _), CompoundInit (ct, l) ->
      CompoundInit (tr_type ct, List.map (fun (o, i) -> (o, tr_init_safe ctx t' i)) l)
  | _, SingleInit e -> SingleInit (tr_exp ctx e)
  | _, CompoundInit (ct, l) ->
      CompoundInit (tr_type ct, List.map (fun (o, i) -> (tr_offset ctx o, tr_init ctx i)) l)

(* The initialisers of the two companions of a pointer (or array of pointers)
   initialised with [i]. *)
and shadow_init ctx t i =
  match (Ast_types.unroll_node t, i) with
  | TArray (t', _), CompoundInit (_, l) ->
      let sh = match ptr_shape t with Some s -> s | None -> assert false in
      let pairs = List.map (fun (o, i) -> (o, shadow_init ctx t' i)) l in
      ( CompoundInit (sh, List.map (fun (o, (b, _)) -> (o, b)) pairs),
        CompoundInit (sh, List.map (fun (o, (_, l)) -> (o, l)) pairs) )
  | _, SingleInit e ->
      let b, l = shadow_of ctx e in
      (SingleInit b, SingleInit l)
  | _, CompoundInit _ -> assert false

(* A character array initialised by a string literal: the initialiser is the
   literal's array itself, [Lval (Var lit)]. *)
let literal_init e =
  match e.enode with
  | Lval (Var lit, NoOffset) when Ast_info.is_string_literal lit -> (
      match Globals.Vars.get_string_literal lit with
      | Str s -> Some s
      | Wstr _ -> not_implemented "a wide string literal")
  | _ -> None

let rec last_field = function
  | NoOffset -> None
  | Index (_, o) -> last_field o
  | Field (f, o) -> ( match last_field o with Some g -> Some g | None -> Some f)

(* The instructions that write initialiser [i] into the input left value
   (host, off) of a variable [v] (an object, its cells already allocated, or
   one whose initialiser is written as stores), each store preceded by the
   loads and checks its value needs, and a pointer's shadow written beside
   it. With [implicit], the parts the initialiser leaves out are written as
   zero, as C requires of a local aggregate's initialiser. The companion
   fields are written with their pointer field, never on their own. *)
let init_stores ctx ~implicit ~loc v i =
  let write off e acc =
    let e' = tr_exp ctx e in
    let lv = (Var v, off) in
    let w = write_lval ctx ~check:false lv e' loc in
    let sh =
      if is_pointer_lval lv && ctx.safety <> None then
        write_shadow ctx lv (captured_shadow ctx e loc) loc
      else []
    in
    let pre = take_pending ctx in
    List.rev_append (pre @ w @ sh) acc
  in
  let rec leaves off init acc =
    match last_field off with
    | Some f when is_companion ctx f -> acc
    | _ -> (
        match init with
        | SingleInit e -> (
            match literal_init e with
            | Some s ->
                (* one store per character, then the terminating zero and, for
                   a longer array, the zeros C requires of the rest *)
                let t = Cil.typeOfLval (Var v, off) in
                let n =
                  match Ast_types.unroll_node t with
                  | TArray (_, len) -> Cil.lenOfArray len
                  | _ -> String.length s + 1
                in
                let elt = Ast_types.direct_element_type t in
                let acc = ref acc in
                for j = 0 to n - 1 do
                  if j <= String.length s || implicit then
                    let c = if j < String.length s then Char.code s.[j] else 0 in
                    acc :=
                      write
                        (Cil.addOffset (Index (iconst j, NoOffset)) off)
                        (Cil.mkCast ~newt:elt (Cil.kinteger ~loc IChar c))
                        !acc
                done;
                !acc
            | None -> write off e acc)
        | CompoundInit (ct, initl) ->
            Cil.foldLeftCompound ~implicit
              ~doinit:(fun o i _ acc -> leaves (Cil.addOffset o off) i acc)
              ~ct ~initl ~acc)
  in
  List.rev (leaves NoOffset i [])

(* ---- allocation and calls ---- *)

(* The cells requested by an allocation of [n] bytes, and, when it differs,
   the cells the block holds whole (the length the safety checks use). In a
   byte region, the bytes (sizeof is translated with everything else, so it
   measures the translated layout). In a typed region of cell type sigma: k
   for [k * sizeof(sigma)], [sizeof(sigma) * k] and [sizeof(sigma)] (1);
   otherwise the bytes divided by the translated cell size, rounded up, and
   rounded down for the length. *)
let alloc_cells ctx info n =
  if info.byte then (to_int ctx n, None)
  else
    let n' = PointsTo.strip_casts n in
    let is_sigma = function
      | SizeOf t -> Regions.same_type t info.sigma
      | SizeOfE e -> Regions.same_type (Cil.typeOf e) info.sigma
      | _ -> false
    in
    match n'.enode with
    | e when is_sigma e -> (iconst 1, None)
    | BinOp (Mult, k, s, _) when is_sigma (PointsTo.strip_casts s).enode -> (to_int ctx k, None)
    | BinOp (Mult, s, k, _) when is_sigma (PointsTo.strip_casts s).enode -> (to_int ctx k, None)
    | _ ->
        Options.warning ~current:true
          "allocation of %a bytes in a region of %a: cells rounded up"
          Cil_datatype.Exp.pretty n Cil_datatype.Typ.pretty info.sigma;
        let size () = int_of (mk (SizeOf (tr_type info.sigma))) in
        let up =
          mk
            (BinOp
               ( Div,
                 mk (BinOp (MinusA, add (to_int ctx n) (size ()), iconst 1, ity)),
                 size (),
                 ity ))
        in
        (* the cells the block holds whole: a cell that only partly fits in
           the requested bytes is outside the block for the safety checks *)
        let whole = mk (BinOp (Div, to_int ctx n, size (), ity)) in
        (up, Some whole)

(* A call of the allocator of [info] for [cells] cells; in the safety modes
   the kind of the block is passed too, for the block table. *)
let call_alloc ?(zeroed = false) ~kind info cells loc ret =
  let fd =
    if zeroed then match info.alloc0 with Some f -> f | None -> assert false
    else info.alloc
  in
  let args = if info.table = None then [ cells ] else [ cells; iconst kind ] in
  Call (ret, Var fd.svar, args, loc)

let alloc_info ctx sid =
  match info_of_node ctx (PointsTo.alloc_node ctx.st sid) with
  | Some i -> i
  | None -> assert false

(* An allocation of [cells] into the input left value [ret]. In the safety
   modes the block's index and length become the shadow of the result, and a
   block from malloc or calloc is recorded as one that free may release. *)
let alloc_into ctx info ~zeroed ~heap (cells, whole) ret loc =
  let kind = if heap then kind_heap else kind_alloca in
  (* a region held in a scalar: the new block's cell is arbitrary *)
  let arbitrary =
    match Hashtbl.find_opt ctx.scalar_cells info.reg.rid with
    | Some (_, call) -> [ call ]
    | None -> []
  in
  (fun is -> is @ arbitrary)
  @@
  match ctx.safety with
  | None -> call_into ctx ret (call_alloc ~zeroed ~kind info cells loc) loc
  | Some _ ->
      let tc = temp ctx ity and t = temp ctx ity in
      let len, set_len =
        match whole with
        | None -> (Cil.evar tc, [])
        | Some w ->
            let tl = temp ctx ity in
            (Cil.evar tl, [ Set (Cil.var tl, w, loc) ])
      in
      let before = take_pending ctx in
      let alloc =
        (Set (Cil.var tc, cells, loc) :: set_len)
        @ [ call_alloc ~zeroed ~kind info (Cil.evar tc) loc (Some (Cil.var t)) ]
      in
      (* the place of the result is checked and written after the
         allocation, as in C *)
      let w =
        match ret with
        | None -> []
        | Some lv ->
            write_lval ctx lv (Cil.evar t) loc
            @ write_shadow ctx lv (Cil.evar t, len) loc
      in
      let after = take_pending ctx in
      before @ alloc @ after @ w

(* p2a_atexit(id): the function numbered id is registered, as atexit does
   (it returns 0; beyond the table's length, the registration fails, -1). *)
let atexit_fn ctx =
  match Hashtbl.find_opt ctx.fns "atexit" with
  | Some f -> f
  | None ->
      let fn, n = match ctx.atexit_table with Some p -> p | None -> assert false in
      let fd = Cil.emptyFunction (fresh_name ctx "p2a_atexit") in
      Cil.setReturnType fd ity;
      let id = Cil.makeFormalVar fd "id" ity in
      let r = Cil.makeLocalVar fd "r" ity in
      fd.sbody.bstmts <-
        (let registered =
           [ stmt (Set (aidx fn (Cil.evar n), Cil.evar id, loc0));
             stmt (Set (Cil.var n, bin PlusA (Cil.evar n) (iconst 1), loc0));
             stmt (Set (Cil.var r, iconst 0, loc0)) ]
         in
         match below_size ctx (Cil.evar n) with
         | Some c -> [ if_stmt c registered [ stmt (Set (Cil.var r, iconst (-1), loc0)) ] ]
         | None -> registered)
        @ [ Cil.mkStmt ~valid_sid:true (Return (Some (Cil.evar r), loc0)) ];
      add_helper ctx fd;
      Hashtbl.replace ctx.fns "atexit" fd.svar;
      fd.svar

(* ---- the block and string functions ---- *)

(* A region whose cells are characters (or bytes): the string functions read
   and write it a cell at a time. *)
let char_region info =
  info.byte
  || match Ast_types.unroll_node info.sigma with TInt (IChar | ISChar | IUChar) -> true | _ -> false

let cell_signed info =
  (not info.byte)
  && match Ast_types.unroll_node info.sigma with TInt ik -> Cil.isSigned ik | _ -> false

(* Does the region hold pointers in its cells directly, with their shadows in
   the parallel arrays (which a copy must copy and memset must clear)? *)
let direct_pointers ctx info =
  ctx.safety <> None
  && (Ast_types.is_ptr info.sigma
     || (info.byte && Regions.find ctx.regs (PointsTo.pt ctx.st info.reg.rep) <> None))

(* The cells the byte count [n] of a block function stands for in [info]:
   bytes in a byte region or a region of one-byte cells, otherwise the
   count [Regions.size_in_cells] reads off the expression (the region would
   be a byte region if it could not). *)
let block_cells ctx info n =
  if info.byte || Cil.bitsSizeOf info.sigma <= 8 then to_int ctx n
  else
    match Regions.size_in_cells info.sigma n with
    | Some (Regions.Count k) -> to_int ctx k
    | Some (Regions.Const c) -> iconst c
    | None -> unsupported "a size that is not a whole number of cells"

(* A value used more than once, in a temporary when it is not a constant. *)
let kept ctx e loc =
  if Cil.isIntegerConstant e then e
  else begin
    let t = temp ctx ity in
    emit ctx (Set (Cil.var t, e, loc));
    Cil.evar t
  end

(* The zero of a region's cell: 0, or a global structure left zero. *)
let zero_value ctx info =
  let cell = tr_type info.sigma in
  if Ast_types.is_struct info.sigma then begin
    let z =
      match info.zero with
      | Some z -> z
      | None ->
          let z = Cil.makeGlobalVar (fresh_name ctx (Printf.sprintf "p2a_zero%d" info.reg.rid)) cell in
          info.zero <- Some z;
          z
    in
    Cil.evar z
  end
  else Cil.mkCast ~newt:cell (iconst 0)

(* A generated function of the models, made once per key. *)
let model_fn ctx key make =
  match Hashtbl.find_opt ctx.fns key with
  | Some f -> f
  | None ->
      let fd = make () in
      add_helper ctx fd;
      Hashtbl.replace ctx.fns key fd.svar;
      fd.svar

(* The value of an integer [v] converted to the cell type of a character
   region [info], by the instructions before it: with --wrap-integers the
   conversion is the reduction to 8 bits. *)
let to_char_cell ctx fd info v =
  let cell = if info.byte then Cil_const.ucharType else tr_type info.sigma in
  match ctx.wrap with
  | Some w ->
      let t = fresh_local ctx fd "p2a_c" cell in
      ([ stmt (Call (Some (Cil.var t), Var (w (8, cell_signed info)), [ v ], loc0)) ], Cil.evar t)
  | None -> ([], Cil.mkCast ~newt:cell v)

(* safety: p2a_checkK(i, w, base, len) as an instruction, at [loc] (the
   location of what it guards, which the record's source map reads). *)
let check_call ?(loc = loc0) ctx info i w (b, l) =
  Call (None, Var (check_fn ctx info), [ i; w; b; l ], loc)

(* The parameters of a pointer argument of a generated function: its index,
   and in a safety mode its shadow. *)
let ptr_params ctx fd name =
  let i = Cil.makeFormalVar fd name ity in
  if ctx.safety = None then (i, None)
  else
    let b = Cil.makeFormalVar fd (name ^ "_base") ity in
    let l = Cil.makeFormalVar fd (name ^ "_len") ity in
    (i, Some (Cil.evar b, Cil.evar l))

let checked ctx info i w sh =
  match sh with Some sh -> [ stmt (check_call ctx info i w sh) ] | None -> []

(* p2a_memsetK(i, n, v): the n cells from i are v; the shadows of the
   pointers they held are cleared. *)
let memset_fn ctx info =
  model_fn ctx (Printf.sprintf "memset%d" info.reg.rid) (fun () ->
      let fd = Cil.emptyFunction (fresh_name ctx (Printf.sprintf "p2a_memset%d" info.reg.rid)) in
      Cil.setReturnType fd Cil_const.voidType;
      let i = Cil.makeFormalVar fd "i" ity in
      let n = Cil.makeFormalVar fd "n" ity in
      let cell = if info.byte then Cil_const.ucharType else tr_type info.sigma in
      let v = Cil.makeFormalVar fd "v" cell in
      let j = Cil.makeLocalVar fd "j" ity in
      let at () = bin PlusA (Cil.evar i) (Cil.evar j) in
      let clear =
        if direct_pointers ctx info then
          let sb, sl = shadow_arrays ctx info in
          [ stmt (Set (aidx sb (at ()), iconst 0, loc0)); stmt (Set (aidx sl (at ()), iconst 0, loc0)) ]
        else []
      in
      fd.sbody.bstmts <-
        Cil.mkForIncr ~iter:j ~first:(iconst 0) ~stopat:(Cil.evar n) ~incr:(iconst 1)
          ~body:(stmt (Set (aidx info.arr (at ()), Cil.evar v, loc0)) :: clear)
          ();
      fd)

(* p2a_memcpyK(d, s, n) and p2a_memmoveK(d, s, n): the n cells from s are
   copied to the n cells from d, with the shadows of the pointers they hold;
   memmove copies backwards when d lies after s, so that overlapping ranges
   are copied as if through a buffer. *)
let memcpy_fn ctx info ~move =
  let name = if move then "memmove" else "memcpy" in
  model_fn ctx (Printf.sprintf "%s%d" name info.reg.rid) (fun () ->
      let fd = Cil.emptyFunction (fresh_name ctx (Printf.sprintf "p2a_%s%d" name info.reg.rid)) in
      Cil.setReturnType fd Cil_const.voidType;
      let d = Cil.makeFormalVar fd "d" ity in
      let s = Cil.makeFormalVar fd "s" ity in
      let n = Cil.makeFormalVar fd "n" ity in
      let j = Cil.makeLocalVar fd "j" ity in
      let one () =
        let src a = rd a (bin PlusA (Cil.evar s) (Cil.evar j)) in
        let dst a = aidx a (bin PlusA (Cil.evar d) (Cil.evar j)) in
        stmt (Set (dst info.arr, src info.arr, loc0))
        ::
        (if direct_pointers ctx info then
           let sb, sl = shadow_arrays ctx info in
           [ stmt (Set (dst sb, src sb, loc0)); stmt (Set (dst sl, src sl, loc0)) ]
         else [])
      in
      let forward () =
        Cil.mkForIncr ~iter:j ~first:(iconst 0) ~stopat:(Cil.evar n) ~incr:(iconst 1) ~body:(one ()) ()
      in
      let backward () =
        Cil.mkFor
          ~start:[ stmt (Set (Cil.var j, bin MinusA (Cil.evar n) (iconst 1), loc0)) ]
          ~guard:(bin Ge (Cil.evar j) (iconst 0))
          ~next:[ stmt (Set (Cil.var j, bin MinusA (Cil.evar j) (iconst 1), loc0)) ]
          ~body:(one ()) ()
      in
      fd.sbody.bstmts <-
        (if move then [ if_stmt (bin Le (Cil.evar d) (Cil.evar s)) (forward ()) (backward ()) ]
         else forward ());
      fd)

(* p2a_reallocK(p, n) (with p's shadow in a safety mode): realloc in the
   region of p. NULL allocates n cells; otherwise p is released (checked as
   free checks it) and, unless n is 0 (the result is then NULL, as glibc
   does), n fresh cells get the first min(old length, n) cells of p with the
   shadows of the pointers they hold. Without the shadow (the normal mode)
   the old length is unknown and n cells are copied: past the old block they
   are cells of other blocks, which C leaves the new block's contents
   arbitrary in anyway. *)
let realloc_fn ctx info =
  model_fn ctx (Printf.sprintf "realloc%d" info.reg.rid) (fun () ->
      let fd = Cil.emptyFunction (fresh_name ctx (Printf.sprintf "p2a_realloc%d" info.reg.rid)) in
      Cil.setReturnType fd ity;
      let p, sh = ptr_params ctx fd "p" in
      let n = Cil.makeFormalVar fd "n" ity in
      let r = Cil.makeLocalVar fd "r" ity in
      let m = Cil.makeLocalVar fd "m" ity in
      let j = Cil.makeLocalVar fd "j" ity in
      let alloc = stmt (call_alloc ~kind:kind_heap info (Cil.evar n) loc0 (Some (Cil.var r))) in
      let copy_cells =
        let src a = rd a (bin PlusA (Cil.evar p) (Cil.evar j)) in
        let dst a = aidx a (bin PlusA (Cil.evar r) (Cil.evar j)) in
        let one =
          stmt (Set (dst info.arr, src info.arr, loc0))
          ::
          (if direct_pointers ctx info then
             let sb, sl = shadow_arrays ctx info in
             [ stmt (Set (dst sb, src sb, loc0)); stmt (Set (dst sl, src sl, loc0)) ]
           else [])
        in
        let one =
          if sh = None then
            when_below ctx
              (bin PlusA (Cil.evar r) (Cil.evar j))
              (when_below ctx (bin PlusA (Cil.evar p) (Cil.evar j)) one)
          else one
        in
        Cil.mkForIncr ~iter:j ~first:(iconst 0) ~stopat:(Cil.evar m) ~incr:(iconst 1) ~body:one ()
      in
      let release, bound =
        match sh with
        | Some (b, l) ->
            ( [ stmt (Call (None, Var (release_fn ctx info), [ Cil.evar p; b ], loc0)) ],
              [ stmt (Set (Cil.var m, l, loc0));
                if_stmt (bin Lt (Cil.evar n) (Cil.evar m)) [ stmt (Set (Cil.var m, Cil.evar n, loc0)) ] [] ] )
        | None -> ([], [ stmt (Set (Cil.var m, Cil.evar n, loc0)) ])
      in
      fd.sbody.bstmts <-
        [ if_stmt (bin Eq (Cil.evar p) (iconst 0)) [ alloc ]
            (release
            @ [ if_stmt (bin Eq (Cil.evar n) (iconst 0))
                  [ stmt (Set (Cil.var r, iconst 0, loc0)) ]
                  ((stmt (call_alloc ~kind:kind_heap info (Cil.evar n) loc0 (Some (Cil.var r)))
                    :: bound)
                  @ copy_cells) ]);
          Cil.mkStmt ~valid_sid:true (Return (Some (Cil.evar r), loc0)) ];
      fd)

(* The string functions, over character regions: one generated function per
   function and regions, each reading (and writing) a cell at a time, every
   access checked in a safety mode. *)
let str_fn ctx name (infos : region_info list) make =
  model_fn ctx (String.concat "_" (name :: List.map (fun i -> string_of_int i.reg.rid) infos)) (fun () ->
      let fd =
        Cil.emptyFunction
          (fresh_name ctx
             (Printf.sprintf "p2a_%s%s" name
                (String.concat "_" (List.map (fun i -> string_of_int i.reg.rid) infos))))
      in
      make fd;
      fd)

let char_at info i = Cil.mkCast ~newt:ity (rd info.arr i)

(* strlen(s): the cells before the first 0. *)
let strlen_fn ctx info =
  str_fn ctx "strlen" [ info ] (fun fd ->
      Cil.setReturnType fd ity;
      let i, sh = ptr_params ctx fd "s" in
      let n = Cil.makeLocalVar fd "n" ity in
      let at () = bin PlusA (Cil.evar i) (Cil.evar n) in
      fd.sbody.bstmts <-
        (stmt (Set (Cil.var n, iconst 0, loc0)) :: checked ctx info (at ()) (iconst 1) sh)
        @ Cil.mkWhile
            ~guard:(bin Ne (char_at info (at ())) (iconst 0))
            ~body:
              (stmt (Set (Cil.var n, bin PlusA (Cil.evar n) (iconst 1), loc0))
              :: checked ctx info (at ()) (iconst 1) sh)
            ()
        @ [ Cil.mkStmt ~valid_sid:true (Return (Some (Cil.evar n), loc0)) ])

(* strcmp(a, b): the difference of the first unsigned characters that differ,
   0 when the strings are equal. *)
let strcmp_fn ctx ia ib =
  str_fn ctx "strcmp" [ ia; ib ] (fun fd ->
      Cil.setReturnType fd ity;
      let a, sa = ptr_params ctx fd "a" in
      let b, sb = ptr_params ctx fd "b" in
      let k = Cil.makeLocalVar fd "k" ity in
      let r = Cil.makeLocalVar fd "r" ity in
      let go = Cil.makeLocalVar fd "go" ity in
      let ca = Cil.makeLocalVar fd "ca" ity in
      let cb = Cil.makeLocalVar fd "cb" ity in
      let at x = bin PlusA (Cil.evar x) (Cil.evar k) in
      let uchar info x = Cil.mkCast ~newt:ity (Cil.mkCast ~newt:Cil_const.ucharType (rd info.arr (at x))) in
      fd.sbody.bstmts <-
        [ stmt (Set (Cil.var k, iconst 0, loc0)); stmt (Set (Cil.var r, iconst 0, loc0));
          stmt (Set (Cil.var go, iconst 1, loc0)) ]
        @ Cil.mkWhile ~guard:(Cil.evar go)
            ~body:
              (checked ctx ia (at a) (iconst 1) sa
              @ checked ctx ib (at b) (iconst 1) sb
              @ [ stmt (Set (Cil.var ca, uchar ia a, loc0)); stmt (Set (Cil.var cb, uchar ib b, loc0));
                  if_stmt (bin Ne (Cil.evar ca) (Cil.evar cb))
                    [ stmt (Set (Cil.var r, bin MinusA (Cil.evar ca) (Cil.evar cb), loc0));
                      stmt (Set (Cil.var go, iconst 0, loc0)) ]
                    [ if_stmt (bin Eq (Cil.evar ca) (iconst 0))
                        [ stmt (Set (Cil.var go, iconst 0, loc0)) ]
                        [ stmt (Set (Cil.var k, bin PlusA (Cil.evar k) (iconst 1), loc0)) ] ] ])
            ()
        @ [ Cil.mkStmt ~valid_sid:true (Return (Some (Cil.evar r), loc0)) ])

(* strcpy(d, s), strncpy(d, s, n) and strcat(d, s): the characters of s up to
   its 0 (strncpy: n cells, padded with 0) written from d (strcat: from d's
   0). *)
let strcpy_fn ctx name id is =
  str_fn ctx name [ id; is ] (fun fd ->
      Cil.setReturnType fd Cil_const.voidType;
      let d, sd = ptr_params ctx fd "d" in
      let s, ss = ptr_params ctx fd "s" in
      let n = if name = "strncpy" then Some (Cil.makeFormalVar fd "n" ity) else None in
      let k = Cil.makeLocalVar fd "k" ity in
      let e = Cil.makeLocalVar fd "e" ity in
      let c = Cil.makeLocalVar fd "c" ity in
      let go = Cil.makeLocalVar fd "go" ity in
      let src () = bin PlusA (Cil.evar s) (Cil.evar k) in
      let dst () = bin PlusA (bin PlusA (Cil.evar d) (Cil.evar e)) (Cil.evar k) in
      let write () =
        let pre, v = to_char_cell ctx fd id (Cil.evar c) in
        checked ctx id (dst ()) (iconst 1) sd @ pre @ [ stmt (Set (aidx id.arr (dst ()), v, loc0)) ]
      in
      let read () = checked ctx is (src ()) (iconst 1) ss @ [ stmt (Set (Cil.var c, char_at is (src ()), loc0)) ] in
      let find_end =
        if name = "strcat" then
          let at () = bin PlusA (Cil.evar d) (Cil.evar e) in
          checked ctx id (at ()) (iconst 1) sd
          @ Cil.mkWhile
              ~guard:(bin Ne (char_at id (at ())) (iconst 0))
              ~body:
                (stmt (Set (Cil.var e, bin PlusA (Cil.evar e) (iconst 1), loc0))
                :: checked ctx id (at ()) (iconst 1) sd)
              ()
        else []
      in
      let incr = stmt (Set (Cil.var k, bin PlusA (Cil.evar k) (iconst 1), loc0)) in
      let copy =
        match n with
        | None ->
            stmt (Set (Cil.var go, iconst 1, loc0))
            :: Cil.mkWhile ~guard:(Cil.evar go)
                 ~body:
                   (read () @ write ()
                   @ [ if_stmt (bin Eq (Cil.evar c) (iconst 0)) [ stmt (Set (Cil.var go, iconst 0, loc0)) ] [ incr ] ])
                 ()
        | Some n ->
            (* go: the source's 0 is not reached yet *)
            stmt (Set (Cil.var go, iconst 1, loc0))
            :: Cil.mkWhile
                 ~guard:(bin Lt (Cil.evar k) (Cil.evar n))
                 ~body:
                   ([ if_stmt (Cil.evar go)
                        (read ()
                        @ [ if_stmt (bin Eq (Cil.evar c) (iconst 0)) [ stmt (Set (Cil.var go, iconst 0, loc0)) ] [] ])
                        [ stmt (Set (Cil.var c, iconst 0, loc0)) ] ]
                   @ write () @ [ incr ])
                 ()
      in
      fd.sbody.bstmts <-
        [ stmt (Set (Cil.var k, iconst 0, loc0)); stmt (Set (Cil.var e, iconst 0, loc0)) ]
        @ find_end @ copy)

(* The pointer argument [e] of a modelled function: its region, its index
   (kept in a temporary) and, in a safety mode, its shadow. *)
let ptr_arg ctx fname e loc =
  match info_of_exp ctx e with
  | None -> unsupported "%s of a pointer that is only ever NULL" fname
  | Some info ->
      let i = kept ctx (to_int ctx e) loc in
      let sh = if ctx.safety = None then None else Some (captured_shadow ctx e loc) in
      (info, i, sh)

let sh_args = function Some (b, l) -> [ b; l ] | None -> []

(* The result of memset, memcpy, memmove, strcpy, strncpy and strcat: their
   first argument, with its shadow. *)
let first_result ctx ret d i sh loc =
  match ret with
  | None -> []
  | Some lv ->
      write_lval ctx lv i loc
      @ (match sh with
         | Some (b, l) when is_pointer_lval lv -> write_shadow ctx lv (b, l) loc
         | _ -> ignore d; [])

(* memset(d, c, n): the cells as the bytes c makes them. An integer cell of
   w bytes gets the w-byte pattern of c (computed here when c is a constant;
   a variable c only for one-byte cells); a pointer or a structure cell only
   for c = 0 (NULL, the zero structure). *)
let model_memset ctx ret d c n loc =
  let info, i, sh = ptr_arg ctx "memset" d loc in
  let cells = kept ctx (block_cells ctx info n) loc in
  Option.iter (fun sh -> emit ctx (check_call ~loc ctx info (copy i) (copy cells) sh)) sh;
  let cell = if info.byte then Cil_const.ucharType else tr_type info.sigma in
  let int_kind t =
    match Ast_types.unroll_node t with
    | TInt ik -> Some ik
    | TEnum ei -> Some ei.ekind
    | _ -> None
  in
  let value =
    let c' = Cil.constFoldToInt c in
    match ((if info.byte then Some IUChar else int_kind info.sigma), c') with
    | Some ik, Some z ->
        let w = Cil.bitsSizeOfInt ik / 8 in
        let b = Z.logand z (Z.of_int 255) in
        let u = ref Z.zero in
        for _ = 1 to w do u := Z.add (Z.mul !u (Z.of_int 256)) b done;
        let u =
          if ik = IBool then (if Z.equal b Z.zero then Z.zero else Z.one)
          else if Cil.isSigned ik && Z.geq !u (Z.shift_left Z.one ((8 * w) - 1)) then
            Z.sub !u (Z.shift_left Z.one (8 * w))
          else !u
        in
        Some (Cil.kinteger64 ~loc ~kind:ik u)
    | Some ik, None when Cil.bitsSizeOfInt ik = 8 -> (
        let v = tr_exp ctx c in
        match ctx.wrap with
        | Some w ->
            let t = temp ctx cell in
            emit ctx (Call (Some (Cil.var t), Var (w (8, Cil.isSigned ik)), [ v ], loc));
            Some (Cil.evar t)
        | None -> Some (Cil.mkCast ~newt:cell v))
    | Some _, None -> unsupported "memset of cells wider than a byte with a value that is not a constant"
    | None, Some z when Z.equal z Z.zero -> Some (zero_value ctx info)
    | None, _ -> unsupported "memset of pointer or structure cells with a value other than 0"
  in
  let v = Option.get value in
  Call (None, Var (memset_fn ctx info), [ i; cells; v ], loc) :: first_result ctx ret d i sh loc

(* memcpy(d, s, n), memmove(d, s, n): within one region (the analysis unifies
   what d and s point to); the source range is checked, then the
   destination's. *)
let model_memcpy ctx ~move ret d s n loc =
  let name = if move then "memmove" else "memcpy" in
  let info, i, sh = ptr_arg ctx name d loc in
  let info', j, sh' = ptr_arg ctx name s loc in
  if info != info' then unsupported "%s between two regions" name;
  let cells = kept ctx (block_cells ctx info n) loc in
  Option.iter (fun sh -> emit ctx (check_call ~loc ctx info (copy j) (copy cells) sh)) sh';
  Option.iter (fun sh -> emit ctx (check_call ~loc ctx info (copy i) (copy cells) sh)) sh;
  Call (None, Var (memcpy_fn ctx info ~move), [ i; j; cells ], loc) :: first_result ctx ret d i sh loc

(* realloc(p, n): the result's shadow is the new block and its length (NULL's
   when n is 0, the cells then being 0 too). *)
let model_realloc ctx ~sid ret p n loc =
  let info = alloc_info ctx sid in
  let cells, whole = alloc_cells ctx info n in
  let cells = kept ctx cells loc in
  let len = match whole with Some w -> kept ctx w loc | None -> copy cells in
  let ip = kept ctx (to_int ctx p) loc in
  let sh = if ctx.safety = None then None else Some (captured_shadow ctx p loc) in
  let r = temp ctx ity in
  let call = Call (Some (Cil.var r), Var (realloc_fn ctx info), (ip :: sh_args sh) @ [ cells ], loc) in
  let w =
    match ret with
    | None -> []
    | Some lv ->
        write_lval ctx lv (Cil.evar r) loc
        @ if ctx.safety <> None then write_shadow ctx lv (Cil.evar r, len) loc else []
  in
  let before = take_pending ctx in
  let after_w = w @ take_pending ctx in
  before @ (call :: after_w)

let model_string ctx ~sid:_ ret name args loc =
  let str_arg e =
    let info, i, sh = ptr_arg ctx name e loc in
    if not (char_region info) then unsupported "%s of a region whose cells are not characters" name;
    (info, i, sh)
  in
  match (name, args) with
  | "strlen", [ s ] ->
      let info, i, sh = str_arg s in
      call_into ctx ret (fun r -> Call (r, Var (strlen_fn ctx info), i :: sh_args sh, loc)) loc
  | "strcmp", [ a; b ] ->
      let ia, i, sa = str_arg a in
      let ib, j, sb = str_arg b in
      call_into ctx ret
        (fun r -> Call (r, Var (strcmp_fn ctx ia ib), (i :: sh_args sa) @ (j :: sh_args sb), loc))
        loc
  | ("strcpy" | "strcat"), [ d; s ] | "strncpy", [ d; s; _ ] ->
      let id, i, sd = str_arg d in
      let is, j, ss = str_arg s in
      let n = match args with [ _; _; n ] -> [ to_int ctx n ] | _ -> [] in
      Call (None, Var (strcpy_fn ctx name id is), (i :: sh_args sd) @ (j :: sh_args ss) @ n, loc)
      :: first_result ctx ret d i sd loc
  | _ -> unsupported "%s with %d arguments" name (List.length args)

(* A call. The allocators and the release are the external functions of those
   names; a function the program defines is an ordinary call whatever its name,
   as it is for the points-to analysis and the fragment check. *)
let tr_call ctx ~sid ret f args loc =
  let name = if PointsTo.is_defined f then "" else f.vname in
  match name with
  | "malloc" | "alloca" | "__builtin_alloca" | "__fc_vla_alloc" -> (
      let info = alloc_info ctx sid in
      match args with
      | [ n ] ->
          let cells = alloc_cells ctx info n in
          alloc_into ctx info ~zeroed:false ~heap:(f.vname = "malloc") cells ret loc
      | _ -> unsupported "%s with %d arguments" f.vname (List.length args))
  | "calloc" -> (
      let info = alloc_info ctx sid in
      match args with
      | [ n; s ] ->
          let bytes = mk (BinOp (Mult, n, s, Cil.typeOf n)) in
          let cells =
            match (PointsTo.strip_casts s).enode with
            | SizeOf t when (not info.byte) && Regions.same_type t info.sigma ->
                (to_int ctx n, None)
            | _ -> alloc_cells ctx info bytes
          in
          alloc_into ctx info ~zeroed:true ~heap:true cells ret loc
      | _ -> unsupported "calloc with %d arguments" (List.length args))
  | "free" -> (
      match (ctx.safety, args) with
      | Some _, [ e ] -> (
          match info_of_exp ctx e with
          | Some info ->
              let b, _ = shadow_of ctx e in
              [ Call (None, Var (release_fn ctx info), [ to_int ctx e; b ], loc) ]
          | None -> [] (* a pointer that only ever holds NULL *))
      | _ -> [])
  | "__fc_vla_free" -> (
      (* the end of a variable-length array's lifetime *)
      match (ctx.safety, args) with
      | Some _, [ e ] -> (
          match info_of_exp ctx e with
          | Some info when released_flag_read ctx info ->
              [ Call (None, Var (release_vla_fn ctx info), [ to_int ctx e ], loc) ]
          | Some _ -> []
          | None -> [])
      | _ -> [])
  | "__VERIFIER_nondet_String" ->
      not_implemented "__VERIFIER_nondet_String (a block of arbitrary length)"
  | "memset" -> (
      match args with
      | [ d; c; n ] -> model_memset ctx ret d c n loc
      | _ -> unsupported "memset with %d arguments" (List.length args))
  | ("memcpy" | "memmove") as m -> (
      match args with
      | [ d; s; n ] -> model_memcpy ctx ~move:(m = "memmove") ret d s n loc
      | _ -> unsupported "%s with %d arguments" m (List.length args))
  | "realloc" -> (
      match args with
      | [ p; n ] -> model_realloc ctx ~sid ret p n loc
      | _ -> unsupported "realloc with %d arguments" (List.length args))
  | ("strlen" | "strcmp" | "strcpy" | "strncpy" | "strcat") as m -> model_string ctx ~sid ret m args loc
  | "atexit" -> (
      match args with
      | [ a ] -> (
          match Fragment.atexit_target a with
          | Some g when Hashtbl.mem ctx.atexit_ids g.vid ->
              let id = iconst (Hashtbl.find ctx.atexit_ids g.vid) in
              call_into ctx ret (fun r -> Call (r, Var (atexit_fn ctx), [ id ], loc)) loc
          | _ -> unsupported "atexit of something other than a function the program defines")
      | _ -> unsupported "atexit with %d arguments" (List.length args))
  | _ ->
      let args' = List.map (tr_exp ctx) args in
      let shadows =
        match (ctx.safety, Hashtbl.find_opt ctx.orig_formals f.vid) with
        | Some _, Some formals ->
            let rec go fs as_ =
              match (fs, as_) with
              | fv :: fs', a :: as' ->
                  (if Ast_types.is_ptr fv.vtype then
                     let b, l = shadow_of ctx a in
                     [ b; l ]
                   else [])
                  @ go fs' as'
              | _ -> []
            in
            go formals args
        | _ -> []
      in
      let inits = if ctx.uninit_check then init_args ctx f args loc else [] in
      let call = call_into ctx ret (fun r -> Call (r, Var f, args' @ shadows @ inits, loc)) loc in
      let result_shadow =
        match (ctx.safety, ret, Hashtbl.find_opt ctx.ret_shadow f.vid) with
        | Some _, Some lv, Some (rb, rl) when is_pointer_lval lv ->
            write_shadow ctx lv (Cil.evar rb, Cil.evar rl) loc
        | Some _, Some lv, None when is_pointer_lval lv ->
            (* an external function returning a pointer is outside the
               fragment; NULL's shadow is the safe default *)
            write_shadow ctx lv (iconst 0, iconst 0) loc
        | _ -> []
      in
      call @ result_shadow

let tr_instr ctx ~sid i =
  assert (ctx.pending = []);
  ctx.cur_sid <- sid;
  let is =
    match i with
    | Set (lv, e, loc) ->
        let v = tr_exp ctx e in
        let sh =
          if is_pointer_lval lv && ctx.safety <> None then
            write_shadow ctx lv (captured_shadow ctx e loc) loc
          else []
        in
        let init = if ctx.uninit_check then init_write ctx lv (Value e) loc else [] in
        init @ write_lval ctx lv v loc @ sh
    | Call (None, Var f, [], loc)
      when ctx.safety <> None && Some f.vname = ctx.bad_call && PointsTo.is_defined f ->
        (* a call through NULL or an invalid function pointer: an invalid
           dereference in the safety modes (in the normal mode the function
           is kept, and ends the execution as abort does) *)
        [ violation ctx Valid_deref loc ]
    | Call (ret, Var f, args, loc) ->
        let call = tr_call ctx ~sid ret f args loc in
        let init =
          match ret with
          | Some lv when ctx.uninit_check -> init_write ctx lv (Result f) loc
          | _ -> []
        in
        call @ init
    | Call (_, Mem _, _, _) ->
        (* refused by the fragment check, unless -ptr2arr-unsupported=warn *)
        unsupported "a call through a function pointer"
    | Local_init (v, AssignInit i, loc) ->
        if is_object ctx v then init_stores ctx ~implicit:true ~loc v i
        else if ctx.safety = None then [ Local_init (v, AssignInit (tr_init ctx i), loc) ]
        else begin
          let init = Local_init (v, AssignInit (tr_init_safe ctx v.vtype i), loc) in
          (* the companions of a pointer or an array of pointers *)
          let shadows =
            match (ptr_shape v.vtype, i) with
            | None, _ -> []
            | Some _, SingleInit e ->
                write_shadow ctx (Var v, NoOffset) (captured_shadow ctx e loc) loc
            | Some _, CompoundInit (ct, initl) ->
                let rec leaves off init acc =
                  match init with
                  | SingleInit e ->
                      List.rev_append
                        (write_shadow ctx (Var v, off) (captured_shadow ctx e loc) loc)
                        acc
                  | CompoundInit (ct, initl) ->
                      Cil.foldLeftCompound ~implicit:false
                        ~doinit:(fun o i _ acc -> leaves (Cil.addOffset o off) i acc)
                        ~ct ~initl ~acc
                in
                List.rev (leaves NoOffset (CompoundInit (ct, initl)) [])
          in
          init :: shadows
        end
    | Local_init (v, ConsInit (f, args, Plain_func), loc) -> (
        if is_object ctx v then tr_call ctx ~sid (Some (Cil.var v)) f args loc
        else
          match tr_call ctx ~sid (Some (Cil.var v)) f args loc with
          | Call (Some (Var v', NoOffset), Var g, args', _) :: rest when v' == v ->
              Local_init (v, ConsInit (g, args', Plain_func), loc) :: rest
          | is -> is)
    | Local_init (_, ConsInit (_, _, Constructor), _) ->
        unsupported "a C++ constructor call"
    | Skip loc -> [ Skip loc ]
    | Code_annot _ -> [] (* annotations about pointers would no longer type *)
    | Asm _ -> unsupported "inline assembly"
  in
  (* a variable declared by an initialisation that became something else is
     declared at the top of its block instead *)
  (match i with
   | Local_init (v, _, _)
     when not (List.exists (function Local_init (v', _, _) -> v' == v | _ -> false) is) ->
       v.vdefined <- false
   | _ -> ());
  take_pending ctx @ is

let gen_stmt skip i =
  let s = stmt i in
  Hashtbl.replace skip s.sid ();
  s

(* ---- functions ---- *)

let block_sids b =
  let h = Hashtbl.create 16 in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vstmt s =
        Hashtbl.replace h s.sid ();
        Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacBlock v b);
  h

(* ---- the ends of the execution: memtrack and memcleanup ---- *)

(* Does a value of input type [t] hold a pointer? *)
let rec has_ptr t =
  match Ast_types.unroll_node t with
  | TPtr _ -> true
  | TArray (t', _) -> has_ptr t'
  | TComp ci -> ci.cstruct && List.exists (fun f -> has_ptr f.ftype) (Option.value ~default:[] ci.cfields)
  | _ -> false

(* The regions a heap block (malloc, calloc) can be in: the only regions in
   which valid-memtrack and valid-memcleanup can fail. *)
let is_heap_region (r : Regions.region) =
  List.exists
    (function
      | Regions.Alloc s -> List.mem s.PointsTo.allocator heap_allocators
      | Regions.Var _ -> false)
    r.objects

let heap_infos ctx =
  List.filter_map
    (fun (r : Regions.region) -> if is_heap_region r then Some (info_of_region ctx r) else None)
    ctx.regs.list

(* The region a pointer held in [n]'s class points into, when it is one with
   heap blocks. *)
let heap_target ctx n =
  match Regions.find ctx.regs (PointsTo.pt ctx.st n) with
  | Some r when is_heap_region r -> Some (info_of_region ctx r)
  | _ -> None

(* The pointers held in a value of input type [t] at the output left value
   [lv]: [k value base] for each, [base] the shadow's first index. A pointer
   field's shadow is in its companion field; the caller gives the place of a
   pointer's (or an array of pointers') shadow at the top, [base], when there
   is one. Arrays are walked by loops over fresh counters from [newvar]. *)
let rec slots ctx ~newvar t lv base k =
  match Ast_types.unroll_node t with
  | TPtr _ -> ( match base with Some b -> k (mk (Lval lv)) (mk (Lval b)) | None -> [])
  | TArray (t', (Some _ as len)) when has_ptr t' ->
      let j = newvar () in
      let at o = Cil.addOffsetLval (Index (Cil.evar j, NoOffset)) o in
      Cil.mkForIncr ~iter:j ~first:(iconst 0) ~stopat:(iconst (Cil.lenOfArray len)) ~incr:(iconst 1)
        ~body:(slots ctx ~newvar t' (at lv) (Option.map at base) k)
        ()
  | TComp ci when ci.cstruct ->
      List.concat_map
        (fun f ->
          if is_companion ctx f || not (has_ptr f.ftype) then []
          else
            let at g o = Cil.addOffsetLval (Field (g, NoOffset)) o in
            let base = Option.map (fun (fb, _) -> at fb lv) (companions_of ctx f) in
            slots ctx ~newvar f.ftype (at f lv) base k)
        (Option.value ~default:[] ci.cfields)
  | _ -> []

(* How many pointers [slots] visits. *)
let rec count_slots ctx t =
  match Ast_types.unroll_node t with
  | TPtr _ -> 1
  | TArray (t', (Some _ as len)) -> Cil.lenOfArray len * count_slots ctx t'
  | TComp ci when ci.cstruct ->
      List.fold_left
        (fun n f -> if is_companion ctx f then n else n + count_slots ctx f.ftype)
        0
        (Option.value ~default:[] ci.cfields)
  | _ -> 0

(* The place of the shadow of a variable that is not an object: its companion
   variables, for a pointer or an array of pointers. *)
let var_shadow_base ctx v =
  match Hashtbl.find_opt ctx.shadow_vars v.vid with Some (vb, _) -> Some (Var vb, NoOffset) | None -> None

(* The table the roots of the function an end is in are passed to the check
   in: values, shadow bases, regions and their count. *)
let site_arrays ctx =
  match ctx.site with
  | Some p -> p
  | None ->
      let arr name = int_array ctx name "generated" in
      let n = Cil.makeGlobalVar (fresh_name ctx "p2a_site_n") ity in
      Hashtbl.replace ctx.roles n.vid "generated";
      ctx.helpers <- GVar (n, { init = None }, loc0) :: ctx.helpers;
      let p = (arr "p2a_site_val", arr "p2a_site_base", arr "p2a_site_reg", n) in
      ctx.site <- Some p;
      p

(* memtrack: the instructions, at an end in a function, that write the roots
   of its frame to the site table: the pointers held in [vars] (the
   variables in scope that are not objects, the parameters included) that
   can point to a heap block. *)
let site_roots ctx fd vars loc =
  let sval, sbase, sreg, sn = site_arrays ctx in
  let roots =
    List.filter_map
      (fun v ->
        if is_object ctx v || not (has_ptr v.vtype) then None
        else
          Option.map (fun info -> (v, info)) (heap_target ctx (PointsTo.var_node ctx.st v)))
      vars
  in
  let total = List.fold_left (fun n (v, _) -> n + count_slots ctx v.vtype) 0 roots in
  ctx.site_max <- max ctx.site_max total;
  let rec loops t =
    match Ast_types.unroll_node t with
    | TArray (t', _) -> has_ptr t'
    | TComp ci -> List.exists (fun f -> loops f.ftype) (Option.value ~default:[] ci.cfields)
    | _ -> false
  in
  let looped = List.exists (fun (v, _) -> loops v.vtype) roots in
  let newvar () =
    let j = Cil.makeLocalVar fd (fresh_name ctx "p2a_j") ity in
    Hashtbl.replace ctx.roles j.vid "generated";
    j
  in
  (* the next free entry: a constant when every root is one pointer, a
     counter otherwise *)
  let counter =
    if looped then begin
      let k = Cil.makeLocalVar fd (fresh_name ctx "p2a_k") ity in
      Hashtbl.replace ctx.roles k.vid "generated";
      Some k
    end
    else None
  in
  let next = ref 0 in
  let entry info value base =
    let at, step =
      match counter with
      | Some k -> (Cil.evar k, [ stmt (Set (Cil.var k, bin PlusA (Cil.evar k) (iconst 1), loc)) ])
      | None ->
          let n = !next in
          incr next;
          (iconst n, [])
    in
    [ stmt (Set (aidx sval at, value, loc));
      stmt (Set (aidx sbase (copy at), base, loc));
      stmt (Set (aidx sreg (copy at), iconst info.reg.rid, loc)) ]
    @ step
  in
  let start = match counter with Some k -> [ stmt (Set (Cil.var k, iconst 0, loc)) ] | None -> [] in
  let writes =
    List.concat_map
      (fun (v, info) -> slots ctx ~newvar v.vtype (Var v, NoOffset) (var_shadow_base ctx v) (entry info))
      roots
  in
  let count = match counter with Some k -> Cil.evar k | None -> iconst !next in
  start @ writes @ [ stmt (Set (Cil.var sn, count, loc)) ]

(* The calls an end is, outside a guard of a fresh allocation: the external
   functions ending the execution (see [end_function_kind]). *)
let end_call_kind f =
  if PointsTo.is_defined f then None else end_function_kind f.vorig_name

(* The statements no execution reaches: the then-branch of a test that a
   fresh allocation is null, [p = malloc(...); ... if (p == 0) ...] or
   [if (!p)], with only instructions that do not write p between (a copy
   [q = p] tests the allocation as well). *)
let find_unreached file tbl =
  let var_of e =
    match (PointsTo.strip_casts e).enode with Lval (Var v, NoOffset) -> Some v | _ -> None
  in
  let null_tested c =
    match (PointsTo.strip_casts c).enode with
    | UnOp (LNot, x, _) -> var_of x
    | BinOp (Eq, a, b, _) when Fragment.is_null_constant b -> var_of a
    | BinOp (Eq, a, b, _) when Fragment.is_null_constant a -> var_of b
    | _ -> None
  in
  let allocator f = (not (PointsTo.is_defined f)) && List.mem f.vname failing_allocators in
  let rec block b =
    let fresh = ref [] in
    let drop v = fresh := List.filter (fun w -> w != v) !fresh in
    let add v = drop v; fresh := v :: !fresh in
    List.iter
      (fun s ->
        (match s.skind with
         | Instr (Call (Some (Var v, NoOffset), Var f, _, _)) when allocator f -> add v
         | Instr (Local_init (v, ConsInit (f, _, Plain_func), _)) when allocator f -> add v
         | Instr (Set ((Var q, NoOffset), e, _)) -> (
             match var_of e with
             | Some v when List.memq v !fresh -> add q
             | _ -> drop q)
         | Instr (Call (Some (Var q, _), _, _, _) | Local_init (q, _, _)) -> drop q
         | Instr (Set ((Var q, _), _, _)) -> drop q
         | Instr _ -> ()
         | If (c, th, _, _) ->
             (match null_tested c with
              | Some v when List.memq v !fresh ->
                  Hashtbl.iter (fun sid () -> Hashtbl.replace tbl sid ()) (block_sids th)
              | _ -> ());
             fresh := []
         | _ -> fresh := []);
        match s.skind with
        | If (_, b1, b2, _) -> block b1; block b2
        | Loop (_, b', _, _, _) | Switch (_, b', _, _) | Block b' -> block b'
        | _ -> ())
      b.bstmts
  in
  List.iter (function GFun (fd, _) -> block fd.sbody | _ -> ()) file.globals

(* The functions atexit registers, in the order of the calls (each once). *)
let atexit_handlers file =
  let acc = ref [] in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vinst i =
        (match i with
         | Call (_, Var f, [ a ], _) | Local_init (_, ConsInit (f, [ a ], _), _)
           when f.vname = Fragment.atexit_function && not (PointsTo.is_defined f) -> (
             match Fragment.atexit_target a with
             | Some g when not (List.memq g !acc) -> acc := g :: !acc
             | _ -> ())
         | _ -> ());
        Cil.SkipChildren
    end
  in
  Visitor.visitFramacFileSameGlobals v file;
  List.rev !acc

(* D22 (a): the functions that are proper ancestors, in the call graph, of a
   function holding an end; the variables of theirs that hold pointers are
   made objects, so that a check at the end sees their blocks among the live
   local blocks. *)
let memtrack_root_vars ?(all_sites = false) ?(handlers = []) file unreached =
  let callers = Hashtbl.create 16 and has_end = Hashtbl.create 16 in
  let add_caller f g =
    Hashtbl.replace callers f.vid (g.vid :: Option.value ~default:[] (Hashtbl.find_opt callers f.vid))
  in
  let funcs = List.filter_map (function GFun (fd, _) -> Some fd | _ -> None) file.globals in
  List.iter
    (fun fd ->
      let v =
        object (self)
          inherit Visitor.frama_c_inplace

          method! vinst i =
            (match i with
             | Call (_, Var f, _, _) | Local_init (_, ConsInit (f, _, _), _) ->
                 let sid = match self#current_stmt with Some s -> s.sid | None -> -1 in
                 if PointsTo.is_defined f then add_caller f fd.svar
                 else if end_call_kind f <> None && not (Hashtbl.mem unreached sid) then begin
                   Hashtbl.replace has_end fd.svar.vid ();
                   (* exit runs the functions atexit registered, below this
                      frame *)
                   if end_call_kind f = Some Exit then List.iter (fun h -> add_caller h fd.svar) handlers
                 end
             | _ -> ());
            Cil.SkipChildren
        end
      in
      ignore (Visitor.visitFramacFunction v fd))
    funcs;
  (* the callers, transitively, of the functions holding an end *)
  let ancestors = Hashtbl.create 16 in
  let rec up f =
    List.iter
      (fun g ->
        if not (Hashtbl.mem ancestors g) then begin
          Hashtbl.replace ancestors g ();
          up g
        end)
      (Option.value ~default:[] (Hashtbl.find_opt callers f))
  in
  (* with checks where executions that do not halt pass, every function
     holds one (its entry) *)
  if all_sites then List.iter (fun fd -> Hashtbl.replace has_end fd.svar.vid ()) funcs;
  Hashtbl.iter (fun f () -> up f) has_end;
  List.concat_map
    (fun fd ->
      if Hashtbl.mem ancestors fd.svar.vid then
        List.filter (fun v -> has_ptr v.vtype) (fd.sformals @ fd.slocals)
      else [])
    funcs

type frame = {
  objs : varinfo list;
  kind : [ `Block | `Loop | `Switch ];
  sids : (int, unit) Hashtbl.t;
  vars : varinfo list;  (** the variables the block declares, as in the input *)
}

(* Safety: the stores that mark the blocks of local objects released. *)
(* A variable made an object only so that an end check sees it as a root
   (its address is never taken) is alone in its region: nothing points into
   the region, so its blocks are allocated and released last in, first out
   (a deeper activation, in a recursion, releases its block first). Such a
   region is used as a stack: releasing the block gives its cells back by
   moving the next free index back to the block's first index, so that a
   variable declared in a loop's body does not use up the region's array.
   No pointer can reach the cells given back, and the blocks past the next
   free index are not enumerated, so the block needs no released mark. *)
let reusable ctx v =
  Hashtbl.mem ctx.memtrack_roots v.vid
  &&
  match (info_of_var ctx v).reg.objects with
  | [ Regions.Var v' ] -> v' == v
  | _ -> false

let mark_released ctx objs loc =
  if ctx.safety = None then []
  else
    List.filter_map
      (fun v ->
        let info = info_of_var ctx v in
        if reusable ctx v then Some (Set (Cil.var info.free, base_index ctx v, loc))
        else if not (released_flag_read ctx info) then None
        else
          let freed = freed_array ctx info in
          Some
            (Set
               ( (Var freed, Index (base_index ctx v, NoOffset)),
                 Cil.mkCast ~newt:Cil_const.ucharType (iconst 1),
                 loc )))
      objs

(* MT3: the weak function whose result decides nondeterministically whether
   memtrack is checked here (a checking tool may replace it), and the
   function that ends the execution after a check that found nothing, without
   reporting anything. *)
let probe_fn ctx =
  match ctx.probe_fn with
  | Some f -> f
  | None ->
      let nd = declare_function ctx "__VERIFIER_nondet_int" ity [] in
      let fd = Cil.emptyFunction (fresh_name ctx "__p2a_probe") in
      Cil.setReturnType fd ity;
      fd.svar.vattr <- Ast_attributes.add ("weak", []) fd.svar.vattr;
      let r = Cil.makeLocalVar fd "r" ity in
      fd.sbody.bstmts <-
        [ stmt (Call (Some (Cil.var r), Var nd, [], loc0));
          Cil.mkStmt ~valid_sid:true (Return (Some (bin Ne (Cil.evar r) (iconst 0)), loc0)) ];
      add_helper ctx fd;
      ctx.probe_fn <- Some fd.svar;
      fd.svar

let stop_fn ctx =
  match ctx.stop_fn with
  | Some f -> f
  | None ->
      let exit_f = exit_function ~attrs:noreturn ctx in
      let fd = Cil.emptyFunction (fresh_name ctx "__p2a_stop") in
      Cil.update_var_type fd.svar (Cil_const.mk_tfun ~tattr:noreturn Cil_const.voidType (Some []) false);
      fd.sbody.bstmts <-
        [ stmt (Call (None, Var exit_f, [ iconst 0 ], loc0)); Cil.mkStmt ~valid_sid:true (Return (None, loc0)) ];
      add_helper ctx fd;
      Hashtbl.replace ctx.roles fd.svar.vid "stop";
      ctx.stop_fn <- Some fd.svar;
      fd.svar

let rewrite_function ctx fd =
  ctx.cur_fd <- Some fd;
  (* index variables for the object locals and parameters *)
  let objs = List.filter (is_object ctx) (fd.sformals @ fd.slocals) in
  List.iter
    (fun v ->
      let a = Cil.makeLocalVar fd ~insert:false (v.vname ^ "_addr") ity in
      Hashtbl.replace ctx.roles a.vid "addr";
      Hashtbl.replace ctx.addr_var v.vid a)
    objs;
  let formal_objs = List.filter (is_object ctx) fd.sformals in
  (* safety: the regions this function allocates alloca blocks or
     variable-length arrays in, each with a local holding the next free index
     at entry; the blocks allocated from there on are released when the
     function returns *)
  let alloca_marks =
    if ctx.safety = None then []
    else
      List.filter_map
        (fun (r : Regions.region) ->
          let here = function
            | Regions.Alloc site ->
                List.mem site.PointsTo.allocator [ "alloca"; "__builtin_alloca"; "__fc_vla_alloc" ]
                && (site.func = fd.svar.vname || site.func = fd.svar.vorig_name)
            | Regions.Var _ -> false
          in
          if List.exists here r.objects && released_flag_read ctx (info_of_region ctx r) then begin
            let info = info_of_region ctx r in
            let v = Cil.makeLocalVar fd (fresh_name ctx (Printf.sprintf "p2a_alloca%d" r.rid)) ity in
            Hashtbl.replace ctx.roles v.vid "generated";
            Some (info, v)
          end
          else None)
        ctx.regs.list
  in
  let release_allocas loc =
    List.map
      (fun (info, v) -> Call (None, Var (release_alloca_fn ctx info), [ Cil.evar v ], loc))
      alloca_marks
  in
  (* safety: companions of the pointer parameters, as extra parameters *)
  let formal_shadows =
    if ctx.safety = None then []
    else
      List.filter_map
        (fun v ->
          if Ast_types.is_ptr v.vtype then begin
            if fd.svar.vname = "main" then
              not_implemented "a pointer parameter of main in a safety mode";
            let vb = Cil.makeFormalVar fd (fresh_name ctx (v.vname ^ "__base")) ity in
            let vl = Cil.makeFormalVar fd (fresh_name ctx (v.vname ^ "__len")) ity in
            Hashtbl.replace ctx.roles vb.vid "shadow";
            Hashtbl.replace ctx.roles vl.vid "shadow";
            if not (is_object ctx v) then Hashtbl.replace ctx.shadow_vars v.vid (vb, vl);
            Some (v, vb, vl)
          end
          else None)
        (Hashtbl.find ctx.orig_formals fd.svar.vid)
  in
  (* --uninit=check: the state of each checked local (declared in the
     function's outermost block, so that it is in scope wherever its
     variable's block can be entered from), and a state parameter after the
     shadow parameters for each structure parameter that receives its
     argument's state *)
  if ctx.uninit_check then begin
    (* the reads of a scalar checked local that every path writes first
       need no check; a local all of whose reads are so needs no state *)
    let fully_elided = Hashtbl.create 8 in
    if Sys.getenv_opt "P2A_UNINIT_NO_ELIDE" = None then begin
      let scalar v =
        Hashtbl.mem ctx.check_targets v.vid
        && match Ast_types.unroll_node v.vtype with TComp _ | TArray _ -> false | _ -> true
      in
      let must = UninitMust.analyse fd ~tracked:scalar in
      let unelided = Hashtbl.create 8 in
      List.iter (fun v -> if scalar v then Hashtbl.replace fully_elided v.vid ()) fd.slocals;
      let reads =
        object (self)
          inherit Visitor.frama_c_inplace

          method! vexpr e =
            match e.enode with
            | SizeOfE _ | AlignOfE _ -> Cil.SkipChildren
            | Lval (Var v, _) when scalar v ->
                (match self#current_stmt with
                 | Some st' -> (
                     match Hashtbl.find_opt must st'.sid with
                     | Some set when UninitMust.S.mem v.vid set ->
                         Hashtbl.replace ctx.elided (st'.sid, v.vid) ()
                     | _ -> Hashtbl.replace unelided v.vid ())
                 | None -> Hashtbl.replace unelided v.vid ());
                Cil.DoChildren
            | _ -> Cil.DoChildren
        end
      in
      ignore (Visitor.visitFramacFunction reads fd);
      Hashtbl.iter (fun id () -> Hashtbl.remove fully_elided id) unelided
    end;
    List.iter
      (fun v ->
        if Hashtbl.mem fully_elided v.vid then
          ctx.uninit_elided <- (fd.svar.vname, v.vdecl, v.vname) :: ctx.uninit_elided
        else if Hashtbl.mem ctx.check_targets v.vid then begin
          let sv = Cil.makeLocalVar fd (fresh_name ctx (v.vname ^ "__init")) (init_type ctx v.vtype) in
          Hashtbl.replace ctx.roles sv.vid "init";
          Hashtbl.replace ctx.init_vars v.vid sv
        end)
      fd.slocals;
    List.iter
      (fun v ->
        if Hashtbl.mem ctx.init_formals v.vid then begin
          let sv = Cil.makeFormalVar fd (fresh_name ctx (v.vname ^ "__init")) (init_type ctx v.vtype) in
          Hashtbl.replace ctx.roles sv.vid "init";
          Hashtbl.replace ctx.init_vars v.vid sv
        end)
      (Hashtbl.find ctx.orig_formals fd.svar.vid)
  end;
  (* statements this pass created: generated instructions are not translated
     again, and a statement wrapped behind the instructions its translation
     needs has its own part translated already *)
  let skip = Hashtbl.create 16 and done_ = Hashtbl.create 16 in
  (* --uninit=check: the states of the checked variables of a block a jump
     enters without passing its start are set where the function starts and
     right before each such jump, so that the variables start anew each time
     their block is entered *)
  let init_entry =
    if not ctx.uninit_check then []
    else begin
      let jumps = UninitTargets.jumps fd in
      let blocks = ref [] in
      List.iter
        (fun v ->
          match tracked ctx v with
          | Some _ when Hashtbl.mem ctx.check_targets v.vid ->
              (match
                 List.find_opt
                   (fun (t : UninitTargets.target) -> t.var == v)
                   (UninitTargets.targets fd)
               with
               | Some t -> (
                   match List.assq_opt t.block !blocks with
                   | Some l -> l := v :: !l
                   | None -> blocks := (t.block, ref [ v ]) :: !blocks)
               | None -> ())
          | _ -> ())
        fd.slocals;
      let before = Hashtbl.create 4 in
      let entry =
        List.concat_map
          (fun (b, vars) ->
            let sources = UninitTargets.jump_sources jumps b in
            if sources = [] then []
            else begin
              let resets () =
                List.concat_map
                  (fun v ->
                    let sv = Option.get (tracked ctx v) in
                    init_fill ctx fd (Cil.var sv) sv.vtype 0)
                  (List.rev !vars)
              in
              List.iter
                (fun v -> Hashtbl.replace ctx.init_jumped v.vid ())
                !vars;
              List.iter
                (fun src ->
                  let prev = match Hashtbl.find_opt before src.sid with Some (_, l) -> l | None -> [] in
                  Hashtbl.replace before src.sid (src, prev @ resets ()))
                sources;
              resets ()
            end)
          (List.rev !blocks)
      in
      (* the labels stay on the jump, so that a jump to them sets the states
         too *)
      Hashtbl.iter
        (fun _ (src, resets) ->
          let inner = Cil.mkStmt ~valid_sid:true src.skind in
          List.iter (fun r -> Hashtbl.replace skip r.sid ()) resets;
          src.skind <- Block (Cil.mkBlock (resets @ [ inner ])))
        before;
      entry
    end
  in
  (* the variables declared by an initialisation (in C, at that point of
     their block) whose initialisation has been visited: a check before it
     must not read such a variable, which C does not have in scope yet *)
  let declared = Hashtbl.create 16 in
  let in_scope v = (not v.vdefined) || Hashtbl.mem declared v.vid in
  let frames = ref [] in
  let next_kind = ref `Block in
  let wrap s pre k =
    match pre with
    | [] -> s.skind <- k
    | pre ->
        let inner = Cil.mkStmt ~valid_sid:true k in
        Hashtbl.replace done_ inner.sid ();
        s.skind <- Block (Cil.mkBlock (List.map (gen_stmt skip) pre @ [ inner ]))
  in
  let visitor =
    object (self)
      inherit Visitor.frama_c_inplace

      method! vinst i =
        let sid = match self#current_stmt with Some s -> s.sid | None -> -1 in
        (match i with Local_init (v, _, _) -> Hashtbl.replace declared v.vid () | _ -> ());
        Cil.ChangeTo (tr_instr ctx ~sid i)

      method! vstmt_aux s =
        if Hashtbl.mem skip s.sid then Cil.SkipChildren
        else
          let runs_atexit f = end_call_kind f = Some Exit && ctx.run_atexit <> None in
          match s.skind with
          | Instr (Call (_, Var f, _, loc) as i)
            when end_call_kind f <> None
                 && (not (Hashtbl.mem ctx.unreached s.sid))
                 && (ctx.end_check <> None || runs_atexit f) ->
              (* an end of the execution: the call's arguments are
                 evaluated (and checked), then the end check runs, with the
                 roots of this frame for memtrack, then the call *)
              let is = tr_instr ctx ~sid:s.sid i in
              let pre, call =
                match List.rev is with c :: rest -> (List.rev rest, c) | [] -> assert false
              in
              let roots =
                if ctx.safety <> Some Memory_safety || ctx.end_check = None then []
                else
                  site_roots ctx fd
                    (List.filter in_scope (List.concat_map (fun f -> f.vars) !frames)
                    @ Hashtbl.find ctx.orig_formals fd.svar.vid)
                    loc
              in
              (* exit runs the functions atexit registered first *)
              let atexit =
                match ctx.run_atexit with
                | Some r when runs_atexit f -> [ stmt (Call (None, Var r.svar, [], loc)) ]
                | _ -> []
              in
              let check =
                match ctx.end_check with
                | Some c ->
                    ctx.end_points <- (s.sid, Option.get (end_call_kind f)) :: ctx.end_points;
                    [ stmt (Call (None, Var c.svar, [], loc)) ]
                | None -> []
              in
              s.skind <- Block (Cil.mkBlock (List.map stmt pre @ atexit @ roots @ check @ [ stmt call ]));
              Cil.SkipChildren
          | _ ->
          begin
          (match s.skind with
           | Loop _ -> next_kind := `Loop
           | Switch _ -> next_kind := `Switch
           | _ -> ());
          if not (Hashtbl.mem done_ s.sid) then begin
            let leaving pred =
              (* the frames left, innermost first, up to and including the
                 first one [pred] stops at *)
              let rec go = function
                | [] -> []
                | f :: rest -> if pred f then [ f ] else f :: go rest
              in
              List.concat_map (fun f -> f.objs) (go !frames)
            in
            ctx.cur_sid <- s.sid;
            match s.skind with
            | Return (eo, loc) ->
                let eo' = Option.map (tr_exp ctx) eo in
                let ret_sh =
                  match (eo, Hashtbl.find_opt ctx.ret_shadow fd.svar.vid) with
                  | Some e, Some (rb, rl) when ctx.safety <> None ->
                      let b, l = shadow_of ctx e in
                      [ Set (Cil.var rb, b, loc); Set (Cil.var rl, l, loc) ]
                  | _ -> []
                in
                let ret_init =
                  match (eo, Hashtbl.find_opt ctx.ret_init fd.svar.vid) with
                  | Some e, Some g -> init_write_global ctx g e loc
                  | _ -> []
                in
                let ret_sh = ret_sh @ ret_init in
                let released =
                  mark_released ctx (List.concat_map (fun f -> f.objs) !frames @ formal_objs) loc
                  @ release_allocas loc
                in
                let pre = take_pending ctx in
                wrap s (pre @ ret_sh @ released) (Return (eo', loc))
            | If (e, b1, b2, loc) ->
                let e' = tr_exp ctx e in
                wrap s (take_pending ctx) (If (e', b1, b2, loc))
            | Switch (e, b, l, loc) ->
                let e' = tr_exp ctx e in
                wrap s (take_pending ctx) (Switch (e', b, l, loc))
            | Break loc ->
                wrap s (mark_released ctx (leaving (fun f -> f.kind <> `Block)) loc) (Break loc)
            | Continue loc ->
                wrap s (mark_released ctx (leaving (fun f -> f.kind = `Loop)) loc) (Continue loc)
            | Goto (target, loc) ->
                let left =
                  List.concat_map
                    (fun f -> if Hashtbl.mem f.sids !target.sid then [] else f.objs)
                    (let rec upto = function
                       | [] -> []
                       | f :: rest -> if Hashtbl.mem f.sids !target.sid then [] else f :: upto rest
                     in
                     upto !frames)
                in
                wrap s (mark_released ctx left loc) (Goto (target, loc))
            | _ -> ()
          end;
          Cil.DoChildren
        end

      method! vblock b =
        let vars = b.blocals in
        (* the variables in scope in this block, for an MT3 check at its head *)
        let scope = List.filter in_scope (vars @ List.concat_map (fun f -> f.vars) !frames) in
        let objs = List.filter (is_object ctx) b.blocals in
        let kind = !next_kind in
        next_kind := `Block;
        let sids = if ctx.safety <> None then block_sids b else Hashtbl.create 1 in
        b.blocals <- List.filter (fun v -> not (is_object ctx v)) b.blocals;
        let prelude =
          List.map
            (fun v ->
              let info = info_of_var ctx v in
              let a = Hashtbl.find ctx.addr_var v.vid in
              b.blocals <- a :: b.blocals;
              gen_stmt skip
                (call_alloc ~kind:kind_local info (iconst (units ctx info v.vtype)) v.vdecl
                   (Some (Cil.var a))))
            objs
        in
        (* safety: the companions of the pointer locals, NULL's shadow until
           assigned (an uninitialised pointer is then caught when used) *)
        let shadows =
          if ctx.safety = None then []
          else
            List.concat_map
              (fun v ->
                match ptr_shape v.vtype with
                | Some shape when not (Hashtbl.mem ctx.shadow_vars v.vid) ->
                    let vb = Cil.makeLocalVar fd ~insert:false (fresh_name ctx (v.vname ^ "__base")) shape in
                    let vl = Cil.makeLocalVar fd ~insert:false (fresh_name ctx (v.vname ^ "__len")) shape in
                    Hashtbl.replace ctx.roles vb.vid "shadow";
                    Hashtbl.replace ctx.roles vl.vid "shadow";
                    Hashtbl.replace ctx.shadow_vars v.vid (vb, vl);
                    b.blocals <- b.blocals @ [ vb; vl ];
                    fd.slocals <- fd.slocals @ [ vb; vl ];
                    if Ast_types.is_ptr v.vtype then
                      [ gen_stmt skip (Set (Cil.var vb, iconst 0, v.vdecl));
                        gen_stmt skip (Set (Cil.var vl, iconst 0, v.vdecl)) ]
                    else []
                | _ -> [])
              b.blocals
        in
        (* --uninit=check: the checked variables of this block start
           unwritten *)
        let resets =
          if not ctx.uninit_check then []
          else
            List.concat_map
              (fun v ->
                match tracked ctx v with
                | Some sv when Hashtbl.mem ctx.check_targets v.vid ->
                    init_fill ctx fd (Cil.var sv) sv.vtype 0
                | _ -> [])
              vars
        in
        frames := { objs; kind; sids; vars } :: !frames;
        Cil.DoChildrenPost
          (fun b ->
            frames := List.tl !frames;
            (* the end of a block that ends with a jump is not reached; marks
               there would be dead code the front end normalises away *)
            let rec ends_with_jump stmts =
              match List.rev stmts with
              | { skind = Return _ | Goto _ | Break _ | Continue _; _ } :: _ -> true
              | { skind = Block b'; _ } :: _ -> ends_with_jump b'.bstmts
              | _ -> false
            in
            let released =
              if ends_with_jump b.bstmts then []
              else List.map (gen_stmt skip) (mark_released ctx objs loc0)
            in
            (* MT3: at the head of a loop's body and at a function's entry
               (after its local blocks are allocated), memtrack is checked
               when the probe says so, and the execution then ends *)
            let probe =
              match ctx.mt3_check with
              | Some c when kind = `Loop || b == fd.sbody ->
                  let q = Cil.makeLocalVar fd (fresh_name ctx "p2a_q") ity in
                  Hashtbl.replace ctx.roles q.vid "generated";
                  let roots =
                    site_roots ctx fd (scope @ Hashtbl.find ctx.orig_formals fd.svar.vid) loc0
                  in
                  let test =
                    if_stmt (Cil.evar q)
                      (roots
                      @ [ stmt (Call (None, Var c.svar, [], loc0));
                          stmt (Call (None, Var (stop_fn ctx), [], loc0)) ])
                      []
                  in
                  ctx.mt3_points <-
                    (test.sid, if kind = `Loop then "loop-head" else "function-entry") :: ctx.mt3_points;
                  [ stmt (Call (Some (Cil.var q), Var (probe_fn ctx), [], loc0)); test ]
              | _ -> []
            in
            b.bstmts <- prelude @ shadows @ resets @ probe @ b.bstmts @ released;
            b)
    end
  in
  ignore (Visitor.visitFramacFunction visitor fd);
  (* object parameters: the parameter is renamed v_in, the object gets a block
     at entry and the value passed in (with its shadow, in a safety mode) *)
  let entry =
    List.concat_map
      (fun v ->
        if not (is_object ctx v) then []
        else begin
          let info = info_of_var ctx v in
          let a = Hashtbl.find ctx.addr_var v.vid in
          let orig = v.vname in
          v.vname <- fresh_name ctx (orig ^ "_in");
          fd.sbody.blocals <- a :: fd.sbody.blocals;
          let store =
            if info.byte then store_bytes ctx info (Cil.evar a) v.vtype (Cil.evar v) v.vdecl
            else [ Set ((Var info.arr, Index (Cil.evar a, NoOffset)), Cil.evar v, v.vdecl) ]
          in
          let shadow =
            match List.find_opt (fun (v', _, _) -> v' == v) formal_shadows with
            | Some (_, vb, vl) ->
                write_shadow ctx (Var v, NoOffset) (Cil.evar vb, Cil.evar vl) v.vdecl
            | None -> []
          in
          let pre = take_pending ctx in
          List.map stmt
            ((call_alloc ~kind:kind_local info (iconst (units ctx info v.vtype)) v.vdecl
                (Some (Cil.var a))
              :: pre)
            @ store @ shadow)
        end)
      formal_objs
  in
  let saves =
    List.map (fun (info, v) -> stmt (Set (Cil.var v, Cil.evar info.free, loc0))) alloca_marks
  in
  fd.sbody.bstmts <- saves @ entry @ init_entry @ fd.sbody.bstmts;
  fd.slocals <-
    List.filter (fun v -> not (is_object ctx v)) fd.slocals
    @ List.filter_map (fun v -> Hashtbl.find_opt ctx.addr_var v.vid) objs
      |> List.filter (fun a -> not (List.memq a fd.sformals));
  ctx.cur_fd <- None

(* The violation markers the output calls, for the record: name, property
   and the status the marker's definition exits with. With the reach-error
   markers the one marker stands for every property and the output only
   declares it, so it has no status of its own. *)
let violations ctx =
  match (ctx.safety, ctx.markers) with
  | Some (Memory_safety | Memory_cleanup), Split ->
      List.map
        (fun (prop, vi) -> (vi.vname, property_name prop, Some (snd (marker_of prop))))
        ctx.marker_fns
  | Some (Memory_safety | Memory_cleanup), Reach_error -> (
      match ctx.violation_fn with
      | Some vi ->
          (vi.vname, "valid-memsafety", None)
          :: (if ctx.init_check <> None || Hashtbl.length ctx.init_struct_checks > 0 then
                [ (vi.vname, property_name Uninit_read, None) ]
              else [])
      | None -> [])
  | _ -> (
      (match ctx.overflow_marker with
       | Some vi -> [ (vi.vname, "no-overflow", None) ]
       | None -> [])
      @
      match ctx.uninit_marker with
      | Some vi -> [ (vi.vname, property_name Uninit_read, None) ]
      | None -> [])

(* ---- regions, static objects, types ---- *)

(* The generated globals of a region: the array, the next free index, the
   allocator. *)
let make_region ctx (reg : Regions.region) ~byte sigma =
  let k = reg.rid in
  let cell = tr_type sigma in
  let arr =
    Cil.makeGlobalVar (fresh_name ctx (Printf.sprintf "p2a_mem%d" k))
      (Cil_const.mk_tarray cell (Some (iconst ctx.size)))
  in
  let free = Cil.makeGlobalVar (fresh_name ctx (Printf.sprintf "p2a_mem%d_free" k)) ity in
  (* the safety modes' block table, written by the allocator *)
  let table =
    if ctx.safety = None then None
    else
      Some
        ( byte_array ctx (Printf.sprintf "p2a_mem%d__kind" k),
          int_array ctx (Printf.sprintf "p2a_mem%d__blen" k) "generated",
          byte_array ctx (Printf.sprintf "p2a_mem%d__freed" k) )
  in
  (* p2a_allocK(n): the index of n fresh cells. In the safety modes
     p2a_allocK(n, kind) also records the block in the table: it occupies
     max(1, n) cells, so that a block of no cells (malloc(0)) does not share
     its first index with the next one, while its shadow length stays n; and
     a block that does not fit in the array stops the execution (see
     [exhausted_call]). *)
  let mk_alloc ?zero ~zeroed () =
    let name = Printf.sprintf (if zeroed then "p2a_alloc0_%d" else "p2a_alloc%d") k in
    let fd = Cil.emptyFunction (fresh_name ctx name) in
    Cil.setReturnType fd ity;
    let n = Cil.makeFormalVar fd "n" ity in
    let r = Cil.makeLocalVar fd "r" ity in
    let body =
      match table with
      | None ->
          [ stmt (Set (Cil.var r, Cil.evar free, loc0));
            stmt (Set (Cil.var free, mk (BinOp (PlusA, Cil.evar free, Cil.evar n, ity)), loc0)) ]
      | Some (kind, blen, _) ->
          let kd = Cil.makeFormalVar fd "kind" ity in
          let c = Cil.makeLocalVar fd "c" ity in
          [ stmt (Set (Cil.var r, Cil.evar free, loc0));
            stmt (Set (Cil.var c, Cil.evar n, loc0));
            if_stmt (bin Lt (Cil.evar c) (iconst 1)) [ stmt (Set (Cil.var c, iconst 1, loc0)) ] [] ]
          (* a block that does not fit in the array: the execution stops; an
             unbounded array fits every block *)
          @ (if ctx.unbounded then []
             else
               [ if_stmt
                   (bin Gt (bin PlusA (Cil.evar r) (Cil.evar c)) (iconst ctx.size))
                   [ stmt (exhausted_call ctx loc0) ]
                   [] ])
          @ stmt (Set (Cil.var free, bin PlusA (Cil.evar free) (Cil.evar c), loc0))
            :: when_below ctx (Cil.evar r)
                 [ stmt (Set (aidx kind (Cil.evar r), Cil.mkCast ~newt:Cil_const.ucharType (Cil.evar kd), loc0));
                   stmt (Set (aidx blen (Cil.evar r), Cil.evar c, loc0)) ]
    in
    let body =
      if not zeroed then body
      else
        let i = Cil.makeLocalVar fd "i" ity in
        body
        @ Cil.mkForIncr ~iter:i ~first:(iconst 0) ~stopat:(Cil.evar n) ~incr:(iconst 1)
            ~body:
              [ stmt
                  (Set
                     ( (Var arr, Index (add (Cil.evar r) (Cil.evar i), NoOffset)),
                       (match zero with
                        | Some z -> z
                        | None -> Cil.mkCast ~newt:cell (iconst 0)),
                       loc0 )) ]
            ()
    in
    fd.sbody.bstmts <- body @ [ Cil.mkStmt ~valid_sid:true (Return (Some (Cil.evar r), loc0)) ];
    fd
  in
  let info =
    { reg; byte; sigma; arr; free; alloc = mk_alloc ~zeroed:false (); alloc0 = None;
      zero = None; next_static = 1; access = Hashtbl.create 4; shadow_arrays = None;
      table; check = None; release = None; release_alloca = None; release_vla = None;
      flag_read = None; clear = None; mark = None; point = None }
  in
  let needs_zeroed =
    List.exists
      (function Regions.Alloc s -> s.PointsTo.allocator = "calloc" | _ -> false)
      reg.objects
  in
  if needs_zeroed then begin
    let zero =
      if Ast_types.is_struct sigma then begin
        let z = Cil.makeGlobalVar (fresh_name ctx (Printf.sprintf "p2a_zero%d" k)) cell in
        info.zero <- Some z;
        Some (Cil.evar z)
      end
      else None
    in
    info.alloc0 <- Some (mk_alloc ?zero ~zeroed:true ())
  end;
  info

(* The call that tells a downstream reading the output's IR that region
   array [arr] starts with arbitrary contents.  The region arrays are C
   globals, so C starts them at 0, while their cells beyond the static
   objects stand for heap and local objects, whose contents are
   indeterminate; a reader of the IR alone would take the 0.  The function
   is named after the array, exactly (a downstream finds the array from the
   name, so a renamed function would name another one), takes and returns
   nothing and does nothing, so the C reading is unchanged. *)
let arbitrary_call ctx arr =
  let name = "__p2a_arbitrary_" ^ arr.vname in
  if Hashtbl.mem ctx.names_used name then
    not_implemented "the name %s, which the output needs for a region" name;
  Hashtbl.add ctx.names_used name ();
  let fd = Cil.emptyFunction name in
  Cil.update_var_type fd.svar (Cil_const.mk_tfun Cil_const.voidType (Some []) false);
  fd.sbody.bstmts <- [ Cil.mkStmt ~valid_sid:true (Return (None, loc0)) ];
  add_helper ctx fd;
  Call (None, Var fd.svar, [], loc0)

(* main's prelude: first each region array made arbitrary (above), then every
   cell of every static object written as C requires (zero, then the
   initialiser), so a static object's cells are as C says whichever reading
   is taken.  Safety mode's shadow arrays and block tables keep C's zeros:
   their meaning depends on them. *)
let static_init ctx main_fd (inits : (varinfo * init_or_str option) list) =
  ctx.cur_fd <- Some main_fd;
  let stmts = ref [] in
  let emit_i i = stmts := stmt i :: !stmts in
  let emit_stmts l = stmts := List.rev_append l !stmts in
  Hashtbl.fold (fun rid info acc -> (rid, info) :: acc) ctx.infos []
  |> List.sort (fun (a, _) (b, _) -> compare a b)
  |> List.iter (fun (_, info) -> emit_i (arbitrary_call ctx info.arr));
  List.iter
    (fun (v, init) ->
      let info = info_of_var ctx v in
      let base = Hashtbl.find ctx.static_index v.vid in
      let n = units ctx info v.vtype in
      let cell = tr_type info.sigma in
      let zero () =
        if Ast_types.is_struct info.sigma then begin
          let z =
            match info.zero with
            | Some z -> z
            | None ->
                let z =
                  Cil.makeGlobalVar
                    (fresh_name ctx (Printf.sprintf "p2a_zero%d" info.reg.rid))
                    cell
                in
                info.zero <- Some z;
                z
          in
          Cil.evar z
        end
        else Cil.mkCast ~newt:cell (iconst 0)
      in
      let at i = (Var info.arr, Index (i, NoOffset)) in
      (match info.table with
       | Some (kind, blen, _) ->
           emit_i (Set (aidx kind (iconst base), Cil.mkCast ~newt:Cil_const.ucharType (iconst kind_static), v.vdecl));
           emit_i (Set (aidx blen (iconst base), iconst (max 1 n), v.vdecl))
       | None -> ());
      if n <= 8 then
        for j = 0 to n - 1 do
          emit_i (Set (at (iconst (base + j)), zero (), v.vdecl))
        done
      else begin
        let it = Cil.makeLocalVar main_fd (fresh_name ctx "p2a_i") ity in
        Hashtbl.replace ctx.roles it.vid "generated";
        emit_stmts
          (Cil.mkForIncr ~iter:it ~first:(iconst base) ~stopat:(iconst (base + n))
             ~incr:(iconst 1)
             ~body:[ stmt (Set (at (Cil.evar it), zero (), v.vdecl)) ]
             ())
      end;
      match init with
      | Some (CInit i) ->
          List.iter emit_i (init_stores ctx ~implicit:false ~loc:v.vdecl v i)
      | Some (StrInit (Str s)) ->
          String.iteri
            (fun j c ->
              emit_i
                (Set
                   ( at (iconst (base + j)),
                     Cil.mkCast ~newt:cell (Cil.kinteger ~loc:loc0 IChar (Char.code c)),
                     v.vdecl )))
            s
      | Some (StrInit (Wstr _)) -> not_implemented "a wide string literal"
      | None -> ())
    inits;
  ctx.cur_fd <- None;
  List.rev !stmts

(* memtrack: the global telling a pass something happened (fixpoint: a block
   was marked; guess: a pointer reached a guessed block). *)
let mt_flag ctx =
  match List.find_map (function GVar (v, _, _) when v.vname = "p2a_mt_flag" -> Some v | _ -> None) ctx.helpers with
  | Some v -> v
  | None ->
      let v = Cil.makeGlobalVar (fresh_name ctx "p2a_mt_flag") ity in
      Hashtbl.replace ctx.roles v.vid "generated";
      ctx.helpers <- GVar (v, { init = None }, loc0) :: ctx.helpers;
      v

(* memtrack: per block of a heap region, marked (fixpoint: tracked; guess: in
   the guessed set S). *)
let mark_array ctx info =
  match info.mark with
  | Some m -> m
  | None ->
      let suffix = if ctx.memtrack = Some Fixpoint then "mark" else "S" in
      let m = byte_array ctx (Printf.sprintf "p2a_mem%d__%s" info.reg.rid suffix) in
      info.mark <- Some m;
      m

(* memtrack: p2a_mt_pointK(v, b), for a pointer of value v and shadow b into
   heap region K: the pointer points to the block b when b is a block's first
   index and v lies in the block or right after it (a pointer moved past it
   by arithmetic points to no block). Fixpoint: the block is marked tracked,
   and the flag set if it was not. Guess: the flag is set if the block is in
   S. *)
let point_fn ctx info =
  match info.point with
  | Some f -> f.svar
  | None ->
      let kind, blen, _ = block_table ctx info in
      let mark = mark_array ctx info in
      let flag = mt_flag ctx in
      let fd = Cil.emptyFunction (fresh_name ctx (Printf.sprintf "p2a_mt_point%d" info.reg.rid)) in
      Cil.setReturnType fd Cil_const.voidType;
      let v = Cil.makeFormalVar fd "v" ity in
      let b = Cil.makeFormalVar fd "b" ity in
      let eb = Cil.evar b and off = bin MinusA (Cil.evar v) (Cil.evar b) in
      let action =
        match ctx.memtrack with
        | Some Fixpoint ->
            [ if_stmt (mk (UnOp (LNot, rd mark eb, ity)))
                [ stmt (Set (aidx mark (copy eb), uchar_one, loc0));
                  stmt (Set (Cil.var flag, iconst 1, loc0)) ]
                [] ]
        | _ -> [ if_stmt (rd mark eb) [ stmt (Set (Cil.var flag, iconst 1, loc0)) ] [] ]
      in
      let rec all conds body =
        match conds with [] -> body | c :: cs -> [ if_stmt c (all cs body) [] ]
      in
      fd.sbody.bstmts <-
        all
          ([ bin Gt (copy eb) (iconst 0) ]
           @ Option.to_list (below_size ctx (copy eb))
           @ [ bin Ne (Cil.mkCast ~newt:ity (rd kind (copy eb))) (iconst 0);
            bin Ge off (iconst 0);
            bin Le (copy off) (rd blen (copy eb)) ])
          action;
      add_helper ctx fd;
      info.point <- Some fd;
      fd.svar

(* The weak function the guess form draws each block's membership in S
   from: a nondeterministic choice for a verifier, which a checking tool can
   replace by its own definition to try every choice. *)
let guess_fn ctx =
  match ctx.guess_fn with
  | Some f -> f
  | None ->
      let nd = declare_function ctx "__VERIFIER_nondet_int" ity [] in
      let fd = Cil.emptyFunction (fresh_name ctx "__p2a_guess") in
      Cil.setReturnType fd ity;
      fd.svar.vattr <- Ast_attributes.add ("weak", []) fd.svar.vattr;
      let r = Cil.makeLocalVar fd "r" ity in
      fd.sbody.bstmts <-
        [ stmt (Call (Some (Cil.var r), Var nd, [], loc0));
          Cil.mkStmt ~valid_sid:true (Return (Some (bin Ne (Cil.evar r) (iconst 0)), loc0)) ];
      add_helper ctx fd;
      ctx.guess_fn <- Some fd.svar;
      fd.svar

(* The body of the end check. memcleanup: a heap block not released is a
   violation. memtrack: a heap block not released that no root reaches is
   one; the roots are the pointers held in globals, in the live blocks that
   are not heap blocks (static, local and alloca blocks: the locals of the
   callers the variables made objects for this are among them) and in the
   site table (the frame the end is in). *)
let fill_end_check ?(memtrack = false) ?(prop = Valid_memtrack) ctx file check =
  Cil.setReturnType check Cil_const.voidType;
  let heaps = heap_infos ctx in
  let is_heap info = List.memq info heaps in
  let newvar () = fresh_local ctx check "p2a_j" ity in
  let body =
    match (if memtrack then ctx.memtrack else None) with
    | None ->
        List.concat_map
          (fun info ->
            let kind, _, freed = block_table ctx info in
            blocks_loop ctx info check (fun b ->
                [ if_stmt (bin Eq (Cil.mkCast ~newt:ity (rd kind b)) (iconst kind_heap))
                    [ if_stmt (mk (UnOp (LNot, rd freed (copy b), ity)))
                        [ stmt (violation ctx Valid_memcleanup loc0) ]
                        [] ]
                    [] ]))
          heaps
    | Some form ->
        let flag = mt_flag ctx in
        let point info v b = [ stmt (Call (None, Var (point_fn ctx info), [ v; b ], loc0)) ] in
        (* the pointers held in the globals *)
        let seen = Hashtbl.create 16 in
        let globals =
          List.concat_map
            (function
              | (GVar (v, _, _) | GVarDecl (v, _))
                when (not (Hashtbl.mem seen v.vid)) && (not (Ast_types.is_fun v.vtype))
                     && (not (Ast_info.is_string_literal v)) && (not (is_object ctx v))
                     && has_ptr v.vtype -> (
                  Hashtbl.replace seen v.vid ();
                  match heap_target ctx (PointsTo.var_node ctx.st v) with
                  | Some info ->
                      slots ctx ~newvar v.vtype (Var v, NoOffset) (var_shadow_base ctx v) (point info)
                  | None -> [])
              | _ -> [])
            file.globals
        in
        (* the site table *)
        let sval, sbase, sreg, sn = site_arrays ctx in
        let site =
          let i = newvar () in
          let ei = Cil.evar i in
          let rec chain = function
            | [] -> []
            | info :: rest ->
                [ if_stmt
                    (bin Eq (rd sreg ei) (iconst info.reg.rid))
                    (point info (rd sval (copy ei)) (rd sbase (copy ei)))
                    (chain rest) ]
          in
          Cil.mkForIncr ~iter:i ~first:(iconst 0) ~stopat:(Cil.evar sn) ~incr:(iconst 1)
            ~body:(chain heaps) ()
        in
        (* the regions whose cells may hold a pointer into a heap region: the
           pointers in the cells of block b *)
        let scanned =
          List.filter_map
            (fun (r : Regions.region) ->
              let info = info_of_region ctx r in
              match heap_target ctx r.rep with
              | Some target when info.byte || has_ptr info.sigma -> Some (info, target)
              | _ -> None)
            ctx.regs.list
        in
        let cells info target b =
          let _, blen, _ = block_table ctx info in
          let i = newvar () in
          let ei = Cil.evar i in
          let inner =
            if info.byte then begin
              let sb, _ = shadow_arrays ctx info in
              let ld, _ = accessors ctx info ity in
              let t = fresh_local ctx check "p2a_p" ity in
              [ if_stmt (bin Ne (rd sb ei) (iconst 0))
                  (stmt (Call (Some (Cil.var t), Var ld.svar, [ copy ei ], loc0))
                   :: point target (Cil.evar t) (rd sb (copy ei)))
                  [] ]
            end
            else if Ast_types.is_ptr info.sigma then begin
              let sb, _ = shadow_arrays ctx info in
              point target (rd info.arr ei) (rd sb (copy ei))
            end
            else slots ctx ~newvar info.sigma (aidx info.arr ei) None (point target)
          in
          Cil.mkForIncr ~iter:i ~first:(copy b) ~stopat:(bin PlusA (copy b) (rd blen (copy b)))
            ~incr:(iconst 1) ~body:inner ()
        in
        (* the contents of the live blocks of the scanned regions; for a heap
           region only those [scan_heap] admits (fixpoint: tracked; guess:
           not in S) *)
        let scan ~heap_cond =
          List.concat_map
            (fun (info, target) ->
              let _, _, freed = block_table ctx info in
              blocks_loop ctx info check (fun b ->
                  let live body = [ if_stmt (mk (UnOp (LNot, rd freed b, ity))) body [] ] in
                  if is_heap info then live [ if_stmt (heap_cond info (copy b)) (cells info target b) [] ]
                  else live (cells info target b)))
            scanned
        in

        (match form with
         | Fixpoint ->
             (* the marks start at the non-heap blocks, the roots add the
                blocks they point to, and the marked blocks' pointers add
                theirs until nothing changes *)
             List.concat_map
               (fun info ->
                 let kind, _, _ = block_table ctx info in
                 let mark = mark_array ctx info in
                 blocks_loop ctx info check (fun b ->
                     [ stmt (Set (aidx mark b, Cil.mkCast ~newt:Cil_const.ucharType (iconst 0), loc0));
                       if_stmt (bin Ne (Cil.mkCast ~newt:ity (rd kind (copy b))) (iconst kind_heap))
                         [ stmt (Set (aidx mark (copy b), uchar_one, loc0)) ]
                         [] ]))
               heaps
             @ globals @ site
             @ [ stmt (Set (Cil.var flag, iconst 1, loc0)) ]
             @ Cil.mkWhile ~guard:(Cil.evar flag)
                 ~body:
                   (stmt (Set (Cil.var flag, iconst 0, loc0))
                   :: scan ~heap_cond:(fun info b -> rd (mark_array ctx info) b))
                 ()
             @ List.concat_map
                 (fun info ->
                   let kind, _, freed = block_table ctx info in
                   let mark = mark_array ctx info in
                   blocks_loop ctx info check (fun b ->
                       [ if_stmt (bin Eq (Cil.mkCast ~newt:ity (rd kind b)) (iconst kind_heap))
                           [ if_stmt (mk (UnOp (LNot, rd freed (copy b), ity)))
                               [ if_stmt (mk (UnOp (LNot, rd mark (copy b), ity)))
                                   [ stmt (violation ctx prop loc0) ]
                                   [] ]
                               [] ]
                           [] ]))
                 heaps
         | Guess ->
             (* S is guessed among the live heap blocks; a violation when S
                holds one, no root points into S, and no live block outside
                S does *)
             let g = fresh_local ctx check "p2a_g" ity in
             let any = fresh_local ctx check "p2a_any" ity in
             let guess = guess_fn ctx in
             [ stmt (Set (Cil.var flag, iconst 0, loc0)); stmt (Set (Cil.var any, iconst 0, loc0)) ]
             @ List.concat_map
                 (fun info ->
                   let kind, _, freed = block_table ctx info in
                   let mark = mark_array ctx info in
                   blocks_loop ctx info check (fun b ->
                       [ stmt (Set (aidx mark b, Cil.mkCast ~newt:Cil_const.ucharType (iconst 0), loc0));
                         if_stmt (bin Eq (Cil.mkCast ~newt:ity (rd kind (copy b))) (iconst kind_heap))
                           [ if_stmt (mk (UnOp (LNot, rd freed (copy b), ity)))
                               [ stmt (Call (Some (Cil.var g), Var guess, [], loc0));
                                 if_stmt (Cil.evar g)
                                   [ stmt (Set (aidx mark (copy b), uchar_one, loc0));
                                     stmt (Set (Cil.var any, iconst 1, loc0)) ]
                                   [] ]
                               [] ]
                           [] ]))
                 heaps
             @ globals @ site
             @ scan ~heap_cond:(fun info b -> mk (UnOp (LNot, rd (mark_array ctx info) b, ity)))
             @ [ if_stmt (Cil.evar any)
                   [ if_stmt (mk (UnOp (LNot, Cil.evar flag, ity)))
                       [ stmt (violation ctx prop loc0) ]
                       [] ]
                   [] ])
  in
  check.sbody.bstmts <- body;
  add_helper ctx check

(* p2a_run_atexit(): the functions atexit registered, the latest first, each
   once, called by number (a function registered meanwhile runs too, before
   the ones registered earlier). *)
let fill_run_atexit ctx fd =
  Cil.setReturnType fd Cil_const.voidType;
  match ctx.atexit_table with
  | None -> ()
  | Some (fn, n) ->
      let k = fresh_local ctx fd "p2a_k" ity in
      let rec chain = function
        | [] -> []
        | g :: rest ->
            [ if_stmt
                (bin Eq (Cil.evar k) (iconst (Hashtbl.find ctx.atexit_ids g.vid)))
                [ stmt (Call (None, Var g, [], loc0)) ]
                (chain rest) ]
      in
      fd.sbody.bstmts <-
        Cil.mkWhile
          ~guard:(bin Gt (Cil.evar n) (iconst 0))
          ~body:
            ([ stmt (Set (Cil.var n, bin MinusA (Cil.evar n) (iconst 1), loc0));
               stmt (Set (Cil.var k, rd fn (Cil.evar n), loc0)) ]
            @ chain ctx.atexit_targets)
          ();
      add_helper ctx fd

(* The end at the return from main: the input's main is renamed and a new
   main calls it, then runs the end check with the globals as the only roots
   (main's frame is gone), then returns its result. The static objects are
   initialised by the new main, before the call. *)
let wrap_main ctx file main statics ~run_atexit check =
  let nm = Cil.emptyFunction "main" in
  let ret = Cil.getReturnType main.svar.vtype in
  Cil.setReturnType nm ret;
  let args = List.map (fun v -> Cil.evar (Cil.makeFormalVar nm v.vname v.vtype)) main.sformals in
  main.svar.vname <- fresh_name ctx "__p2a_main";
  let init = static_init ctx nm statics in
  let r =
    if Ast_types.is_void ret then None
    else begin
      let r = Cil.makeLocalVar nm (fresh_name ctx "p2a_r") ret in
      Some r
    end
  in
  let roots =
    match (ctx.safety, check) with
    | Some Memory_safety, Some _ ->
        let _, _, _, sn = site_arrays ctx in
        [ stmt (Set (Cil.var sn, iconst 0, loc0)) ]
    | _ -> []
  in
  let chk = Option.map (fun c -> stmt (Call (None, Var c.svar, [], loc0))) check in
  let atexit =
    match run_atexit with Some f -> [ stmt (Call (None, Var f.svar, [], loc0)) ] | None -> []
  in
  nm.sbody.bstmts <-
    init
    @ [ stmt (Call (Option.map Cil.var r, Var main.svar, args, loc0)) ]
    @ atexit @ roots @ Option.to_list chk
    @ [ Cil.mkStmt ~valid_sid:true (Return (Option.map Cil.evar r, loc0)) ];
  Option.iter (fun c -> ctx.end_points <- (c.sid, Main_return) :: ctx.end_points) chk;
  Hashtbl.replace ctx.roles nm.svar.vid "generated";
  List.iter (fun v -> Hashtbl.replace ctx.roles v.vid "generated") (nm.sformals @ nm.slocals);
  file.globals <-
    List.concat_map
      (function GFun (fd, _) as g when fd == main -> [ g; GFun (nm, loc0) ] | g -> [ g ])
      file.globals

(* Safety: the companion fields of every pointer field (and array of
   pointers), placed right after it, so that a structure carries the shadows
   of the pointers it holds. *)
let add_companion_fields ctx file =
  List.iter
    (function
      | GCompTag (ci, _) when ci.cstruct ->
          let taken = Hashtbl.create 8 in
          Option.iter (List.iter (fun f -> Hashtbl.replace taken f.fname ())) ci.cfields;
          let fresh base =
            let rec go n =
              let c = if n = 0 then base else Printf.sprintf "%s_%d" base n in
              if Hashtbl.mem taken c then go (n + 1) else (Hashtbl.replace taken c (); c)
            in
            go 0
          in
          Option.iter
            (fun fields ->
              let fields' =
                List.concat_map
                  (fun f ->
                    match ptr_shape f.ftype with
                    | Some shape ->
                        let mk_f suffix =
                          let name = fresh (f.fname ^ suffix) in
                          { f with
                            fname = name; forig_name = name; ftype = shape; faddrof = false;
                            fsize_in_bits = None; foffset_in_bits = None; fattr = [] }
                        in
                        let fb = mk_f "__base" and fl = mk_f "__len" in
                        Hashtbl.replace ctx.companions (field_key ci f) (fb, fl);
                        Hashtbl.replace ctx.companion_names (field_key ci fb) ();
                        Hashtbl.replace ctx.companion_names (field_key ci fl) ();
                        [ f; fb; fl ]
                    | None -> [ f ])
                  fields
              in
              List.iteri (fun j f -> f.forder <- j) fields';
              ci.cfields <- Some fields')
            ci.cfields
      | _ -> ())
    file.globals

(* Translate every type that names a pointer, now that no expression of the
   original remains to be translated. *)
let retype file =
  List.iter
    (function
      | GType (ti, _) -> ti.ttype <- tr_type ti.ttype
      | GCompTag (ci, _) ->
          Option.iter
            (List.iter (fun fi ->
                 fi.ftype <- tr_type fi.ftype;
                 fi.fsize_in_bits <- None;
                 fi.foffset_in_bits <- None))
            ci.cfields
      | GVar (vi, _, _) when not (Ast_info.is_string_literal vi) ->
          Cil.update_var_type vi (tr_type vi.vtype)
      | GVarDecl (vi, _) when not (Ast_types.is_fun vi.vtype) ->
          Cil.update_var_type vi (tr_type vi.vtype)
      | GFun (fd, _) ->
          List.iter (fun v -> Cil.update_var_type v (tr_type v.vtype)) fd.sformals;
          List.iter (fun v -> Cil.update_var_type v (tr_type v.vtype)) fd.slocals;
          Cil.setReturnType fd (tr_type (Cil.getReturnType fd.svar.vtype));
          Cil.setFormals fd fd.sformals;
          Cil.unsafeSetFormalsDecl fd.svar fd.sformals
      | _ -> ())
    file.globals

(* With the reach-error markers, reach_error() is the violation marker, so
   whatever the input names reach_error at file scope is renamed: its own
   reach_error function (its definition, declarations and calls share one
   variable), and equally a variable, a typedef or an enumeration constant of
   that name, since the marker's declaration would clash with any of them.
   __VERIFIER_error, the older name of the same error event, is renamed
   alike, so that a consumer reading it as the error event never takes the
   input's for a violation. The new name of a variable or function is
   recorded as a name of the program. A renamed function the input only
   declares stays declared: a consumer reads its call as the end of the
   execution, not a violation (llvm2lts recognises the __p2a_input_ names). *)
let rename_input_error_events ctx file =
  let rename original =
    let name = lazy (fresh_name ctx ("__p2a_input_" ^ original)) in
    List.iter
      (function
        | GFun ({ svar = vi; _ }, _) | GFunDecl (_, vi, _) | GVar (vi, _, _) | GVarDecl (vi, _)
          when vi.vname = original ->
            vi.vname <- Lazy.force name;
            Hashtbl.replace ctx.roles vi.vid "program"
        | GType (ti, _) when ti.tname = original -> ti.tname <- Lazy.force name
        | GEnumTag (ei, _) | GEnumTagDecl (ei, _) ->
            List.iter
              (fun it -> if it.einame = original then it.einame <- Lazy.force name)
              ei.eitems
        | _ -> ())
      file.globals
  in
  rename "reach_error";
  rename "__VERIFIER_error"

(* The regions held in one scalar instead of an array: a region whose only
   object is a block alloca allocates with room for one cell of an integer
   type wider than a byte, at a statement no loop holds of a function no
   cycle of calls holds (so one call of it allocates the block at most once,
   and no two calls of it are live together), into which no pointer is moved
   by arithmetic or indexing, no left value reaches past the cell (a field
   or an index), no block function writes, and no pointer outlives the
   function that holds it (stored in memory, in a global or returned). Then
   every valid pointer into the region points to the block of the one live
   call, so the cell is one variable, made arbitrary again where each call
   allocates it: a termination proof needs no invariant about an array, as
   for the same program with a local variable. The pointers and the checks
   are kept as they are; only the cell's contents move. *)
let scalar_regions st (regs : Regions.t) file =
  let ints t =
    match Ast_types.unroll_node t with
    | TInt _ | TEnum _ -> Cil.bitsSizeOf t > 8
    | _ -> false
  in
  let moved = Hashtbl.create 8 in
  let mark e =
    match Regions.find regs (PointsTo.ptee st e) with
    | Some r -> Hashtbl.replace moved r.Regions.rid ()
    | None -> ()
  in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vexpr e =
        (match e.enode with
         | BinOp ((PlusPI | MinusPI), p, _, _) -> mark p
         | _ -> ());
        Cil.DoChildren

      method! vlval lv =
        (match lv with Mem e, (Field _ | Index _) -> mark e | _ -> ());
        Cil.DoChildren
    end
  in
  Visitor.visitFramacFileSameGlobals v file;
  let in_loop = Hashtbl.create 16 and sizes = Hashtbl.create 8 in
  let calls = Hashtbl.create 16 in
  List.iter
    (function
      | GFun (fd, _) ->
          let rec block ~loop b =
            List.iter
              (fun s ->
                if loop then Hashtbl.replace in_loop s.sid ();
                (match s.skind with
                 | Instr (Call (_, Var f, [ n ], _) | Local_init (_, ConsInit (f, [ n ], _), _))
                   when List.mem f.vname [ "alloca"; "__builtin_alloca" ] -> Hashtbl.replace sizes s.sid n
                 | Instr (Call (_, Var f, _, _) | Local_init (_, ConsInit (f, _, _), _))
                   when PointsTo.is_defined f -> Hashtbl.add calls fd.svar.vname f.vname
                 | _ -> ());
                match s.skind with
                | If (_, b1, b2, _) -> block ~loop b1; block ~loop b2
                | Loop (_, b', _, _, _) -> block ~loop:true b'
                | Switch (_, b', _, _) | Block b' -> block ~loop b'
                | _ -> ())
              b.bstmts
          in
          block ~loop:false fd.sbody
      | _ -> ())
    file.globals;
  (* a function no cycle of calls holds: it does not reach itself *)
  let recursive f =
    let seen = Hashtbl.create 16 in
    let rec reach g =
      List.exists
        (fun h -> h = f || ((not (Hashtbl.mem seen h)) && (Hashtbl.add seen h (); reach h)))
        (Hashtbl.find_all calls g)
    in
    reach f
  in
  List.filter
    (fun (reg : Regions.region) ->
      match (reg.kind, reg.objects) with
      | Regions.Typed sigma, [ Regions.Alloc site ] ->
          ints sigma
          && List.mem site.PointsTo.allocator [ "alloca"; "__builtin_alloca" ]
          && (not (recursive site.func))
          && (not (Hashtbl.mem in_loop site.sid))
          && (match Hashtbl.find_opt sizes site.sid with
              | Some n -> Regions.size_in_cells sigma n = Some (Regions.Const 1)
              | None -> false)
          && (not reg.field_address) && reg.mem_sizes = []
          && (not (Hashtbl.mem moved reg.rid))
          && not (pointers_escape st regs file reg)
      | _ -> false)
    regs.list

(* [uninit_targets]: with --uninit=check, the variables that start
   uninitialised, each with its function, found before the passes that run
   ahead of this one added their temporaries (which they write before they
   read). *)
let run ~size ?(unbounded = false) ?(scalar_cells = false) ~safety ?(markers = Split) ?(memtrack_check = Guess) ?(check_memtrack = true)
    ?(nonterminating = false) ?wrap ?bad_call ?(uninit = "keep") ?(uninit_targets = []) () =
  let file = Ast.get () in
  let st = PointsTo.analyse () in
  (* the ends of the execution are checked in --memory-safety (memtrack) and
     --memory-cleanup, when the program allocates a heap block: without one
     neither property can fail.  Without [check_memtrack], --memory-safety
     checks valid-deref and valid-free only, and so no end. *)
  let ends =
    ((safety = Some Memory_safety && check_memtrack) || safety = Some Memory_cleanup)
    && Hashtbl.fold
         (fun _ (site : PointsTo.site) acc -> acc || List.mem site.allocator heap_allocators)
         st.sites false
  in
  let unreached = Hashtbl.create 8 and memtrack_roots = Hashtbl.create 8 in
  let handlers = atexit_handlers file in
  if ends then find_unreached file unreached;
  (* memtrack's roots in the callers of the functions it is checked in: at
     the ends in --memory-safety, and everywhere with checks where
     executions that do not halt pass *)
  if ends && (safety = Some Memory_safety || nonterminating) then
    List.iter
      (fun v ->
        if not (Hashtbl.mem st.address_taken v.vid) then begin
          Hashtbl.replace st.address_taken v.vid v;
          Hashtbl.replace memtrack_roots v.vid ()
        end)
      (memtrack_root_vars ~all_sites:nonterminating ~handlers file unreached);
  let regs = Regions.compute st in
  let ctx =
    { st; regs; size; unbounded; safety; infos = Hashtbl.create 8; static_index = Hashtbl.create 8;
      addr_var = Hashtbl.create 8; names_used = Hashtbl.create 64;
      roles = Hashtbl.create 32; pointers = []; layouts = Hashtbl.create 8;
      pending = []; cur_fd = None; shadow_vars = Hashtbl.create 16;
      companions = Hashtbl.create 8; companion_names = Hashtbl.create 8;
      ret_shadow = Hashtbl.create 8; orig_formals = Hashtbl.create 16; helpers = [];
      markers; violation_fn = None; marker_fns = []; violation_calls = []; check_index = None; wrap;
      memtrack =
        (if (safety = Some Memory_safety && check_memtrack)
            || (safety = Some Memory_cleanup && nonterminating)
         then Some memtrack_check
         else None);
      end_check = None; end_points = []; unreached; memtrack_roots; site = None; site_max = 0;
      guess_fn = None; nonterminating = nonterminating && ends; mt3_check = None;
      mt3_points = []; probe_fn = None; stop_fn = None; fns = Hashtbl.create 8;
      atexit_ids = Hashtbl.create 4; atexit_targets = []; atexit_table = None; run_atexit = None;
      exhausted_fn = None; heap_released = released_regions st regs file;
      inner_locals = inner_scope_locals file; scalar_cells = Hashtbl.create 4;
      overflow_marker = None; uninit_targets = []; uninit_elided = [];
      uninit_parameters = [];
      uninit_check = uninit = "check"; init_vars = Hashtbl.create 8;
      check_targets = Hashtbl.create 8; init_formals = Hashtbl.create 4;
      ret_init = Hashtbl.create 4; init_comps = Hashtbl.create 4; init_comptags = [];
      init_check = None; init_struct_checks = Hashtbl.create 4; init_ones = Hashtbl.create 4;
      uninit_marker = None; init_counters = Hashtbl.create 8; elided = Hashtbl.create 16;
      cur_sid = -1; init_jumped = Hashtbl.create 4;
      uninit_generators = []; bad_call }
  in
  (* every ordinary identifier of the program is taken: variables, functions,
     parameters, locals, typedef names and enumeration constants *)
  let note_name n = Hashtbl.replace ctx.names_used n () in
  let note vi = note_name vi.vname in
  List.iter
    (function
      | GVar (vi, _, _) | GVarDecl (vi, _) | GFunDecl (_, vi, _) -> note vi
      | GFun (fd, _) ->
          note fd.svar;
          List.iter note fd.sformals;
          List.iter note fd.slocals
      | GType (ti, _) -> note_name ti.tname
      | GEnumTag (ei, _) | GEnumTagDecl (ei, _) ->
          List.iter (fun it -> note_name it.einame) ei.eitems
      | _ -> ())
    file.globals;
  List.iter
    (function
      | GFun (fd, _) -> Hashtbl.replace ctx.orig_formals fd.svar.vid fd.sformals
      | _ -> ())
    file.globals;
  if ((safety = Some Memory_safety || safety = Some Memory_cleanup) && markers = Reach_error)
     || (uninit = "check" && safety = None)
  then rename_input_error_events ctx file;
  (* --uninit=check: the variables whose reads are checked are the targets
     whose address the input never takes (a variable made an object only to
     be a root of the end checks included) other than variable-length
     arrays, whose elements are a block of a region; the structure
     parameters that receive their argument's state are those some call
     passes a checked variable (or such a parameter) in, to a fixpoint; and
     a function returning a structure passes its result's state in a global
     when one of its returns returns a checked variable *)
  if uninit = "check" then begin
    let checked (t : UninitTargets.target) =
      t.vla = None
      && ((not (Hashtbl.mem st.address_taken t.var.vid)) || Hashtbl.mem memtrack_roots t.var.vid)
    in
    List.iter
      (fun (_, (t : UninitTargets.target)) ->
        if checked t then Hashtbl.replace ctx.check_targets t.var.vid ())
      uninit_targets;
    let is_checked v =
      Hashtbl.mem ctx.check_targets v.vid || Hashtbl.mem ctx.init_formals v.vid
    in
    let calls = ref [] and returns = ref [] in
    List.iter
      (function
        | GFun (fd, _) ->
            let v =
              object
                inherit Visitor.frama_c_inplace

                method! vinst i =
                  (match i with
                   | Call (_, Var f, args, _) | Local_init (_, ConsInit (f, args, _), _) ->
                       calls := (f, args) :: !calls
                   | _ -> ());
                  Cil.SkipChildren

                method! vstmt_aux st' =
                  (match st'.skind with
                   | Return (Some e, _) -> returns := (fd, e) :: !returns
                   | _ -> ());
                  Cil.DoChildren
              end
            in
            ignore (Visitor.visitFramacFunction v fd)
        | _ -> ())
      file.globals;
    let changed = ref true in
    while !changed do
      changed := false;
      List.iter
        (fun (f, args) ->
          match Hashtbl.find_opt ctx.orig_formals f.vid with
          | Some formals ->
              let rec go fs as_ =
                match (fs, as_) with
                | fv :: fs', a :: as' ->
                    (match (Ast_types.unroll_node fv.vtype, a.enode) with
                     | TComp ci, Lval (Var y, _)
                       when ci.cstruct && is_checked y
                            && (not (Hashtbl.mem ctx.init_formals fv.vid))
                            && not (Hashtbl.mem st.address_taken fv.vid) ->
                         Hashtbl.replace ctx.init_formals fv.vid ();
                         changed := true
                     | _ -> ());
                    go fs' as'
                | _ -> ()
              in
              go formals args
          | None -> ())
        !calls
    done;
    List.iter
      (fun (fd, e) ->
        match (Ast_types.unroll_node (Cil.getReturnType fd.svar.vtype), e.enode) with
        | TComp ci, Lval (Var y, _)
          when ci.cstruct && is_checked y && not (Hashtbl.mem ctx.ret_init fd.svar.vid) ->
            let g =
              Cil.makeGlobalVar (fresh_name ctx (fd.svar.vname ^ "__ret_init"))
                (init_type ctx (Cil.getReturnType fd.svar.vtype))
            in
            Hashtbl.replace ctx.roles g.vid "init";
            ctx.helpers <- GVar (g, { init = None }, loc0) :: ctx.helpers;
            Hashtbl.replace ctx.ret_init fd.svar.vid g
        | _ -> ())
      (List.rev !returns)
  end;
  if safety <> None then add_companion_fields ctx file;
  List.iter
    (fun (r : Regions.region) ->
      let info =
        match r.kind with
        | Regions.Typed sigma -> make_region ctx r ~byte:false sigma
        | Regions.Byte _ -> make_region ctx r ~byte:true Cil_const.ucharType
      in
      Hashtbl.add ctx.infos r.rid info)
    regs.list;
  (* --scalar-cells: the regions held in one scalar, made arbitrary where
     their block is allocated, as the region's array is at main's head *)
  if scalar_cells then
    List.iter
      (fun (r : Regions.region) ->
        match r.kind with
        | Regions.Typed sigma ->
            let c = Cil.makeGlobalVar (fresh_name ctx (Printf.sprintf "p2a_cell%d" r.rid)) (tr_type sigma) in
            Hashtbl.replace ctx.roles c.vid "generated";
            ctx.helpers <- GVar (c, { init = None }, loc0) :: ctx.helpers;
            Hashtbl.replace ctx.scalar_cells r.rid (c, arbitrary_call ctx c)
        | Regions.Byte _ -> ())
      (scalar_regions st regs file);
  (* the pointer locations, while the types still say which they are *)
  let pointer_loc ?func kind vi =
    if Ast_types.is_ptr vi.vtype && not (is_object ctx vi) then begin
      Hashtbl.replace ctx.roles vi.vid "index";
      let reg =
        Option.map
          (fun (r : Regions.region) -> r.rid)
          (Regions.find regs (PointsTo.pt st (PointsTo.var_node st vi)))
      in
      ctx.pointers <- (vi.vorig_name, func, kind, reg) :: ctx.pointers
    end
  in
  List.iter
    (function
      | GVar (vi, _, _) when not (Ast_info.is_string_literal vi) -> pointer_loc "global" vi
      | GFun (fd, _) ->
          let func = fd.svar.vname in
          List.iter (pointer_loc ~func "formal") fd.sformals;
          List.iter (pointer_loc ~func "local") fd.slocals;
          if Ast_types.is_ptr (Cil.getReturnType fd.svar.vtype) then
            ctx.pointers <-
              ( func, Some func, "result",
                Option.map
                  (fun (r : Regions.region) -> r.rid)
                  (Regions.find regs (PointsTo.pt st (PointsTo.ret_node st fd.svar))) )
              :: ctx.pointers
      | GCompTag (ci, _) ->
          Option.iter
            (List.iter (fun fi ->
                 if Ast_types.is_ptr fi.ftype then
                   ctx.pointers <- (ci.cname ^ "." ^ fi.fname, None, "field", None) :: ctx.pointers))
            ci.cfields
      | _ -> ())
    file.globals;
  ctx.pointers <- List.rev ctx.pointers;
  (* fixed indices of the static objects, in the order of the globals *)
  let statics = ref [] in
  List.iter
    (function
      | GVar (vi, ii, _) when is_object ctx vi ->
          let info = info_of_var ctx vi in
          Hashtbl.replace ctx.static_index vi.vid info.next_static;
          (* in the safety modes a block occupies at least one cell (see
             the allocator) *)
          let n = units ctx info vi.vtype in
          info.next_static <- info.next_static + (if safety = None then n else max 1 n);
          statics := (vi, ii.init) :: !statics
      | _ -> ())
    file.globals;
  let statics = List.rev !statics in
  (* safety: the globals that pass a pointer result's shadow, and the
     companions of the global pointers (with the shadows of their
     initialisers, which are constants) *)
  if safety <> None then begin
    List.iter
      (function
        | GFun (fd, _) when Ast_types.is_ptr (Cil.getReturnType fd.svar.vtype) ->
            let g suffix =
              let v = Cil.makeGlobalVar (fresh_name ctx (fd.svar.vname ^ suffix)) ity in
              Hashtbl.replace ctx.roles v.vid "shadow";
              ctx.helpers <- GVar (v, { init = None }, loc0) :: ctx.helpers;
              v
            in
            let rb = g "__ret_base" in
            let rl = g "__ret_len" in
            Hashtbl.replace ctx.ret_shadow fd.svar.vid (rb, rl)
        | _ -> ())
      file.globals;
    List.iter
      (function
        | (GVar (vi, _, _) | GVarDecl (vi, _))
          when (not (is_object ctx vi)) && (not (Ast_types.is_fun vi.vtype))
               && (not (Ast_info.is_string_literal vi))
               && not (Hashtbl.mem ctx.shadow_vars vi.vid) -> (
            match ptr_shape vi.vtype with
            | Some shape ->
                let g suffix = Cil.makeGlobalVar (fresh_name ctx (vi.vname ^ suffix)) shape in
                let vb = g "__base" and vl = g "__len" in
                Hashtbl.replace ctx.roles vb.vid "shadow";
                Hashtbl.replace ctx.roles vl.vid "shadow";
                Hashtbl.replace ctx.shadow_vars vi.vid (vb, vl);
                let init =
                  List.find_map
                    (function
                      | GVar (v', { init = Some (CInit i) }, _) when v' == vi -> Some i
                      | _ -> None)
                    file.globals
                in
                let ib, il =
                  match init with
                  | Some i ->
                      let b, l = shadow_init ctx vi.vtype i in
                      let rec fold = function
                        | SingleInit e -> SingleInit (Cil.constFold true e)
                        | CompoundInit (t, l) ->
                            CompoundInit (t, List.map (fun (o, i) -> (o, fold i)) l)
                      in
                      (Some (CInit (fold b)), Some (CInit (fold l)))
                  | None -> (None, None)
                in
                if ctx.pending <> [] then
                  not_implemented "a global pointer initialised by reading a region";
                ctx.helpers <-
                  GVar (vl, { init = il }, loc0) :: GVar (vb, { init = ib }, loc0) :: ctx.helpers
            | None -> ())
        | _ -> ())
      file.globals
  end;

  let main =
    List.find_map
      (function GFun (fd, _) when fd.svar.vname = "main" -> Some fd | _ -> None)
      file.globals
  in
  let main =
    match main with Some m -> m | None -> not_implemented "a program without main"
  in
  (* the end check, called at each end of the execution (see [rewrite_function]
     and [wrap_main]) *)
  if ends then begin
    ctx.end_check <-
      Some
        (Cil.emptyFunction
           (fresh_name ctx (if safety = Some Memory_safety then "p2a_memtrack" else "p2a_memcleanup")));
    if ctx.nonterminating then
      ctx.mt3_check <-
        (if safety = Some Memory_safety then ctx.end_check
         else Some (Cil.emptyFunction (fresh_name ctx "p2a_memtrack")))
  end;
  (* atexit: the registered functions, numbered, and the function that runs
     them at the ends that run them (exit and the return from main) *)
  List.iteri
    (fun k g -> Hashtbl.replace ctx.atexit_ids g.vid (k + 1))
    handlers;
  ctx.atexit_targets <- handlers;
  if handlers <> [] then begin
    let fn = int_array ctx "p2a_atexit_fn" "generated" in
    let n = Cil.makeGlobalVar (fresh_name ctx "p2a_atexit_n") ity in
    Hashtbl.replace ctx.roles n.vid "generated";
    ctx.helpers <- GVar (n, { init = None }, loc0) :: ctx.helpers;
    ctx.atexit_table <- Some (fn, n);
    ctx.run_atexit <- Some (Cil.emptyFunction (fresh_name ctx "p2a_run_atexit"))
  end;
  (* rewrite the bodies (types are still the original ones) *)
  List.iter (function GFun (fd, _) -> rewrite_function ctx fd | _ -> ()) file.globals;
  if uninit = "check" then begin
    ctx.uninit_parameters <-
      List.concat_map
        (function
          | GFun (fd, _) ->
              List.filter_map
                (fun v ->
                  if Hashtbl.mem ctx.init_formals v.vid then Some (v.vname, fd.svar.vname) else None)
                (Hashtbl.find ctx.orig_formals fd.svar.vid)
          | _ -> [])
        file.globals;
    ctx.uninit_targets <-
      List.map
        (fun (func, (t : UninitTargets.target)) ->
          let checked = Hashtbl.mem ctx.check_targets t.var.vid in
          { u_name = t.var.vorig_name; u_var = t.var.vname; u_func = func; u_loc = t.var.vdecl;
            u_leaves = (if t.vla <> None then None else Some (UninitTargets.leaves t.var.vtype));
            u_placed =
              (if not checked then []
               else if Hashtbl.mem ctx.init_jumped t.var.vid then
                 [ "block-entry"; "function-entry"; "jump-source" ]
               else [ "block-entry" ]);
            u_checked = Some checked })
        uninit_targets
  end;
  (* global initialisers of variables that are not objects *)
  List.iter
    (function
      | GVar (vi, ({ init = Some (CInit i) } as ii), _) when not (is_object ctx vi) ->
          let i' = if safety = None then tr_init ctx i else tr_init_safe ctx vi.vtype i in
          if ctx.pending <> [] then
            not_implemented "a global initialiser that reads a byte region";
          let rec fold = function
            | SingleInit e -> SingleInit (Cil.constFold true e)
            | CompoundInit (t, l) -> CompoundInit (t, List.map (fun (o, i) -> (o, fold i)) l)
          in
          ii.init <- Some (CInit (fold i'))
      | _ -> ())
    file.globals;
  Option.iter (fill_run_atexit ctx) ctx.run_atexit;
  (match (ctx.end_check, ctx.run_atexit) with
   | None, None -> main.sbody.bstmts <- static_init ctx main statics @ main.sbody.bstmts
   | check, run_atexit ->
       wrap_main ctx file main statics ~run_atexit check;
       Option.iter
         (fun check -> fill_end_check ~memtrack:(safety = Some Memory_safety) ctx file check)
         check;
       (match ctx.mt3_check with
        | Some c when safety = Some Memory_cleanup ->
            fill_end_check ~memtrack:true ~prop:Valid_memcleanup ctx file c
        | _ -> ());
       (* the site table holds the roots of the largest frame *)
       Option.iter
         (fun (sval, sbase, sreg, _) ->
           List.iter
             (fun v ->
               Cil.update_var_type v
                 (Cil_const.mk_tarray ity (Some (iconst (max 1 ctx.site_max)))))
             [ sval; sbase; sreg ])
         ctx.site);
  (* drop the declarations of the objects and of the front end's allocators *)
  file.globals <-
    List.filter
      (function
        | GVar (vi, _, _) | GVarDecl (vi, _) -> not (is_object ctx vi)
        | GFunDecl (_, vi, _) -> not (List.mem vi.vname [ "__fc_vla_alloc"; "__fc_vla_free" ])
        | _ -> true)
      file.globals;
  let rec drop_statics b =
    b.bstatics <- List.filter (fun v -> not (is_object ctx v)) b.bstatics;
    List.iter
      (fun s ->
        match s.skind with
        | Block b' -> drop_statics b'
        | If (_, b1, b2, _) -> drop_statics b1; drop_statics b2
        | Loop (_, b', _, _, _) | Switch (_, b', _, _) -> drop_statics b'
        | _ -> ())
      b.bstmts
  in
  List.iter (function GFun (fd, _) -> drop_statics fd.sbody | _ -> ()) file.globals;
  retype file;
  (* the generated globals go before the first function definition *)
  let generated =
    List.concat_map
      (fun (r : Regions.region) ->
        let info = Hashtbl.find ctx.infos r.rid in
        let free_init =
          { init = Some (CInit (SingleInit (iconst info.next_static))) }
        in
        let accessors =
          Hashtbl.fold (fun tag p acc -> (tag, p) :: acc) info.access []
          |> List.sort compare
          |> List.concat_map (fun (_, (ld, sf)) -> [ GFun (ld, loc0); GFun (sf, loc0) ])
        in
        [ GVar (info.arr, { init = None }, loc0);
          GVar (info.free, free_init, loc0) ]
        @ (match info.zero with Some z -> [ GVar (z, { init = None }, loc0) ] | None -> [])
        @ [ GFun (info.alloc, loc0) ]
        @ (match info.alloc0 with Some f -> [ GFun (f, loc0) ] | None -> [])
        @ accessors)
      regs.list
  in
  (* The generated variables and the prototypes of the generated functions go
     before the first function definition of the input; the definitions go at
     the end of the file, after every declaration of the input, so that a
     function of the input they call (the input's own _Exit) is declared. *)
  let generated = generated @ List.rev ctx.helpers in
  let vars, funs = List.partition (function GVar _ | GFunDecl _ -> true | _ -> false) generated in
  let prototypes =
    List.filter_map
      (function
        | GFun (fd, loc) ->
            Cil.unsafeSetFormalsDecl fd.svar fd.sformals;
            Some (GFunDecl (Cil.empty_funspec (), fd.svar, loc))
        | _ -> None)
      funs
  in
  let rec insert = function
    | (GFun _ as g) :: rest -> vars @ prototypes @ (g :: rest)
    | g :: rest -> g :: insert rest
    | [] -> vars @ prototypes
  in
  file.globals <- insert file.globals @ funs;
  (* the state structures of --uninit=check after the input's last type
     definition, where the front end, which reads every type definition
     first, puts them when it reads the output back *)
  if ctx.init_comptags <> [] then begin
    let is_type = function
      | GType _ | GCompTag _ | GCompTagDecl _ | GEnumTag _ | GEnumTagDecl _ -> true
      | _ -> false
    in
    let last =
      List.fold_left (fun (i, l) g -> (i + 1, if is_type g then i else l)) (0, -1) file.globals
      |> snd
    in
    file.globals <-
      List.concat
        (List.mapi
           (fun i g -> if i = last then g :: List.rev ctx.init_comptags else [ g ])
           file.globals);
    if last < 0 then file.globals <- List.rev ctx.init_comptags @ file.globals
  end;
  let generated_var v =
    if not (Hashtbl.mem ctx.roles v.vid) then Hashtbl.replace ctx.roles v.vid "generated"
  in
  List.iter
    (function
      | GVar (v, _, _) -> generated_var v
      | GFun (fd, _) ->
          generated_var fd.svar;
          List.iter generated_var (fd.sformals @ fd.slocals)
      | _ -> ())
    generated;
  ctx
