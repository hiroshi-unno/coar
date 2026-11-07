(* Access to LLVM IR beyond what the OCaml bindings provide, and the type
   predicates the rest of llvm2lts shares. *)

external called_function_type : Llvm.llvalue -> Llvm.lltype
  = "llvm2lts_called_function_type"

external allocated_type : Llvm.llvalue -> Llvm.lltype
  = "llvm2lts_allocated_type"

(* The type of a global variable's value, or a function's type; the global
   itself is a pointer. *)
external global_value_type : Llvm.llvalue -> Llvm.lltype
  = "llvm2lts_global_value_type"

external gep_source_element_type : Llvm.llvalue -> Llvm.lltype
  = "llvm2lts_gep_source_element_type"

external tail_call_kind_code : Llvm.llvalue -> int = "llvm2lts_tail_call_kind"
external attr_kind_code : Llvm.llattribute -> int = "llvm2lts_attr_kind"
external debug_line : Llvm.llvalue -> int = "llvm2lts_debug_line"
external is_atomic : Llvm.llvalue -> bool = "llvm2lts_is_atomic"
external attr_kind_for_name : string -> int = "llvm2lts_attr_kind_for_name"
external set_notail : Llvm.llvalue -> unit = "llvm2lts_set_notail"
external has_nsw : Llvm.llvalue -> bool = "llvm2lts_has_nsw"
external has_nuw : Llvm.llvalue -> bool = "llvm2lts_has_nuw"
external is_exact : Llvm.llvalue -> bool = "llvm2lts_is_exact"

(* The bindings' getters of these names allocate an array of 0 elements as a
   block of size 0 in the minor heap, which a minor collection corrupts the
   next block through (it writes a forwarding pointer into field 0); these
   build every array with caml_alloc, the empty one being the atom outside
   the heap.  Use them, never Llvm's, for every array that may be empty. *)
external params : Llvm.llvalue -> Llvm.llvalue array = "llvm2lts_params"
external param_types : Llvm.lltype -> Llvm.lltype array = "llvm2lts_param_types"

external struct_element_types : Llvm.lltype -> Llvm.lltype array
  = "llvm2lts_struct_element_types"

external get_mdnode_operands : Llvm.llvalue -> Llvm.llvalue array
  = "llvm2lts_mdnode_operands"

external basic_blocks : Llvm.llvalue -> Llvm.llbasicblock array
  = "llvm2lts_basic_blocks"

external indices : Llvm.llvalue -> int array = "llvm2lts_indices"

external function_attrs_at : Llvm.llvalue -> int -> Llvm.llattribute array
  = "llvm2lts_function_attrs"

external call_site_attrs_at : Llvm.llvalue -> int -> Llvm.llattribute array
  = "llvm2lts_call_site_attrs"

(* the attribute index the LLVM C API reads, as the bindings compute it *)
let attr_index : Llvm.AttrIndex.t -> int = function
  | Function -> -1
  | Return -> 0
  | Param n -> n + 1

let function_attrs fn index = function_attrs_at fn (attr_index index)
let call_site_attrs call index = call_site_attrs_at call (attr_index index)

type tail_call_kind = No_marker | Tail | Must_tail | No_tail

let tail_call_kind call =
  match tail_call_kind_code call with
  | 0 -> No_marker
  | 1 -> Tail
  | 2 -> Must_tail
  | _ -> No_tail

(* The enum and type attribute names of LLVM 19.1.7 (llvm/IR/Attributes.td),
   used to name an attribute in a message; the C API maps a name to its kind
   but not back. *)
let attribute_names =
  [ "allocalign"; "allocptr"; "alwaysinline"; "builtin"; "cold"; "convergent";
    "coro_only_destroy_when_complete"; "dead_on_unwind";
    "disable_sanitizer_instrumentation"; "fn_ret_thunk_extern"; "hot";
    "hybrid_patchable"; "immarg"; "inreg"; "inlinehint"; "jumptable";
    "minsize"; "mustprogress"; "naked"; "nest"; "noalias"; "nobuiltin";
    "nocallback"; "nocapture"; "nocf_check"; "noduplicate"; "nofree";
    "noimplicitfloat"; "noinline"; "nomerge"; "noprofile"; "norecurse";
    "noredzone"; "noreturn"; "nosanitize_bounds"; "nosanitize_coverage";
    "nosync"; "noundef"; "nounwind"; "nonlazybind"; "nonnull";
    "null_pointer_is_valid"; "optforfuzzing"; "optdebug"; "optnone";
    "optsize"; "presplitcoroutine"; "readnone"; "readonly"; "returned";
    "returns_twice"; "signext"; "safestack"; "sanitize_address";
    "sanitize_hwaddress"; "sanitize_memtag"; "sanitize_memory";
    "sanitize_numerical_stability"; "sanitize_thread"; "shadowcallstack";
    "skipprofile"; "speculatable"; "speculative_load_hardening"; "ssp";
    "sspreq"; "sspstrong"; "strictfp"; "swiftasync"; "swifterror";
    "swiftself"; "willreturn"; "writable"; "writeonly"; "zeroext"; "align";
    "alignstack"; "allockind"; "allocsize"; "dereferenceable";
    "dereferenceable_or_null"; "memory"; "nofpclass"; "uwtable";
    "vscale_range"; "range"; "byref"; "byval"; "elementtype"; "inalloca";
    "preallocated"; "sret" ]

let attribute_name =
  let table = Hashtbl.create 128 in
  List.iter
    (fun name ->
      let kind = attr_kind_for_name name in
      if kind <> 0 then Hashtbl.replace table kind name)
    attribute_names;
  fun kind ->
    match Hashtbl.find_opt table kind with
    | Some name -> name
    | None -> Printf.sprintf "attribute kind %d" kind

(* The kinds of the named attributes, to test an attribute against. *)
let attribute_kinds names = List.map attr_kind_for_name names

let is_integer ty =
  match Llvm.classify_type ty with Integer -> true | _ -> false

let is_pointer ty =
  match Llvm.classify_type ty with Pointer -> true | _ -> false

let is_union ty =
  match Llvm.struct_name ty with
  | Some name -> String.starts_with ~prefix:"union." name
  | None -> false

(* A type an object in memory may have: an integer, or an array or a struct
   (not a union) built from such types.  Each leaf field of a struct is read
   as a variable of its own, so a struct whose type is opaque, or one that is
   a union, is not one. *)
let rec is_memory_type ty =
  match Llvm.classify_type ty with
  | Integer -> true
  | Array -> is_memory_type (Llvm.element_type ty)
  | Struct ->
      (not (is_union ty))
      && (not (Llvm.is_opaque ty))
      && Array.for_all is_memory_type (struct_element_types ty)
  | _ -> false

let callee call = Llvm.operand call (Llvm.num_operands call - 1)

(* The slot an [llvm.dbg.declare] describes: its first operand is the
   metadata wrapping the slot, which the C API reads as a one-operand node. *)
let declared_slot declare =
  match get_mdnode_operands (Llvm.operand declare 0) with
  | [| slot |] -> Some slot
  | _ -> None

(* The name of an instruction's opcode as the IR writes it, for messages. *)
let opcode_name (op : Llvm.Opcode.t) =
  match op with
  | Ret -> "ret" | Br -> "br" | Switch -> "switch" | IndirectBr -> "indirectbr"
  | Invoke -> "invoke" | Unreachable -> "unreachable" | Add -> "add"
  | FAdd -> "fadd" | Sub -> "sub" | FSub -> "fsub" | Mul -> "mul"
  | FMul -> "fmul" | UDiv -> "udiv" | SDiv -> "sdiv" | FDiv -> "fdiv"
  | URem -> "urem" | SRem -> "srem" | FRem -> "frem" | Shl -> "shl"
  | LShr -> "lshr" | AShr -> "ashr" | And -> "and" | Or -> "or" | Xor -> "xor"
  | Alloca -> "alloca" | Load -> "load" | Store -> "store"
  | GetElementPtr -> "getelementptr" | Trunc -> "trunc" | ZExt -> "zext"
  | SExt -> "sext" | FPToUI -> "fptoui" | FPToSI -> "fptosi"
  | UIToFP -> "uitofp" | SIToFP -> "sitofp" | FPTrunc -> "fptrunc"
  | FPExt -> "fpext" | PtrToInt -> "ptrtoint" | IntToPtr -> "inttoptr"
  | BitCast -> "bitcast" | ICmp -> "icmp" | FCmp -> "fcmp" | PHI -> "phi"
  | Call -> "call" | Select -> "select" | VAArg -> "va_arg"
  | ExtractElement -> "extractelement" | InsertElement -> "insertelement"
  | ShuffleVector -> "shufflevector" | ExtractValue -> "extractvalue"
  | InsertValue -> "insertvalue" | Fence -> "fence"
  | AtomicCmpXchg -> "cmpxchg" | AtomicRMW -> "atomicrmw" | Resume -> "resume"
  | LandingPad -> "landingpad" | AddrSpaceCast -> "addrspacecast"
  | CleanupRet -> "cleanupret" | CatchRet -> "catchret"
  | CatchPad -> "catchpad" | CleanupPad -> "cleanuppad"
  | CatchSwitch -> "catchswitch" | FNeg -> "fneg" | CallBr -> "callbr"
  | Freeze -> "freeze" | Invalid | Invalid2 | UserOp1 | UserOp2 -> "?"

(* For a debug intrinsic describing a variable, the position of the
   parameter it is (from 1), or 0 when it is not a parameter. *)
external declared_arg : Llvm.llvalue -> int = "llvm2lts_declared_arg"
