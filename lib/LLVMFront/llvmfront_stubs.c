/* Getters the LLVM 19 OCaml bindings do not expose, written against the
   LLVM C API.  Values cross the boundary in the bindings' own encoding: an
   LLVM pointer with its low bit set, so that OCaml sees an integer
   (to_val/from_val, defined in the bindings' library). */

#include <llvm-c/Core.h>

#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

value to_val(void *ptr);
void *from_val(value v);

#define Value_val(v) ((LLVMValueRef)from_val(v))
#define Attribute_val(v) ((LLVMAttributeRef)from_val(v))
#define Type_val(v) ((LLVMTypeRef)from_val(v))

/* llvalue (a call) -> lltype: the function type the call was written with,
   which may differ from the callee's own type. */
value llvmfront_called_function_type(value call) {
  return to_val(LLVMGetCalledFunctionType(Value_val(call)));
}

/* llvalue (an alloca) -> lltype */
value llvmfront_allocated_type(value alloca) {
  return to_val(LLVMGetAllocatedType(Value_val(alloca)));
}

/* llvalue (a global variable or function) -> lltype */
value llvmfront_global_value_type(value global) {
  return to_val(LLVMGlobalGetValueType(Value_val(global)));
}

/* llvalue (a getelementptr instruction or constant expression) -> lltype */
value llvmfront_gep_source_element_type(value gep) {
  return to_val(LLVMGetGEPSourceElementType(Value_val(gep)));
}

/* llvalue (a call) -> int: 0 none, 1 tail, 2 musttail, 3 notail. */
value llvmfront_tail_call_kind(value call) {
  return Val_int(LLVMGetTailCallKind(Value_val(call)));
}

/* llattribute -> int: the attribute's kind, or -1 for a string attribute.
   Unlike the bindings' repr_of_attr, this also answers for type attributes
   such as byval(<ty>), on which repr_of_attr fails. */
value llvmfront_attr_kind(value attr) {
  LLVMAttributeRef a = Attribute_val(attr);
  if (LLVMIsStringAttribute(a))
    return Val_int(-1);
  return Val_int(LLVMGetEnumAttributeKind(a));
}

/* llvalue (an instruction) -> int: the line of its debug location, 0 when it
   has none. */
value llvmfront_debug_line(value instr) {
  return Val_int(LLVMGetDebugLocLine(Value_val(instr)));
}

/* llvalue (a load or store) -> bool: whether it is atomic. */
value llvmfront_is_atomic(value access) {
  return Val_bool(LLVMGetOrdering(Value_val(access)) != LLVMAtomicOrderingNotAtomic);
}

/* string -> int: the kind of the enum or type attribute with this name, 0 if
   LLVM has none by that name. */
value llvmfront_attr_kind_for_name(value name) {
  return Val_int(
      LLVMGetEnumAttributeKindForName(String_val(name), caml_string_length(name)));
}

/* llvalue (a call) -> unit: marks it notail, which keeps tail-call
   elimination from turning it into a jump (clearing the tail marker is not
   enough: the pass sets it again itself). */
value llvmfront_set_notail(value call) {
  LLVMSetTailCallKind(Value_val(call), LLVMTailCallKindNoTail);
  return Val_unit;
}

/* llvalue (an add, sub, mul or shl) -> bool */
value llvmfront_has_nsw(value instr) {
  return Val_bool(LLVMGetNSW(Value_val(instr)));
}

/* llvalue (an add, sub, mul or shl) -> bool */
value llvmfront_has_nuw(value instr) {
  return Val_bool(LLVMGetNUW(Value_val(instr)));
}

/* llvalue (a udiv, sdiv, lshr or ashr) -> bool */
value llvmfront_is_exact(value instr) {
  return Val_bool(LLVMGetExact(Value_val(instr)));
}

/* llattribute (a type attribute such as byval(<ty>) or sret(<ty>)) ->
   lltype: the type it carries. */
value llvmfront_type_attr_value(value attr) {
  return to_val(LLVMGetTypeAttributeValue(Attribute_val(attr)));
}

/* The arrays below replace the bindings' getters of the same names.  The
   bindings allocate an array of N elements with caml_alloc_small(N, 0) even
   when N is 0, and a block of size 0 in the minor heap is not a valid OCaml
   value: when a minor collection promotes it, the collector writes the
   forwarding pointer into its field 0, which is the next block's header, so
   a later read of that block finds garbage (an array of attributes read as
   the integer 2683, a segmentation fault).  Whether it bites depends on when
   a minor collection happens, so one program crashed on every run and another
   only rarely.  caml_alloc answers the empty array, an atom outside the
   heap, for 0 elements and initialises every field before anything can
   collect.  Each getter fills a C buffer first, since the elements are LLVM
   pointers that become OCaml values only once tagged (to_val). */

/* An OCaml array of the N pointers in BUF, each tagged by to_val; BUF is
   freed. */
static value llvmfront_tagged_array(void **buf, unsigned n) {
  value a = caml_alloc(n, 0);
  for (unsigned i = 0; i < n; ++i)
    Field(a, i) = to_val(buf[i]);
  caml_stat_free(buf);
  return a;
}

static void **llvmfront_buffer(unsigned n) {
  return caml_stat_alloc((n == 0 ? 1 : n) * sizeof(void *));
}

/* llvalue (a function) -> llvalue array */
value llvmfront_params(value fn) {
  unsigned n = LLVMCountParams(Value_val(fn));
  void **buf = llvmfront_buffer(n);
  LLVMGetParams(Value_val(fn), (LLVMValueRef *)buf);
  return llvmfront_tagged_array(buf, n);
}

/* lltype (a function type) -> lltype array */
value llvmfront_param_types(value ty) {
  unsigned n = LLVMCountParamTypes(Type_val(ty));
  void **buf = llvmfront_buffer(n);
  LLVMGetParamTypes(Type_val(ty), (LLVMTypeRef *)buf);
  return llvmfront_tagged_array(buf, n);
}

/* lltype (a struct type) -> lltype array */
value llvmfront_struct_element_types(value ty) {
  unsigned n = LLVMCountStructElementTypes(Type_val(ty));
  void **buf = llvmfront_buffer(n);
  LLVMGetStructElementTypes(Type_val(ty), (LLVMTypeRef *)buf);
  return llvmfront_tagged_array(buf, n);
}

/* llvalue (a metadata node) -> llvalue array */
value llvmfront_mdnode_operands(value node) {
  unsigned n = LLVMGetMDNodeNumOperands(Value_val(node));
  void **buf = llvmfront_buffer(n);
  LLVMGetMDNodeOperands(Value_val(node), (LLVMValueRef *)buf);
  return llvmfront_tagged_array(buf, n);
}

/* llvalue (a function) -> llbasicblock array */
value llvmfront_basic_blocks(value fn) {
  unsigned n = LLVMCountBasicBlocks(Value_val(fn));
  void **buf = llvmfront_buffer(n);
  LLVMGetBasicBlocks(Value_val(fn), (LLVMBasicBlockRef *)buf);
  return llvmfront_tagged_array(buf, n);
}

/* llvalue (a function) -> int (the bindings' attribute index) ->
   llattribute array */
value llvmfront_function_attrs(value fn, value index) {
  unsigned n = LLVMGetAttributeCountAtIndex(Value_val(fn), Int_val(index));
  void **buf = llvmfront_buffer(n);
  LLVMGetAttributesAtIndex(Value_val(fn), Int_val(index), (LLVMAttributeRef *)buf);
  return llvmfront_tagged_array(buf, n);
}

/* llvalue (a call) -> int (the bindings' attribute index) ->
   llattribute array */
value llvmfront_call_site_attrs(value call, value index) {
  unsigned n = LLVMGetCallSiteAttributeCount(Value_val(call), Int_val(index));
  void **buf = llvmfront_buffer(n);
  LLVMGetCallSiteAttributes(Value_val(call), Int_val(index), (LLVMAttributeRef *)buf);
  return llvmfront_tagged_array(buf, n);
}

/* llvalue (an extractvalue or insertvalue) -> int array */
value llvmfront_indices(value instr) {
  unsigned n = LLVMGetNumIndices(Value_val(instr));
  const unsigned *indices = LLVMGetIndices(Value_val(instr));
  value a = caml_alloc(n, 0);
  for (unsigned i = 0; i < n; ++i)
    Field(a, i) = Val_int(indices[i]);
  return a;
}
