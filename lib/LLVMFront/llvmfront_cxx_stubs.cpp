// Getters that need LLVM's C++ API (the C API has no counterpart).  Values
// cross the boundary in the OCaml bindings' encoding, as in llvmfront_stubs.c.

#include <llvm-c/Core.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/BinaryFormat/Dwarf.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Metadata.h>

extern "C" {
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
void *from_val(value v);
value to_val(void *ptr);
value llvmfront_declared_arg(value call);
value llvmfront_dbg_variable(value call);
value llvmfront_dbg_value_operand(value call);
value llvmfront_global_dbg_variable(value global);
value llvmfront_loop_start(value term);
}

static llvm::Value *unwrap_value(value v) {
  return llvm::unwrap(static_cast<LLVMValueRef>(from_val(v)));
}

// llvalue (a call) -> int: for a debug intrinsic describing a variable, the
// position of the parameter the variable is (1 for the first), or 0 when it
// is not a parameter; 0 for any other call.
value llvmfront_declared_arg(value call) {
  llvm::Value *v = llvm::unwrap(static_cast<LLVMValueRef>(from_val(call)));
  if (auto *d = llvm::dyn_cast<llvm::DbgVariableIntrinsic>(v))
    return Val_int(d->getVariable()->getArg());
  return Val_int(0);
}

// How a C type reads as an integer, after typedefs and qualifiers: 0 signed,
// 1 unsigned, 2 _Bool, -1 not an integer type (a pointer, an enumeration, a
// struct, a floating type); [bits] is then its width.
static int int_kind(llvm::DIType *t, uint64_t *bits) {
  while (auto *d = llvm::dyn_cast_or_null<llvm::DIDerivedType>(t)) {
    unsigned tag = d->getTag();
    if (tag != llvm::dwarf::DW_TAG_typedef && tag != llvm::dwarf::DW_TAG_const_type &&
        tag != llvm::dwarf::DW_TAG_volatile_type)
      return -1;
    t = d->getBaseType();
  }
  auto *b = llvm::dyn_cast_or_null<llvm::DIBasicType>(t);
  if (!b)
    return -1;
  *bits = b->getSizeInBits();
  switch (b->getEncoding()) {
  case llvm::dwarf::DW_ATE_signed:
  case llvm::dwarf::DW_ATE_signed_char:
    return 0;
  case llvm::dwarf::DW_ATE_unsigned:
  case llvm::dwarf::DW_ATE_unsigned_char:
    return 1;
  case llvm::dwarf::DW_ATE_boolean:
    return 2;
  default:
    return -1;
  }
}

// Some (name, kind, bits, plain) for a variable, kind and bits as int_kind
// gives them, plain saying the location expression is empty (the value
// described is the operand itself, not computed from it).
static value variable_info(llvm::DIVariable *var, bool plain) {
  CAMLparam0();
  CAMLlocal2(name, tuple);
  uint64_t bits = 0;
  int kind = int_kind(var->getType(), &bits);
  name = caml_copy_string(var->getName().str().c_str());
  tuple = caml_alloc_tuple(4);
  Store_field(tuple, 0, name);
  Store_field(tuple, 1, Val_int(kind));
  Store_field(tuple, 2, Val_int(static_cast<long>(bits)));
  Store_field(tuple, 3, Val_bool(plain));
  CAMLreturn(caml_alloc_some(tuple));
}

// llvalue (a call) -> (string * int * int * bool) option: for a debug
// intrinsic describing a variable, the variable as variable_info gives it;
// None for any other call.
value llvmfront_dbg_variable(value call) {
  CAMLparam1(call);
  if (auto *d = llvm::dyn_cast<llvm::DbgVariableIntrinsic>(unwrap_value(call))) {
    bool plain = !d->hasArgList() && d->getExpression()->getNumElements() == 0;
    CAMLreturn(variable_info(d->getVariable(), plain));
  }
  CAMLreturn(Val_none);
}

// llvalue (a call) -> llvalue option: for an llvm.dbg.value with one
// location operand that is not a kill location, that operand (the value the
// variable holds from the call on); None otherwise.
value llvmfront_dbg_value_operand(value call) {
  CAMLparam1(call);
  if (auto *d = llvm::dyn_cast<llvm::DbgValueInst>(unwrap_value(call)))
    if (!d->hasArgList() && !d->isKillLocation())
      if (llvm::Value *v = d->getValue(0))
        CAMLreturn(caml_alloc_some(to_val(llvm::wrap(v))));
  CAMLreturn(Val_none);
}

// llvalue (a global variable) -> (string * int * int * bool) option: the C
// variable its debug information describes, as variable_info gives it, when
// there is exactly one; None otherwise.
value llvmfront_global_dbg_variable(value global) {
  CAMLparam1(global);
  if (auto *g = llvm::dyn_cast<llvm::GlobalVariable>(unwrap_value(global))) {
    llvm::SmallVector<llvm::DIGlobalVariableExpression *, 1> gvs;
    g->getDebugInfo(gvs);
    if (gvs.size() == 1) {
      llvm::DIExpression *e = gvs[0]->getExpression();
      CAMLreturn(variable_info(gvs[0]->getVariable(), e == nullptr || e->getNumElements() == 0));
    }
  }
  CAMLreturn(Val_none);
}

// llvalue (a terminator) -> (int * int) option: the line and column of the
// loop's start that its llvm.loop metadata carries (clang -g attaches it to
// every branch back to a loop's header and writes the loop statement's first
// character there), None when it carries none.
value llvmfront_loop_start(value term) {
  CAMLparam1(term);
  CAMLlocal1(pair);
  if (auto *i = llvm::dyn_cast<llvm::Instruction>(unwrap_value(term)))
    if (llvm::MDNode *loop = i->getMetadata(llvm::LLVMContext::MD_loop))
      for (unsigned k = 1; k < loop->getNumOperands(); ++k)
        if (auto *loc = llvm::dyn_cast_or_null<llvm::DILocation>(loop->getOperand(k).get())) {
          pair = caml_alloc_tuple(2);
          Store_field(pair, 0, Val_int(loc->getLine()));
          Store_field(pair, 1, Val_int(loc->getColumn()));
          CAMLreturn(caml_alloc_some(pair));
        }
  CAMLreturn(Val_none);
}
