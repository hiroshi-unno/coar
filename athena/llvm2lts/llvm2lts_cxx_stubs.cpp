// Getters that need LLVM's C++ API (the C API has no counterpart).  Values
// cross the boundary in the OCaml bindings' encoding, as in llvm2lts_stubs.c.

#include <llvm-c/Core.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/IntrinsicInst.h>

extern "C" {
#include <caml/mlvalues.h>
void *from_val(value v);
value llvm2lts_declared_arg(value call);
}

// llvalue (a call) -> int: for a debug intrinsic describing a variable, the
// position of the parameter the variable is (1 for the first), or 0 when it
// is not a parameter; 0 for any other call.
value llvm2lts_declared_arg(value call) {
  llvm::Value *v = llvm::unwrap(static_cast<LLVMValueRef>(from_val(call)));
  if (auto *d = llvm::dyn_cast<llvm::DbgVariableIntrinsic>(v))
    return Val_int(d->getVariable()->getArg());
  return Val_int(0);
}
