// Decision-variable switch for the solvers of the OCaml [minisat] binding.
//
// [Minisat::Solver::setDecisionVar] is an inline member of core/Solver.h, so
// the binding's compiled library does not export it; this stub compiles it
// against a copy of the headers of the same minisat (2.2.0, as shipped in
// the opam package minisat.0.6, MIT licence, see minisat_headers/LICENSE).
// The copy must match the version the binding was built from: the stub
// reads the solver object the binding allocated, so a different class
// layout would corrupt it.

#include <caml/memory.h>
#include <caml/mlvalues.h>

#include "core/Solver.h"

using namespace Minisat;

extern "C" {

// the binding keeps the [Solver *] as the first field of an abstract block
static inline Solver *bitframe_solver(value block) {
  return *((Solver **)Data_custom_val(block));
}

// whether variable [v] (the binding's [Minisat.Lit.to_int] of its
// literals) may be picked by the decision heuristic
CAMLprim value caml_bitframe_set_decision_var(value block, value v_var,
                                              value v_b) {
  bitframe_solver(block)->setDecisionVar(Int_val(v_var), Bool_val(v_b));
  return Val_unit;
}
}
