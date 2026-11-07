(* Z3 calls that can run for a long time, with the OCaml runtime lock
   released while Z3 runs.  Each function is the bindings' function of the
   same name -- the same Z3 call on the same arguments, the same answer and
   the same [Z3.Error] -- except that other OCaml threads run meanwhile.

   Why: the bindings release the lock around [Z3.Solver.check] and
   [Z3.Expr.simplify] only.  While any other call runs, no other thread runs
   OCaml code and no OCaml signal handler runs, and other domains stall at
   their next stop-the-world collection.  A run stopped by SIGTERM at its
   limit (the phase account's watcher thread handles it) then ended only when
   the call in flight returned: a Spacer query budgeted at 256 s ended more
   than 200 s after a 300 s limit, and one quantifier-elimination tactic held
   a SIGTERM sent at 30 s until 176 s.  With the lock released the watcher
   reports and exits within its polling interval.  A one-shot alarm
   ([Common.Timer]) is unchanged: its handler raises only in the thread that
   armed it, which is inside Z3 until the call returns, as during
   [Z3.Solver.check].

   Precondition of every function: no callback is registered on the object
   (Z3 must call no OCaml code during the call), and no other thread uses the
   object's context while the call runs.  The C side restates the bindings'
   custom-block layout ([z3Released_stubs.c], one place); the property test
   that compares each function with the bindings' guards it. *)

external fixedpoint_query_raw : Z3.Fixedpoint.fixedpoint -> Z3.Expr.expr -> int
  = "coar_z3_fixedpoint_query_released"

external fixedpoint_query_relations_raw :
  Z3.Fixedpoint.fixedpoint -> Z3.FuncDecl.func_decl list -> int
  = "coar_z3_fixedpoint_query_relations_released"

external optimize_check_raw : Z3.Optimize.optimize -> int
  = "coar_z3_optimize_check_released"

external tactic_apply_raw :
  Z3.Tactic.tactic ->
  Z3.Goal.goal ->
  Z3.Params.params option ->
  Z3.Tactic.ApplyResult.apply_result ->
  Z3.Tactic.ApplyResult.apply_result = "coar_z3_tactic_apply_released"

(* the bindings' own stubs, generated for every object type: a goal's
   context, and a fresh apply_result block of a context holding NULL (not
   exported by [Z3native]) *)
external context_of_goal : Z3.Goal.goal -> Z3.context = "n_context_of_goal"

external mk_null_apply_result : Z3.context -> Z3.Tactic.ApplyResult.apply_result
  = "n_mk_null_apply_result"

(* the bindings' mapping of a [Z3_lbool] *)
let status_of_lbool = function
  | 1 -> Z3.Solver.SATISFIABLE
  | -1 -> Z3.Solver.UNSATISFIABLE
  | _ -> Z3.Solver.UNKNOWN

(* [Z3.Fixedpoint.query] *)
let fixedpoint_query fp q = status_of_lbool (fixedpoint_query_raw fp q)

(* [Z3.Fixedpoint.query_r] *)
let fixedpoint_query_r fp rels =
  status_of_lbool (fixedpoint_query_relations_raw fp rels)

(* [Z3.Optimize.check] *)
let optimize_check opt = status_of_lbool (optimize_check_raw opt)

(* [Z3.Tactic.apply] *)
let tactic_apply t g p =
  tactic_apply_raw t g p (mk_null_apply_result (context_of_goal g))
