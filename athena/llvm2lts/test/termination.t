Translation for the termination property.  There is no ERROR location:
reach_error, abort, exit and __assert_fail end the execution, as returning
from main does (a move to `end`, which has no outgoing transition), and
__VERIFIER_assume(0) loops forever (a move to `diverge`, which loops).  The
verdicts are checked with CoAR by script/llvm2lts/check_verdicts.sh.

  $ llvm2lts --property termination termination/assume_false.ll
  START: start;
  TYPE v2: bv(32);
  TYPE v3: bv(1);
  TYPE v5: bv(32);
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  assume(v2 > 0);
  v3 := 1;
  TO: b1_4;
  
  FROM: b1;
  v2 := nondet();
  assume(!(v2 > 0));
  v3 := 0;
  TO: b1_4;
  
  FROM: b1_4;
  v5 := zero_extend(1, 32, v3);
  assume(!(v5 != 0));
  TO: diverge;
  
  FROM: b1_4;
  v5 := zero_extend(1, 32, v3);
  assume(v5 != 0);
  TO: end;
  
  FROM: diverge;
  TO: diverge;

reach_error ends the execution instead of moving to ERROR:

  $ llvm2lts --property termination termination/reach_error_true.ll | grep -c ERROR
  0
  [1]
  $ llvm2lts --property termination termination/reach_error_true.ll | grep -B3 'TO: end;' | grep -c 'FROM:'
  2

__VERIFIER_error, the error event's name in older tasks, is read as
reach_error: it ends the execution too:

  $ llvm2lts --property termination termination/verifier_error_true.ll | grep -c ERROR
  0
  [1]
  $ llvm2lts --property termination termination/verifier_error_true.ll | grep -B3 'TO: end;' | grep -c 'FROM:'
  2

Every input translates in both modes:

  $ for f in termination/*.ll; do for m in bv int; do llvm2lts --property termination --mode $m $f > /dev/null 2>&1 || echo "$f $m"; done; done

--hoist=yes reads an array cell no transition of a loop writes once, on the
transition into the loop, rather than in every iteration:

  $ llvm2lts --property termination --mode int termination/hoist_true.ll | grep -c 'select_array'
  2
  $ llvm2lts --property termination --mode int --hoist=yes termination/hoist_true.ll | grep 'hoisted'
  hoisted1 := select_array(g_bound, 1);
  v5 := hoisted1;

