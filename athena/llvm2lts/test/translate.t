Translation of main into T2 for the unreach-call property.  The verdicts
CoAR gives on these inputs are checked by script/llvm2lts/check_verdicts.sh
(it needs CoAR); here the output itself is checked.

A comparison used as a value becomes two transitions; the call to
reach_error becomes a move to the ERROR location.  BV mode declares every
variable's width:

  $ llvm2lts translate/cmpvalue_false.ll
  START: start;
  TYPE v2: bv(32);
  TYPE v3: bv(1);
  TYPE v5: bv(32);
  TYPE v6: bv(1);
  TYPE v8: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  assume(v2 == 7);
  v3 := 1;
  TO: b1_4;
  
  FROM: b1;
  v2 := nondet();
  assume(!(v2 == 7));
  v3 := 0;
  TO: b1_4;
  
  FROM: b1_4;
  v5 := zero_extend(1, 32, v3);
  assume(v5 == 0);
  v6 := 1;
  TO: b1_4_7;
  
  FROM: b1_4;
  v5 := zero_extend(1, 32, v3);
  assume(!(v5 == 0));
  v6 := 0;
  TO: b1_4_7;
  
  FROM: b1_4_7;
  v8 := zero_extend(1, 32, v6);
  assume(v6 != 0);
  TO: b9;
  
  FROM: b1_4_7;
  v8 := zero_extend(1, 32, v6);
  assume(!(v6 != 0));
  TO: b10;
  
  FROM: b10;
  TO: error;
  
  FROM: b9;
  TO: end;

Int mode writes no widths, and its nondet has the range of the C type:

  $ llvm2lts --mode int translate/cmpvalue_false.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet_int();
  assume(v2 == 7);
  v3 := 1;
  TO: b1_4;
  
  FROM: b1;
  v2 := nondet_int();
  assume(!(v2 == 7));
  v3 := 0;
  TO: b1_4;
  
  FROM: b1_4;
  v5 := v3;
  assume(v5 == 0);
  v6 := 1;
  TO: b1_4_7;
  
  FROM: b1_4;
  v5 := v3;
  assume(!(v5 == 0));
  v6 := 0;
  TO: b1_4_7;
  
  FROM: b1_4_7;
  v8 := v6;
  assume(v6 != 0);
  TO: b9;
  
  FROM: b1_4_7;
  v8 := v6;
  assume(!(v6 != 0));
  TO: b10;
  
  FROM: b10;
  TO: error;
  
  FROM: b9;
  TO: end;

Every input translates in both modes, except a bitwise operation in Int
mode:

  $ for f in translate/*.ll; do for m in bv int; do llvm2lts --mode $m $f > /dev/null 2>&1 || echo "$f $m"; done; done
  translate/bitops64_true.ll int
  translate/bitops_false.ll int
  translate/bitops_true.ll int
  translate/bitwise.ll int
  $ llvm2lts --mode int translate/bitwise.ll > /dev/null
  UNKNOWN: main, line 2: a bitwise operation in Int mode
  [1]

The bit-manipulation intrinsics in BV mode: ctlz counts the bits left after
the highest set bit is spread to every lower bit; with its flag true a zero
argument gives poison, so the path stops there (the assume before it):

  $ llvm2lts translate/bitops_false.ll | grep -m1 -B1 -A6 'lshr(v2, 1)'
  assume(v2 != 0);
  t6 := or(v2, lshr(v2, 1));
  t7 := or(t6, lshr(t6, 2));
  t8 := or(t7, lshr(t7, 4));
  t9 := or(t8, lshr(t8, 8));
  t10 := or(t9, lshr(t9, 16));
  v5 := (32 - (((((((((((((((((((((((((((((((zero_extend(1, 32, extract(0, 0, t10)) + zero_extend(1, 32, extract(1, 1, t10))) + zero_extend(1, 32, extract(2, 2, t10))) + zero_extend(1, 32, extract(3, 3, t10))) + zero_extend(1, 32, extract(4, 4, t10))) + zero_extend(1, 32, extract(5, 5, t10))) + zero_extend(1, 32, extract(6, 6, t10))) + zero_extend(1, 32, extract(7, 7, t10))) + zero_extend(1, 32, extract(8, 8, t10))) + zero_extend(1, 32, extract(9, 9, t10))) + zero_extend(1, 32, extract(10, 10, t10))) + zero_extend(1, 32, extract(11, 11, t10))) + zero_extend(1, 32, extract(12, 12, t10))) + zero_extend(1, 32, extract(13, 13, t10))) + zero_extend(1, 32, extract(14, 14, t10))) + zero_extend(1, 32, extract(15, 15, t10))) + zero_extend(1, 32, extract(16, 16, t10))) + zero_extend(1, 32, extract(17, 17, t10))) + zero_extend(1, 32, extract(18, 18, t10))) + zero_extend(1, 32, extract(19, 19, t10))) + zero_extend(1, 32, extract(20, 20, t10))) + zero_extend(1, 32, extract(21, 21, t10))) + zero_extend(1, 32, extract(22, 22, t10))) + zero_extend(1, 32, extract(23, 23, t10))) + zero_extend(1, 32, extract(24, 24, t10))) + zero_extend(1, 32, extract(25, 25, t10))) + zero_extend(1, 32, extract(26, 26, t10))) + zero_extend(1, 32, extract(27, 27, t10))) + zero_extend(1, 32, extract(28, 28, t10))) + zero_extend(1, 32, extract(29, 29, t10))) + zero_extend(1, 32, extract(30, 30, t10))) + zero_extend(1, 32, extract(31, 31, t10))));
  assume(v5 != 5);

In Int mode they are not translated, like every bitwise operation:

  $ llvm2lts --mode int translate/bitops_false.ll > /dev/null
  UNKNOWN: main, line 9: a bit-manipulation intrinsic in Int mode
  [1]

Constants of any size are written exactly: T2 literals have no size limit.
BV mode compares bit patterns (`ule (-1)`); Int mode reads the unsigned
comparison's i64 constant -1 as 2^64 - 1:

  $ llvm2lts translate/bigconst_true.ll | grep -E 'assume.*(ule|9223372036854775807|9223372036854775808)'
  assume(v2 ule (-1));
  assume(!(v2 ule (-1)));
  assume(v3 <= 9223372036854775807);
  assume(!(v3 <= 9223372036854775807));
  assume(v3 >= (-9223372036854775808));
  assume(!(v3 >= (-9223372036854775808)));
  $ llvm2lts --mode int translate/bigconst_true.ll | grep -E 'assume.*(18446744073709551615|9223372036854775807|9223372036854775808)'
  assume(v2 <= 18446744073709551615);
  assume(!(v2 <= 18446744073709551615));
  assume(v3 <= 9223372036854775807);
  assume(!(v3 <= 9223372036854775807));
  assume(v3 >= (-9223372036854775808));
  assume(!(v3 >= (-9223372036854775808)));

__VERIFIER_error, the error event's name in older tasks, moves to ERROR as
reach_error does:

  $ llvm2lts translate/verifier_error_false.ll | grep -c 'TO: error;'
  1

The input's own error event that Ptr2Arr renames (__p2a_input_reach_error,
declared only) ends the execution and is no error:

  $ llvm2lts translate/input_error_true.ll | grep -c 'TO: error;'
  0
  [1]
