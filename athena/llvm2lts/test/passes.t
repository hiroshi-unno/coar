The passes between reading and checking: the marker pre-pass, mem2reg,
tail-call elimination narrowed to `return f(x);`, the check that no
recursion is left, and inlining.

Tail recursion of the form `return f(n - 1);` becomes a loop:

  $ llvm2lts passes/tailrec.ll
  START: start;
  TYPE v2: bv(32);
  TYPE v4: bv(32);
  TYPE v7: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  v4 := v2;
  TO: b3;
  
  FROM: b3;
  assume(v4 <= 0);
  TO: b5;
  
  FROM: b3;
  assume(!(v4 <= 0));
  TO: b6;
  
  FROM: b6;
  assume((extract(32, 31, (sign_extend(32, 33, v4) - sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v4) - sign_extend(32, 33, 1))) == 3));
  v7 := (v4 - 1);
  v4 := v7;
  TO: b3;
  
  FROM: b5;
  TO: end;

Other self calls are marked notail and stay, so the recursion is left and
the answer is UNKNOWN.  Without the narrowing, tail-call elimination would
convert them too, changing the order of the additions (form 2) or running
`100 / d` on paths that never reached it (form 1):

  $ llvm2lts passes/accumulate.ll
  UNKNOWN: recursion other than `return f(x);`: h -> h
  [1]
  $ llvm2lts passes/form1.ll
  UNKNOWN: recursion other than `return f(x);`: g -> g
  [1]
  $ llvm2lts --tailcallelim=no passes/tailrec.ll
  UNKNOWN: recursion other than `return f(x);`: f -> f
  [1]

With --tailcallelim-accumulator=yes the accumulator form (form 2, `return n
+ h(n - 1);`) becomes a loop too, when the integers are unbounded: the add
then has no guard, and the sum computed in the opposite order is the same.
Form 1 stays: `100 / d` would run before the recursion returns, and its
guard could stop a path that never reaches it:

  $ llvm2lts --mode=int-bitwise --unbounded-nondet --tailcallelim-accumulator=yes passes/accumulate.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  v4 := 0;
  v5 := v2;
  TO: b3;
  
  FROM: b3;
  assume(v5 <= 0);
  TO: b6;
  
  FROM: b3;
  assume(!(v5 <= 0));
  TO: b7;
  
  FROM: b7;
  v8 := (v5 - 1);
  v9 := (v5 + v4);
  v4 := v9;
  v5 := v8;
  TO: b3;
  
  FROM: b6;
  TO: end;
  $ llvm2lts --mode=int-bitwise --unbounded-nondet --tailcallelim-accumulator=yes passes/form1.ll
  UNKNOWN: recursion other than `return f(x);`: g -> g
  [1]

A `void` function's `f(x); return;` behind nested conditions, in the shape
Frama-C's normalisation gives it (one return point), leaves an empty block
between the call's block and the return, through which tail-call
elimination does not fold the return; simplifycfg merges it:

  $ llvm2lts --mode=int-bitwise --unbounded-nondet passes/emptyblock.ll
  UNKNOWN: recursion other than `return f(x);`: rec -> rec
  [1]
  $ llvm2lts --mode=int-bitwise --unbounded-nondet --simplifycfg=yes passes/emptyblock.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  v3 := (v2 + 1);
  v5 := v2;
  v6 := v3;
  TO: b4;
  
  FROM: b4;
  assume(v5 <= 23);
  TO: b7;
  
  FROM: b4;
  assume(!(v5 <= 23));
  TO: b8;
  
  FROM: b7;
  assume(v5 >= (-42));
  TO: b9;
  
  FROM: b7;
  assume(!(v5 >= (-42)));
  TO: b8;
  
  FROM: b9;
  v10 := (2 * v6);
  v11 := (v10 - 2);
  v12 := (v5 + 1);
  v5 := v11;
  v6 := v12;
  TO: b4;
  
  FROM: b8;
  TO: end;

Under any other reading the accumulator switch is refused before the input is read,
since there nsw is a guard whose place the reordering would move:

  $ llvm2lts --tailcallelim-accumulator=yes passes/accumulate.ll
  INPUT_ERROR: the accumulator form is admitted only with unbounded integers (int or int-bitwise with unbounded nondeterministic values)
  [2]
  $ llvm2lts --mode=int-wrap-unsigned --tailcallelim-accumulator=yes passes/accumulate.ll
  INPUT_ERROR: the accumulator form is admitted only with unbounded integers (int or int-bitwise with unbounded nondeterministic values)
  [2]

Mutual recursion is left as well:

  $ llvm2lts passes/mutual.ll
  UNKNOWN: recursion other than `return f(x);`: even -> odd -> even
  [1]

A variable declared in a loop gets a fresh value on every iteration; on the
path that does not write it, the value read is the marker's:

  $ llvm2lts --dump-ll loop.ll passes/loopvar.ll
  START: start;
  TYPE v11: bv(32);
  TYPE v12: bv(32);
  TYPE v14: bv(32);
  TYPE v3: bv(32);
  TYPE v4: bv(32);
  TYPE v7: bv(32);
  TYPE v8: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v3 := 0;
  v4 := 0;
  TO: b2;
  
  FROM: b2;
  assume(v3 < 3);
  TO: b5;
  
  FROM: b2;
  assume(!(v3 < 3));
  TO: b6;
  
  FROM: b5;
  v7 := nondet();
  v8 := nondet();
  assume(v8 != 0);
  TO: b9;
  
  FROM: b5;
  v7 := nondet();
  v8 := nondet();
  assume(!(v8 != 0));
  v11 := v7;
  TO: b10;
  
  FROM: b9;
  v11 := 1;
  TO: b10;
  
  FROM: b10;
  assume((extract(32, 31, (sign_extend(32, 33, v4) + sign_extend(32, 33, v11))) == 0 || extract(32, 31, (sign_extend(32, 33, v4) + sign_extend(32, 33, v11))) == 3));
  v12 := (v4 + v11);
  TO: b13;
  
  FROM: b13;
  assume((extract(32, 31, (sign_extend(32, 33, v3) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v3) + sign_extend(32, 33, 1))) == 3));
  v14 := (v3 + 1);
  v3 := v14;
  v4 := v12;
  TO: b2;
  
  FROM: b6;
  TO: end;
  $ grep -c 'call i32 @__llvm2lts_uninit_i32' loop.ll
  1
  $ grep -o 'phi i32 \[ 1, %[0-9]* \], \[ %uninit[0-9]*, %[0-9]* \]' loop.ll
  phi i32 [ 1, %6 ], [ %uninit, %3 ]

A parameter's slot gets no marker at its declaration, which follows the
copy of the argument into it.  clang copies a `_Bool` parameter through a
`zext`, so the store into the slot is not of the argument itself; the
declaration's debug variable (`arg: 1`) says it is a parameter, and without
that check the marker overwrote `cond` and made `reach_error` reachable:

  $ llvm2lts --dump-ll boolparam.ll passes/boolparam.ll > /dev/null
  $ grep -c 'call i8 @__llvm2lts_uninit_i8' boolparam.ll
  0
  [1]

Calls to defined functions are inlined, which removes a pointer passed to
one; reach_error stays a call:

  $ llvm2lts passes/ptrparam.ll
  START: start;
  TYPE ix: bv(64);
  TYPE t4: bv(32);
  TYPE v3: bv(32);
  ERROR: error;
  
  FROM: start;
  t4 := select_array(m2, ix);
  TO: b1;
  
  FROM: b1;
  m2 := nondet();
  m2 := nondet();
  m2 := const_array(0);
  v3 := select_array(m2, 1);
  TO: end;
  $ llvm2lts --dump-ll accepted.ll scope/accepted.ll > /dev/null
  $ grep -c 'call void @reach_error' accepted.ll
  2
  $ grep -c 'call i32 @f(' accepted.ll
  0
  [1]

main may have parameters as long as nothing uses them:

  $ llvm2lts passes/mainargs.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  TO: end;
  $ llvm2lts passes/mainargs_used.ll
  UNKNOWN: main: its parameter 1 is used
  [1]

The optional passes run without changing these answers:

  $ llvm2lts --simplifycfg=yes --licm=yes passes/tailrec.ll
  START: start;
  TYPE v2: bv(32);
  TYPE v4: bv(32);
  TYPE v7: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  v4 := v2;
  TO: b3;
  
  FROM: b3;
  assume(v4 <= 0);
  TO: b5;
  
  FROM: b3;
  assume(!(v4 <= 0));
  TO: b6;
  
  FROM: b6;
  assume((extract(32, 31, (sign_extend(32, 33, v4) - sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v4) - sign_extend(32, 33, 1))) == 3));
  v7 := (v4 - 1);
  v4 := v7;
  TO: b3;
  
  FROM: b5;
  TO: end;
  $ llvm2lts --simplifycfg=yes --licm=yes passes/loopvar.ll
  START: start;
  TYPE v12: bv(32);
  TYPE v13: bv(32);
  TYPE v14: bv(32);
  TYPE v3: bv(32);
  TYPE v4: bv(32);
  TYPE v7: bv(32);
  TYPE v8: bv(32);
  TYPE v9: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v3 := 0;
  v4 := 0;
  TO: b2;
  
  FROM: b2;
  assume(v3 < 3);
  TO: b5;
  
  FROM: b2;
  assume(!(v3 < 3));
  v7 := v4;
  TO: b6;
  
  FROM: b5;
  v8 := nondet();
  v9 := nondet();
  assume(v9 != 0);
  TO: b10;
  
  FROM: b5;
  v8 := nondet();
  v9 := nondet();
  assume(!(v9 != 0));
  v12 := v8;
  TO: b11;
  
  FROM: b10;
  v12 := 1;
  TO: b11;
  
  FROM: b11;
  assume((extract(32, 31, (sign_extend(32, 33, v4) + sign_extend(32, 33, v12))) == 0 || extract(32, 31, (sign_extend(32, 33, v4) + sign_extend(32, 33, v12))) == 3));
  v13 := (v4 + v12);
  assume((extract(32, 31, (sign_extend(32, 33, v3) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v3) + sign_extend(32, 33, 1))) == 3));
  v14 := (v3 + 1);
  v3 := v14;
  v4 := v13;
  TO: b2;
  
  FROM: b6;
  TO: end;
  $ llvm2lts --simplifycfg=yes --licm=yes scope/accepted.ll > /dev/null
