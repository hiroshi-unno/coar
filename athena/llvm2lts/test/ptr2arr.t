The functions the new Ptr2Arr writes to carry a meaning the IR alone does not
have, and the output functions it leaves in place.  The inputs are written in
the shape of its output.

A region array starts with arbitrary contents: its marker, called at the head
of main before the static objects are written, gives the whole array an
arbitrary value.  The cell past the static objects is then arbitrary (the
error is reachable), while the static cell written after the marker keeps its
value:

  $ llvm2lts ptr2arr/region_false.ll
  START: start;
  TYPE g_p2a_mem0_free: bv(32);
  TYPE ix: bv(64);
  TYPE t12: bv(32);
  TYPE v2: bv(32);
  TYPE v3: bv(32);
  TYPE v4: bv(32);
  TYPE v5: bv(32);
  TYPE v8: bv(64);
  TYPE v9: bv(32);
  ERROR: error;
  
  FROM: start;
  g_p2a_mem0 := const_array(0);
  g_p2a_mem0_free := 2;
  t12 := select_array(g_p2a_mem0, ix);
  TO: b1;
  
  FROM: b1;
  g_p2a_mem0 := nondet();
  g_p2a_mem0 := store_array(g_p2a_mem0, 1, 7);
  v2 := g_p2a_mem0_free;
  v3 := g_p2a_mem0_free;
  assume((extract(32, 31, (sign_extend(32, 33, v3) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v3) + sign_extend(32, 33, 1))) == 3));
  v4 := (v3 + 1);
  g_p2a_mem0_free := v4;
  v5 := select_array(g_p2a_mem0, 1);
  assume(v5 != 7);
  TO: b6;
  
  FROM: b1;
  g_p2a_mem0 := nondet();
  g_p2a_mem0 := store_array(g_p2a_mem0, 1, 7);
  v2 := g_p2a_mem0_free;
  v3 := g_p2a_mem0_free;
  assume((extract(32, 31, (sign_extend(32, 33, v3) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v3) + sign_extend(32, 33, 1))) == 3));
  v4 := (v3 + 1);
  g_p2a_mem0_free := v4;
  v5 := select_array(g_p2a_mem0, 1);
  assume(!(v5 != 7));
  TO: b7;
  
  FROM: b6;
  TO: error;
  
  FROM: b7;
  v8 := sign_extend(32, 64, v2);
  v9 := select_array(g_p2a_mem0, v8);
  assume(v9 != 0);
  TO: b10;
  
  FROM: b7;
  v8 := sign_extend(32, 64, v2);
  v9 := select_array(g_p2a_mem0, v8);
  assume(!(v9 != 0));
  TO: b11;
  
  FROM: b10;
  TO: error;
  
  FROM: b11;
  TO: end;

  $ llvm2lts --mode int ptr2arr/region_true.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  g_p2a_mem0 := const_array(0);
  TO: b1;
  
  FROM: b1;
  g_p2a_mem0 := nondet();
  g_p2a_mem0 := store_array(g_p2a_mem0, 1, 7);
  v2 := select_array(g_p2a_mem0, 1);
  assume(v2 != 7);
  TO: b3;
  
  FROM: b1;
  g_p2a_mem0 := nondet();
  g_p2a_mem0 := store_array(g_p2a_mem0, 1, 7);
  v2 := select_array(g_p2a_mem0, 1);
  assume(!(v2 != 7));
  TO: b4;
  
  FROM: b3;
  TO: error;
  
  FROM: b4;
  TO: end;

A marker naming no array of the module:

  $ llvm2lts ptr2arr/region_missing.ll
  UNKNOWN: main, line 4: __p2a_arbitrary_p2a_mem9 names no global array defined in the module
  [1]

--wrap-integers' reductions: in BV mode the call's own conversion has made
the C value, and the function is the identity; in Int mode the argument is
reduced into the type's range (256 to 0, -1 to 255, 200 to -56 for a signed
char):

  $ llvm2lts ptr2arr/wrap_true.ll
  START: start;
  TYPE v10: bv(8);
  TYPE v11: bv(32);
  TYPE v14: bv(8);
  TYPE v15: bv(32);
  TYPE v18: bv(8);
  TYPE v19: bv(8);
  TYPE v2: bv(8);
  TYPE v20: bv(32);
  TYPE v3: bv(32);
  TYPE v7: bv(32);
  TYPE v8: bv(32);
  TYPE v9: bv(8);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  v3 := zero_extend(8, 32, v2);
  assume(v3 != 255);
  TO: b4;
  
  FROM: b1;
  v2 := nondet();
  v3 := zero_extend(8, 32, v2);
  assume(!(v3 != 255));
  TO: b5;
  
  FROM: b4;
  TO: b6;
  
  FROM: b5;
  v7 := zero_extend(8, 32, v2);
  assume((extract(32, 31, (sign_extend(32, 33, v7) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v7) + sign_extend(32, 33, 1))) == 3));
  v8 := (v7 + 1);
  v9 := extract(7, 0, v8);
  v10 := v9;
  v11 := zero_extend(8, 32, v10);
  assume(v11 != 0);
  TO: b12;
  
  FROM: b5;
  v7 := zero_extend(8, 32, v2);
  assume((extract(32, 31, (sign_extend(32, 33, v7) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v7) + sign_extend(32, 33, 1))) == 3));
  v8 := (v7 + 1);
  v9 := extract(7, 0, v8);
  v10 := v9;
  v11 := zero_extend(8, 32, v10);
  assume(!(v11 != 0));
  TO: b13;
  
  FROM: b12;
  TO: error;
  
  FROM: b13;
  v14 := (-1);
  v15 := zero_extend(8, 32, v14);
  assume(v15 != 255);
  TO: b16;
  
  FROM: b13;
  v14 := (-1);
  v15 := zero_extend(8, 32, v14);
  assume(!(v15 != 255));
  TO: b17;
  
  FROM: b16;
  TO: error;
  
  FROM: b17;
  v18 := extract(7, 0, 200);
  v19 := v18;
  v20 := sign_extend(8, 32, v19);
  assume(v20 != (-56));
  TO: b21;
  
  FROM: b17;
  v18 := extract(7, 0, 200);
  v19 := v18;
  v20 := sign_extend(8, 32, v19);
  assume(!(v20 != (-56)));
  TO: b22;
  
  FROM: b21;
  TO: error;
  
  FROM: b22;
  TO: b6;
  
  FROM: b6;
  TO: end;

  $ llvm2lts --mode int ptr2arr/wrap_true.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet_uchar();
  v3 := v2;
  assume(v3 != 255);
  TO: b4;
  
  FROM: b1;
  v2 := nondet_uchar();
  v3 := v2;
  assume(!(v3 != 255));
  TO: b5;
  
  FROM: b4;
  TO: b6;
  
  FROM: b5;
  v7 := v2;
  v8 := (v7 + 1);
  v9 := v8;
  v10 := (((v9 % 256) + 256) % 256);
  v11 := v10;
  assume(v11 != 0);
  TO: b12;
  
  FROM: b5;
  v7 := v2;
  v8 := (v7 + 1);
  v9 := v8;
  v10 := (((v9 % 256) + 256) % 256);
  v11 := v10;
  assume(!(v11 != 0));
  TO: b13;
  
  FROM: b12;
  TO: error;
  
  FROM: b13;
  v14 := ((((-1) % 256) + 256) % 256);
  v15 := v14;
  assume(v15 != 255);
  TO: b16;
  
  FROM: b13;
  v14 := ((((-1) % 256) + 256) % 256);
  v15 := v14;
  assume(!(v15 != 255));
  TO: b17;
  
  FROM: b16;
  TO: error;
  
  FROM: b17;
  v18 := 200;
  v19 := (((((v18 + 128) % 256) + 256) % 256) - 128);
  v20 := v19;
  assume(v20 != (-56));
  TO: b21;
  
  FROM: b17;
  v18 := 200;
  v19 := (((((v18 + 128) % 256) + 256) % 256) - 128);
  v20 := v19;
  assume(!(v20 != (-56)));
  TO: b22;
  
  FROM: b21;
  TO: error;
  
  FROM: b22;
  TO: b6;
  
  FROM: b6;
  TO: end;

  $ llvm2lts --mode int ptr2arr/wrap_false.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet_uchar();
  v3 := v2;
  assume(v3 != 255);
  TO: b4;
  
  FROM: b1;
  v2 := nondet_uchar();
  v3 := v2;
  assume(!(v3 != 255));
  TO: b5;
  
  FROM: b4;
  TO: b6;
  
  FROM: b5;
  v7 := v2;
  v8 := (v7 + 1);
  v9 := v8;
  v10 := (((v9 % 256) + 256) % 256);
  v11 := v10;
  assume(v11 == 0);
  TO: b12;
  
  FROM: b5;
  v7 := v2;
  v8 := (v7 + 1);
  v9 := v8;
  v10 := (((v9 % 256) + 256) % 256);
  v11 := v10;
  assume(!(v11 == 0));
  TO: b13;
  
  FROM: b12;
  TO: error;
  
  FROM: b13;
  TO: b6;
  
  FROM: b6;
  TO: end;

--integers=auto's reduction of an argument shown non-negative is one truncating
remainder in Int mode (4300000000 to 5032704):

  $ llvm2lts --mode int ptr2arr/wrapnn_true.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet_uint();
  assume(v2 != (-294967296));
  TO: b3;
  
  FROM: b1;
  v2 := nondet_uint();
  assume(!(v2 != (-294967296)));
  TO: b4;
  
  FROM: b3;
  TO: b5;
  
  FROM: b4;
  v6 := (v2 + 300000000);
  v7 := (v6 % 4294967296);
  assume(v7 != 5032704);
  TO: b8;
  
  FROM: b4;
  v6 := (v2 + 300000000);
  v7 := (v6 % 4294967296);
  assume(!(v7 != 5032704));
  TO: b9;
  
  FROM: b8;
  TO: error;
  
  FROM: b9;
  TO: b5;
  
  FROM: b5;
  TO: end;

printf, puts and putchar change nothing; a result that is used is arbitrary:

  $ llvm2lts ptr2arr/printf_true.ll
  START: start;
  TYPE v11: bv(32);
  TYPE v2: bv(32);
  TYPE v7: bv(32);
  TYPE v8: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  assume(v2 < 0);
  TO: b3;
  
  FROM: b1;
  v2 := nondet();
  assume(!(v2 < 0));
  TO: b4;
  
  FROM: b4;
  assume(v2 > 10);
  TO: b3;
  
  FROM: b4;
  assume(!(v2 > 10));
  TO: b5;
  
  FROM: b3;
  v7 := 0;
  TO: b6;
  
  FROM: b5;
  v8 := nondet();
  assume(v2 > 10);
  TO: b9;
  
  FROM: b5;
  v8 := nondet();
  assume(!(v2 > 10));
  TO: b10;
  
  FROM: b9;
  TO: error;
  
  FROM: b10;
  assume((extract(32, 31, (sign_extend(32, 33, v8) - sign_extend(32, 33, v8))) == 0 || extract(32, 31, (sign_extend(32, 33, v8) - sign_extend(32, 33, v8))) == 3));
  v11 := (v8 - v8);
  v7 := v11;
  TO: b6;
  
  FROM: b6;
  TO: end;

  $ llvm2lts --mode int ptr2arr/printf_true.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet_int();
  assume(v2 < 0);
  TO: b3;
  
  FROM: b1;
  v2 := nondet_int();
  assume(!(v2 < 0));
  TO: b4;
  
  FROM: b4;
  assume(v2 > 10);
  TO: b3;
  
  FROM: b4;
  assume(!(v2 > 10));
  TO: b5;
  
  FROM: b3;
  v7 := 0;
  TO: b6;
  
  FROM: b5;
  v8 := nondet();
  assume(v2 > 10);
  TO: b9;
  
  FROM: b5;
  v8 := nondet();
  assume(!(v2 > 10));
  TO: b10;
  
  FROM: b9;
  TO: error;
  
  FROM: b10;
  v11 := (v8 - v8);
  v7 := v11;
  TO: b6;
  
  FROM: b6;
  TO: end;

Ptr2Arr's --assume-safety cut, __ptr2arr_assume(c), ends the execution where c
is 0.  It is read as a guard on its transition, the comparison its argument
widens taken in place: no branch, and for termination no move to `diverge`,
which SV-COMP's __VERIFIER_assume makes (the loop runs forever only from a
negative x, which the cut excludes):

  $ llvm2lts --property termination --mode int ptr2arr/cut_true.ll
  START: start;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet_int();
  assume(v2 >= 0);
  v4 := v2;
  TO: b3;
  
  FROM: b3;
  assume(v4 != 0);
  TO: b5;
  
  FROM: b3;
  assume(!(v4 != 0));
  TO: b6;
  
  FROM: b5;
  v7 := (v4 + (-1));
  v4 := v7;
  TO: b3;
  
  FROM: b6;
  TO: end;
