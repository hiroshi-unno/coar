Arrays and variables whose address is taken (memory objects).  The verdicts
CoAR gives on these inputs are checked by script/llvm2lts/check_verdicts.sh;
here the output itself is checked.

A local array gets arbitrary contents where it is allocated and again where
it is declared; a read is select_array.  In BV mode the start transition
reads every array once into variables of its index and element widths,
which fixes the array's type for T2:

  $ llvm2lts arrays/uninit_false.ll
  START: start;
  TYPE ix: bv(64);
  TYPE t6: bv(32);
  TYPE v3: bv(32);
  ERROR: error;
  
  FROM: start;
  t6 := select_array(m2, ix);
  TO: b1;
  
  FROM: b1;
  m2 := nondet();
  m2 := nondet();
  v3 := select_array(m2, 2);
  assume(v3 == 5);
  TO: b4;
  
  FROM: b1;
  m2 := nondet();
  m2 := nondet();
  v3 := select_array(m2, 2);
  assume(!(v3 == 5));
  TO: b5;
  
  FROM: b4;
  TO: error;
  
  FROM: b5;
  TO: end;
  $ llvm2lts --mode int arrays/uninit_false.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  m2 := nondet();
  m2 := nondet();
  v3 := select_array(m2, 2);
  assume(v3 == 5);
  TO: b4;
  
  FROM: b1;
  m2 := nondet();
  m2 := nondet();
  v3 := select_array(m2, 2);
  assume(!(v3 == 5));
  TO: b5;
  
  FROM: b4;
  TO: error;
  
  FROM: b5;
  TO: end;

An initialiser is a memcpy from a constant global (an array variable
initialised in the start transition); a copy of a whole array is one
assignment:

  $ llvm2lts --mode int arrays/copy_true.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  g___const_main_a := const_array(0);
  g___const_main_a := store_array(g___const_main_a, 0, 7);
  g___const_main_a := store_array(g___const_main_a, 1, 8);
  g___const_main_a := store_array(g___const_main_a, 2, 9);
  TO: b1;
  
  FROM: b1;
  m2 := nondet();
  m3 := nondet();
  m2 := nondet();
  m2 := g___const_main_a;
  m3 := nondet();
  m3 := m2;
  v4 := select_array(m3, 2);
  assume(v4 == 9);
  v5 := 1;
  TO: b1_6;
  
  FROM: b1;
  m2 := nondet();
  m3 := nondet();
  m2 := nondet();
  m2 := g___const_main_a;
  m3 := nondet();
  m3 := m2;
  v4 := select_array(m3, 2);
  assume(!(v4 == 9));
  v5 := 0;
  TO: b1_6;
  
  FROM: b1_6;
  v7 := v5;
  assume(v5 != 0);
  TO: b8;
  
  FROM: b1_6;
  v7 := v5;
  assume(!(v5 != 0));
  TO: b9;
  
  FROM: b9;
  TO: error;
  
  FROM: b8;
  TO: end;

A string initialiser:

  $ llvm2lts --mode int arrays/string_true.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  g___const_main_s := const_array(0);
  g___const_main_s := store_array(g___const_main_s, 0, 97);
  g___const_main_s := store_array(g___const_main_s, 1, 98);
  g___const_main_s := store_array(g___const_main_s, 2, 99);
  TO: b1;
  
  FROM: b1;
  m2 := nondet();
  m2 := nondet();
  m2 := g___const_main_s;
  v3 := select_array(m2, 1);
  v4 := v3;
  assume(v4 == 98);
  TO: b5;
  
  FROM: b1;
  m2 := nondet();
  m2 := nondet();
  m2 := g___const_main_s;
  v3 := select_array(m2, 1);
  v4 := v3;
  assume(!(v4 == 98));
  v7 := 0;
  TO: b6;
  
  FROM: b5;
  v8 := select_array(m2, 3);
  v9 := v8;
  assume(v9 == 0);
  v10 := 1;
  TO: b5_11;
  
  FROM: b5;
  v8 := select_array(m2, 3);
  v9 := v8;
  assume(!(v9 == 0));
  v10 := 0;
  TO: b5_11;
  
  FROM: b5_11;
  v7 := v10;
  TO: b6;
  
  FROM: b6;
  v12 := v7;
  assume(v7 != 0);
  TO: b13;
  
  FROM: b6;
  v12 := v7;
  assume(!(v7 != 0));
  TO: b14;
  
  FROM: b14;
  TO: error;
  
  FROM: b13;
  TO: end;

A memset of a variable number of elements is a loop with its own counter:

  $ llvm2lts arrays/memset_var_true.ll
  START: start;
  TYPE ix: bv(64);
  TYPE t10: bv(64);
  TYPE t20: bv(32);
  TYPE v12: bv(32);
  TYPE v13: bv(64);
  TYPE v14: bv(32);
  TYPE v15: bv(1);
  TYPE v17: bv(32);
  TYPE v3: bv(32);
  TYPE v8: bv(64);
  TYPE v9: bv(64);
  ERROR: error;
  
  FROM: start;
  t20 := select_array(m2, ix);
  TO: b1;
  
  FROM: b1;
  m2 := nondet();
  m2 := nondet();
  v3 := nondet();
  assume(v3 < 1);
  TO: b4;
  
  FROM: b1;
  m2 := nondet();
  m2 := nondet();
  v3 := nondet();
  assume(!(v3 < 1));
  TO: b5;
  
  FROM: b5;
  assume(v3 > 10);
  TO: b4;
  
  FROM: b5;
  assume(!(v3 > 10));
  TO: b6;
  
  FROM: b4;
  TO: b7;
  
  FROM: b6;
  v8 := sign_extend(32, 64, v3);
  v9 := (v8 * 4);
  t10 := 0;
  TO: b6_11;
  
  FROM: b6_11;
  assume(t10 ult v8);
  m2 := store_array(m2, t10, 0);
  t10 := (t10 + 1);
  TO: b6_11;
  
  FROM: b6_11;
  assume(t10 uge v8);
  assume((extract(32, 31, (sign_extend(32, 33, v3) - sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v3) - sign_extend(32, 33, 1))) == 3));
  v12 := (v3 - 1);
  v13 := sign_extend(32, 64, v12);
  v14 := select_array(m2, v13);
  assume(v14 == 0);
  v15 := 1;
  TO: b6_11_16;
  
  FROM: b6_11;
  assume(t10 uge v8);
  assume((extract(32, 31, (sign_extend(32, 33, v3) - sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v3) - sign_extend(32, 33, 1))) == 3));
  v12 := (v3 - 1);
  v13 := sign_extend(32, 64, v12);
  v14 := select_array(m2, v13);
  assume(!(v14 == 0));
  v15 := 0;
  TO: b6_11_16;
  
  FROM: b6_11_16;
  v17 := zero_extend(1, 32, v15);
  assume(v15 != 0);
  TO: b18;
  
  FROM: b6_11_16;
  v17 := zero_extend(1, 32, v15);
  assume(!(v15 != 0));
  TO: b19;
  
  FROM: b19;
  TO: error;
  
  FROM: b18;
  TO: b7;
  
  FROM: b7;
  TO: end;

A two-dimensional global array is one array indexed by i * 3 + j:

  $ llvm2lts --mode int arrays/matrix_true.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  g_m := const_array(0);
  TO: b1;
  
  FROM: b1;
  v3 := 0;
  TO: b2;
  
  FROM: b2;
  assume(v3 < 2);
  TO: b4;
  
  FROM: b2;
  assume(!(v3 < 2));
  TO: b5;
  
  FROM: b4;
  v7 := 0;
  TO: b6;
  
  FROM: b6;
  assume(v7 < 3);
  TO: b8;
  
  FROM: b6;
  assume(!(v7 < 3));
  TO: b9;
  
  FROM: b8;
  v10 := (v3 + v7);
  v11 := v3;
  v12 := v7;
  g_m := store_array(g_m, ((v11 * 3) + v12), v10);
  TO: b13;
  
  FROM: b13;
  v14 := (v7 + 1);
  v7 := v14;
  TO: b6;
  
  FROM: b9;
  TO: b15;
  
  FROM: b15;
  v16 := (v3 + 1);
  v3 := v16;
  TO: b2;
  
  FROM: b5;
  v17 := select_array(g_m, 5);
  assume(v17 == 3);
  v18 := 1;
  TO: b5_19;
  
  FROM: b5;
  v17 := select_array(g_m, 5);
  assume(!(v17 == 3));
  v18 := 0;
  TO: b5_19;
  
  FROM: b5_19;
  v20 := v18;
  assume(v18 != 0);
  TO: b21;
  
  FROM: b5_19;
  v20 := v18;
  assume(!(v18 != 0));
  TO: b22;
  
  FROM: b22;
  TO: error;
  
  FROM: b21;
  TO: end;

An address-taken integer variable is a plain variable; the function that
takes the address is inlined:

  $ llvm2lts --mode int arrays/scalar_addr_true.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v3 := nondet();
  m2 := v3;
  v4 := nondet();
  m2 := v4;
  m2 := 0;
  v5 := m2;
  v6 := (v5 + 1);
  m2 := v6;
  v7 := m2;
  v8 := (v7 + 1);
  m2 := v8;
  v9 := m2;
  assume(v9 == 2);
  v10 := 1;
  TO: b1_11;
  
  FROM: b1;
  v3 := nondet();
  m2 := v3;
  v4 := nondet();
  m2 := v4;
  m2 := 0;
  v5 := m2;
  v6 := (v5 + 1);
  m2 := v6;
  v7 := m2;
  v8 := (v7 + 1);
  m2 := v8;
  v9 := m2;
  assume(!(v9 == 2));
  v10 := 0;
  TO: b1_11;
  
  FROM: b1_11;
  v12 := v10;
  assume(v10 != 0);
  TO: b13;
  
  FROM: b1_11;
  v12 := v10;
  assume(!(v10 != 0));
  TO: b14;
  
  FROM: b14;
  TO: error;
  
  FROM: b13;
  TO: end;

Each inlined call gets its callee's array afresh (llvm.lifetime.start):

  $ llvm2lts --mode int arrays/callee_array_false.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  m2 := nondet();
  m3 := nondet();
  m2 := nondet();
  m2 := nondet();
  m2 := store_array(m2, 1, 5);
  v4 := select_array(m2, 1);
  m3 := nondet();
  m3 := nondet();
  v5 := select_array(m3, 1);
  assume(v5 == 5);
  v6 := 1;
  TO: b1_7;
  
  FROM: b1;
  m2 := nondet();
  m3 := nondet();
  m2 := nondet();
  m2 := nondet();
  m2 := store_array(m2, 1, 5);
  v4 := select_array(m2, 1);
  m3 := nondet();
  m3 := nondet();
  v5 := select_array(m3, 1);
  assume(!(v5 == 5));
  v6 := 0;
  TO: b1_7;
  
  FROM: b1_7;
  v8 := v6;
  assume(v6 != 0);
  TO: b9;
  
  FROM: b1_7;
  v8 := v6;
  assume(!(v6 != 0));
  TO: b10;
  
  FROM: b10;
  TO: error;
  
  FROM: b9;
  TO: end;

A byte of an int array (an access to part of a leaf) is not translated:

  $ llvm2lts arrays/bytes.ll
  UNKNOWN: main, line 8: an access to part of an integer
  [1]
