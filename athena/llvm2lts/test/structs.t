Structs: each leaf field of an object is a variable of its own, or an array
variable when the object or the field is inside an array (fields.t's
nodes[k].val is one array indexed by k).  The verdicts are checked by
script/llvm2lts/check_verdicts.sh; here the output itself is checked.

Fields, nested structs, an array inside a struct, struct assignment (a
memcpy between values of one shape, field by field) and a global array of
structs:

  $ llvm2lts --mode int structs/fields_true.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  g_g.0 := 0;
  g_g.1.0 := const_array(0);
  g_g.1.1 := 0;
  g_nodes.0 := const_array(0);
  g_nodes.1 := const_array(0);
  TO: b1;
  
  FROM: b1;
  m2.0 := nondet();
  m2.1.0 := nondet();
  m2.1.1 := nondet();
  m3.0 := nondet();
  m3.1.0 := nondet();
  m3.1.1 := nondet();
  m2.0 := nondet();
  m2.1.0 := nondet();
  m2.1.1 := nondet();
  m2.0 := 0;
  m2.1.0 := const_array(0);
  m2.1.1 := 0;
  m3.0 := nondet();
  m3.1.0 := nondet();
  m3.1.1 := nondet();
  v4 := nondet_int();
  assume(v4 < 0);
  TO: b5;
  
  FROM: b1;
  m2.0 := nondet();
  m2.1.0 := nondet();
  m2.1.1 := nondet();
  m3.0 := nondet();
  m3.1.0 := nondet();
  m3.1.1 := nondet();
  m2.0 := nondet();
  m2.1.0 := nondet();
  m2.1.1 := nondet();
  m2.0 := 0;
  m2.1.0 := const_array(0);
  m2.1.1 := 0;
  m3.0 := nondet();
  m3.1.0 := nondet();
  m3.1.1 := nondet();
  v4 := nondet_int();
  assume(!(v4 < 0));
  TO: b6;
  
  FROM: b6;
  assume(v4 >= 3);
  TO: b5;
  
  FROM: b6;
  assume(!(v4 >= 3));
  TO: b7;
  
  FROM: b5;
  TO: b8;
  
  FROM: b7;
  v9 := v4;
  m2.1.0 := store_array(m2.1.0, v9, 9);
  m3.0 := m2.0;
  m3.1.0 := m2.1.0;
  m3.1.1 := m2.1.1;
  g_g.0 := m3.0;
  g_g.1.0 := m3.1.0;
  g_g.1.1 := m3.1.1;
  v10 := v4;
  g_nodes.0 := store_array(g_nodes.0, v10, 4);
  v11 := (v4 + 1);
  v12 := v4;
  g_nodes.1 := store_array(g_nodes.1, v12, v11);
  v13 := v4;
  v14 := select_array(g_g.1.0, v13);
  assume(v14 == 9);
  TO: b15;
  
  FROM: b7;
  v9 := v4;
  m2.1.0 := store_array(m2.1.0, v9, 9);
  m3.0 := m2.0;
  m3.1.0 := m2.1.0;
  m3.1.1 := m2.1.1;
  g_g.0 := m3.0;
  g_g.1.0 := m3.1.0;
  g_g.1.1 := m3.1.1;
  v10 := v4;
  g_nodes.0 := store_array(g_nodes.0, v10, 4);
  v11 := (v4 + 1);
  v12 := v4;
  g_nodes.1 := store_array(g_nodes.1, v12, v11);
  v13 := v4;
  v14 := select_array(g_g.1.0, v13);
  assume(!(v14 == 9));
  v17 := 0;
  TO: b16;
  
  FROM: b15;
  v18 := m3.0;
  assume(v18 == 0);
  TO: b19;
  
  FROM: b15;
  v18 := m3.0;
  assume(!(v18 == 0));
  v17 := 0;
  TO: b16;
  
  FROM: b19;
  v20 := v4;
  v21 := select_array(g_nodes.0, v20);
  v22 := v4;
  v23 := select_array(g_nodes.1, v22);
  v24 := (v21 + v23);
  v25 := (v4 + 5);
  assume(v24 == v25);
  v26 := 1;
  TO: b19_27;
  
  FROM: b19;
  v20 := v4;
  v21 := select_array(g_nodes.0, v20);
  v22 := v4;
  v23 := select_array(g_nodes.1, v22);
  v24 := (v21 + v23);
  v25 := (v4 + 5);
  assume(!(v24 == v25));
  v26 := 0;
  TO: b19_27;
  
  FROM: b19_27;
  v17 := v26;
  TO: b16;
  
  FROM: b16;
  v28 := v17;
  assume(v17 != 0);
  TO: b29;
  
  FROM: b16;
  v28 := v17;
  assume(!(v17 != 0));
  TO: b30;
  
  FROM: b30;
  TO: error;
  
  FROM: b29;
  TO: b8;
  
  FROM: b8;
  TO: end;

An initialised global array of structs: one array per field.

  $ llvm2lts --mode int structs/table_true.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  g_table.0 := const_array(0);
  g_table.0 := store_array(g_table.0, 0, 1);
  g_table.0 := store_array(g_table.0, 1, 2);
  g_table.0 := store_array(g_table.0, 2, 3);
  g_table.1 := const_array(0);
  g_table.1 := store_array(g_table.1, 0, 10);
  g_table.1 := store_array(g_table.1, 1, 20);
  g_table.1 := store_array(g_table.1, 2, 30);
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
  assume(v2 >= 3);
  TO: b3;
  
  FROM: b4;
  assume(!(v2 >= 3));
  TO: b5;
  
  FROM: b3;
  TO: b6;
  
  FROM: b5;
  v7 := v2;
  v8 := select_array(g_table.1, v7);
  v9 := v2;
  v10 := select_array(g_table.0, v9);
  v11 := v10;
  v12 := (10 * v11);
  v13 := v12;
  assume(v8 == v13);
  v14 := 1;
  TO: b5_15;
  
  FROM: b5;
  v7 := v2;
  v8 := select_array(g_table.1, v7);
  v9 := v2;
  v10 := select_array(g_table.0, v9);
  v11 := v10;
  v12 := (10 * v11);
  v13 := v12;
  assume(!(v8 == v13));
  v14 := 0;
  TO: b5_15;
  
  FROM: b5_15;
  v16 := v14;
  assume(v14 != 0);
  TO: b17;
  
  FROM: b5_15;
  v16 := v14;
  assume(!(v14 != 0));
  TO: b18;
  
  FROM: b18;
  TO: error;
  
  FROM: b17;
  TO: b6;
  
  FROM: b6;
  TO: end;

A memset over a variable number of structs is a loop per field:

  $ llvm2lts structs/clear_true.ll
  START: start;
  TYPE ix: bv(64);
  TYPE t10: bv(64);
  TYPE t12: bv(64);
  TYPE t27: bv(16);
  TYPE t28: bv(64);
  TYPE v14: bv(32);
  TYPE v15: bv(64);
  TYPE v16: bv(16);
  TYPE v17: bv(32);
  TYPE v20: bv(1);
  TYPE v21: bv(64);
  TYPE v22: bv(1);
  TYPE v24: bv(32);
  TYPE v3: bv(32);
  TYPE v8: bv(64);
  TYPE v9: bv(64);
  ERROR: error;
  
  FROM: start;
  t27 := select_array(m2.0, ix);
  t28 := select_array(m2.1, ix);
  TO: b1;
  
  FROM: b1;
  m2.0 := nondet();
  m2.1 := nondet();
  m2.0 := nondet();
  m2.1 := nondet();
  v3 := nondet();
  assume(v3 < 1);
  TO: b4;
  
  FROM: b1;
  m2.0 := nondet();
  m2.1 := nondet();
  m2.0 := nondet();
  m2.1 := nondet();
  v3 := nondet();
  assume(!(v3 < 1));
  TO: b5;
  
  FROM: b5;
  assume(v3 > 8);
  TO: b4;
  
  FROM: b5;
  assume(!(v3 > 8));
  TO: b6;
  
  FROM: b4;
  TO: b7;
  
  FROM: b6;
  v8 := sign_extend(32, 64, v3);
  v9 := (v8 * 16);
  t10 := 0;
  TO: b6_11;
  
  FROM: b6_11;
  assume(t10 ult v8);
  m2.0 := store_array(m2.0, t10, 0);
  t10 := (t10 + 1);
  TO: b6_11;
  
  FROM: b6_11;
  assume(t10 uge v8);
  t12 := 0;
  TO: b6_11_13;
  
  FROM: b6_11_13;
  assume(t12 ult v8);
  m2.1 := store_array(m2.1, t12, 0);
  t12 := (t12 + 1);
  TO: b6_11_13;
  
  FROM: b6_11_13;
  assume(t12 uge v8);
  assume((extract(32, 31, (sign_extend(32, 33, v3) - sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v3) - sign_extend(32, 33, 1))) == 3));
  v14 := (v3 - 1);
  v15 := sign_extend(32, 64, v14);
  v16 := select_array(m2.0, v15);
  v17 := sign_extend(16, 32, v16);
  assume(v17 == 0);
  TO: b18;
  
  FROM: b6_11_13;
  assume(t12 uge v8);
  assume((extract(32, 31, (sign_extend(32, 33, v3) - sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v3) - sign_extend(32, 33, 1))) == 3));
  v14 := (v3 - 1);
  v15 := sign_extend(32, 64, v14);
  v16 := select_array(m2.0, v15);
  v17 := sign_extend(16, 32, v16);
  assume(!(v17 == 0));
  v20 := 0;
  TO: b19;
  
  FROM: b18;
  v21 := select_array(m2.1, 0);
  assume(v21 == 0);
  v22 := 1;
  TO: b18_23;
  
  FROM: b18;
  v21 := select_array(m2.1, 0);
  assume(!(v21 == 0));
  v22 := 0;
  TO: b18_23;
  
  FROM: b18_23;
  v20 := v22;
  TO: b19;
  
  FROM: b19;
  v24 := zero_extend(1, 32, v20);
  assume(v20 != 0);
  TO: b25;
  
  FROM: b19;
  v24 := zero_extend(1, 32, v20);
  assume(!(v20 != 0));
  TO: b26;
  
  FROM: b26;
  TO: error;
  
  FROM: b25;
  TO: b7;
  
  FROM: b7;
  TO: end;

A struct of 8 bytes passed by value travels as one i64 that is only stored:
it is kept as its fields and stored field by field, in both modes (padding
bits are not carried).  The argument stored into the callee's parameter is
not overwritten by the parameter's declaration:

  $ llvm2lts --mode int structs/byvalue_true.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  g___const_main_p.0 := 1;
  g___const_main_p.1 := 2;
  g___const_main_rr.0 := const_array(0);
  g___const_main_rr.0 := store_array(g___const_main_rr.0, 2, 7);
  g___const_main_s.0 := 1;
  g___const_main_s.1 := 5;
  TO: b1;
  
  FROM: b1;
  m2.0 := nondet();
  m2.1 := nondet();
  m3.0 := nondet();
  m4.0 := nondet();
  m4.1 := nondet();
  m5.0 := nondet();
  m5.1 := nondet();
  m6.0 := nondet();
  m6.1 := nondet();
  m7.0 := nondet();
  m7.1 := nondet();
  m8.0 := nondet();
  m9.0 := nondet();
  m9.1 := nondet();
  m6.0 := nondet();
  m6.1 := nondet();
  m6.0 := g___const_main_p.0;
  m6.1 := g___const_main_p.1;
  m7.0 := nondet();
  m7.1 := nondet();
  t10 := m6.0;
  t11 := m6.1;
  m4.0 := nondet();
  m4.1 := nondet();
  m5.0 := nondet();
  m5.1 := nondet();
  m5.0 := t10;
  m5.1 := t11;
  m4.0 := nondet();
  m4.1 := nondet();
  v12 := m5.1;
  m4.0 := v12;
  v13 := m5.0;
  m4.1 := v13;
  t14 := m4.0;
  t15 := m4.1;
  m7.0 := t14;
  m7.1 := t15;
  m8.0 := nondet();
  m8.0 := g___const_main_rr.0;
  m9.0 := nondet();
  m9.1 := nondet();
  m9.0 := g___const_main_s.0;
  m9.1 := g___const_main_s.1;
  v16 := m7.0;
  assume(v16 == 2);
  TO: b17;
  
  FROM: b1;
  m2.0 := nondet();
  m2.1 := nondet();
  m3.0 := nondet();
  m4.0 := nondet();
  m4.1 := nondet();
  m5.0 := nondet();
  m5.1 := nondet();
  m6.0 := nondet();
  m6.1 := nondet();
  m7.0 := nondet();
  m7.1 := nondet();
  m8.0 := nondet();
  m9.0 := nondet();
  m9.1 := nondet();
  m6.0 := nondet();
  m6.1 := nondet();
  m6.0 := g___const_main_p.0;
  m6.1 := g___const_main_p.1;
  m7.0 := nondet();
  m7.1 := nondet();
  t10 := m6.0;
  t11 := m6.1;
  m4.0 := nondet();
  m4.1 := nondet();
  m5.0 := nondet();
  m5.1 := nondet();
  m5.0 := t10;
  m5.1 := t11;
  m4.0 := nondet();
  m4.1 := nondet();
  v12 := m5.1;
  m4.0 := v12;
  v13 := m5.0;
  m4.1 := v13;
  t14 := m4.0;
  t15 := m4.1;
  m7.0 := t14;
  m7.1 := t15;
  m8.0 := nondet();
  m8.0 := g___const_main_rr.0;
  m9.0 := nondet();
  m9.1 := nondet();
  m9.0 := g___const_main_s.0;
  m9.1 := g___const_main_s.1;
  v16 := m7.0;
  assume(!(v16 == 2));
  v19 := 0;
  TO: b18;
  
  FROM: b17;
  v20 := m7.1;
  assume(v20 == 1);
  TO: b21;
  
  FROM: b17;
  v20 := m7.1;
  assume(!(v20 == 1));
  v19 := 0;
  TO: b18;
  
  FROM: b21;
  m3.0 := nondet();
  m3.0 := m8.0;
  v22 := select_array(m3.0, 2);
  assume(v22 == 7);
  TO: b23;
  
  FROM: b21;
  m3.0 := nondet();
  m3.0 := m8.0;
  v22 := select_array(m3.0, 2);
  assume(!(v22 == 7));
  v19 := 0;
  TO: b18;
  
  FROM: b23;
  t24 := m9.0;
  t25 := m9.1;
  m2.0 := nondet();
  m2.1 := nondet();
  m2.0 := t24;
  m2.1 := t25;
  v26 := m2.1;
  v27 := m2.0;
  v28 := v27;
  v29 := (v26 + v28);
  assume(v29 == 6);
  v30 := 1;
  TO: b23_31;
  
  FROM: b23;
  t24 := m9.0;
  t25 := m9.1;
  m2.0 := nondet();
  m2.1 := nondet();
  m2.0 := t24;
  m2.1 := t25;
  v26 := m2.1;
  v27 := m2.0;
  v28 := v27;
  v29 := (v26 + v28);
  assume(!(v29 == 6));
  v30 := 0;
  TO: b23_31;
  
  FROM: b23_31;
  v19 := v30;
  TO: b18;
  
  FROM: b18;
  v32 := v19;
  assume(v19 != 0);
  TO: b33;
  
  FROM: b18;
  v32 := v19;
  assume(!(v19 != 0));
  TO: b34;
  
  FROM: b34;
  TO: error;
  
  FROM: b33;
  TO: end;

A struct of 12 bytes goes through a { i64, i32 } temporary, whose i64 holds
two int fields: assembled by bit operations in BV mode, with padding bits
arbitrary, and not translated in Int mode:

  $ llvm2lts structs/byvalue12_true.ll
  START: start;
  TYPE g___const_main_q.0: bv(32);
  TYPE g___const_main_q.1: bv(32);
  TYPE g___const_main_q.2: bv(32);
  TYPE m2.0: bv(32);
  TYPE m2.1: bv(32);
  TYPE m2.2: bv(32);
  TYPE m3.0: bv(64);
  TYPE m3.1: bv(32);
  TYPE m4.0: bv(32);
  TYPE m4.1: bv(32);
  TYPE m4.2: bv(32);
  TYPE m5.0: bv(64);
  TYPE m5.1: bv(32);
  TYPE t11: bv(64);
  TYPE t12: bv(32);
  TYPE t6: bv(32);
  TYPE t7: bv(32);
  TYPE t8: bv(32);
  TYPE v10: bv(32);
  TYPE v13: bv(32);
  TYPE v14: bv(32);
  TYPE v15: bv(32);
  TYPE v16: bv(32);
  TYPE v17: bv(32);
  TYPE v18: bv(1);
  TYPE v20: bv(32);
  TYPE v9: bv(64);
  ERROR: error;
  
  FROM: start;
  g___const_main_q.0 := 1;
  g___const_main_q.1 := 2;
  g___const_main_q.2 := 3;
  TO: b1;
  
  FROM: b1;
  m2.0 := nondet();
  m2.1 := nondet();
  m2.2 := nondet();
  m3.0 := nondet();
  m3.1 := nondet();
  m4.0 := nondet();
  m4.1 := nondet();
  m4.2 := nondet();
  m5.0 := nondet();
  m5.1 := nondet();
  m4.0 := nondet();
  m4.1 := nondet();
  m4.2 := nondet();
  m4.0 := g___const_main_q.0;
  m4.1 := g___const_main_q.1;
  m4.2 := g___const_main_q.2;
  t6 := m4.0;
  t7 := m4.1;
  t8 := m4.2;
  m5.0 := or(zero_extend(32, 64, t6), shl(zero_extend(32, 64, t7), 32));
  m5.1 := t8;
  v9 := m5.0;
  v10 := m5.1;
  m2.0 := nondet();
  m2.1 := nondet();
  m2.2 := nondet();
  m3.0 := nondet();
  m3.1 := nondet();
  m3.0 := v9;
  m3.1 := v10;
  t11 := m3.0;
  t12 := m3.1;
  m2.0 := extract(31, 0, t11);
  m2.1 := extract(63, 32, t11);
  m2.2 := t12;
  v13 := m2.0;
  v14 := m2.1;
  assume((extract(32, 31, (sign_extend(32, 33, v13) + sign_extend(32, 33, v14))) == 0 || extract(32, 31, (sign_extend(32, 33, v13) + sign_extend(32, 33, v14))) == 3));
  v15 := (v13 + v14);
  v16 := m2.2;
  assume((extract(32, 31, (sign_extend(32, 33, v15) + sign_extend(32, 33, v16))) == 0 || extract(32, 31, (sign_extend(32, 33, v15) + sign_extend(32, 33, v16))) == 3));
  v17 := (v15 + v16);
  assume(v17 == 6);
  v18 := 1;
  TO: b1_19;
  
  FROM: b1;
  m2.0 := nondet();
  m2.1 := nondet();
  m2.2 := nondet();
  m3.0 := nondet();
  m3.1 := nondet();
  m4.0 := nondet();
  m4.1 := nondet();
  m4.2 := nondet();
  m5.0 := nondet();
  m5.1 := nondet();
  m4.0 := nondet();
  m4.1 := nondet();
  m4.2 := nondet();
  m4.0 := g___const_main_q.0;
  m4.1 := g___const_main_q.1;
  m4.2 := g___const_main_q.2;
  t6 := m4.0;
  t7 := m4.1;
  t8 := m4.2;
  m5.0 := or(zero_extend(32, 64, t6), shl(zero_extend(32, 64, t7), 32));
  m5.1 := t8;
  v9 := m5.0;
  v10 := m5.1;
  m2.0 := nondet();
  m2.1 := nondet();
  m2.2 := nondet();
  m3.0 := nondet();
  m3.1 := nondet();
  m3.0 := v9;
  m3.1 := v10;
  t11 := m3.0;
  t12 := m3.1;
  m2.0 := extract(31, 0, t11);
  m2.1 := extract(63, 32, t11);
  m2.2 := t12;
  v13 := m2.0;
  v14 := m2.1;
  assume((extract(32, 31, (sign_extend(32, 33, v13) + sign_extend(32, 33, v14))) == 0 || extract(32, 31, (sign_extend(32, 33, v13) + sign_extend(32, 33, v14))) == 3));
  v15 := (v13 + v14);
  v16 := m2.2;
  assume((extract(32, 31, (sign_extend(32, 33, v15) + sign_extend(32, 33, v16))) == 0 || extract(32, 31, (sign_extend(32, 33, v15) + sign_extend(32, 33, v16))) == 3));
  v17 := (v15 + v16);
  assume(!(v17 == 6));
  v18 := 0;
  TO: b1_19;
  
  FROM: b1_19;
  v20 := zero_extend(1, 32, v18);
  assume(v18 != 0);
  TO: b21;
  
  FROM: b1_19;
  v20 := zero_extend(1, 32, v18);
  assume(!(v18 != 0));
  TO: b22;
  
  FROM: b22;
  TO: error;
  
  FROM: b21;
  TO: end;
  $ llvm2lts --mode int structs/byvalue12_true.ll > /dev/null
  UNKNOWN: main, line 10: an integer assembled from several fields or padding (Int mode)
  [1]

Unions are not translated:

  $ llvm2lts structs/union.ll
  UNKNOWN: main: a local variable of type %union.U = type { i32 }
  [1]
