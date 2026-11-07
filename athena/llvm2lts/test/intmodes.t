The integer readings of --mode on inputs where they differ.  The verdicts
CoAR gives on these files in each mode are checked by
script/llvm2lts/check_verdicts.sh; here the translation is checked.

Which inputs each mode translates (a line names a refused input and its
reason):

  $ for f in intmodes/*.ll; do for m in bv int int-bitwise int-wrap-unsigned int-wrap-all; do llvm2lts --mode $m $f > /dev/null 2> err || echo "$(basename $f) $m: $(tail -1 err)"; done; done
  bitconst_false.ll int: UNKNOWN: main, line 11: a bitwise operation in Int mode
  bitconst_true.ll int: UNKNOWN: main, line 13: a bitwise operation in Int mode
  overflow_builtin_true.ll int: UNKNOWN: main, line 14: an overflow-checking intrinsic in Int mode
  overflow_builtin_true.ll int-bitwise: UNKNOWN: main, line 14: an overflow-checking intrinsic in Int mode

int-bitwise reads x | 4 in infinite two's complement as x + 4 - (x & 4),
and x & 4 (the bits [2, 3) of x) as (x mod 8) - (x mod 4), each remainder
made non-negative; nothing is reduced:

  $ llvm2lts --mode int-bitwise intmodes/bitconst_false.ll | grep ':='
  v2 := nondet_int();
  v3 := ((v2 + 4) - ((((v2 % 8) + 8) % 8) - (((v2 % 4) + 4) % 4)));
  v4 := 1;
  v2 := nondet_int();
  v3 := ((v2 + 4) - ((((v2 % 8) + 8) % 8) - (((v2 % 4) + 4) % 4)));
  v4 := 0;
  v6 := v4;
  v6 := v4;

The wrapping modes keep every value as its unsigned representative: the
nondet is confined to [0, 2^32), the sum is reduced, and nsw is read
(assumed) by int-wrap-unsigned only:

  $ llvm2lts --mode int-wrap-unsigned intmodes/signed_overflow_true.ll | grep -E 'assume|:='
  v2 := nondet();
  assume((v2 >= 0 && v2 < 4294967296));
  assume(v2 == 2147483647);
  v2 := nondet();
  assume((v2 >= 0 && v2 < 4294967296));
  assume(!(v2 == 2147483647));
  assume((((v2 - (4294967296 * (v2 / 2147483648))) + 1) >= (-2147483648) && ((v2 - (4294967296 * (v2 / 2147483648))) + 1) < 2147483648));
  v5 := ((v2 + 1) % 4294967296);
  assume((v5 - (4294967296 * (v5 / 2147483648))) > 0);
  v6 := 1;
  assume((((v2 - (4294967296 * (v2 / 2147483648))) + 1) >= (-2147483648) && ((v2 - (4294967296 * (v2 / 2147483648))) + 1) < 2147483648));
  v5 := ((v2 + 1) % 4294967296);
  assume(!((v5 - (4294967296 * (v5 / 2147483648))) > 0));
  v6 := 0;
  v8 := v6;
  assume(v6 != 0);
  v8 := v6;
  assume(!(v6 != 0));
  $ llvm2lts --mode int-wrap-all intmodes/signed_overflow_true.ll | grep -E 'assume|:='
  v2 := nondet();
  assume((v2 >= 0 && v2 < 4294967296));
  assume(v2 == 2147483647);
  v2 := nondet();
  assume((v2 >= 0 && v2 < 4294967296));
  assume(!(v2 == 2147483647));
  v5 := ((v2 + 1) % 4294967296);
  assume((v5 - (4294967296 * (v5 / 2147483648))) > 0);
  v6 := 1;
  v5 := ((v2 + 1) % 4294967296);
  assume(!((v5 - (4294967296 * (v5 / 2147483648))) > 0));
  v6 := 0;
  v8 := v6;
  assume(v6 != 0);
  v8 := v6;
  assume(!(v6 != 0));

trunc reduces (v6) and sext adds 2^32 - 2^8 when the sign bit is set (v7):

  $ llvm2lts --mode int-wrap-unsigned intmodes/conversion_true.ll | grep -E 'assume|:=' | head -12
  v2 := nondet();
  assume((v2 >= 0 && v2 < 4294967296));
  assume(v2 == 200);
  v3 := 1;
  v2 := nondet();
  assume((v2 >= 0 && v2 < 4294967296));
  assume(!(v2 == 200));
  v3 := 0;
  v5 := v3;
  assume(v5 != 0);
  v6 := (v2 % 256);
  v7 := (v6 + ((v6 / 128) * 4294967040));

llvm.sadd.with.overflow is an addition with the signed overflow test, in BV
(one bit wider) and in the wrapping modes (the exact signed sum in range):

  $ llvm2lts --mode bv intmodes/overflow_builtin_true.ll | grep -E '^p[0-9]+ :=|extract' | head -3
  p3 := (v2 + 1);
  assume((extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 3));
  p4 := 0;
  $ llvm2lts --mode int-wrap-unsigned intmodes/overflow_builtin_true.ll | grep -E '^p[0-9]+ :=|assume' | head -4
  assume((v2 >= 0 && v2 < 4294967296));
  p3 := ((v2 + 1) % 4294967296);
  assume((((v2 - (4294967296 * (v2 / 2147483648))) + 1) >= (-2147483648) && ((v2 - (4294967296 * (v2 / 2147483648))) + 1) < 2147483648));
  p4 := 0;

--unbounded-nondet, in int and int-bitwise: a __VERIFIER_nondet_int returns
any integer, written as T2's unconstrained nondet() rather than nondet_int():

  $ llvm2lts --mode int-bitwise --unbounded-nondet intmodes/bitconst_false.ll | grep 'v2 :='
  v2 := nondet();
  v2 := nondet();

It is refused with a mode that has no unbounded value:

  $ llvm2lts --mode bv --unbounded-nondet intmodes/bitconst_false.ll
  --unbounded-nondet is used only with --mode int or int-bitwise
  [2]
  $ llvm2lts --mode int-wrap-all --unbounded-nondet intmodes/bitconst_false.ll
  --unbounded-nondet is used only with --mode int or int-bitwise
  [2]
