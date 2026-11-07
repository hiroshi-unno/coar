Reading and checking the input.  Exit codes: 0 success, 1 UNKNOWN,
2 INPUT_ERROR, 3 INTERNAL_ERROR.

clang 19.1.7 output with -g, for x86-64 and for i386, is read:

  $ llvm2lts inputs/small64.ll
  START: start;
  TYPE v2: bv(32);
  TYPE v3: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  assume((extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 3));
  v3 := (v2 + 1);
  TO: end;
  $ llvm2lts inputs/small32.ll
  START: start;
  TYPE v2: bv(32);
  TYPE v3: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  assume((extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 3));
  v3 := (v2 + 1);
  TO: end;
  $ llvm2lts --data-model LP64 inputs/small64.ll
  START: start;
  TYPE v2: bv(32);
  TYPE v3: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  assume((extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 3));
  v3 := (v2 + 1);
  TO: end;
  $ llvm2lts --data-model ILP32 inputs/small32.ll
  START: start;
  TYPE v2: bv(32);
  TYPE v3: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  assume((extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 3));
  v3 := (v2 + 1);
  TO: end;

The task's data model must match the one the input was compiled for:

  $ llvm2lts --data-model ILP32 inputs/small64.ll
  INPUT_ERROR: the input is compiled for LP64, but ILP32 was asked for
  [2]

Every input must carry debug information:

  $ llvm2lts inputs/nodebug.ll
  INPUT_ERROR: the module has no "Debug Info Version" flag; compile with -g
  [2]

Invalid debug information is dropped by LLVM with a warning, which rejects the
input:

  $ llvm2lts inputs/baddebug.ll
  inlinable function call in a function with debug info must have a !dbg location
    %5 = call i32 @inc(i32 noundef %4)
  INPUT_ERROR: ignoring invalid debug info in inputs/baddebug.ll
  [2]

A module that fails the verifier run while parsing is an input error, not an
internal one:

  $ llvm2lts inputs/verify.ll 2>&1 | tail -1
  INPUT_ERROR: Broken module found, compilation aborted!

  $ llvm2lts inputs/verify.ll > /dev/null 2>&1
  [2]

Targets other than x86-64 and i386-i686 Linux are rejected:

  $ llvm2lts inputs/aarch64.ll
  INPUT_ERROR: target "aarch64-unknown-linux-gnu" is not x86-64 or i386-i686 Linux
  [2]

Unreadable and unparsable files:

  $ llvm2lts inputs/missing.ll
  INPUT_ERROR: inputs/missing.ll: No such file or directory
  [2]
  $ llvm2lts inputs/syntax.ll
  INPUT_ERROR: inputs/syntax.ll:1:1: error: expected top-level entity
  this is not LLVM IR
  ^
  [2]

After reading, debug information is in the intrinsic form, so a declaration's
position is an ordinary call:

  $ llvm2lts --dump-ll out.ll inputs/small64.ll
  START: start;
  TYPE v2: bv(32);
  TYPE v3: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  assume((extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 0 || extract(32, 31, (sign_extend(32, 33, v2) + sign_extend(32, 33, 1))) == 3));
  v3 := (v2 + 1);
  TO: end;
  $ grep -c 'call void @llvm.dbg.declare' out.ll
  0
  [1]
