The translated part of a module, and the check that it uses only what the
translation supports, run after llvm2lts's passes.  The inputs are clang
19.1.7 output with the flags llvm2lts expects.

The SV-COMP task functions, local and global arrays, a struct, a
variable-length array, memcpy and memset from initialisers, abs and
__builtin_add_overflow are accepted; the body of reach_error and an
unreached function using floating point are not looked at:

  $ llvm2lts scope/accepted.ll > /dev/null

A call of a modelled external that glibc declares __leaf__, which clang 19
reads as the attribute nocallback (preprocessed tasks carry it on
__assert_fail and abort), is accepted:

  $ llvm2lts scope/leaf.ll > /dev/null

srand, rand and time(NULL), with which the Juliet tasks seed and draw, are
modelled: srand changes nothing, rand is a value in [0, RAND_MAX] (glibc's
2^31 - 1) and time(NULL) any value of its type:

  $ llvm2lts --mode int-wrap-unsigned scope/randtime.ll | grep -q 'assume((v[0-9]* >= 0 && v[0-9]* <= 2147483647))' && echo modelled
  modelled
  $ llvm2lts scope/randtime.ll | grep -q 'assume((v[0-9]* >= 0 && v[0-9]* <= 2147483647))' && echo modelled
  modelled

time with an argument other than NULL would write through it, and is refused:

  $ llvm2lts scope/timeptr.ll
  UNKNOWN: main, line 6: time with an argument other than NULL
  [1]

socket, listen, accept with null address arguments and close, which the
Juliet socket tasks call, are modelled: socket and accept give a value >= -1
read as signed (any descriptor, or the failure value), listen and close 0
or -1; a result nothing uses (the first close) gives no command.  The
inputs from here to socket2.ll are written by hand in clang's form (their
C is beside them):

  $ llvm2lts scope/socket.ll | grep -c 'assume(v[0-9]* >= (-1));'
  4
  $ llvm2lts scope/socket.ll | grep -c 'assume((v[0-9]* == 0 || v[0-9]* == (-1)));'
  4
  $ llvm2lts --mode int-wrap-unsigned scope/socket.ll | grep -c 'v[0-9]* := nondet();'
  8

htons and htonl reverse the bytes of their argument read as unsigned, with
division and remainder by powers of 256 (27015 becomes 34665, 0x84030201
becomes 0x01020384, an argument int reads as negative first reduced into
[0, 2^32)), and inet_addr of the constant "127.0.0.1" is 0x0100007F:

  $ llvm2lts scope/byteswap.ll
  START: start;
  TYPE t3: bv(16);
  TYPE t8: bv(32);
  TYPE v10: bv(32);
  TYPE v2: bv(16);
  TYPE v4: bv(32);
  TYPE v7: bv(32);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  t3 := 27015;
  v2 := (((t3 urem 256) * 256) + (t3 udiv 256));
  v4 := zero_extend(16, 32, v2);
  assume(v4 != 34665);
  TO: b5;
  
  FROM: b1;
  t3 := 27015;
  v2 := (((t3 urem 256) * 256) + (t3 udiv 256));
  v4 := zero_extend(16, 32, v2);
  assume(!(v4 != 34665));
  TO: b6;
  
  FROM: b6;
  t8 := (-2080177663);
  v7 := (((((t8 urem 256) * 16777216) + (((t8 udiv 256) urem 256) * 65536)) + (((t8 udiv 65536) urem 256) * 256)) + (t8 udiv 16777216));
  assume(v7 != 16909188);
  TO: b5;
  
  FROM: b6;
  t8 := (-2080177663);
  v7 := (((((t8 urem 256) * 16777216) + (((t8 udiv 256) urem 256) * 65536)) + (((t8 udiv 65536) urem 256) * 256)) + (t8 udiv 16777216));
  assume(!(v7 != 16909188));
  TO: b9;
  
  FROM: b9;
  v10 := 16777343;
  assume(v10 != 16777343);
  TO: b5;
  
  FROM: b9;
  v10 := 16777343;
  assume(!(v10 != 16777343));
  TO: b11;
  
  FROM: b11;
  TO: end;
  
  FROM: b5;
  TO: error;
  $ llvm2lts --mode int scope/byteswap.ll
  START: start;
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  t3 := (((27015 % 65536) + 65536) % 65536);
  v2 := (((t3 % 256) * 256) + (t3 / 256));
  v4 := v2;
  assume(v4 != 34665);
  TO: b5;
  
  FROM: b1;
  t3 := (((27015 % 65536) + 65536) % 65536);
  v2 := (((t3 % 256) * 256) + (t3 / 256));
  v4 := v2;
  assume(!(v4 != 34665));
  TO: b6;
  
  FROM: b6;
  t8 := ((((-2080177663) % 4294967296) + 4294967296) % 4294967296);
  v7 := (((((t8 % 256) * 16777216) + (((t8 / 256) % 256) * 65536)) + (((t8 / 65536) % 256) * 256)) + (t8 / 16777216));
  assume(v7 != 16909188);
  TO: b5;
  
  FROM: b6;
  t8 := ((((-2080177663) % 4294967296) + 4294967296) % 4294967296);
  v7 := (((((t8 % 256) * 16777216) + (((t8 / 256) % 256) * 65536)) + (((t8 / 65536) % 256) * 256)) + (t8 / 16777216));
  assume(!(v7 != 16909188));
  TO: b9;
  
  FROM: b9;
  v10 := 16777343;
  assume(v10 != 16777343);
  TO: b5;
  
  FROM: b9;
  v10 := 16777343;
  assume(!(v10 != 16777343));
  TO: b11;
  
  FROM: b11;
  TO: end;
  
  FROM: b5;
  TO: error;

imaxabs reads as llvm.abs.i64 with poison at INTMAX_MIN, and the
declaration of an alias scope translates to nothing:

  $ llvm2lts scope/imaxabs.ll
  START: start;
  TYPE v2: bv(64);
  TYPE v3: bv(64);
  ERROR: error;
  
  FROM: start;
  TO: b1;
  
  FROM: b1;
  v2 := nondet();
  assume((v2 == 0 || v2 != (-v2)));
  assume(v2 < 0);
  v3 := (-v2);
  TO: b1_4;
  
  FROM: b1;
  v2 := nondet();
  assume((v2 == 0 || v2 != (-v2)));
  assume(!(v2 < 0));
  v3 := v2;
  TO: b1_4;
  
  FROM: b1_4;
  assume(v3 < 0);
  TO: b5;
  
  FROM: b1_4;
  assume(!(v3 < 0));
  TO: b6;
  
  FROM: b6;
  TO: end;
  
  FROM: b5;
  TO: error;
  $ llvm2lts --mode int-wrap-unsigned scope/imaxabs.ll | grep 'assume(v2 != 9223372036854775808);'
  assume(v2 != 9223372036854775808);
  assume(v2 != 9223372036854775808);

htons above is declared as glibc declares it, __attribute__((const)), which
clang reads as willreturn and memory(none) on the declaration and the call:
promises every model that returns and touches no variable of the program
keeps.  An external that does not return cannot keep willreturn, and the
promise is refused there:

  $ llvm2lts scope/abortwr.ll
  UNKNOWN: main: the call has the attribute willreturn
  [1]

accept with an address argument other than NULL would write through it,
inet_addr is read only on a constant decimal dotted quad (not on a writable
array, nor on the hexadecimal form), and a modelled external declared with
another type is refused:

  $ llvm2lts scope/acceptptr.ll
  UNKNOWN: main: accept with an address argument other than NULL
  [1]
  $ llvm2lts scope/inetvar.ll
  UNKNOWN: main: inet_addr of anything but a constant decimal dotted quad
  [1]
  $ llvm2lts scope/inethex.ll
  UNKNOWN: main: inet_addr of anything but a constant decimal dotted quad
  [1]
  $ llvm2lts scope/socket2.ll
  UNKNOWN: main: socket is not declared as int (int, int, int)
  [1]

main returning void, as the SV-COMP tasks from Linux drivers write it, is
accepted; its return moves to the end location as int main's does:

  $ llvm2lts scope/voidmain.ll | grep -c 'TO: end;'
  1

A volatile access is read as an ordinary one:

  $ llvm2lts scope/volatile.ll
  START: start;
  TYPE m2: bv(32);
  TYPE v3: bv(32);
  TYPE v4: bv(32);
  TYPE v5: bv(32);
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
  TO: end;

What makes the answer UNKNOWN (exit code 1), with the place and the reason:

  $ llvm2lts scope/fnptr.ll
  UNKNOWN: main, line 4: indirect call (through a function pointer)
  [1]
  $ llvm2lts scope/float.ll
  UNKNOWN: main, line 2: the instruction sitofp
  [1]
  $ llvm2lts scope/malloc.ll
  UNKNOWN: main, line 2: call to malloc (Ptr2Arr is expected to have turned the heap into arrays)
  [1]
  $ llvm2lts scope/external.ll
  UNKNOWN: main, line 2: call to the external function getchar
  [1]
  $ llvm2lts scope/union.ll
  UNKNOWN: main: a local variable of type %union.U = type { i32 }
  [1]
  $ llvm2lts scope/asm.ll
  UNKNOWN: main, line 1: inline assembly
  [1]
  $ llvm2lts scope/mainargs.ll
  UNKNOWN: main: its parameter 1 is used
  [1]
  $ llvm2lts scope/extglobal.ll
  UNKNOWN: main, line 2: the global variable g is declared but not defined
  [1]

A pointer passed to a defined function is accepted once inlining has removed
the call:

  $ llvm2lts scope/ptrparam.ll
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

A __VERIFIER_nondet_T or __VERIFIER_assume the module defines is translated
by its definition, not by the model: this __VERIFIER_nondet_int returns 0,
and this __VERIFIER_assume exits when its condition is false, so for
termination the path ends at `end` rather than looping at `diverge`:

  $ llvm2lts scope/defnondet.ll | grep -c 'nondet'
  0
  [1]
  $ llvm2lts --property termination scope/defassume.ll | grep -c 'diverge'
  0
  [1]
  $ llvm2lts --property termination scope/defassume.ll | grep -c 'TO: end;'
  2

