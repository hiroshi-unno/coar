# Ptr2ArrFC: Ptr2Arr on Frama-C

A C-to-C transformation that replaces pointers by indices into per-region
arrays, written in OCaml on the Frama-C kernel (33.0 Arsenic). It is the
rewrite of `athena/Ptr2Arr` (C++ on Clang's `Rewriter` and DG's text dump).
The output is meant to be checkable: beside `ptr2arr.c` it writes a JSON
*transformation record*, and `tools/` holds the differential runner that
compares the input and the output execution by execution.

## Status

All five stages before the connection to a rewritten downstream: the normal
mode with typed and byte regions, the two safety modes and
`--wrap-integers`; and the first two parts of the SV-COMP MemSafety stage:
one violation marker per property, the input's own `reach_error` left an
ordinary function, the data model, the checks on combinations of options;
then the block table, the lifetime of `alloca` blocks and variable-length
arrays, the checks at the ends of the execution (valid-memtrack in
`--memory-safety`, and the new mode `--memory-cleanup`).

| stage | content | state |
| --- | --- | --- |
| M0 | front end, fragment check, identity rewrite, printing, record, checks | done |
| M1 | objects, points-to (Steensgaard over CIL), typed regions, rewriting, region monitor | done |
| M2 | byte regions (load/store, layout, allocation sizes) | done |
| M3 | safety modes (shadow base/length, checks) | done |
| M3w | `--wrap-integers` | done |
| M5 (part 1) | violation markers per property, `--data-model`, option combinations | done |
| M5 (part 2) | block table, `alloca`/VLA lifetime, end checks: memtrack (at the ends only), `--memory-cleanup`, `--memtrack-check` | done |
| M5 (part 3) | memtrack in executions that do not halt (`--memtrack-nonterminating`), models of `memset`, `memcpy`, `memmove`, `realloc`, `atexit`, `strlen`, `strcmp`, `strcpy`, `strncpy`, `strcat` | done |
| M6 | integer options: `--wrap-integers=all` (signed wrap-around), `--check-overflow` (SV-COMP's no-overflow) | done |
| M7 | uninitialised local variables: `--uninit=check` (a read of one whose address is never taken reaches a marker), `--uninit=nondet` (each starts with a nondeterministic value) | done |
| M8 | function pointers, by defunctionalization (`src/defunc.ml`): a function pointer value becomes a function number (NULL is 0, type `__p2a_fnid`), and a call through one becomes direct calls of the address-taken functions of a compatible type, selected by the number; a call through NULL or an invalid value calls `__p2a_bad_function_call()` (`abort()`; the invalid-dereference marker in the safety modes). Casts to and from integers and data pointers read the number (minus the number in a data pointer; D88). Function pointers given to or returned by external functions, and pointers to variadic functions stay unsupported | done |
| D80-D82 | inputs SV-COMP refused for one construct: a string literal reaching an external function through a local variable written once (`src/literalLocals.ml`); models of the input-reading `fscanf`, `scanf`, `fgets`, `atoi`, `recv`, `connect`, `bind` as functions added to the program (`src/libModels.ml`); unions whose accessed members share one type made structures of the same size and alignment (`src/unionFold.ml`) | done |
| D83-D87 | the unused `max_align_t` of an ILP32 `.i` left out of the copy the front end reads (`bin/ptr2arr.ml`); variadic functions that never read their variable arguments made fixed-arity (`src/varargsDrop.ml`); models of `memcmp`, `strncmp`, `strchr`, `strrchr`, `memchr`, GCC's unsigned overflow builtins, `__builtin_object_size`, `__VERIFIER_nondet_memory`; two front-end artefacts clang refuses removed (`src/frontendFixes.ml`); bit-fields in byte regions | done |

## Build

Needs `opam install frama-c.33.0` in the switch. The library, the plugin and
the executable are `(optional)`, so a build of the repository without Frama-C
skips them.

```sh
dune build --root athena/Ptr2ArrFC          # -> athena/Ptr2ArrFC/_build/default/bin/ptr2arr.exe
```

The command line (`cli/`, the library `frama-c-ptr2arr.cli`) is shared by
this executable and by CoAR's `main.exe`, which links the transformation in
and runs it as the first step of `-p cterm` and `-p csafe` with an Athena
configuration (`config/solver/athena*.json`). Either program runs Frama-C
in a copy of itself started with `PTR2ARR_FRAMAC_CHILD=1`, since Frama-C
reads its command line once, when its kernel is initialised; a program that
links the library calls `Ptr2arr_cli.boot_child` first thing when
`Ptr2arr_cli.is_child` holds, and must be linked with `-linkall`.

## Run

```sh
ptr2arr [--memory-safety | --memory-cleanup | --assume-safety] [-o OUT.c] [options] IN.c
ptr2arr --check [--allow-pointers] OUT.c
```

| option | meaning |
| --- | --- |
| `-o OUT.c` | output file (default `./<stem>_Ptr2Arr.c`) |
| `--record=FILE` | the record (default `<output stem>.p2a.json`) |
| `--unsupported=error\|warn` | on an unsupported construct: write nothing (default), or write anyway with exit status 3 |
| `--region-size=N` | length of each region array (default 100000) |
| `--scalar-cells` | keep a region whose only object is one alloca cell of an integer type, allocated once per call of a non-recursive function and never moved from or escaping, in a scalar variable instead of an array |
| `--unbounded-regions` | read the region arrays as having no length: no allocation exhausts a region and no index is compared with the length. For a consumer whose arrays have no length (llvm2lts); the output is not meant to be run as C |
| `--points-to=steens\|alias\|eva` | points-to analysis |
| `--wrap-integers[=unsigned\|all]` | make fixed-width integer wrap-around explicit: of the unsigned operations (default), or of the signed ones too (below) |
| `--check-overflow` | normal mode: call `reach_error()` right before a signed operation that overflows (below) |
| `--violation-markers=split\|reach-error` | with `--memory-safety` or `--memory-cleanup`: what a violation calls (below) |
| `--memtrack-check=guess\|fixpoint\|none` | with `--memory-safety` (or `--memory-cleanup --memtrack-nonterminating`): how valid-memtrack is checked (below; default guess); `none` (memory-safety only) checks no leak, so only valid-deref and valid-free |
| `--memtrack-nonterminating` | with `--memory-safety` or `--memory-cleanup`: also check where an execution that does not halt passes (below) |
| `--uninit=keep\|check\|nondet` | uninitialised local variables: as in the input (default), checked reads, or nondeterministic starting values (below) |
| `--data-model=LP64\|ILP32` | the data model the input is read in (default LP64) |
| `--line-directives` | precede every printed statement with a `#line` line naming its input line (below) |
| `--identity` | print the normalised program only (testing the tools) |
| `--monitor` | write the input instrumented with the region monitor instead |
| `--z-reading` | write an output of `--wrap-integers` as run with mathematical integers (128-bit), for testing |
| `--frama-c=ARGS` | extra arguments for the Frama-C kernel |
| `--clang=PROGRAM` | the clang that preprocesses the input (default `clang-19`), presenting the GCC version of Frama-C's machine descriptions (14.2.1), so that glibc's headers read as they do under gcc |
| `--gcc` | preprocess the input with gcc, Frama-C's own default, instead of clang |

An option given with an action that does not use it, two of `--check`,
`--identity`, `--monitor` and `--z-reading`, and an option given twice with
different values are errors (exit status 1) rather than ignored: the
transformation takes a mode and the options that shape its output;
`--check` takes `--allow-pointers`; `--identity` and `--z-reading` take
`-o`, `--record` and `--unsupported`, and `--monitor` these and
`--points-to`; every action takes `--frama-c`, `--clang`, `--gcc` and `--data-model`, and every
action that prints a program `--line-directives`.
`tests/options.sh` runs each combination against the executable and the
plugin.

Exit status: 0 written; 1 unreadable input, invalid option or internal error;
2 unsupported construct, nothing written (one line per construct on stderr);
3 written despite unsupported constructs (`--unsupported=warn`); 4 (`--check`)
the file violates an output property. Frama-C's progress messages go to
stderr. The same transformation is available as a plugin,
`frama-c -ptr2arr IN.c -ptr2arr-output OUT.c ...`, whose own exit statuses are
64, 65 and 66 for 2, 3 and 4 (Frama-C itself uses 2 and 3).

In the safety modes every pointer location also holds the first index and the
length of the block its value comes from (companion variables, parameters,
structure fields, or arrays parallel to a region), every access through a
pointer is checked against them and against the released blocks, and a
subscript of an array outside the regions against its length. In
`--assume-safety` a violation ends the execution with status 0. In
`--memory-safety` it calls a marker: with `--violation-markers=split` (the
default) `__p2a_violation_valid_deref()` for an access or a subscript and
`__p2a_violation_valid_free()` for a release, defined in the output as
noreturn functions that end the execution with status 77 and 78, so that a
violation is reported with its property as SV-COMP's MemSafety category
asks; the input's own `reach_error` is then an ordinary function of the
program. With `--violation-markers=reach-error` every violation calls
`reach_error()`, declared only, for consumers that predate the split, and
the input's own `reach_error` is renamed `__p2a_input_reach_error`. A marker
whose name the input already uses gets a fresh one; the record's
`violations` lists the markers the output calls, with their properties.

The library functions `memset`, `memcpy`, `memmove`, `realloc`, `atexit`,
`strlen`, `strcmp`, `strcpy`, `strncpy` and `strcat` are modelled in every
mode, as loops over the cells of a region (generated functions); the
safety modes check every range they read or write, `memcpy`, `memmove` and
`realloc` copy the shadows of the pointers they copy, `memset` clears them
(a pointer or structure cell only to 0), `realloc` checks its argument as
`free` does, and `atexit` keeps a table of the registered functions, run in
reverse at `exit` and after the return from `main`. A typed region given a
`memset`, `memcpy` or `memmove` size that is not a known number of cells
becomes a byte region; the string functions need character cells.

An allocation that does not fit in its region's array (the arrays are not
reused, and are `--region-size` cells long) stops a safety mode's output at
`__p2a_region_exhausted()` (status 81), which reports neither a violation
nor its absence (a consumer answers "unknown"); with
`--violation-markers=reach-error` it calls `reach_error()` instead. The
record's `region_exhausted` names it.

The safety modes keep a block table per region (the kind of each block, the
cells it occupies, released or not); a block of no bytes still occupies a
cell, and the `alloca` blocks of a function and its variable-length arrays
are released when their lifetime ends, so a use after it is a valid-deref
violation. When the program allocates a heap block, `--memory-safety` and
`--memory-cleanup` also check the ends of the execution: the return from
`main` (the input's `main` becomes `__p2a_main`, called by a new `main`),
`exit`, `abort`, `_Exit`, `__assert_fail`, and `reach_error` and
`__VERIFIER_error` when the program does not define them (a call guarded by
a null test of a fresh allocation is not an end: allocation does not fail).
`--memory-safety` reports valid-memtrack there
(`__p2a_violation_valid_memtrack()`, status 79) when a heap block is not
released and no root reaches it: the globals, the live static, local and
`alloca` blocks, and the variables of the frames on the call stack (those of
the callers of a function with an end are made local objects for this,
listed in the record's `objects` with the reason `memtrack-root`; nothing
points to such a variable, so its region is used as a stack and a block
entered on every iteration of a loop does not use up the array).
Executions that do not halt are not checked yet. `--memtrack-check=guess`
(the default) writes the check as one pass over a nondeterministically
guessed set of blocks, drawn from the weak function `__p2a_guess`;
`--memtrack-check=fixpoint` computes the reachable blocks and is what the
differential runner can execute. With `--memtrack-nonterminating` (memory
safety or memory cleanup) the check also runs at every function's entry and
every loop's head when the weak function `__p2a_probe` chooses so, and the
execution then ends (`__p2a_stop`, status 0) unless it reports, so that a
block lost by an execution that never ends is found too; in
`--memory-cleanup` such a report is valid-memcleanup. `--memory-cleanup` checks valid-deref and
valid-free as `--memory-safety` does, and reports valid-memcleanup
(`__p2a_violation_valid_memcleanup()`, status 80) at an end where a heap
block is not released. The record's `end_points` lists the checks and
`memtrack` the form. With `--wrap-integers` the output also means the C
program when its integers are read as mathematical integers: every place where
an unsigned ring expression's exact value is observed, every narrowing or
sign-changing conversion and every integer an external function returns goes
through `__p2a_wrap_k`, the identity at integer type k in C and the reduction
modulo 2^w in that reading (signed arithmetic is not reduced: without
undefined behaviour it does not overflow). With `--wrap-integers=all` signed
`+`, `-`, `*`, negation and `<<` wrap as under gcc's `-fwrapv`: a maximal
signed ring expression is computed in the unsigned type of the same width
and reduced to its signed type where it is used, so the output stays
defined C without `-fwrapv`; `INT_MIN / -1`, which traps even under
`-fwrapv`, stays excluded.

`--check-overflow` (normal mode only; not with `--wrap-integers=all`)
reports SV-COMP's no-overflow: right before each signed `+`, `-`, `*`,
negation, `/`, `%` and `<<` of the program the output calls a check function
(`__p2a_overflow_add_s32` and so on, one per operation and width) that calls
`reach_error()`, declared only, when the exact result is outside the range
of its type. A check cannot overflow itself: an addition is tested against
`MAX - b` or `MIN - b` by the sign of `b`, a product of 32-bit operands is
computed in 64 bits, a 64-bit product by CERT INT32-C's division test, a
left shift for a count in `[0, w)` against `MAX >> b` and `MIN >> b`.
Conversions to signed types, unsigned operations, division by zero and
shift counts out of range are not overflows and are not checked. An
operand that is not a constant or an lvalue is computed once, into a
temporary, after its own check; an operation on constants whose result is in
range gets no check. The input's own `reach_error` is renamed
`__p2a_input_reach_error`, and the record's `violations` lists
`reach_error` with the property `no-overflow`.

`--uninit` says what an automatic local variable declared without an
initialiser means (the front end's temporaries and the arrays of
variable-length arrays are such variables too; globals and static locals
start at zero as in C and are left alone). `keep`, the default, leaves the
output as before. Values other than `keep` go with the transformation only.
The front end moves such a declaration to the start of its block, so the
starting state is given there; a block a jump enters without passing its
start (a switch's body, a label a goto from outside reaches) gets it also at
the function's start and right before each such jump, and a goto that jumps
back over such a declaration is refused (exit status 2,
`uninit-backward-goto`), since C makes the value indeterminate again there.

- `--uninit=nondet`: each such variable starts with a nondeterministic value
  of its type: every scalar of it gets the result of a weak function
  `__p2a_uninit_<kind>()` whose body returns `__VERIFIER_nondet_<kind>()`
  (an enumeration a value of its underlying type, a pointer NULL); a
  variable-length array is filled right after its allocation. A
  `long double` has no such function and is refused. The record lists the
  functions (`uninit_generators`); `tools/p2a_uninit_zero.c` defines strong
  versions that return zero, which `p2a_diff.py --uninit nondet` links into
  the output. With `--wrap-integers` the generators' draws are reduced as
  any external function's result.
- `--uninit=check` (not with `--check-overflow`): reading such a variable,
  or an element or field of it, before it is written is C11's undefined
  behaviour (6.3.2.1p2) when its address is never taken, and the output
  then calls the marker: `reach_error()` in the normal mode (the input's
  own renamed `__p2a_input_reach_error`), in a safety mode the marker of
  the property `uninit-read` (`__p2a_violation_uninit_read()`, status 82,
  with the split markers; `reach_error()` with the reach-error markers;
  the end of the execution in `--assume-safety`). Each such variable has a
  state variable `x__init` of the same shape with every scalar an
  `unsigned char`; a read of a scalar checks its state
  (`p2a_uninit_check`), a structure read whole (assigned, passed,
  returned) must have some field written (`p2a_uninit_check_<S>`) and
  carries its state along (a structure parameter that receives one gets a
  state parameter, a function that returns one passes it in a global). A
  variable whose address is taken (an array used as a pointer, a
  variable-length array) is not checked; reading it uninitialised is not
  undefined in C11. A read that every path writes first is not checked
  (a forward must analysis over scalars; the record's `uninit_elided`), and
  `P2A_UNINIT_NO_ELIDE=1` in the environment turns that off for testing.

The front end reads the input with the system's headers (`-no-frama-c-stdlib`),
a GCC machine description and the GNU dialect for the preprocessor;
`bin/ptr2arr.ml` says why each one. `--data-model` chooses the machine
description and the preprocessor's word size together: `gcc_x86_64` and
`-m64` for LP64, `gcc_x86_32` and `-m32` for ILP32 (without `-m32` the
system headers are read as 64-bit ones). Under ILP32 the preprocessor also
defines `_GCC_MAX_ALIGN_T`, so that gcc's `stddef.h` leaves out
`max_align_t`, whose `-m32` definition has a `__float128` member the front
end cannot read; an input that uses `max_align_t` is then unreadable. The
record's `input.machdep` says which. An output of ILP32 is meant to be compiled with `-m32`; the
mathematical reading (`--z-reading`) widens integers to `__int128`, which
gcc does not have under `-m32`.

## The source map

The record's `source_map` says, for every statement the output prints, where
it is (`output_line`, `output_column`: its first character, after its
labels), in which function, the role it plays for a witness of the input,
and the position of the input statement it comes from (`input`: line,
column and function; physical positions of the input file, columns in
bytes, a tab one column): `loop-head` for the loop of an input `for` or
`while` (its head is right before the condition; a `do` loop is `other`),
`branch` for an `if` that evaluates a whole controlling expression of an
input `if`, `while`, `do` or `for` (`cond_negated`: the output prints it
negated), `target` for a call where a property is violated (`property`:
the input's `reach_error` in the normal mode, an overflow check with
`--check-overflow`, a check that reaches a violation marker in
`--memory-safety` and `--memory-cleanup`), `call` for a call of a
function of the input, and `other`. A target's input is the statement or
full expression the check guards; an end check after the return from
`main` is at `main`'s return. A statement of another file (a header of a
`.c` input) or made by the transformation has `input` null; a `.i` input's
positions are its own lines, its line markers notwithstanding. The output's
positions are counted while it is printed; the input's come from Frama-C's
untyped AST, which keeps the extent of every statement and expression (its
statement locations are not their first characters), mapped through the
preprocessor's output to the input's lines and columns.

With `--line-directives` every statement is preceded by a line
`#line N "IN.c"`, or `#line N "OUT.c"` (the output's own next line) for one
with no input position, and each function definition by the latter, so
that a compiler's debug information names input lines; the source map still counts physical lines. Such an output reads
back with `--check` and runs under `p2a_diff.py`.

## Checking an output

```sh
python3 athena/Ptr2ArrFC/tools/p2a_diff.py IN.c OUT.c [--seeds 1,2,3,4,5] [--timeout 2]
athena/Ptr2ArrFC/tests/run_tests.sh [--identity] OUTDIR   # every test input
athena/Ptr2ArrFC/tests/options.sh                         # option combinations
python3 athena/Ptr2ArrFC/tests/markers.py                 # what the markers are and who calls them
python3 athena/Ptr2ArrFC/tools/p2a_memtrack_eq.py IN.c    # the two memtrack forms agree
python3 athena/Ptr2ArrFC/tools/p2a_srcmap_check.py IN.c OUT.c OUT.p2a.json   # the source map
athena/Ptr2ArrFC/tests/source_map.sh [--diff] OUTDIR      # the source map on every test input
athena/Ptr2ArrFC/tests/integers_auto.sh [WORKDIR]         # what --integers=auto decides on its falsifying inputs
```

With `--monitor MON.c` (the output of `ptr2arr --monitor IN.c -o MON.c`) the
runner also runs the input instrumented to check, before every dereference,
that the pointer reaches an object of the region the analysis gives it
(`tools/p2a_monitor.c` is its runtime): a violation means the region
partition is unsound for that execution. The instrumented input also counts
the heap blocks left allocated at its end (`P2A_HEAP_LEFT`), the reference
for valid-memcleanup.

For `--check-overflow`, `p2a_diff.py --check-overflow --sanitize-source
NORM.c IN.c OUT.c` (NORM.c the output of `ptr2arr --identity IN.c`) takes
UndefinedBehaviorSanitizer's first report of a signed overflow on the
normalised input, whose evaluation order is the output's, as the place the
output must reach `reach_error`; `tests/mutate_overflow.sh` removes each
check of an output in turn and reports which removals some seed detects, and
`tests/overflow_conds.sh` tests every check function against gcc's
`__builtin_*_overflow` on edge and random operands in both data models.
For `--wrap-integers=all`, `p2a_diff.py --fwrapv` compiles the input with
`-fwrapv`, its reference meaning.

For `--uninit=check`, `p2a_diff.py --uninit check` takes the input built
with E-ACSL (`e-acsl-gcc` of Frama-C 33, with RTE's initialisation
annotations) as the reference: an assertion handler generated from the
record stops it at the first failure about a checked variable, and the
output must stop at its marker after the same draws. E-ACSL annotates
scalar reads only and counts a structure assigned whole as initialised in
full, so a stop the reference does not explain is reported as `struct-read`
when gdb shows it came from the check of a structure read whole, and as
`uninit-pattern` when the input built with gcc's
`-ftrivial-auto-var-init=pattern` is observed otherwise than with zero;
anything else is a false alarm. E-ACSL does not build under ILP32 (its own
headers fail with `--mbits=32`), where only those two checks remain.
`tests/mutate_uninit.sh` removes each check, state write and state copy of
an output in turn. For `--uninit=nondet`, `p2a_diff.py --uninit nondet`
links the zero generators into the output and compares as in the normal
mode.

For `--wrap-integers`, `ptr2arr --z-reading OUT.c -o Z.c` rewrites an output
to run as in the mathematical reading (integers widened to `__int128`,
integer conversions dropped, each `__p2a_wrap_k` computing the reduction), and
`p2a_diff.py IN.c Z.c` compares it with the input: a place that relies on C's
wrap-around without a reduction shows up as a different value.

`p2a_diff.py` compiles both programs with gcc against `tools/p2a_env.c`, runs
them on the same seeded nondeterministic values and compares exit status,
standard output and the trace of nondeterministic draws; seeds on which the
input shows undefined behaviour under AddressSanitizer and
UndefinedBehaviorSanitizer are excluded, since the transformation preserves
meaning only for executions without it. Memory read before it is written is
zero in both programs (automatic variables, `alloca` and `malloc` blocks), as
the output's region arrays are, so that reading uninitialised memory does not
make two correct runs differ. With `--mode memory-safety|memory-cleanup|assume-safety` a
seed with a violation is compared against where the input violated, and
with the split markers the output must stop at the marker of the property
the sanitizers' report is about (a double free or a free of what malloc did
not return is valid-free; a use after free, an overflow, a use after scope
or a null dereference valid-deref). The sanitizers say nothing about leaks:
an output that stops at its end check's marker after the same draws as the
whole run of the input gets the verdict `memtrack` or `memcleanup` (`end-stop`
with the reach-error markers, which do not say the property), which
the monitor's count judges for memcleanup and `p2a_memtrack_eq.py` (the
fixpoint form against the guess form tried with every guess, through
`tools/p2a_guess.c`) for memtrack. `--violation-markers` and `--data-model`
say how the output was made (ILP32 compiles every program with `-m32`). Its
docstring lists the verdicts.

The test inputs are `tests/cases/` (one small program per transformation rule
or past defect) and the 40 repository benchmarks named in `tests/bench.list`. The
preprocessed inputs `tests/cases/*.i` are read by `tests/source_map.sh` only,
which checks the source map of every input and the entries
`tests/source_map.expect` lists.
An input may state the exit status its output must end with, per mode, in a
comment among its first ten lines (`p2a-expect: memory-safety=78
assume-safety=0`); `run_tests.sh` checks it (column `expect`).
