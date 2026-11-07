#!/usr/bin/env python3
"""Differential run of a C input and its Ptr2Arr output.

usage: p2a_diff.py ORIG.c OUT.c [--seeds 1,2,3,4,5] [--timeout 2] [--workdir DIR]
                   [--no-sanitize] [--monitor MON.c]
                   [--mode normal|memory-safety|memory-cleanup|assume-safety]
                   [--violation-markers split|reach-error]
                   [--data-model LP64|ILP32] [--check-overflow] [--fwrapv]
                   [--sanitize-source NORMALISED.c] [--uninit keep|nondet|check]

Both programs are compiled with gcc against tools/p2a_env.c and run once per
seed. A run's observation is its exit status, its standard output and its
trace (the sequence of nondeterministic draws and error events, see
p2a_env.c). For each seed:

  match        both runs finished with the same observation
  match-prefix both runs timed out and one trace and output are prefixes of the
               other's (a run that does not stop is compared as far as it went)
  DIFF         the observations differ
  inconclusive one run finished and the other timed out
  ub           the input, compiled with AddressSanitizer and
               UndefinedBehaviorSanitizer, reported a violation for this seed;
               the transformation preserves meaning only for executions without
               undefined behaviour, so the seed is not compared

With --mode memory-safety, memory-cleanup or assume-safety, OUT.c is an
output of that mode and a seed on which the input violates memory safety (under the sanitizers)
is compared rather than skipped: the output must stop where the input
violated, with the same trace up to there. Each report is read as a
violation of one property, as SV-COMP names them: valid-free for a double
free and a free of what malloc did not return, valid-deref for a use after
free, an overflow of any kind, a use after scope or return, a SEGV and
UndefinedBehaviorSanitizer's out-of-bounds index, null pointer and
misaligned address; another report has no known property. A memory-safety
or memory-cleanup output with the split markers (--violation-markers split,
the default) must end at the marker of that property: status 77 for
valid-deref and 78 for valid-free, with no event of its own in the trace,
either marker for a report of no known property. One with the reach-error markers must reach
reach_error (status 77, its event last in the trace), whatever the property.
An assume-safety output must end with status 0. The verdicts of such a seed
are match, wrong-property (the output stopped at the marker of the other
property) or missed (the output did not stop so). A seed without a
violation is compared as in the normal mode; when the observations differ,
the verdict says how: false-alarm (memory-safety, memory-cleanup: the output
stopped at a marker), truncated (assume-safety: the output ended with status 0 before the
input did; this can turn non-termination into a wrong YES), or DIFF. Neither
sanitizer reports an uninitialised pointer that is dereferenced, so a false
alarm can be the output being right.

An output of a safety mode (except with the reach-error markers) stops with
status 81 at an allocation past the end of a region's array
(__p2a_region_exhausted): a seed on which it does so after a prefix of the
input's draws has the verdict exhausted (nothing is known past there), and
the result is exhausted when no seed differs otherwise.

A memory-safety or memory-cleanup output also checks the ends of the
execution: valid-memtrack (memory-safety, marker status 79) and
valid-memcleanup (memory-cleanup, 80). The sanitizers say nothing about
either (a leak is not undefined behaviour), so a seed on which the input
violates neither valid-deref nor valid-free and the output stops at that
marker is not a false alarm when the input ended (it did not time out) and
the output made the same nondeterministic draws as the whole run of the
input: the output stopped at the input's end, where the check runs. Its
verdict is memtrack or memcleanup, a report this tool cannot judge. With the
reach-error markers the verdict is end-stop: the output reached
reach_error there, which says no property (a violation of another
property right before the end looks the same), and the environment stands
in for an input's own reach_error, renamed in the output, by calling
reach_error, so an input ending there looks the same too. For memcleanup
the monitor (--monitor) judges it: it counts the heap blocks the input
leaves allocated at its end, and a memcleanup verdict needs a count above
zero (otherwise false-alarm), while an output that ends as the input does
where the count is above zero has missed it (missed-memcleanup). For
memtrack, tools/p2a_memtrack_eq.py compares the two forms of the check. A
guess-form output (--memtrack-check=guess, the default) is linked with
tools/p2a_guess.c, which guesses the empty set unless P2A_GUESS_MASK says
otherwise, so that its check makes no nondeterministic draw and never
reports: the runs here compare the rest of the output. So is an output of
--memtrack-nonterminating, whose probes then never choose to check (unless
P2A_PROBE_AT says otherwise).

With --data-model ILP32 every program is compiled with -m32, as an output of
ptr2arr --data-model=ILP32 must be (its integer widths are ILP32's).

With --check-overflow, OUT.c is an output of ptr2arr --check-overflow
(normal mode), which calls reach_error() right before a signed operation
that overflows. A seed on which UndefinedBehaviorSanitizer's first report on
the input is such an overflow (a signed +, -, * or negation out of range,
INT_MIN / -1 or INT_MIN % -1, a left shift whose exact value is out of
range) is compared rather than skipped: the output must reach reach_error
(status 77, its event last in the trace) after the same draws, verdict
match, or else missed. The sanitized build that decides where the input
overflows should be of the normalised input (ptr2arr --identity, given as
--sanitize-source): the front end evaluates a call inside an expression
before the rest of it, an order C leaves unspecified, and gcc compiling the
raw input may evaluate the overflowing operation first, reporting it before
a draw the output makes before its check. Any other report (a shift count out of range, a left
shift of a negative value, a memory error, a division by zero) is ub as
usual. A seed without a report on which the output stops at reach_error and
the input does not is a false-alarm. The line before RESULT, "PROPERTIES
no-overflow=N", counts the seeds on which the input overflows. The
environment stands in for the input's own reach_error, renamed in the
output, by calling reach_error, so an input that only declares reach_error
and reaches it looks the same as an overflow.

With --fwrapv the input (and its sanitized build) is compiled with gcc's
-fwrapv, under which signed +, - and * wrap: the reference meaning of an
output of ptr2arr --wrap-integers=all. The output is compiled without it,
since it must not need it.

With --uninit nondet, OUT.c is an output of ptr2arr --uninit=nondet, whose
uninitialised local variables start with values drawn from weak generator
functions: the output is linked with tools/p2a_uninit_zero.c, whose strong
definitions of the generators the record lists (uninit_generators) return
zero and draw nothing. The input reads zero where it reads uninitialised
memory (see ZERO_FLAGS), so the two runs compare as in the normal mode, with
the same draws.

With --uninit check, OUT.c is an output of ptr2arr --uninit=check, which
stops at a marker when it reads a checked variable (an automatic variable
whose address is never taken, or a structure parameter that received such
a variable's state) before it is written. The reference is the input built
with E-ACSL (e-acsl-gcc) and its RTE annotations of initialisation, with an
assertion handler (generated from the record's uninit_targets) that
reports and stops at the first failure about a checked variable and lets
every other failure pass (a read through a pointer is not undefined
behaviour in C11, only that of a variable whose address is never taken).
A structure parameter that receives its argument's state is left out:
E-ACSL (Frama-C 33) reports every read of a field of a structure
parameter, its argument written or not, so such reads are judged by the
pattern build below. The instrumented code is compiled here with the
same zero-filling as the other programs, so that the reference follows the
input's run. A seed on which the reference stops so is compared rather than
compared as usual: the output must stop at the marker (77 and reach_error
last in the trace in the normal mode and with the reach-error markers, the
split marker's 82 in a safety mode, status 0 in --assume-safety) after the
same draws, verdict match, or else missed; when the sanitizers report a
violation too, the one after fewer draws is the first, and with as many
either stop is accepted. A seed on which the reference does not stop and
the output stops at the marker is a false-alarm, unless the output stopped
in the check of a structure read whole, which no reference reports (E-ACSL
annotates scalar reads only): gdb tells which check the marker was reached
from, verdict struct-read. E-ACSL also counts a structure as initialised
in full once it is assigned (or passed, or returned) whole, while a field
whose state the copy carried is still unwritten for the check; so a seed
on which the input, built with its automatic variables filled with a
pattern instead of zero (gcc's -ftrivial-auto-var-init=pattern), is
observed differently from its build with zero reads an uninitialised local
there, and its verdict is uninit-pattern (a sufficient sign only: the
local read may be one the check does not cover). Conversely, on a seed on
which neither the reference nor the output stops, a pattern build observed
otherwise than the zero build means the input read an uninitialised
automatic variable (heap and alloca blocks are zero in both builds); when
the record says every variable that starts uninitialised is checked (none
has its address taken, none is a variable-length array), the read was a
checked one the output let pass, verdict missed; otherwise it may have
been an unchecked one, verdict pattern-unreported, a note. In
--assume-safety it is always the note: the marker ends the run with status
0, so a stop at the input's last read cannot be told from its end. The line before RESULT, "PROPERTIES
uninit-read=N", counts the seeds on which the reference stops. Without
E-ACSL (or when it cannot build the input) such seeds have the verdict
no-reference.

For OUT.c an output of ptr2arr --z-reading of such an output, which has no
record of its own, --uninit-record names the transformed output's record
(for --uninit check too) and --uninit-wide makes the zero generators return
__int128, as the mathematical reading widens them.

With --monitor, MON.c (the input instrumented by ptr2arr --monitor) is also
run on every seed without undefined behaviour, and the line before RESULT is
"MONITOR ok checks=N unknown=M" or "MONITOR VIOLATION" (a dereferenced
pointer reached an object outside the region the analysis gives it: the
region partition is unsound for that execution) or "MONITOR compile-fail".

The last line is "RESULT <verdict> <counts>": DIFF if any seed differs (a
false alarm, a missed violation, ...), else compile-fail-orig /
compile-fail-out when a program does not compile, else memtrack,
memcleanup, end-stop, exhausted, struct-read, uninit-pattern,
pattern-unreported or no-reference when a seed
has that verdict, else match when at least one seed was compared, else
no-comparable-seed. In a safety mode the line before it, "PROPERTIES
<counts>", counts the seeds on which the input violates each property. The
exit status is 0 for match and the verdicts named with it, 1 for DIFF, 2
otherwise.
"""

import argparse
import os
import re
import resource
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ENV_C = os.path.join(HERE, "p2a_env.c")
# Memory a program reads before writing is zero in every program compiled
# here: automatic variables (and variable-length arrays) by gcc's
# -ftrivial-auto-var-init=zero, alloca's blocks by a redefinition of
# __builtin_alloca that fills each block (glibc's alloca expands to it), and
# malloc's blocks by MALLOC_PERTURB_ (see run). The output's region arrays
# start zero and are never reused, so a run of the output reads zero where
# the input reads uninitialised memory; without this the two runs read
# different garbage and differ though both are right (the transformation
# preserves meaning reading uninitialised memory as arbitrary, and zero is
# one such value).
ZERO_FLAGS = ["-ftrivial-auto-var-init=zero",
              "-include", os.path.join(HERE, "p2a_zero.h"),
              "-D__builtin_alloca(n)=({ unsigned long p2a_n_ = (n); "
              "p2a_zero_fill(__builtin_alloca(p2a_n_), p2a_n_); })"]
# -fgnu89-inline: an inline function gets an external definition, as in the
# GNU89 dialect. In C99's rules it does not, a call to it fails to link, and
# the stand-ins below would replace the program's own function.
CFLAGS = ["-O0", "-w", "-std=gnu11", "-fno-strict-aliasing", "-fgnu89-inline",
          "-Wno-error=implicit-function-declaration",
          "-Wno-error=int-conversion", "-Wno-error=incompatible-pointer-types"] + ZERO_FLAGS
MEMORY_LIMIT = 1 << 30
# -m32 for --data-model ILP32 (see main)
ARCH_FLAGS = []

# The exit status of each split marker of a memory-safety output, by the
# property whose violation it marks, and the trace events with which the
# environment's own functions (p2a_env.c) end a run with those statuses.
MARKER_STATUS = {"valid-deref": 77, "valid-free": 78, "valid-memtrack": 79,
                 "valid-memcleanup": 80}
# The status of __p2a_region_exhausted(): the output stopped at an allocation
# past the end of a region's array, which says nothing about the input.
EXHAUSTED = 81
# The property each safety mode checks at the ends of the execution.
END_PROPERTY = {"memory-safety": "valid-memtrack", "memory-cleanup": "valid-memcleanup"}
GUESS_C = os.path.join(HERE, "p2a_guess.c")
PROPERTY_OF_STATUS = {v: k for k, v in MARKER_STATUS.items()}
ENV_STOP_EVENTS = (b"reach_error 0", b"assume_false 0")

# AddressSanitizer's report kinds, by the property they are a violation of.
ASAN_FREE = ("attempting double-free",
             "attempting free on address which was not malloc()-ed",
             "bad-free", "alloc-dealloc-mismatch")
ASAN_DEREF = ("heap-use-after-free", "heap-buffer-overflow",
              "stack-buffer-overflow", "stack-buffer-underflow",
              "global-buffer-overflow", "dynamic-stack-buffer-overflow",
              "stack-use-after-scope", "stack-use-after-return",
              "use-after-poison", "container-overflow",
              "intra-object-overflow", "SEGV on unknown address")


def compile_c(src, exe, extra=(), stubs=None, more=()):
    # A preprocessed input (.i) is compiled as C source, so that it is
    # preprocessed again: otherwise gcc skips the preprocessor and the
    # zero-filling definitions above (-include, -D) do not reach it, and the
    # input reads garbage where the output reads zero.
    first = ["-x", "c", src, "-x", "none"] if src.endswith(".i") else [src]
    files = first + [ENV_C] + ([stubs] if stubs else []) + list(more)
    r = subprocess.run(["gcc", *CFLAGS, *ARCH_FLAGS, *extra, *files, "-o", exe],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    with open(exe + ".log", "wb") as f:
        f.write(r.stdout)
    return r.returncode == 0


def undefined_functions(log_path):
    with open(log_path, "rb") as f:
        text = f.read().decode("utf-8", "replace")
    # ld reports the first references one by one and the rest as "more
    # undefined references to `f' follow"
    return sorted(set(re.findall(r"undefined references? to [`']([A-Za-z_][A-Za-z0-9_]*)'", text)))


def write_stubs(names, path):
    """Stand-ins for external functions the input declares but never defines:
    each returns a nondeterministic integer and records the call. A function
    that returns a pointer cannot be stood in for this way; such an input is
    outside the fragment and is refused by the transformation before this
    tool sees it."""
    with open(path, "w") as f:
        f.write("long long p2a_extern_value(const char *);\n")
        for n in names:
            f.write('long long %s() { return p2a_extern_value("%s"); }\n' % (n, n))


def limit_memory():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_LIMIT, MEMORY_LIMIT))


def run(exe, seed, timeout, trace, limit=True):
    if os.path.exists(trace):
        os.remove(trace)
    # A leak is not undefined behaviour, so LeakSanitizer is off. malloc's
    # blocks are filled with the complement of MALLOC_PERTURB_ (glibc), and
    # AddressSanitizer's malloc with malloc_fill_byte: zero in both cases.
    env = dict(os.environ, P2A_SEED=str(seed), P2A_TRACE=trace,
               MALLOC_PERTURB_="255",
               ASAN_OPTIONS="detect_leaks=0:malloc_fill_byte=0:max_malloc_fill_size=2147483647")
    try:
        r = subprocess.run([exe], env=env, stdin=subprocess.DEVNULL,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           timeout=timeout,
                           preexec_fn=limit_memory if limit else None)
        status, out, err = r.returncode, r.stdout, r.stderr
    except subprocess.TimeoutExpired as e:
        status, out, err = "timeout", e.stdout or b"", e.stderr or b""
    events = []
    if os.path.exists(trace):
        with open(trace, "rb") as f:
            events = f.read().splitlines()
    return status, out, err, events


def sanitizer_reported(status, err):
    return status != 0 and (b"ERROR: AddressSanitizer" in err
                            or b"runtime error:" in err)


def memory_violation(status, err):
    """Did the sanitizers stop the run at a memory-safety violation (an
    AddressSanitizer report, or an UndefinedBehaviorSanitizer one about an
    index out of bounds, a null pointer or a misaligned address)? Other
    undefined behaviour, such as a signed overflow, is not one."""
    if status == 0:
        return False
    if b"ERROR: AddressSanitizer" in err:
        return True
    for m in re.finditer(rb"runtime error: ([^\n]*)", err):
        msg = m.group(1)
        if b"out of bounds" in msg or b"null pointer" in msg or b"misaligned" in msg:
            return True
    return False


# UndefinedBehaviorSanitizer's reports of a signed overflow in SV-COMP's
# sense (the result of a signed operation out of range): gcc 13's wording.
OVERFLOW_REPORTS = (rb"signed integer overflow",
                    rb"negation of .* cannot be represented",
                    rb"division of .* by -1 cannot be represented",
                    rb"left shift of .* by .* places cannot be represented")


def overflow_reported(status, err):
    """Is the sanitizers' first report a signed overflow (and not another
    kind of undefined behaviour or a memory error)?"""
    if status == 0 or b"ERROR: AddressSanitizer" in err:
        return False
    m = re.search(rb"runtime error: ([^\n]*)", err)
    return bool(m) and any(re.search(r, m.group(1)) for r in OVERFLOW_REPORTS)


def violated_property(err):
    """The property a sanitizer report is a violation of: "valid-free",
    "valid-deref", or None for a report of no known property (a stack
    overflow, say). Only called on a report memory_violation accepts."""
    m = re.search(rb"ERROR: AddressSanitizer: ([^\n]*)", err)
    if m:
        what = m.group(1).decode("utf-8", "replace")
        if what.startswith(ASAN_FREE):
            return "valid-free"
        if what.startswith(ASAN_DEREF):
            return "valid-deref"
        return None
    for m in re.finditer(rb"runtime error: ([^\n]*)", err):
        msg = m.group(1)
        if b"out of bounds" in msg or b"null pointer" in msg or b"misaligned" in msg:
            return "valid-deref"
    return None


def choice_functions(out_c):
    """The names of the guess and probe functions of a memory-safety or
    memory-cleanup output, from its record (OUT.p2a.json beside OUT.c);
    None for one the output does not have."""
    rec = os.path.splitext(out_c)[0] + ".p2a.json"
    try:
        import json
        with open(rec) as f:
            m = json.load(f).get("memtrack")
        if not m:
            return None, None
        return m.get("guess_function"), m.get("probe_function")
    except (OSError, ValueError):
        return None, None


def guess_object(out_c, work):
    """tools/p2a_guess.c compiled for the output's choice functions, or None
    when the output has none."""
    guess, probe = choice_functions(out_c)
    if not (guess or probe):
        return None
    defs = (["-DP2A_GUESS_NAME=" + guess] if guess else []) + \
        (["-DP2A_PROBE_NAME=" + probe] if probe else [])
    obj = os.path.join(work, "p2a_guess.o")
    r = subprocess.run(["gcc", "-c", *ARCH_FLAGS, *defs, GUESS_C, "-o", obj],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return obj if r.returncode == 0 else None


UNINIT_ZERO_C = os.path.join(HERE, "p2a_uninit_zero.c")


def uninit_object(out_c, work, rec=None, wide=False):
    """tools/p2a_uninit_zero.c compiled for the generators an --uninit=nondet
    output names in its record (REC, or the one beside OUT.c), or None when
    it has none; WIDE for an output of ptr2arr --z-reading, whose integers
    are __int128."""
    rec = rec or os.path.splitext(out_c)[0] + ".p2a.json"
    try:
        import json
        with open(rec) as f:
            gens = json.load(f).get("uninit_generators") or []
    except (OSError, ValueError):
        return None
    if not gens:
        return None
    defs = ["-DP2A_UNINIT_%s=%s" % (g["kind"], g["name"]) for g in gens]
    if wide:
        defs.append("-DP2A_UNINIT_WIDE")
    obj = os.path.join(work, "p2a_uninit_zero.o")
    r = subprocess.run(["gcc", "-c", *ARCH_FLAGS, *defs, UNINIT_ZERO_C, "-o", obj],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return obj if r.returncode == 0 else None


EACSL_ZHEAP_C = os.path.join(HERE, "p2a_eacsl_zheap.c")
EACSL_ZHEAP_H = os.path.join(HERE, "p2a_eacsl_zheap.h")
# the status the reference's assertion handler stops with
EACSL_STOP = 86

EACSL_ASSERT_TEMPLATE = r'''
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "instrumentation_model/e_acsl_assert_data.h"
static const char *p2a_checked[][2] = {
%s
  {0, 0}};
/* Is the predicate the initialisation of (a part of) a checked variable of
   the function: \initialized(&x...) with (fct, x) in the table? */
static int p2a_is_checked(const char *fct, const char *pred) {
  const char *p = "\\initialized(&";
  size_t n = strlen(p), k = 0;
  char name[256];
  int i;
  if (!fct || !pred || strncmp(pred, p, n)) return 0;
  pred += n;
  while (k < sizeof name - 1 && (isalnum((unsigned char)pred[k]) || pred[k] == '_')) {
    name[k] = pred[k];
    k++;
  }
  name[k] = 0;
  for (i = 0; p2a_checked[i][0]; i++)
    if (!strcmp(p2a_checked[i][0], fct) && !strcmp(p2a_checked[i][1], name)) return 1;
  return 0;
}
void __e_acsl_assert(int predicate, eacsl_assert_data_t *data) {
  if (predicate) return;
  if (data->name && !strcmp(data->name, "rte/initialization")
      && p2a_is_checked(data->fct, data->pred_txt)) {
    fprintf(stderr, "P2A_UNINIT_READ %%s %%s:%%d %%s\n", data->fct, data->file, data->line,
            data->pred_txt);
    fflush(stderr);
    _Exit(%d);
  }
  fprintf(stderr, "P2A_EACSL_OTHER %%s %%s %%s:%%d %%s\n", data->name ? data->name : "",
          data->fct ? data->fct : "", data->file ? data->file : "", data->line,
          data->pred_txt ? data->pred_txt : "");
}
'''


def read_record(out_c):
    """The record of OUT.c (OUT.p2a.json), or the record named itself."""
    rec = out_c if out_c.endswith(".json") else os.path.splitext(out_c)[0] + ".p2a.json"
    try:
        import json
        with open(rec) as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def eacsl_reference(orig, out_c, work, stubs):
    """The input built with E-ACSL as the reference of --uninit check, or
    None (with a note) when it cannot be built."""
    import shutil
    tool = shutil.which("e-acsl-gcc")
    if not tool:
        print("note: e-acsl-gcc not found; no reference for uninitialised reads")
        return None
    prefix = os.path.dirname(os.path.dirname(os.path.realpath(tool)))
    share = os.path.join(prefix, "share", "frama-c", "share", "e-acsl")
    lib = os.path.join(prefix, "lib", "frama-c-e-acsl", "libeacsl-dlmalloc.a")
    rec = read_record(out_c)
    # not the structure parameters: E-ACSL (Frama-C 33) does not count a
    # parameter's copy of its argument as initialised, and reports every read
    # of one of its fields, written or not
    pairs = [(t["function"], t.get("variable", t["name"]))
             for t in rec.get("uninit_targets", []) if t.get("checked")]
    rows = "\n".join('  {"%s", "%s"},' % (f, v) for f, v in pairs)
    asrt = os.path.join(work, "p2a_eacsl_assert.c")
    with open(asrt, "w") as f:
        f.write(EACSL_ASSERT_TEMPLATE % (rows, EACSL_STOP))
    inst = os.path.join(work, "eacsl_inst.c")
    mbits = ["--mbits=32"] if ARCH_FLAGS == ["-m32"] else []
    log = os.path.join(work, "eacsl.log")
    with open(log, "wb") as lf:
        r = subprocess.run([tool, "-n", *mbits, "--rte=pointer-call",
                            "-F", "-rte-initialized=@all", "-o", inst, os.path.abspath(orig)],
                           stdout=lf, stderr=subprocess.STDOUT, cwd=work)
    if r.returncode != 0 or not os.path.exists(inst):
        print("note: E-ACSL could not instrument the input (see eacsl.log); "
              "no reference for uninitialised reads")
        return None
    defs = ["-DE_ACSL_SEGMENT_MMODEL", "-DE_ACSL_EXTERNAL_ASSERT", "-I" + share]
    objs = []
    for src, flags in ((inst, ["-std=gnu11", "-O0", *ZERO_FLAGS, "-include", EACSL_ZHEAP_H]),
                       (os.path.join(share, "e_acsl_rtl.c"), ["-std=c99", "-O2"]),
                       (asrt, ["-std=gnu11", "-O0"]),
                       (EACSL_ZHEAP_C, ["-std=gnu11", "-O0"]),
                       (ENV_C, ["-std=gnu11", "-O0"])):
        obj = os.path.join(work, os.path.basename(src) + ".eacsl.o")
        cmd = ["gcc", "-c", "-w", "-g", "-fno-builtin", *ARCH_FLAGS, *defs, *flags, src, "-o", obj]
        with open(log, "ab") as lf:
            r = subprocess.run(cmd, stdout=lf, stderr=subprocess.STDOUT)
        if r.returncode != 0:
            print("note: the E-ACSL build of the input does not compile (see eacsl.log); "
                  "no reference for uninitialised reads")
            return None
        objs.append(obj)
    exe = os.path.join(work, "orig_eacsl.exe")
    with open(log, "ab") as lf:
        r = subprocess.run(["gcc", *ARCH_FLAGS, *objs, *([stubs] if stubs else []), lib,
                            "-lgmp", "-lm", "-o", exe], stdout=lf, stderr=subprocess.STDOUT)
    if r.returncode != 0:
        print("note: the E-ACSL build of the input does not link (see eacsl.log); "
              "no reference for uninitialised reads")
        return None
    return exe


def eacsl_stop(obs):
    """The reference stopped at an uninitialised read of a checked
    variable: its report line, or None."""
    status, _, err, _ = obs
    if status != EACSL_STOP:
        return None
    m = re.search(rb"P2A_UNINIT_READ ([^\n]*)", err)
    return m.group(1).decode("utf-8", "replace") if m else None


def stopped_at_uninit(p, mode, markers):
    """Did a run of a --uninit=check output stop at its marker? (In
    --assume-safety the marker ends the run with status 0, which only the
    draws can tell from an end.)"""
    status, _, _, events = p
    if mode == "normal" or markers == "reach-error":
        return status == 77 and events[-1:] == [b"reach_error 0"]
    if mode == "assume-safety":
        return status == 0
    return status == 82 and not (events and events[-1] in ENV_STOP_EVENTS)


def uninit_stop_ok(p, ref_events, mode, markers):
    """Did the output stop at the marker after the reference's draws?"""
    status, _, _, events = p
    if mode == "normal" or markers == "reach-error":
        return status == 77 and events[-1:] == [b"reach_error 0"] and events[:-1] == ref_events
    if mode == "assume-safety":
        return status == 0 and events == ref_events
    return status == 82 and events == ref_events


def stopped_in_struct_check(out_exe, out_c, seed, timeout):
    """Run the output under gdb on [seed]: was the marker reached from the
    check of a structure read whole (a generated function whose name starts
    with p2a_uninit_check_)?"""
    import shutil
    gdb = shutil.which("gdb")
    if not gdb:
        return False
    env = dict(os.environ, P2A_SEED=str(seed), P2A_TRACE=os.devnull)
    cmd = [gdb, "-batch", "-nx", "-ex", "set pagination off", "-ex", "set breakpoint pending on",
           "-ex", "break reach_error", "-ex", "break __p2a_violation_uninit_read",
           "-ex", "break _Exit", "-ex", "run", "-ex", "bt", "--args", out_exe]
    try:
        r = subprocess.run(cmd, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=max(timeout * 10, 20))
    except subprocess.TimeoutExpired:
        return False
    return re.search(rb"in p2a_uninit_check_\w+ ", r.stdout) is not None


def draws(events):
    """The events of a trace other than the environment's stop events."""
    return [e for e in events if e not in ENV_STOP_EVENTS]


def stopped_at_end(o, p, mode, markers):
    """Did the output stop at the marker of its end check (or at reach_error
    with the reach-error markers) after the same draws as the whole run of
    the input, which ended? Then it stopped where the input ended."""
    (so, _, _, to), (sp, _, _, tp) = o, p
    if so == "timeout" or mode not in END_PROPERTY:
        return False
    if markers == "reach-error":
        return sp == 77 and tp[-1:] == [b"reach_error 0"] and draws(tp[:-1]) == draws(to)
    return (sp == MARKER_STATUS[END_PROPERTY[mode]]
            and not (tp and tp[-1] in ENV_STOP_EVENTS) and tp == draws(to))


def stopped_at_marker(obs, markers):
    """Did a run of a memory-safety output stop at a violation marker? A
    split marker exits with its status and leaves no event; reach_error is
    the environment's, exiting with 77."""
    status, _, _, events = obs
    if markers == "reach-error":
        return status == 77
    return status in PROPERTY_OF_STATUS and not (events and events[-1] in ENV_STOP_EVENTS)


def is_prefix(a, b):
    return len(a) <= len(b) and b[:len(a)] == a


def compare(o, p):
    (so, oo, _, to), (sp, op, _, tp) = o, p
    if so != "timeout" and sp != "timeout":
        same = so == sp and oo == op and to == tp
        return "match" if same else "DIFF"
    if so == "timeout" and sp == "timeout":
        ok = ((is_prefix(to, tp) or is_prefix(tp, to))
              and (is_prefix(oo, op) or is_prefix(op, oo)))
        return "match-prefix" if ok else "DIFF"
    # One run stopped and the other did not: if what the stopped run did is
    # not a prefix of what the other did, they differ; otherwise nothing is
    # known (the slower run might stop later with the same observation).
    stopped, running = (o, p) if so != "timeout" else (p, o)
    if not (is_prefix(stopped[3], running[3]) and is_prefix(stopped[1], running[1])):
        return "DIFF"
    return "inconclusive"


def describe(obs):
    status, out, _, events = obs
    return "status=%s stdout=%dB events=%d" % (status, len(out), len(events))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("orig")
    ap.add_argument("out")
    ap.add_argument("--seeds", default="1,2,3,4,5")
    ap.add_argument("--timeout", type=float, default=2.0)
    ap.add_argument("--workdir", default=None)
    ap.add_argument("--no-sanitize", action="store_true")
    ap.add_argument("--monitor", default=None)
    ap.add_argument("--mode", default="normal",
                    choices=["normal", "memory-safety", "memory-cleanup", "assume-safety"])
    ap.add_argument("--violation-markers", default="split",
                    choices=["split", "reach-error"])
    ap.add_argument("--data-model", default="LP64", choices=["LP64", "ILP32"])
    ap.add_argument("--check-overflow", action="store_true")
    ap.add_argument("--fwrapv", action="store_true")
    ap.add_argument("--sanitize-source", default=None)
    ap.add_argument("--uninit", default="keep", choices=["keep", "nondet", "check"])
    ap.add_argument("--uninit-record", default=None)
    ap.add_argument("--uninit-wide", action="store_true")
    a = ap.parse_args()
    # an output of --unbounded-regions reads its arrays as having no length:
    # run as C it writes past their end on a large allocation, so it is not
    # compared execution by execution
    if read_record(a.out).get("unbounded_regions"):
        print("RESULT unbounded-regions (the output is not meant to be run as C)")
        return 2
    orig_flags = ["-fwrapv"] if a.fwrapv else []
    if a.data_model == "ILP32":
        ARCH_FLAGS.append("-m32")
    seeds = [int(s) for s in a.seeds.split(",") if s]
    work = a.workdir or os.path.join(os.path.dirname(os.path.abspath(a.out)),
                                     "p2a_diff_" + os.path.basename(a.out))
    os.makedirs(work, exist_ok=True)
    # absolute, since the E-ACSL build runs in it
    work = os.path.abspath(work)
    orig_exe = os.path.join(work, "orig.exe")
    san_exe = os.path.join(work, "orig_san.exe")
    out_exe = os.path.join(work, "out.exe")

    # stand-ins for the external functions either program calls and neither
    # defines, the same for both
    stubs = None
    missing = set()
    guess = guess_object(a.out, work) if a.mode in END_PROPERTY else None
    out_more = [guess] if guess else []
    if a.uninit == "nondet":
        zero = uninit_object(a.out, work, a.uninit_record, a.uninit_wide)
        if zero:
            out_more.append(zero)
    for src, exe, more, extra in ((a.orig, orig_exe, [], orig_flags),
                                  (a.out, out_exe, out_more, [])):
        if not compile_c(src, exe, extra=extra, more=more):
            missing |= set(undefined_functions(exe + ".log"))
    if missing:
        stubs = os.path.join(work, "p2a_externs.c")
        write_stubs(sorted(missing), stubs)
        print("note: stand-ins for undefined external functions: " + " ".join(sorted(missing)))
    if not compile_c(a.orig, orig_exe, extra=orig_flags, stubs=stubs):
        print("RESULT compile-fail-orig")
        return 2
    sanitize = not a.no_sanitize
    if sanitize and not compile_c(a.sanitize_source or a.orig, san_exe,
                                  ["-fsanitize=address,undefined",
                                   "-fno-sanitize-recover=all", "-g"] + orig_flags,
                                  stubs=stubs):
        print("note: the input does not compile with sanitizers; seeds are "
              "compared without excluding undefined behaviour")
        sanitize = False
    if not compile_c(a.out, out_exe, stubs=stubs, more=out_more):
        print("RESULT compile-fail-out")
        return 2

    mon_exe = None
    monitor = {"checks": 0, "unknown": 0, "violation": None}
    if a.monitor:
        mon_exe = os.path.join(work, "monitor.exe")
        mon_rt = os.path.join(HERE, "p2a_monitor.c")
        if not compile_c(a.monitor, mon_exe, stubs=stubs, extra=[mon_rt]):
            mon_exe = None
            monitor["violation"] = "compile-fail"

    def run_monitor(seed):
        """Runs the monitor on [seed]; the heap blocks it counts left at the
        end of the execution, or None when the run reached no end."""
        st, _, err, _ = run(mon_exe, seed, a.timeout,
                            os.path.join(work, "mon_%d.trace" % seed))
        left = None
        for line in err.decode("utf-8", "replace").splitlines():
            if line.startswith("P2A_REGION_CHECKS "):
                monitor["checks"] += int(line.split()[1])
            elif line.startswith("P2A_REGION_UNKNOWN "):
                monitor["unknown"] += int(line.split()[1])
            elif line.startswith("P2A_REGION_VIOLATION") and not monitor["violation"]:
                monitor["violation"] = "seed %d: %s" % (seed, line)
            elif line.startswith("P2A_HEAP_LEFT "):
                left = int(line.split()[1])
        return left

    rec_of = a.uninit_record or a.out
    ref_exe = eacsl_reference(a.orig, rec_of, work, stubs) if a.uninit == "check" else None
    all_checked = all(t.get("checked") for t in read_record(rec_of).get("uninit_targets", []))
    pattern = {}

    def pattern_differs(seed, o):
        """Is the input's run on [seed], its automatic variables filled
        with gcc's pattern, observed differently from [o], its run with
        them zero?"""
        if "exe" not in pattern:
            exe = os.path.join(work, "orig_pattern.exe")
            flags = [f.replace("-ftrivial-auto-var-init=zero", "-ftrivial-auto-var-init=pattern")
                     for f in CFLAGS]
            r = subprocess.run(["gcc", *flags, *ARCH_FLAGS, *orig_flags,
                                *(["-x", "c", a.orig, "-x", "none"] if a.orig.endswith(".i")
                                  else [a.orig]), ENV_C, *([stubs] if stubs else []), "-o", exe],
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            pattern["exe"] = exe if r.returncode == 0 else None
        if not pattern["exe"]:
            return False
        q = run(pattern["exe"], seed, a.timeout, os.path.join(work, "pattern_%d.trace" % seed))
        return compare(o, q) != "match"

    counts = {}
    properties = {}
    for s in seeds:
        if ref_exe:
            ref = run(ref_exe, s, max(a.timeout, 5.0), os.path.join(work, "eacsl_%d.trace" % s),
                      limit=False)
            where = eacsl_stop(ref)
            if where:
                # the sanitizers' report, when there is one, decides which
                # violation comes first: the one after fewer draws
                first, tie = True, False
                if sanitize:
                    san = run(san_exe, s, max(a.timeout, 5.0),
                              os.path.join(work, "san_%d.trace" % s), limit=False)
                    if sanitizer_reported(san[0], san[2]):
                        ns, nr = len(draws(san[3])), len(draws(ref[3]))
                        first, tie = nr < ns, nr == ns
                if first or tie:
                    properties["uninit-read"] = properties.get("uninit-read", 0) + 1
                    p = run(out_exe, s, a.timeout, os.path.join(work, "out_%d.trace" % s))
                    ok = uninit_stop_ok(p, ref[3], a.mode, a.violation_markers)
                    if ok:
                        verdict = "match"
                    elif tie:
                        # the input stops at the other violation as early: the
                        # output may report either
                        verdict = "ub"
                    else:
                        verdict = "missed"
                    counts[verdict] = counts.get(verdict, 0) + 1
                    print("seed %d %s (the input reads uninitialised: %s) out[%s]"
                          % (s, verdict, where, describe(p)))
                    continue
        if sanitize:
            san = run(san_exe, s, max(a.timeout, 5.0),
                      os.path.join(work, "san_%d.trace" % s), limit=False)
            if sanitizer_reported(san[0], san[2]):
                if a.check_overflow and overflow_reported(san[0], san[2]):
                    properties["no-overflow"] = properties.get("no-overflow", 0) + 1
                    p = run(out_exe, s, a.timeout, os.path.join(work, "out_%d.trace" % s))
                    ok = p[0] == 77 and p[3][-1:] == [b"reach_error 0"] and p[3][:-1] == san[3]
                    verdict = "match" if ok else "missed"
                    counts[verdict] = counts.get(verdict, 0) + 1
                    print("seed %d %s (the input overflows) out[%s]" % (s, verdict, describe(p)))
                    continue
                if a.mode == "normal" or not memory_violation(san[0], san[2]):
                    # undefined behaviour that is not a memory-safety
                    # violation is outside every mode's claim
                    verdict = "ub"
                    counts[verdict] = counts.get(verdict, 0) + 1
                    print("seed %d ub" % s)
                    continue
                prop = violated_property(san[2])
                properties[prop or "unknown"] = properties.get(prop or "unknown", 0) + 1
                p = run(out_exe, s, a.timeout, os.path.join(work, "out_%d.trace" % s))
                if p[0] == EXHAUSTED and is_prefix(draws(p[3]), draws(san[3])):
                    verdict = "exhausted"
                elif a.mode in END_PROPERTY and a.violation_markers == "reach-error":
                    ok = p[0] == 77 and p[3][:-1] == san[3] and p[3][-1:] == [b"reach_error 0"]
                    verdict = "match" if ok else "missed"
                elif a.mode in END_PROPERTY:
                    if p[0] in PROPERTY_OF_STATUS and p[3] == san[3]:
                        right = prop is None or PROPERTY_OF_STATUS[p[0]] == prop
                        verdict = "match" if right else "wrong-property"
                    else:
                        verdict = "missed"
                else:
                    verdict = "match" if p[0] == 0 and p[3] == san[3] else "missed"
                counts[verdict] = counts.get(verdict, 0) + 1
                print("seed %d %s (the input violates %s) out[%s]"
                      % (s, verdict, prop or "memory safety, property unknown", describe(p)))
                continue
        o = run(orig_exe, s, a.timeout, os.path.join(work, "orig_%d.trace" % s))
        p = run(out_exe, s, a.timeout, os.path.join(work, "out_%d.trace" % s))
        left = run_monitor(s) if mon_exe else None
        verdict = compare(o, p)
        if (verdict != "match" and a.mode != "normal" and p[0] == EXHAUSTED
                and (is_prefix(draws(p[3]), draws(o[3]))
                     # the input timed out before the output ran out
                     or (o[0] == "timeout" and is_prefix(draws(o[3]), draws(p[3]))))):
            # the output stopped where it ran out of cells, after a prefix of
            # the input's draws: no comparison past there
            verdict = "exhausted"
        end = "memtrack" if a.mode == "memory-safety" else "memcleanup"
        if a.violation_markers == "reach-error":
            end = "end-stop"
        if verdict == "exhausted":
            pass
        elif (verdict == "match" and a.uninit == "check" and o[0] != "timeout"
              and pattern_differs(s, o)):
            # the input read an uninitialised automatic variable, and
            # neither the reference nor the output stopped
            # (in --assume-safety the marker ends the run with status 0, so an
            # output that stopped at its last read looks the same as one that
            # ran to the end: there the sign stays a note)
            verdict = ("missed" if all_checked and a.mode != "assume-safety"
                       else "pattern-unreported")
        elif (verdict != "match" and a.uninit == "check"
              and stopped_at_uninit(p, a.mode, a.violation_markers)
              and is_prefix(draws(p[3]), draws(o[3]))):
            # the output stopped at the uninitialised-read marker, where the
            # reference (when there is one) found no such read
            if stopped_in_struct_check(out_exe, a.out, s, a.timeout):
                verdict = "struct-read"
            elif pattern_differs(s, o):
                verdict = "uninit-pattern"
            elif ref_exe:
                verdict = "false-alarm"
            else:
                verdict = "no-reference"
        elif verdict == "DIFF" and stopped_at_end(o, p, a.mode, a.violation_markers):
            verdict = end
            if a.mode == "memory-cleanup" and mon_exe and left == 0:
                verdict = "false-alarm"
        elif (verdict == "DIFF" and a.mode in END_PROPERTY
                and stopped_at_marker(p, a.violation_markers)):
            verdict = "false-alarm"
        elif (verdict == "DIFF" and a.check_overflow and p[0] == 77
              and p[3][-1:] == [b"reach_error 0"]):
            verdict = "false-alarm"
        elif (verdict == "DIFF" and a.mode == "assume-safety" and p[0] == 0
              and is_prefix(p[3], o[3])):
            verdict = "truncated"
        elif (verdict == "match" and a.mode == "memory-cleanup" and mon_exe
              and left and o[0] != "timeout"):
            # the input left heap blocks allocated at its end, and the output
            # ended as it did: a miss, unless both ended at reach_error, where
            # the reach-error marker and the input's own reach_error look the
            # same; the check runs before the input's end, so with blocks left
            # the output stopped at the marker
            if a.violation_markers == "reach-error" and p[3][-1:] == [b"reach_error 0"]:
                verdict = "end-stop"
            else:
                verdict = "missed-memcleanup"
        counts[verdict] = counts.get(verdict, 0) + 1
        print("seed %d %s orig[%s] out[%s]%s" % (s, verdict, describe(o), describe(p),
                                                 "" if left is None else " heap-left=%d" % left))

    if a.monitor:
        v = monitor["violation"]
        if v == "compile-fail":
            print("MONITOR compile-fail")
        elif v:
            print("MONITOR VIOLATION " + v)
        else:
            print("MONITOR ok checks=%d unknown=%d" % (monitor["checks"], monitor["unknown"]))

    if a.mode != "normal" or a.check_overflow or a.uninit == "check":
        print("PROPERTIES " + (" ".join("%s=%d" % kv for kv in sorted(properties.items()))
                               or "none"))
    summary = " ".join("%s=%d" % kv for kv in sorted(counts.items()))
    if any(counts.get(k) for k in ("DIFF", "missed", "false-alarm", "truncated",
                                   "wrong-property", "missed-memcleanup")):
        print("RESULT DIFF " + summary)
        return 1
    # a reported leak, which this tool cannot judge, is named in the result
    for end in ("memtrack", "memcleanup", "end-stop", "exhausted", "struct-read",
                "uninit-pattern", "pattern-unreported", "no-reference"):
        if counts.get(end):
            print("RESULT %s %s" % (end, summary))
            return 0
    if counts.get("match") or counts.get("match-prefix"):
        print("RESULT match " + summary)
        return 0
    print("RESULT no-comparable-seed " + summary)
    return 2


if __name__ == "__main__":
    sys.exit(main())
