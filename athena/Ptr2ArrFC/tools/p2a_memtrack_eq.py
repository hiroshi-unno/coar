#!/usr/bin/env python3
"""Do the two forms of the valid-memtrack check of a --memory-safety output
agree?

usage: p2a_memtrack_eq.py IN.c [--seeds 1,2,3,4,5] [--timeout 2] [--workdir DIR]
                          [--data-model LP64|ILP32] [--max-blocks 12]
                          [--nonterminating] [--max-probes 30]
       p2a_memtrack_eq.py --guess-status EXE [--seed N] [--timeout 2]
                          [--max-blocks 12]

The first form transforms IN.c with --memory-safety twice, with
--memtrack-check=fixpoint and with --memtrack-check=guess (split markers),
compiles both against tools/p2a_env.c (the guess form also against
tools/p2a_guess.c, which answers the check's choices from a mask) and, for
each seed, checks that the fixpoint output stops at the memtrack marker
(status 79) exactly when the guess output does for some choice of the set S.
S is tried in full: a run with the empty set counts the choices k (one per
live heap block at the end the check runs at), and the runs over every mask
below 2^k try every set. A seed whose k exceeds --max-blocks is skipped and
counted. One line per seed (agree, DISAGREE or skipped, with both statuses
and k); the script ends with "RESULT agree=A disagree=D skipped=S" (or
"RESULT not-transformed ..." / "RESULT compile-fail ...") and the exit
status is 1 when a seed disagrees, 2 when nothing was compared, 0 otherwise.

With --nonterminating both outputs also check where an execution that
does not halt passes (--memtrack-nonterminating): each seed is run with the
probe firing at none of its calls and at each of its first --max-probes
calls, and the two forms must agree on whether some run stops at 79.

The second form runs EXE, an output compiled with tools/p2a_guess.c (as
tools/p2a_diff.py compiles it), on one seed with every choice of S and of
the probe and prints the status a verifier can reach: a marker's status
(77 to 80) when some choice reaches one, else the status of the run with no
choice made, followed by the largest number of guesses k (with "skipped"
when a check made more than --max-blocks). tests/run_tests.sh uses it for
the expected status of an output with choices.
"""

import argparse
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import p2a_diff  # noqa: E402

EXE = os.path.join(HERE, "..", "_build", "default", "bin", "ptr2arr.exe")
MEMTRACK = 79


# The statuses a violation marker ends a run with (77 also reach_error).
MARKERS = (77, 78, 79, 80)
CHOICE_VARS = ("P2A_GUESS_MASK", "P2A_GUESS_LOG", "P2A_PROBE_AT", "P2A_PROBE_LOG")


def count_lines(path):
    if not os.path.exists(path):
        return 0
    with open(path) as f:
        return sum(1 for _ in f)


def run_chosen(exe, seed, timeout, trace, mask, probe, glog=None, plog=None):
    """A run with the guesses of [mask] and the probe firing at call [probe]
    (0: never); the calls are counted in [glog] and [plog]."""
    env = {"P2A_GUESS_MASK": str(mask), "P2A_PROBE_AT": str(probe)}
    for var, path in (("P2A_GUESS_LOG", glog), ("P2A_PROBE_LOG", plog)):
        if path:
            env[var] = path
            if os.path.exists(path):
                os.remove(path)
    os.environ.update(env)
    try:
        return p2a_diff.run(exe, seed, timeout, trace)[0]
    finally:
        for var in CHOICE_VARS:
            os.environ.pop(var, None)


def guess_status(exe, seed, timeout, work, max_blocks, max_probes=30):
    """(status, k, skipped): the status a verifier can reach on [seed]: a
    marker's status when some choice reaches one (the probe firing at one of
    its first [max_probes] calls, or at none, and some set S of the guesses),
    else the status with no choice made. k is the largest number of guesses
    a check made; a check with more than [max_blocks] is not tried in full
    (skipped)."""
    glog = os.path.join(work, "guess_%d.log" % seed)
    plog = os.path.join(work, "probe_%d.log" % seed)
    trace = os.path.join(work, "guess_%d.trace" % seed)
    st0 = run_chosen(exe, seed, timeout, trace, 0, 0, glog, plog)
    probes = min(count_lines(plog), max_probes)
    kmax, skipped = 0, False
    for probe in range(0, probes + 1):
        st = run_chosen(exe, seed, timeout, trace, 0, probe, glog)
        if st in MARKERS:
            return st, kmax, skipped
        k = count_lines(glog)
        kmax = max(kmax, k)
        if k > max_blocks:
            skipped = True
            continue
        for m in range(1, 1 << k):
            st = run_chosen(exe, seed, timeout, trace, m, probe)
            if st in MARKERS:
                return st, kmax, skipped
    return st0, kmax, skipped


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input", nargs="?")
    ap.add_argument("--guess-status", default=None)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--seeds", default="1,2,3,4,5")
    ap.add_argument("--timeout", type=float, default=2.0)
    ap.add_argument("--workdir", default=None)
    ap.add_argument("--data-model", default="LP64", choices=["LP64", "ILP32"])
    ap.add_argument("--max-blocks", type=int, default=12)
    ap.add_argument("--max-probes", type=int, default=30)
    ap.add_argument("--nonterminating", action="store_true")
    a = ap.parse_args()

    if a.guess_status:
        work = a.workdir or os.path.dirname(os.path.abspath(a.guess_status))
        st, k, skipped = guess_status(a.guess_status, a.seed, a.timeout, work, a.max_blocks,
                                      a.max_probes)
        print("%s %s%d" % (st, "skipped " if skipped else "", k))
        return 0

    if not a.input:
        ap.error("an input file is needed")
    if a.data_model == "ILP32":
        p2a_diff.ARCH_FLAGS.append("-m32")
    stem = os.path.splitext(os.path.basename(a.input))[0]
    work = a.workdir or os.path.join(os.getcwd(), "p2a_memtrack_eq_" + stem)
    os.makedirs(work, exist_ok=True)
    outs = {}
    for form in ("fixpoint", "guess"):
        out = os.path.join(work, "%s.c" % form)
        r = subprocess.run([EXE, "--memory-safety", "--memtrack-check=" + form,
                            "--data-model=" + a.data_model, "-o", out, a.input]
                           + (["--memtrack-nonterminating"] if a.nonterminating else []),
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        with open(os.path.join(work, "%s.log" % form), "wb") as f:
            f.write(r.stdout)
        if r.returncode != 0:
            print("RESULT not-transformed %s status=%d" % (form, r.returncode))
            return 2
        outs[form] = out
    exes = {}
    for form, out in outs.items():
        exe = os.path.join(work, "%s.exe" % form)
        sub = os.path.join(work, form)
        os.makedirs(sub, exist_ok=True)
        obj = p2a_diff.guess_object(out, sub)
        more = [obj] if obj else []
        if not p2a_diff.compile_c(out, exe, more=more):
            missing = p2a_diff.undefined_functions(exe + ".log")
            stubs = None
            if missing:
                stubs = os.path.join(work, "p2a_externs_%s.c" % form)
                p2a_diff.write_stubs(missing, stubs)
            if not p2a_diff.compile_c(out, exe, stubs=stubs, more=more):
                print("RESULT compile-fail %s" % form)
                return 2
        exes[form] = exe
    counts = {"agree": 0, "DISAGREE": 0, "skipped": 0}
    for s in [int(x) for x in a.seeds.split(",") if x]:
        fp, _, _ = guess_status(exes["fixpoint"], s, a.timeout, os.path.join(work, "fixpoint"),
                                a.max_blocks, a.max_probes)
        gs, k, skipped = guess_status(exes["guess"], s, a.timeout, os.path.join(work, "guess"),
                                      a.max_blocks, a.max_probes)
        if skipped:
            verdict = "skipped"
        else:
            verdict = "agree" if (fp == MEMTRACK) == (gs == MEMTRACK) else "DISAGREE"
        counts[verdict] += 1
        print("seed %d %s fixpoint=%s guess=%s k=%d" % (s, verdict, fp, gs, k))
    print("RESULT agree=%d disagree=%d skipped=%d"
          % (counts["agree"], counts["DISAGREE"], counts["skipped"]))
    if counts["DISAGREE"]:
        return 1
    return 0 if counts["agree"] else 2


if __name__ == "__main__":
    sys.exit(main())
