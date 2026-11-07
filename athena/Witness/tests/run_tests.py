#!/usr/bin/env python3
"""The tests of athena-witness.

usage: tests/run_tests.py [--ptr2arr EXE] [--validate SCRIPT] [--keep DIR]

Each case runs athena-witness on an input under tests/cases, a property file
under tests/properties and a transformation record, and checks its exit
status, the witness's main fields and what it says on stderr. Every witness
written is then checked by witnesslint (validate.sh --validator none).

The records are the hand-written ones under tests/records, which follow the
record's documented source_map; with --ptr2arr they are instead made by
running that Ptr2ArrFC executable on the inputs, and the same expectations
must hold.

One line per case, then the counts and DONE; exit status 1 if anything failed.
"""

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

import yaml

HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.path.dirname(HERE)
REPO = os.path.dirname(os.path.dirname(PROJECT))
EXE = os.path.join(PROJECT, "_build", "default", "bin", "main.exe")
CASES = os.path.join(HERE, "cases")
PROPS = os.path.join(HERE, "properties")
TASKS = os.path.join(HERE, "tasks")

# How Ptr2ArrFC is run to make each record with --ptr2arr.
PTR2ARR_OPTIONS = {
    "unreach1": ["--data-model=ILP32"],
    "unreach2": [],
    "unreach0": [],
    "overflow": ["--check-overflow"],
    "memsafety": ["--memory-safety"],
    "memtrack": ["--memory-safety"],
    "loop1": [],
}

FORMULA = {
    "unreach-call": "CHECK( init(main()), LTL(G ! call(reach_error())) )",
    "no-overflow": "CHECK( init(main()), LTL(G ! overflow) )",
    "termination": "CHECK( init(main()), LTL(F end) )",
    "valid-deref": "CHECK( init(main()), LTL(G valid-deref) )",
    "valid-free": "CHECK( init(main()), LTL(G valid-free) )",
}


def case(name, record, prop, result, code, args=(), input=None, target=None, spec=None,
         data_model=None, stderr=(), transform=None, content=None, path=None):
    """A case: run on tests/cases/<input or record>.c with the record of
    [record], expect exit status [code]; for a written witness, expect the
    specification [spec] (a key of FORMULA), the data model, for a
    violation witness the target's (line, column, function) after the
    segments [path] (none by default), and for a correctness witness the
    content [content] (none by default)."""
    return dict(name=name, record=record, prop=prop, result=result, code=code, args=list(args),
                input=input or record + ".c", target=target, spec=spec, data_model=data_model,
                stderr=list(stderr), transform=transform, content=content or [], path=path or [])


def with_machdep(m):
    def f(r):
        r["input"]["machdep"] = m
        return r
    return f


def without_source_map(r):
    del r["source_map"]
    return r


ILP32 = ["--data-model", "ILP32"]
LP64 = ["--data-model", "LP64"]
INVARIANTS = os.path.join(HERE, "invariants")


def invariants(name):
    return ["--invariants", os.path.join(INVARIANTS, name + ".lines")]


# The loop invariant of tests/invariants/loop1.lines: the conjuncts over i,
# each with the second holder of a negative i, lifted to long long; the
# conjunct over n * 2^32, which may not fit a long long, and the one over t,
# which is not a name of the input, are dropped.
LOOP1_VALUE = ("(((long long)i >= 0LL) || (((long long)i < 0LL) && (((long long)i + 4294967296LL) >= 0LL)))"
               " && (((long long)i <= 100LL) || (((long long)i < 0LL) && (((long long)i + 4294967296LL)"
               " <= 100LL)))")
LOOP1_CONTENT = [{"invariant": {
    "type": "loop_invariant",
    "location": {"file_name": "loop1.c", "line": 7, "column": 3, "function": "main"},
    "value": LOOP1_VALUE, "format": "c_expression"}}]

# tests/invariants/loop1_transition.lines: the transition, with (prev i) as
# \at(i, AnyPrev), and the invariant line's conjunct over i, the one over
# (prev i) dropped since an invariant has no earlier visit.
LOOP1_TRANSITION_CONTENT = [
    {"invariant": {
        "type": "loop_transition_invariant",
        "location": {"file_name": "loop1.c", "line": 7, "column": 3, "function": "main"},
        "value": "((long long)\\at(i, AnyPrev) < 100LL) && ((long long)\\at(i, AnyPrev) < (long long)i)",
        "format": "ext_c_expression"}},
    {"invariant": {
        "type": "loop_invariant",
        "location": {"file_name": "loop1.c", "line": 7, "column": 3, "function": "main"},
        "value": "((long long)i >= 0LL)", "format": "c_expression"}}]


def assumption(line, column, func, value):
    return {"segment": [{"waypoint": {
        "type": "assumption", "action": "follow",
        "location": {"file_name": "loop1.c", "line": line, "column": column, "function": func},
        "constraint": {"value": value, "format": "c_expression"}}}]}


# tests/invariants/loop1_path.lines: two visits of the loop head, of which
# the first, when the loop is entered, is kept, and one at an output location
# that is no loop head of the input, left out.
LOOP1_PATH = [assumption(7, 3, "main", "((long long)i == 0LL)")]

CASES_LIST = [
    # Correctness witnesses: an empty invariant set, or none.
    case("true-unreach-call", "unreach1", "unreach-call", "true", 0, ILP32, spec="unreach-call",
         data_model="ILP32"),
    case("true-unreach-call-task", "unreach1", "unreach-call", "true", 0,
         ["--task", os.path.join(TASKS, "ilp32.yml")], spec="unreach-call", data_model="ILP32"),
    case("true-no-overflow", "overflow", "no-overflow", "true", 0, LP64, spec="no-overflow",
         data_model="LP64"),
    case("true-termination", "unreach0", "termination", "true", 0, LP64, spec="termination",
         data_model="LP64"),
    # Correctness witnesses with the loop invariants of the direct LLVM route.
    case("true-invariants", "loop1", "unreach-call", "true", 0, LP64 + invariants("loop1"),
         spec="unreach-call", data_model="LP64", content=LOOP1_CONTENT,
         stderr=["dropped: a subterm may not fit a long long", "dropped: t is not in the record's names",
                 "1 loop invariants from 2 lines"]),
    case("true-invariants-elsewhere", "loop1", "unreach-call", "true", 0, LP64 + invariants("elsewhere"),
         spec="unreach-call", data_model="LP64", stderr=["0 loop invariants from 1 lines"]),
    case("true-invariants-termination", "loop1", "termination", "true", 0, LP64 + invariants("loop1"),
         spec="termination", data_model="LP64", content=LOOP1_CONTENT,
         stderr=["0 loop transition invariants and 1 loop invariants from 2 lines"]),
    case("true-transition", "loop1", "termination", "true", 0, LP64 + invariants("loop1_transition"),
         spec="termination", data_model="LP64", content=LOOP1_TRANSITION_CONTENT,
         stderr=["dropped: an earlier value outside a transition",
                 "1 loop transition invariants and 1 loop invariants from 2 lines"]),
    case("false-path", "loop1", "unreach-call", "false", 0, LP64 + invariants("loop1_path"),
         spec="unreach-call", data_model="LP64", target=(10, 17, "main"), path=LOOP1_PATH,
         stderr=["a state at 40:3, which is no loop head of the input", "1 assumption waypoints from the path"]),
    case("true-memsafety", "memsafety", "valid-memsafety", "true", 2, LP64,
         stderr=["no correctness witness for valid-memsafety"]),
    case("true-memcleanup", "memtrack", "valid-memcleanup", "true", 2, LP64,
         stderr=["no correctness witness for valid-memcleanup"]),
    # Violation witnesses: one target, or none.
    case("false-unreach-call-1", "unreach1", "unreach-call", "false", 0, ILP32, spec="unreach-call",
         data_model="ILP32", target=(13, 2, "main")),
    case("false-unreach-call-2", "unreach2", "unreach-call", "false", 0, LP64, spec="unreach-call",
         data_model="LP64", target=(7, 16, "check"), stderr=["guessed the target: 2 candidates"]),
    case("false-unreach-call-0", "unreach0", "unreach-call", "false", 2, LP64,
         stderr=["no target of unreach-call"]),
    case("false-unreach-call-other-function", "unreach1", "unreach-call-verifier-error", "false", 2,
         ILP32, stderr=["about __VERIFIER_error"]),
    case("false-no-overflow", "overflow", "no-overflow", "false", 0, LP64, spec="no-overflow",
         data_model="LP64", target=(7, 5, "main")),
    case("false-valid-deref", "memsafety", "valid-memsafety", "false", 0,
         LP64 + ["--violated", "valid-deref"], spec="valid-deref", target=(8, 5, "main")),
    case("false-valid-free", "memsafety", "valid-memsafety", "false", 0,
         LP64 + ["--violated", "valid-free"], spec="valid-free", target=(10, 3, "main"),
         stderr=["guessed the target: 2 candidates"]),
    case("false-memsafety-unnamed", "memsafety", "valid-memsafety", "false", 0, LP64,
         spec="valid-deref", target=(8, 5, "main"),
         stderr=["violated sub-property: valid-deref (guessed"]),
    case("false-valid-memtrack", "memsafety", "valid-memsafety", "false", 2,
         LP64 + ["--violated", "valid-memtrack"], stderr=["needs format 2.3"]),
    case("false-memtrack-unnamed", "memtrack", "valid-memsafety", "false", 2, LP64,
         stderr=["violated sub-property: valid-memtrack (the only", "needs format 2.3"]),
    case("false-valid-memcleanup", "memtrack", "valid-memcleanup", "false", 2, LP64,
         stderr=["needs format 2.3"]),
    case("false-termination", "unreach0", "termination", "false", 2, LP64, stderr=["needs a cycle"]),
    # Errors.
    case("error-sha256", "unreach1", "unreach-call", "false", 1, ILP32, input="unreach2.c",
         stderr=["SHA-256"]),
    case("error-data-model", "unreach1", "unreach-call", "false", 1, LP64,
         stderr=["machdep gcc_x86_32"]),
    case("error-data-model-task", "unreach1", "unreach-call", "true", 1,
         ["--task", os.path.join(TASKS, "lp64.yml")], stderr=["machdep gcc_x86_32"]),
    case("error-data-model-conflict", "unreach1", "unreach-call", "true", 1,
         ["--task", os.path.join(TASKS, "ilp32.yml")] + LP64, stderr=["disagrees with --data-model"]),
    case("error-no-data-model", "unreach1", "unreach-call", "true", 1, stderr=["no data model"]),
    case("error-task-without-data-model", "unreach1", "unreach-call", "true", 1,
         ["--task", os.path.join(TASKS, "no_data_model.yml")], stderr=["states no options.data_model"]),
    case("error-unknown-machdep", "unreach1", "unreach-call", "true", 1, ILP32,
         transform=with_machdep("gcc_ppc_64"), stderr=["no known data model"]),
    case("error-no-source-map", "unreach1", "unreach-call", "true", 1, ILP32,
         transform=without_source_map, stderr=["missing field source_map"]),
    case("error-format-version", "unreach1", "unreach-call", "true", 1,
         ILP32 + ["--format-version", "2.2"], stderr=["only 2.1"]),
    case("error-violated-with-true", "memsafety", "valid-memsafety", "true", 1,
         LP64 + ["--violated", "valid-deref"], stderr=["--violated is for --result false"]),
    case("error-violated-other-property", "unreach1", "unreach-call", "false", 1,
         ILP32 + ["--violated", "valid-free"], stderr=["not the property file's unreach-call"]),
]


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def make_records(ptr2arr, out):
    """The records to test with: copies of the hand-written ones, or ones made by ptr2arr."""
    recs = {}
    for name, opts in PTR2ARR_OPTIONS.items():
        dest = os.path.join(out, name + ".p2a.json")
        if ptr2arr:
            cmd = [ptr2arr] + opts + ["-o", os.path.join(out, name + "_Ptr2Arr.c"), "--record=" + dest,
                                      os.path.join(CASES, name + ".c")]
            p = subprocess.run(cmd, cwd=out, capture_output=True, text=True)
            if p.returncode != 0:
                sys.exit("ptr2arr failed on %s:\n%s%s" % (name, p.stdout, p.stderr))
        else:
            shutil.copy(os.path.join(HERE, "records", name + ".p2a.json"), dest)
            with open(dest) as f:
                if json.load(f)["input"]["sha256"] != sha256(os.path.join(CASES, name + ".c")):
                    sys.exit("tests/records/%s.p2a.json does not hold the SHA-256 of cases/%s.c" % (name, name))
        recs[name] = dest
    return recs


def check(c, p, witness_path, recs):
    """The list of failures of case [c], run as [p]."""
    bad = []
    if p.returncode != c["code"]:
        bad.append("exit status %d, expected %d" % (p.returncode, c["code"]))
    for s in c["stderr"]:
        if s not in p.stderr:
            bad.append("stderr lacks %r" % s)
    if c["code"] != 0:
        if os.path.exists(witness_path):
            bad.append("a witness was written")
        return bad
    if not os.path.exists(witness_path):
        return bad + ["no witness written"]
    with open(witness_path) as f:
        w = yaml.safe_load(f)
    if not (isinstance(w, list) and len(w) == 1):
        return bad + ["not a list of one entry"]
    e = w[0]
    md = e["metadata"]
    task = md["task"]
    expect = {
        "format_version": (md["format_version"], "2.1"),
        "producer": (md["producer"], {"name": "MuVal", "version": "test"}),
        "input_files": (task["input_files"], [c["input"]]),
        "input_file_hashes": (task["input_file_hashes"], {c["input"]: sha256(os.path.join(CASES, c["input"]))}),
        "specification": (task["specification"], FORMULA[c["spec"]]),
        "language": (task["language"], "C"),
    }
    if c["data_model"]:
        expect["data_model"] = (task["data_model"], c["data_model"])
    if c["result"] == "true":
        expect["entry_type"] = (e["entry_type"], "invariant_set")
        expect["content"] = (e["content"], c["content"])
    else:
        expect["entry_type"] = (e["entry_type"], "violation_sequence")
        line, column, func = c["target"]
        expect["content"] = (e["content"], c["path"] + [{"segment": [{"waypoint": {
            "type": "target", "action": "follow",
            "location": {"file_name": c["input"], "line": line, "column": column, "function": func}}}]}])
    for k, (got, want) in expect.items():
        if got != want:
            bad.append("%s is %r, expected %r" % (k, got, want))
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ptr2arr", help="make the records with this Ptr2ArrFC executable")
    ap.add_argument("--validate", default=os.path.join(REPO, "script", "svcomp", "validation", "validate.sh"),
                    help="validate.sh, for witnesslint")
    ap.add_argument("--keep", help="write everything under this directory and keep it")
    a = ap.parse_args()
    if not os.access(EXE, os.X_OK):
        sys.exit("missing %s; build with: dune build --root %s" % (EXE, PROJECT))
    out = a.keep or tempfile.mkdtemp(prefix="athena-witness-tests-")
    os.makedirs(out, exist_ok=True)
    out = os.path.abspath(out)
    recs = make_records(a.ptr2arr and os.path.abspath(a.ptr2arr), out)

    passed = failed = 0
    written = []
    for c in CASES_LIST:
        rec = recs[c["record"]]
        if c["transform"]:
            with open(rec) as f:
                r = c["transform"](json.load(f))
            rec = os.path.join(out, c["name"] + ".p2a.json")
            with open(rec, "w") as f:
                json.dump(r, f)
        witness = os.path.join(out, c["name"] + ".yml")
        if os.path.exists(witness):
            os.remove(witness)
        cmd = [EXE, "--input", c["input"], "--record", rec,
               "--property", os.path.join(PROPS, c["prop"] + ".prp"), "--result", c["result"],
               "--producer-version", "test", "-o", witness] + c["args"]
        # Run in the inputs' directory, so that the input is named as a
        # verifier given tests/cases/<input> by a relative path would see it.
        p = subprocess.run(cmd, cwd=CASES, capture_output=True, text=True)
        bad = check(c, p, witness, recs)
        if bad:
            failed += 1
            print("FAIL %s: %s" % (c["name"], "; ".join(bad)))
            if p.stderr:
                print("  stderr: " + p.stderr.strip().replace("\n", "\n  stderr: "))
        else:
            passed += 1
            print("PASS %s (exit %d)" % (c["name"], p.returncode))
        if p.returncode == 0:
            written.append((c, witness))

    lint_ok = lint_bad = 0
    for c, witness in written:
        with open(witness) as f:
            dm = yaml.safe_load(f)[0]["metadata"]["task"]["data_model"]
        arch = "32bit" if dm == "ILP32" else "64bit"
        prop = os.path.join(PROPS, c["prop"] + ".prp")
        if c["prop"] == "valid-memsafety":
            # A witness of one sub-property is linted against that property alone.
            prop = os.path.join(out, c["name"] + ".prp")
            with open(witness) as f, open(prop, "w") as g:
                g.write(yaml.safe_load(f)[0]["metadata"]["task"]["specification"] + "\n")
        p = subprocess.run([a.validate, "--validator", "none", "--arch", arch,
                            "--out", os.path.join(out, "lint-" + c["name"]),
                            witness, os.path.join(CASES, c["input"]), prop],
                           capture_output=True, text=True)
        line = next((l for l in p.stdout.splitlines() if l.startswith("witnesslint:")), "witnesslint: (no line)")
        if p.returncode == 0 and line == "witnesslint: PASS":
            lint_ok += 1
            print("LINT %s: PASS" % c["name"])
        else:
            lint_bad += 1
            print("LINT %s: FAIL (%s) %s" % (c["name"], line, p.stderr.strip()))

    if not a.keep:
        shutil.rmtree(out)
    print("records: %s" % ("made by " + a.ptr2arr if a.ptr2arr else "tests/records"))
    print("cases: %d passed, %d failed; witnesslint: %d passed, %d failed" % (passed, failed, lint_ok, lint_bad))
    print("DONE")
    sys.exit(1 if failed or lint_bad else 0)


if __name__ == "__main__":
    main()
