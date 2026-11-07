#!/usr/bin/env python3
"""Dump the transition systems HyHorn builds for its Pdsc comparator benchmarks, as JSON for hyhorn_to_pcsp.py.

    PY script/hyhorn_pdsc_dump.py --hyhorn DIR --out FILE.json [--only STEM ...]

PY is a Python with the `z3-solver` and `bitstring` packages (a virtual environment outside the tree).

THIS RUNS THE ARTIFACT'S CODE.  HyHorn (Itzhaky, Shoham, Vizel, ESOP 2024; artifact Zenodo 10449234, CC-BY-4.0)
reads the 32 comparator programs of its Appendix A through the Pdsc front end it bundles (Shemer, Gurfinkel,
Shoham, Vizel, CAV 2019): SeaHorn's CHC for the `compare` method become a transition system per copy, and each
property's relational precondition is built from the copies' variable names.  The heuristics are Pdsc's and the
two preconditions HyHorn adds are HyHorn's (`hyhorn/adapter/pdsc.py`, `read_comparator`), so the only faithful
reading is to run them: DIR must be the artifact's `/hyhorn` directory *with* its `lib/pdsc/` (the fetched copy
omits it; take the whole directory out of the image).  This script calls exactly what HyHorn's
`AdaptedDoomedEncoding.of_dp` uses -- `read_comparator`, `DynamicProgramAdapter`, `TS_of_DPA`, the barrier of
exit locations -- and writes, per instance, what its clauses are built from:

  copies: per copy its state variables (name, sort), its initial condition, its step formula and its
          observation point (the program counter at the copy's exit), over the variables `<v>__c<i>` (current)
          and `<v>__c<i>n` (next); any other constant of a step formula is a nondeterministic choice;
  pre:    the relational precondition (Pdsc's `rel_init` with HyHorn's additions), over the current variables;
  bad:    the negated property (Pdsc's `rel_bad`), over the current variables;
  consts: the sort of every constant that occurs.

Formulas are Z3's SMT-LIB printing.  Nothing is solved.  Exit 0 when every instance was dumped or recorded with
its failure, 1 otherwise.
"""
import argparse
import json
import os
import sys
import traceback


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hyhorn", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--only", nargs="*")
    a = ap.parse_args()
    hy = os.path.abspath(a.hyhorn)
    for sub in ("lib", "hyhorn", "benchmarks", os.path.join("lib", "pdsc")):
        sys.path.append(os.path.join(hy, sub))
    import z3
    from z3.z3util import get_vars
    from symbolic_interp import State
    from adapter.pdsc import read_comparator, DynamicProgramAdapter, TS_of_DPA
    import pdsc

    out, rc = [], 0
    for fn in pdsc.INPUT_FILES:
        stem = os.path.splitext(fn)[0]
        if a.only and stem not in a.only:
            continue
        for prop in (1, 2, 3):
            name = f"{stem}_p{prop}"
            try:
                dp = read_comparator(os.path.join(hy, "benchmarks", "pdsc", fn), prop)
                dpa = DynamicProgramAdapter(dp)
                ids = list(dpa.copy_ids())
                tss = [TS_of_DPA(dpa, i, nm) for i, nm in zip(ids, "abc")]
                cur = [State(dpa.sig, f"__c{j}") for j in range(len(tss))]
                nxt = [State(dpa.sig, f"__c{j}n") for j in range(len(tss))]
                exits = dpa.exits
                formulas = []
                copies = []
                for j, ts in enumerate(tss):
                    init = ts.tr.init(cur[j])
                    tr = ts.tr(cur[j], nxt[j])
                    obs = cur[j].locals["pc"] == exits[j]
                    formulas += [init, tr, obs]
                    copies.append({
                        "name": ts.name,
                        "vars": [[v, cur[j].locals[v].sort().sexpr()] for v in dpa.sig.vars()],
                        "init": init.sexpr(), "tr": tr.sexpr(), "obs": obs.sexpr(),
                    })
                sub = [el for ts, s in zip(tss, cur) for el in ts.tr.subst(s)]
                pre = z3.substitute(dp.rel_init, *sub)
                bad = z3.substitute(dp.rel_bad, *sub)
                formulas += [pre, bad]
                consts = {}
                for f in formulas:
                    for v in get_vars(f):
                        consts[v.decl().name()] = v.sort().sexpr()
                out.append({"name": name, "file": fn, "prop": prop, "status": "dumped",
                            "copies": copies, "pre": pre.sexpr(), "bad": bad.sexpr(), "consts": consts})
                print(f"dumped   {name}: {len(tss)} copies", file=sys.stderr)
            except Exception:
                rc = 1
                last = traceback.format_exc().strip().splitlines()[-1]
                out.append({"name": name, "file": fn, "prop": prop, "status": "failed", "error": last})
                print(f"FAILED   {name}: {last}", file=sys.stderr)
    with open(a.out, "w") as f:
        json.dump(out, f, indent=1)
    print(f"DONE {sum(1 for x in out if x['status'] == 'dumped')} dumped, "
          f"{sum(1 for x in out if x['status'] != 'dumped')} failed", file=sys.stderr)
    return rc


if __name__ == "__main__":
    sys.exit(main())
