#!/usr/bin/env python3
"""What the violation markers of a --memory-safety output are and who calls
them, checked on the printed outputs and their records.

usage: tests/markers.py [WORKDIR]

Transforms each input below with --memory-safety and with --memory-cleanup,
in both marker styles, and checks:
  split (the default):
    - the record's violations are __p2a_violation_valid_* markers (or such a
      name with a number, when the input took the name), each defined in the
      output as a noreturn function whose body ends the execution with
      _Exit(77) for valid-deref, _Exit(78) for valid-free, _Exit(79) for
      valid-memtrack and _Exit(80) for valid-memcleanup; valid-memcleanup
      only in --memory-cleanup and valid-memtrack only in --memory-safety,
      and, for an input listed in END_MARKER, the marker of its end check
      among them;
    - a marker is called from the generated functions only, and no generated
      function calls reach_error;
    - every function of the input is still defined under its own name, and
      the output calls reach_error exactly where the input does.
  reach-error:
    - the record's violations are the one reach_error marker, and the output
      only declares reach_error;
    - reach_error is called from the generated functions only;
    - when the input has a reach_error, the record's names list it renamed
      (original reach_error), and the output calls the new name exactly where
      the input calls reach_error.
With --uninit=check (in the normal mode, --memory-safety in both marker
styles, --memory-cleanup and --assume-safety), on the inputs of
UNINIT_INPUTS:
  - the record lists the marker of an uninitialised read: reach_error
    (declared only, its exit status null) in the normal mode and with the
    reach-error markers, __p2a_violation_uninit_read (defined noreturn with
    _Exit(82)) with the split markers, none in --assume-safety;
  - that marker (or __ptr2arr_assume) is called from the generated
    functions only, and the input's own reach_error, renamed when the
    marker is reach_error, is called where the input calls it.
With --uninit=nondet, on c134 (every kind of scalar), every generator the
record lists is defined weak in the output and returns what
__VERIFIER_nondet_<kind> draws (char's for the signed char one).
"Where the input calls" is counted per function on the input as the front end
normalises it (ptr2arr --identity), a function the output renamed (main,
when the output checks the return from it) counted under its name in the
input, which the record's names give. A generated function is one whose
name starts with p2a_. One line per check (ok or FAIL); the script ends with the
counts and DONE, and exits 1 if a check failed.
"""
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
EXE = os.path.join(HERE, "..", "_build", "default", "bin", "ptr2arr.exe")
INPUTS = ["c26_free_twice.c", "c71_double_free_copy.c", "c74_input_reach_error.c",
          "c75_marker_name_clash.c", "c76_input_reach_error_clash.c", "c78_declared_reach_error.c",
          "c18_svcomp_style.c", "c79_memtrack_overwrite.c", "c84_memtrack_caller_local_abort.c"]
MARKER_STATUS = {"valid-deref": 77, "valid-free": 78, "valid-memtrack": 79,
                 "valid-memcleanup": 80}
# The property each mode checks at the ends of the execution, and the inputs
# whose output must have the marker of that property (a heap allocation).
MODES = {"memory-safety": "valid-memtrack", "memory-cleanup": "valid-memcleanup"}
END_MARKER = {"c74_input_reach_error.c", "c79_memtrack_overwrite.c",
              "c84_memtrack_caller_local_abort.c", "c26_free_twice.c",
              "c71_double_free_copy.c"}
HEAD = re.compile(r"^(?:\s*__attribute__\(\([^)]*\)\)\s*)?[A-Za-z_][\w\s\*]*?\b([A-Za-z_]\w*)\s*\(.*\)\s*$")

UNINIT_INPUTS = ["c116_uninit_scalar.c", "c121_uninit_struct_copy_none.c",
                 "c133_uninit_input_reach.c", "c135_uninit_memtrack_root.c"]

results = {"ok": 0, "FAIL": 0}


def check(cond, what):
    r = "ok" if cond else "FAIL"
    results[r] += 1
    print("%s\t%s" % (r, what))


def functions(path):
    """The functions a file printed by Frama-C defines: name -> (head line,
    body lines). A definition is a head line at depth 0 followed by a line
    holding only an opening brace."""
    lines = open(path, errors="replace").read().splitlines()
    out = {}
    i = 0
    while i < len(lines):
        m = HEAD.match(lines[i])
        if m and i + 1 < len(lines) and lines[i + 1] == "{":
            depth, j = 0, i + 1
            body = []
            while j < len(lines):
                depth += lines[j].count("{") - lines[j].count("}")
                body.append(lines[j])
                j += 1
                if depth == 0:
                    break
            out[m.group(1)] = (lines[i], body)
            i = j
        else:
            i += 1
    return out


def calls(fns, callee):
    """Function name -> number of calls of [callee] in its body."""
    pat = re.compile(r"\b%s\s*\(" % re.escape(callee))
    return {f: n for f, (_, body) in fns.items()
            if (n := sum(len(pat.findall(l)) for l in body))}


def run(args):
    return subprocess.run([EXE] + args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def main():
    work = sys.argv[1] if len(sys.argv) > 1 else tempfile.mkdtemp()
    os.makedirs(work, exist_ok=True)
    for name in INPUTS:
        src = os.path.join(HERE, "cases", name)
        stem = name[:-2]
        ident = os.path.join(work, stem + ".identity.c")
        run(["--identity", "-o", ident, src])
        in_fns = functions(ident)
        in_calls = calls(in_fns, "reach_error")
        for mode, style in [(m, st) for m in MODES for st in ("split", "reach-error")]:
            out = os.path.join(work, "%s.%s.%s.c" % (stem, mode, style))
            r = run(["--" + mode, "--violation-markers=" + style, "-o", out, src])
            tag = "%s [%s %s]" % (stem, mode, style)
            check(r.returncode == 0, "%s: transformed" % tag)
            if r.returncode != 0:
                continue
            rec = json.load(open(out[:-2] + ".p2a.json"))
            # the output's functions under their names in the input
            renamed = {n["name"]: n["original"] for n in rec["names"]
                       if n["kind"] == "function" and n["original"] not in (None, n["name"])
                       and n["original"] != "reach_error"}
            # (the new main that calls the renamed one is generated)
            fns = {renamed.get(f, f): v for f, v in functions(out).items()
                   if not (f in renamed.values() and f not in renamed)}
            generated = {f for f in fns if f.startswith("p2a_")}
            violations = rec["violations"]
            if style == "split":
                other = [p for p in MODES.values() if p != MODES[mode]]
                check(all(v["property"] in MARKER_STATUS
                          and v["exit_status"] == MARKER_STATUS[v["property"]]
                          and v["property"] not in other
                          and re.fullmatch(r"__p2a_violation_%s(_\d+)?"
                                           % v["property"].replace("-", "_"), v["name"])
                          for v in violations) and violations != []
                      and (name not in END_MARKER
                           or MODES[mode] in [v["property"] for v in violations]),
                      "%s: record violations %s" % (tag, [v["name"] for v in violations]))
                for v in violations:
                    head, body = fns.get(v["name"], ("", []))
                    check("__noreturn__" in head
                          and any("_Exit(%d);" % v["exit_status"] in l for l in body),
                          "%s: %s defined noreturn with _Exit(%d)"
                          % (tag, v["name"], v["exit_status"]))
                    callers = calls(fns, v["name"])
                    check(callers and set(callers) <= generated,
                          "%s: %s called from %s" % (tag, v["name"], sorted(callers)))
                own = calls(fns, "reach_error")
                check(not (set(own) & generated) and own == in_calls,
                      "%s: reach_error calls %s, the input's %s" % (tag, own, in_calls))
                check(set(in_fns) <= set(fns),
                      "%s: the input's functions kept: %s"
                      % (tag, sorted(set(in_fns) - set(fns)) or "all"))
            else:
                check([(v["name"], v["exit_status"]) for v in violations]
                      == [("reach_error", None)],
                      "%s: record violations %s" % (tag, violations))
                check("reach_error" not in fns,
                      "%s: reach_error only declared" % tag)
                callers = calls(fns, "reach_error")
                check(callers and set(callers) <= generated,
                      "%s: reach_error called from %s" % (tag, sorted(callers)))
                re_renamed = [n["name"] for n in rec["names"]
                              if n["kind"] == "function" and n["original"] == "reach_error"
                              and n["name"] != "reach_error"]
                if "reach_error" in in_fns or in_calls:
                    check(len(re_renamed) == 1,
                          "%s: the input's reach_error renamed %s" % (tag, re_renamed))
                    if re_renamed:
                        check(calls(fns, re_renamed[0]) == in_calls,
                              "%s: %s calls %s, the input's reach_error calls %s"
                              % (tag, re_renamed[0], calls(fns, re_renamed[0]), in_calls))
                else:
                    check(re_renamed == [], "%s: nothing renamed" % tag)
    # --memtrack-nonterminating: the stop function ends the execution with
    # status 0, is called only after a check, and the record names it
    src = os.path.join(HERE, "cases", "c87_memtrack_leak_then_loop.c")
    for mode in MODES:
        out = os.path.join(work, "c87.%s.nonterminating.c" % mode)
        r = run(["--" + mode, "--memtrack-nonterminating", "-o", out, src])
        tag = "c87 [%s nonterminating]" % mode
        check(r.returncode == 0, "%s: transformed" % tag)
        if r.returncode != 0:
            continue
        rec = json.load(open(out[:-2] + ".p2a.json"))
        m = rec["memtrack"] or {}
        stop, probe = m.get("stop_function"), m.get("probe_function")
        fns = functions(out)
        head, body = fns.get(stop, ("", []))
        check(m.get("nonterminating") is True and stop and probe
              and "__noreturn__" in head and any("_Exit(0);" in l for l in body),
              "%s: stop %s defined noreturn with _Exit(0), probe %s" % (tag, stop, probe))
        check([n["role"] for n in rec["names"] if n["name"] == stop] == ["stop"],
              "%s: %s has the role stop" % (tag, stop))
        check(len(rec.get("memtrack_points", [])) >= 2,
              "%s: memtrack_points %s" % (tag, [p["kind"] for p in rec.get("memtrack_points", [])]))
        prop = MODES[mode]
        check(prop in [v["property"] for v in rec["violations"]],
              "%s: the check reports %s" % (tag, prop))
    # an allocation past the end of a region's array stops at
    # __p2a_region_exhausted (81), called by the allocators alone; with the
    # reach-error markers it calls reach_error instead
    src = os.path.join(HERE, "cases", "c101_region_exhausted.c")
    for args, style in ((["--memory-safety"], "split"), (["--memory-cleanup"], "split"),
                        (["--assume-safety"], "assume"),
                        (["--memory-safety", "--violation-markers=reach-error"], "reach-error")):
        out = os.path.join(work, "c101.%s.%s.c" % (args[0][2:], style))
        r = run(args + ["-o", out, src])
        tag = "c101 [%s %s]" % (args[0][2:], style)
        check(r.returncode == 0, "%s: transformed" % tag)
        if r.returncode != 0:
            continue
        rec = json.load(open(out[:-2] + ".p2a.json"))
        fns = functions(out)
        ex = rec.get("region_exhausted")
        if style == "reach-error":
            check(ex is None and "__p2a_region_exhausted" not in fns,
                  "%s: no region_exhausted stop (%s)" % (tag, ex))
            continue
        name = (ex or {}).get("name")
        head, body = fns.get(name, ("", []))
        check(ex and ex.get("exit_status") == 81 and "__noreturn__" in head
              and any("_Exit(81);" in l for l in body),
              "%s: %s defined noreturn with _Exit(81)" % (tag, name))
        callers = calls(fns, name) if name else {}
        check(callers and all(f.startswith("p2a_alloc") for f in callers),
              "%s: %s called from %s" % (tag, name, sorted(callers)))
    # --uninit=check: the marker of an uninitialised read
    for name in UNINIT_INPUTS:
        src = os.path.join(HERE, "cases", name)
        stem = name[:-2]
        ident = os.path.join(work, stem + ".identity.c")
        run(["--identity", "-o", ident, src])
        in_calls = calls(functions(ident), "reach_error")
        for args, style in (([], "normal"), (["--memory-safety"], "split"),
                            (["--memory-safety", "--violation-markers=reach-error"], "reach-error"),
                            (["--memory-cleanup"], "split"), (["--assume-safety"], "assume")):
            out = os.path.join(work, "%s.uninit.%s.%s.c" % (stem, (args or ["normal"])[0][2:], style))
            r = run(["--uninit=check"] + args + ["-o", out, src])
            tag = "%s [uninit=check %s]" % (stem, " ".join(args) or "normal")
            check(r.returncode == 0, "%s: transformed" % tag)
            if r.returncode != 0:
                continue
            rec = json.load(open(out[:-2] + ".p2a.json"))
            fns = functions(out)
            generated = {f for f in fns if f.startswith("p2a_") or f.startswith("__p2a_")}
            uninit = [v for v in rec["violations"] if v["property"] == "uninit-read"]
            if style == "assume":
                check(uninit == [], "%s: no uninit-read marker in the record" % tag)
                callers = calls(fns, "__ptr2arr_assume")
                check(callers and set(callers) <= generated,
                      "%s: __ptr2arr_assume called from %s" % (tag, sorted(callers)))
                continue
            if style == "split":
                v = uninit[0] if len(uninit) == 1 else {}
                head, body = fns.get(v.get("name"), ("", []))
                check(v.get("exit_status") == 82
                      and re.fullmatch(r"__p2a_violation_uninit_read(_\d+)?", v.get("name", ""))
                      and "__noreturn__" in head and any("_Exit(82);" in l for l in body),
                      "%s: %s defined noreturn with _Exit(82)" % (tag, v.get("name")))
                marker = v.get("name")
            else:
                check([(v["name"], v["exit_status"]) for v in uninit] == [("reach_error", None)]
                      and "reach_error" not in fns,
                      "%s: reach_error, declared only, is the marker: %s" % (tag, uninit))
                marker = "reach_error"
                renamed = [n["name"] for n in rec["names"]
                           if n["kind"] == "function" and n["original"] == "reach_error"
                           and n["name"] != "reach_error"]
                if in_calls:
                    check(len(renamed) == 1 and calls(fns, renamed[0]) == in_calls,
                          "%s: the input's reach_error renamed %s, called as the input does"
                          % (tag, renamed))
            callers = calls(fns, marker) if marker else {}
            check(callers and set(callers) <= generated,
                  "%s: %s called from %s" % (tag, marker, sorted(callers)))
    # --uninit=nondet: the generators
    src = os.path.join(HERE, "cases", "c134_uninit_types.c")
    out = os.path.join(work, "c134.uninit.nondet.c")
    r = run(["--uninit=nondet", "-o", out, src])
    check(r.returncode == 0, "c134 [uninit=nondet]: transformed")
    if r.returncode == 0:
        rec = json.load(open(out[:-2] + ".p2a.json"))
        fns = functions(out)
        text = open(out).read()
        gens = rec["uninit_generators"]
        check(len(gens) >= 10, "c134 [uninit=nondet]: %d generators" % len(gens))
        for g in gens:
            nd = "__VERIFIER_nondet_" + ("char" if g["kind"] == "schar" else g["kind"])
            _, body = fns.get(g["name"], ("", []))
            weak = re.search(r"\b%s\(void\) __attribute__\(\(__weak__\)\);" % re.escape(g["name"]), text)
            check(weak and any(nd + "()" in l for l in body)
                  and [n["role"] for n in rec["names"] if n["name"] == g["name"]] == ["generated"],
                  "c134 [uninit=nondet]: %s weak, returns %s" % (g["name"], nd))
    print("ok: %d" % results["ok"])
    print("FAIL: %d" % results["FAIL"])
    print("DONE")
    return 1 if results["FAIL"] else 0


if __name__ == "__main__":
    sys.exit(main())
