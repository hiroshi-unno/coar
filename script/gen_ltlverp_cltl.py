#!/usr/bin/env python3
"""Write `-p cltl` inputs for LTL-VerP's corpus from its C sources (run with python3 -I).

LTL-VerP (Chatterjee, Goharshady, Goharshady, Karrabi, Zikelic, "Sound and Complete Witnesses for
Template-Based Verification of LTL Properties on Polynomial Programs", FM 2024) checks four LTL
properties (its Table 1) on 318 C programs, 297 from TermComp'22 "C-Integer" and 21 from SV-COMP'22
nla-digbench.  Its corpus ships each pair as a T2 transition system already multiplied with a Buchi
automaton; this script instead states each pair as a C program annotated with the LTL formula, the
input of CoAR's `-p cltl`, which builds the automaton itself (with ltl3ba).

The four properties, x being the alphabetically first variable of the program (the first in byte
order of the variables named by the `.t2` file's PRE line) and term the terminal location:
  RA  (F at(term)) /\\ (G x >= 0)          precondition: every variable in [0, 64]
  OV  F (at(term) \\/ x < -64 \\/ x > 63)    precondition: every variable in [-64, 63]
  RC  G F (x >= 0)                         precondition: every variable in [-64, 63]
  PR  G (x < -5 => F (x > 0))              precondition: every variable in [-64, 63]
The precondition is copied from the PRE line of the spec's `.t2` file, which also carries the
assumptions LTL-VerP's translation took from the source (e.g. `x1>=0 && x2>0`).

The program is rewritten into the form the C frontend reads and the `.t2` translation agrees with:
  * every variable of `main` becomes a global, so the LTL atoms can name it;
  * `main` begins with `v = __VERIFIER_nondet_int();` for every variable and one
    `__VERIFIER_assume(PRE)`, and a `v = __VERIFIER_nondet_int();` of the source before the first
    control statement is dropped: the `.t2` translation reads it as `v := v`, the initial value;
  * termination is made an absorbing location: every `return` of `main`, and its end, become
    `__term = 1; while (1) {}`, so at(term) is `AP(__term == 1)` and the variables keep their final
    values forever, as LTL-VerP's terminal location does;
  * `assume_abort_if_not(c)` and `__VERIFIER_assert(c)` become `__VERIFIER_assume(c)`: the `.t2`
    translation reads both as blocking guards (a failed assertion ends no run);
  * `typedef enum {false,true} bool;` is dropped and `bool`, `true`, `false` become `int`, 1, 0.
A nondet branch `if (__VERIFIER_nondet_int() != 0)` is kept: the `.t2` translation reads it as a
choice, as the C frontend does.  A program is refused (nothing written, the reason recorded) when it
draws a nondet value after its initial block (the `.t2` translation has no nondet, so its reading
of such a draw is not a C reading), declares one name twice, names a PRE variable it does not declare, names a variable `X`, `U`,
`R`, `WU` or `AP` (keywords of the C frontend's LTL lexer, which reads them as operators everywhere), or has a construct
the rewriting does not handle (`goto`, `exit`, `abort` outside the helpers, a function other than
main and the SV-COMP helpers).

Two differences of reading remain and are not refused (they are stated in the record of this
comparison): the C frontend steps once per statement where the `.t2` translation steps once per
basic block, so G/F atoms also see intermediate values; and the `.t2` start state, where x has its
PRE value before the initial assignments, is not a state of the C run, whose first state is after
the initial straight-line block.

Usage: gen_ltlverp_cltl.py T2_ROOT C_ROOTS... OUT_DIR
  T2_ROOT  the fetched corpus (benchmarks/LTS/ltlverp), read for the program list and PRE lines
  C_ROOTS  directories searched for the C sources by file name
  OUT_DIR  receives OUT_DIR/<spec>/<program> and OUT_DIR/STATUS.tsv
           (one line per program and spec: program, spec, written|refused, reason)
"""

import os
import re
import sys

SPECS = {
    "RA": "<>(AP(__term == 1)) && [](AP({x} >= 0))",
    "OV": "<>(AP(__term == 1) || AP({x} < -64) || AP({x} > 63))",
    "RC": "[]<>(AP({x} >= 0))",
    "PR": "[](AP({x} < -5) ==> <>(AP({x} > 0)))",
}

TYPE_RE = r"(?:unsigned\s+|signed\s+)?(?:long\s+long(?:\s+int)?|long(?:\s+int)?|int|short|char|bool|unsigned)"
NONDET_RE = r"__VERIFIER_nondet_\w+\s*\(\s*\)"
HELPERS = ("reach_error", "assume_abort_if_not", "__VERIFIER_assert", "main")


class Refused(Exception):
    pass


def pre_of(t2_path):
    with open(t2_path) as f:
        for line in f:
            m = re.match(r"\s*PRE:\s*\{(.*)\}\s*;", line)
            if m:
                return m.group(1).strip()
    raise Refused("no PRE line")


def strip_comments(src):
    src = re.sub(r"/\*.*?\*/", " ", src, flags=re.S)
    return re.sub(r"//[^\n]*", "", src)


def match_brace(src, i):
    """index just past the brace matching src[i] == '{'"""
    depth = 0
    for j in range(i, len(src)):
        if src[j] == "{":
            depth += 1
        elif src[j] == "}":
            depth -= 1
            if depth == 0:
                return j + 1
    raise Refused("unbalanced braces")


def functions(src):
    """(name, start, body_start, end) of every function definition at top level"""
    out = []
    i = 0
    for m in re.finditer(r"\b(\w+)\s*\(([^;{}()]*)\)\s*(?:__attribute__\s*\(\(.*?\)\)\s*)*\{", src):
        if m.start() < i:
            continue
        name = m.group(1)
        if name in ("if", "while", "for", "switch"):
            continue
        b = m.end() - 1
        e = match_brace(src, b)
        # the start of the definition: back to the previous ';' or '}' at top level
        k = max(src.rfind(";", 0, m.start()), src.rfind("}", 0, m.start()))
        out.append((name, k + 1, b, e))
        i = e
    return out


def rewrite(src, pre, x_formula):
    src = strip_comments(src)
    src = re.sub(r"#include[^\n]*\n", "\n", src)
    src = re.sub(r"typedef\s+enum\s*\{\s*false\s*,\s*true\s*\}\s*bool\s*;", "", src)
    src = re.sub(r"\bbool\b", "int", src)
    src = re.sub(r"\btrue\b", "1", src)
    src = re.sub(r"\bfalse\b", "0", src)
    # extern declarations of the SV-COMP functions
    src = re.sub(r"extern[^;]*;", "", src)
    fns = functions(src)
    names = [f[0] for f in fns]
    if "main" not in names:
        raise Refused("no main")
    others = [n for n in names if n not in HELPERS]
    if others:
        raise Refused("a function other than main: " + ", ".join(others))
    main = [f for f in fns if f[0] == "main"][0]
    outside = "".join(src[a:b] for a, b in gaps(fns, len(src)))
    if outside.strip():
        # global declarations: keep them as they are
        glob_decls = outside
    else:
        glob_decls = ""
    body = src[main[2] + 1 : main[3] - 1]
    for bad in ("goto", "exit", "abort", "__VERIFIER_error", "reach_error", "switch"):
        if re.search(r"\b" + bad + r"\b", body):
            raise Refused("'%s' in main" % bad)
    body = re.sub(r"\bassume_abort_if_not\s*\(", "__VERIFIER_assume(", body)
    body = re.sub(r"\b__VERIFIER_assert\s*\(", "__VERIFIER_assume(", body)
    # local declarations -> globals; initialisers -> assignments
    declared = {}

    def decl(m):
        ty, rest = m.group(1), m.group(2)
        stmts = []
        for part in split_top(rest, ","):
            part = part.strip()
            dm = re.match(r"(\w+)\s*(?:=\s*(.*))?$", part, re.S)
            if not dm:
                raise Refused("declaration not understood: " + part)
            v = dm.group(1)
            if v in declared:
                raise Refused("'%s' declared twice" % v)
            declared[v] = ty
            if dm.group(2) is not None:
                stmts.append("%s = %s;" % (v, dm.group(2).strip()))
        return " ".join(stmts)

    body = re.sub(r"(?<![\w.])(" + TYPE_RE + r")\s+((?:\w+(?:\s*=\s*[^;,]+)?\s*,\s*)*\w+(?:\s*=\s*[^;]+)?)\s*;", decl, body)
    for v in re.findall(r"(?:^|[;{}])\s*(?:" + TYPE_RE + r")\s+(\w+)\b(?!\s*\()", glob_decls):
        if v in declared:
            raise Refused("'%s' declared twice" % v)
        declared[v] = "int"
    # the initial block: the statements before the first control keyword
    first = re.search(r"\b(while|for|if|do)\b", body)
    cut = first.start() if first else len(body)
    init, rest = body[:cut], body[cut:]
    init = re.sub(r"\b\w+\s*=\s*" + NONDET_RE + r"\s*;", "", init)
    # a nondet branch, `if (__VERIFIER_nondet_int() != 0)`, is a choice in both readings
    branch = r"\(\s*" + NONDET_RE + r"\s*(?:!=\s*0\s*)?\)"
    if re.search(NONDET_RE, re.sub(branch, "(1)", init + rest)):
        raise Refused("a nondet value after the initial block")
    # the C frontend's lexer reads these as LTL operators wherever they occur
    for v in sorted(declared):
        if v in ("X", "U", "R", "WU", "AP"):
            raise Refused("a variable named %s, an LTL keyword of the C frontend's lexer" % v)
    pre_vars = sorted(set(re.findall(r"\b([A-Za-z_]\w*)\b", pre)))
    for v in pre_vars:
        if v not in declared:
            raise Refused("PRE names '%s', which the program does not declare" % v)
    stop = "{ __term = 1; while (1) { } }"
    rest = re.sub(r"\breturn\b[^;]*;", stop, init + rest)
    lines = ["extern int __VERIFIER_nondet_int();", "", "int __term;"]
    for v in sorted(declared):
        ty = declared[v]
        lines.append("%s %s;" % (ty if not ty.startswith("unsigned") else "int", v))
    lines.append("")
    lines.append("int main() {")
    lines.append("  __term = 0;")
    for v in sorted(declared):
        lines.append("  %s = __VERIFIER_nondet_int();" % v)
    lines.append("  __VERIFIER_assume(%s);" % pre)
    lines.append(rest.strip("\n"))
    lines.append("  " + stop)
    lines.append("}")
    return "\n".join(lines) + "\n"


def gaps(fns, n):
    prev = 0
    for _, s, _, e in fns:
        yield prev, s
        prev = e
    yield prev, n


def split_top(s, sep):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    return out


def label(path):
    """the path from its `benchmarks/` component on, which names the source in any checkout"""
    i = path.rfind("benchmarks/")
    return path[i:] if i >= 0 else path


def main(argv):
    if len(argv) < 4:
        print(__doc__, file=sys.stderr)
        return 2
    t2_root, c_roots, out_dir = argv[1], argv[2:-1], argv[-1]
    sources = {}
    for root in c_roots:
        for d, _, fs in os.walk(root):
            for f in fs:
                if f.endswith(".c"):
                    sources.setdefault(f, []).append(os.path.join(d, f))
    programs = sorted(f[: -len(".t2")] for f in os.listdir(os.path.join(t2_root, "RA")) if f.endswith(".t2"))
    status = []
    written = 0
    for p in programs:
        for spec in sorted(SPECS):
            try:
                if len(sources.get(p, [])) != 1:
                    raise Refused("C source not found uniquely (%d)" % len(sources.get(p, [])))
                pre = pre_of(os.path.join(t2_root, spec, p + ".t2"))
                pre_vars = sorted(set(re.findall(r"\b([A-Za-z_]\w*)\b", pre)))
                x = pre_vars[0]
                with open(sources[p][0]) as f:
                    src = f.read()
                prog = rewrite(src, pre, x)
                os.makedirs(os.path.join(out_dir, spec), exist_ok=True)
                with open(os.path.join(out_dir, spec, p), "w") as f:
                    f.write("//@ ltl invariant %s: %s;\n" % (spec, SPECS[spec].format(x=x)))
                    f.write("// LTL-VerP %s on %s, x = %s, from %s\n" % (spec, p, x, label(sources[p][0])))
                    f.write(prog)
                status.append((p, spec, "written", "x=" + x))
                written += 1
            except Refused as e:
                status.append((p, spec, "refused", str(e)))
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, "STATUS.tsv"), "w") as f:
        for row in status:
            f.write("\t".join(row) + "\n")
    print("written %d of %d" % (written, len(status)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
