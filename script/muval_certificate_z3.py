#!/usr/bin/env python3
"""Check a MuVal certificate against the muCLP problem it is about, with Z3 and
nothing of CoAR's but the problem's printed text.

    muval_certificate_z3.py PROBLEM.txt CERTIFICATE.txt [Z3]

PROBLEM.txt is the muCLP as CoAR's Printer writes it (`-c config/solver/printer.json`):
a query line, `s.t.`, then one equation per predicate,
`NAME (x:int) ... : bool =nu|=mu|=mu_or_nu BODY;`.  CERTIFICATE.txt is MuVal's
output with `print_certificates` on: the verdict line, then S-expression lines
(`(invariant NAME PARAMS FORMULA ...)`, `(ranking NAME PARAMS (pieces ...)
(transition PREV RELATION) ...)`, `(skipped ...)`).  Z3 is the solver binary
(default: `z3` on the PATH).

What it asks, each as one SMT-LIB script whose `unsat` answer is the pass:
- for every predicate P with an invariant I_P: forall params. I_P => body_P,
  every predicate application in body_P replaced by the invariant of the
  callee (the assignment is closed under the bodies);
- the query with every application replaced by the invariant (it holds);
- for every ranking of a predicate W with relation R(prev, cur): every
  return of W to itself through predicates that are not cut points (the
  `mu_or_nu` ones, unfolded) satisfies R from W's current parameters to the
  ones it is called with, starting from a state in I_W (the direct returns);
  and R is transitive (so it relates any earlier visit to any later one along
  such returns).
Together the first two make the invariants a post-fixpoint of the problem read
with greatest fixpoints that contains the query's states: every reachable
state at a predicate satisfies its invariant.

The parser covers the printed syntax LLVMFront's integer problems use
(integers, booleans, + - *, comparisons, not, /\\, \\/, =>, <=>, forall,
exists); anything else is reported as unparsed and counts as a failure.
Exit status 0 when every obligation is `unsat`, 1 otherwise, 2 on bad input.
"""
import os
import re
import subprocess
import sys
import tempfile

# -- S-expressions -----------------------------------------------------------

def sexp_tokens(s):
    i, out = 0, []
    while i < len(s):
        c = s[i]
        if c.isspace():
            i += 1
        elif c in "()":
            out.append(c)
            i += 1
        elif c == '"':
            j = i + 1
            while j < len(s) and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append(s[i:j + 1])
            i = j + 1
        elif c == "|":
            j = s.index("|", i + 1)
            out.append(s[i:j + 1])
            i = j + 1
        else:
            j = i
            while j < len(s) and not s[j].isspace() and s[j] not in "()":
                j += 1
            out.append(s[i:j])
            i = j
    return out


def sexp_parse(s):
    toks = sexp_tokens(s)
    pos = 0

    def go():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t == "(":
            lst = []
            while toks[pos] != ")":
                lst.append(go())
            pos += 1
            return lst
        return t

    return go()


def sexp_str(e):
    if isinstance(e, list):
        return "(" + " ".join(sexp_str(x) for x in e) + ")"
    return e

# -- The printed muCLP ---------------------------------------------------------

TOKEN = re.compile(r"\s*(<=>|=>|/\\|\\/|<=|>=|<>|!=|[-+*()<>=.:,]|[A-Za-z_][A-Za-z0-9_.'#]*|\d+)")


def tokenize(s):
    s = s.strip()
    pos, out = 0, []
    while pos < len(s):
        m = TOKEN.match(s, pos)
        if not m or m.end() == pos:
            raise ValueError("cannot read %r" % s[pos:pos + 30])
        out.append(m.group(1))
        pos = m.end()
    return out


class Parser:
    """Infix formulas as CoAR prints them, to SMT-LIB terms (strings).
    [arity] gives each predicate's arity, so that an application's arguments
    are read greedily as atoms."""

    def __init__(self, toks, arity):
        self.t, self.i, self.arity = toks, 0, arity

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self, x=None):
        tok = self.peek()
        if x is not None and tok != x:
            raise ValueError("expected %r, got %r at %d" % (x, tok, self.i))
        self.i += 1
        return tok

    def formula(self):
        if self.peek() in ("forall", "exists"):
            q = self.eat()
            binds = []
            while self.peek() == "(":
                self.eat("(")
                name = self.eat()
                self.eat(":")
                sort = self.eat()
                self.eat(")")
                binds.append("(%s %s)" % (name, {"int": "Int", "bool": "Bool"}[sort]))
            self.eat(".")
            body = self.formula()
            return "(%s (%s) %s)" % (q, " ".join(binds), body)
        lhs = self.disj()
        if self.peek() == "=>":
            self.eat()
            return "(=> %s %s)" % (lhs, self.formula())
        if self.peek() == "<=>":
            self.eat()
            return "(= %s %s)" % (lhs, self.formula())
        return lhs

    def disj(self):
        x = self.conj()
        while self.peek() == "\\/":
            self.eat()
            x = "(or %s %s)" % (x, self.conj())
        return x

    def conj(self):
        x = self.neg()
        while self.peek() == "/\\":
            self.eat()
            x = "(and %s %s)" % (x, self.neg())
        return x

    def neg(self):
        if self.peek() == "not":
            self.eat()
            return "(not %s)" % self.neg()
        return self.atom()

    def atom(self):
        tok = self.peek()
        if tok in ("true", "false"):
            self.eat()
            return tok
        if tok in ("forall", "exists"):
            return self.formula()
        if tok in self.arity:
            self.eat()
            args = [self.simple_term() for _ in range(self.arity[tok])]
            return "(%s%s)" % (tok, "".join(" " + a for a in args)) if args else tok
        if tok == "(":
            # a parenthesised formula or the left term of a comparison
            save = self.i
            try:
                self.eat("(")
                f = self.formula()
                self.eat(")")
                if self.peek() not in ("<", "<=", ">", ">=", "=", "<>", "!=", "+", "-", "*"):
                    return f
            except (ValueError, KeyError, IndexError):
                pass
            self.i = save
        lhs = self.term()
        op = self.eat()
        rhs = self.term()
        if op in ("<>", "!="):
            return "(not (= %s %s))" % (lhs, rhs)
        if op not in ("<", "<=", ">", ">=", "="):
            raise ValueError("not a comparison: %r" % op)
        return "(%s %s %s)" % (op, lhs, rhs)

    def term(self):
        x = self.prod()
        while self.peek() in ("+", "-"):
            op = self.eat()
            x = "(%s %s %s)" % (op, x, self.prod())
        return x

    def prod(self):
        x = self.unary()
        while self.peek() == "*":
            self.eat()
            x = "(* %s %s)" % (x, self.unary())
        return x

    def unary(self):
        if self.peek() == "-":
            self.eat()
            return "(- %s)" % self.unary()
        return self.simple_term()

    def simple_term(self):
        tok = self.eat()
        if tok == "(":
            x = self.term()
            self.eat(")")
            return x
        if tok == "-":
            return "(- %s)" % self.simple_term()
        if re.fullmatch(r"\d+", tok) or re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.'#]*", tok):
            return tok
        raise ValueError("not a term: %r" % tok)


def read_problem(text):
    lines = [l.strip() for l in text.splitlines() if l.strip()]
    i = lines.index("s.t.")
    query_text = lines[i - 1]
    preds = {}
    for l in lines[i + 1:]:
        m = re.match(r"([A-Za-z_][A-Za-z0-9_]*)((?:\s*\([^()]*:[a-z]+\))*)\s*:\s*bool\s*=(mu_or_nu|nu|mu)\s*(.*);$", l)
        if not m:
            raise ValueError("cannot read the equation %r" % l[:60])
        params = re.findall(r"\(([^():]+):([a-z]+)\)", m.group(2))
        preds[m.group(1)] = {
            "params": [(n.strip(), {"int": "Int", "bool": "Bool"}[s]) for n, s in params],
            "kind": m.group(3),
            "body_text": m.group(4),
        }
    arity = {p: len(d["params"]) for p, d in preds.items()}
    for d in preds.values():
        pr = Parser(tokenize(d["body_text"]), arity)
        d["body"] = pr.formula()
        if pr.peek() is not None:
            raise ValueError("trailing text in a body")
    pq = Parser(tokenize(query_text), arity)
    query = pq.formula()
    return preds, query

# -- Obligations ---------------------------------------------------------------

def z3_unsat(z3, script):
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
        f.write(script)
        name = f.name
    try:
        r = subprocess.run([z3, "-T:60", name], capture_output=True, text=True)
        return r.stdout.strip().splitlines()[0] if r.stdout.strip() else "error: " + r.stderr.strip()
    finally:
        os.unlink(name)


def define(preds, invs, override=None):
    """define-fun per predicate: its invariant, or [override] for some."""
    out = []
    for p, d in preds.items():
        params = " ".join("(%s %s)" % ps for ps in d["params"])
        body = (override or {}).get(p, invs.get(p))
        if body is None:
            continue
        out.append("(define-fun %s (%s) Bool %s)" % (p, params, body))
    return "\n".join(out)


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    preds, query = read_problem(open(sys.argv[1]).read())
    z3 = sys.argv[3] if len(sys.argv) > 3 else "z3"
    lines = open(sys.argv[2]).read().splitlines()
    invs, ranks = {}, {}
    for l in lines[1:]:
        if not l.startswith("("):
            continue
        e = sexp_parse(l)
        if e[0] == "invariant":
            name, params, phi = e[1], e[2], e[3]
            # rename the certificate's parameters to the problem's (same order)
            mine = [p for p, _ in preds[name]["params"]]
            theirs = [p[0] for p in params]
            if mine != theirs:
                print("FAIL %s: parameters %s, the problem says %s" % (name, theirs, mine))
                return 1
            invs[name] = sexp_str(phi)
        elif e[0] == "ranking":
            name = e[1]
            trans = next(x for x in e if isinstance(x, list) and x and x[0] == "transition")
            ranks[name] = (e[2], trans[1], sexp_str(trans[2]))
    if not invs:
        print("no invariant lines")
        return 1
    missing = [p for p in preds if p not in invs]
    failures = 0
    if missing:
        print("FAIL: no invariant for %s" % ", ".join(missing))
        failures += 1
    decls = define(preds, invs)
    for p, d in preds.items():
        if p not in invs:
            continue
        params = " ".join("(%s %s)" % ps for ps in d["params"])
        closed = "(forall (%s) %s)" % (params, "(=> %s %s)" % (invs[p], d["body"])) if params else "(=> %s %s)" % (invs[p], d["body"])
        ans = z3_unsat(z3, "%s\n(assert (not %s))\n(check-sat)\n" % (decls, closed))
        ok = ans == "unsat"
        failures += not ok
        print("%s closed under its body: %s" % (p, "pass" if ok else "FAIL (%s)" % ans))
    ans = z3_unsat(z3, "%s\n(assert (not %s))\n(check-sat)\n" % (decls, query))
    ok = ans == "unsat"
    failures += not ok
    print("query holds under the invariants: %s" % ("pass" if ok else "FAIL (%s)" % ans))
    # rankings: the direct returns, the fix predicates unfolded
    names = set(preds)

    def calls(body):
        return set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", body)) & names

    for w, (params, prev, rel) in ranks.items():
        # the predicates W reaches through mu_or_nu predicates only: a return
        # through another cut point is not unfolded, so it is not checked here
        seen, todo = set(), list(calls(preds[w]["body"]))
        while todo:
            q = todo.pop()
            if q in seen:
                continue
            seen.add(q)
            if preds[q]["kind"] == "mu_or_nu":
                todo += list(calls(preds[q]["body"]))
        others = sorted(q for q in seen if q != w and preds[q]["kind"] != "mu_or_nu")
        if w not in seen:
            print("%s ranking: no return avoids the cut points %s; NOT CHECKED" % (w, ", ".join(others)))
        elif others:
            print("%s ranking: the returns through %s are not checked" % (w, ", ".join(others)))
        cur = [p[0] for p in params]
        prv = [p[0] for p in prev]
        sorts = [p[1] for p in params]
        # W(args) becomes R(cur -> args) and I_W(args); a cut point its invariant;
        # a mu_or_nu predicate its body (they form no cycle among themselves)
        argn = ["a%d__" % k for k in range(len(cur))]
        decls_r = []
        bnd = " ".join("(%s %s)" % (a, s) for a, s in zip(argn, sorts))
        # R as a function of (prev..., cur...)
        decls_r.append("(define-fun R__ (%s) Bool %s)" % (
            " ".join("(%s %s)" % (p, s) for p, s in zip(prv, sorts)) + " " +
            " ".join("(%s %s)" % (c, s) for c, s in zip(cur, sorts)), rel))
        # W's own parameters are global constants for this obligation
        decls_r += ["(declare-const %s %s)" % (c, s) for c, s in zip(cur, sorts)]
        ret = "(and (R__ %s %s) (%s %s))" % (" ".join(cur), " ".join(argn), w + "__inv", " ".join(argn)) if argn else "(R__)"
        defs = []
        for p, d in preds.items():
            ps = " ".join("(%s %s)" % x for x in d["params"])
            if p == w:
                defs.append("(define-fun %s__inv (%s) Bool %s)" % (w, ps, invs[w]))
                defs.append("(define-fun %s (%s) Bool %s)" % (p, bnd, ret))
            elif d["kind"] == "mu_or_nu":
                pass  # defined below, in dependency order
            else:
                defs.append("(define-fun %s (%s) Bool %s)" % (p, ps, invs[p]))
        # mu_or_nu predicates in an order where every callee comes first
        fix = [p for p, d in preds.items() if d["kind"] == "mu_or_nu"]
        done = set()
        while fix:
            progressed = False
            for p in list(fix):
                calls = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", preds[p]["body"])) & set(preds)
                if all(c not in fix or c == p for c in calls) and p not in calls:
                    ps = " ".join("(%s %s)" % x for x in preds[p]["params"])
                    defs.append("(define-fun %s (%s) Bool %s)" % (p, ps, preds[p]["body"]))
                    fix.remove(p)
                    progressed = True
            if not progressed:
                print("FAIL %s: the mu_or_nu predicates form a cycle" % w)
                failures += 1
                break
        script = "\n".join(decls_r + defs) + "\n(assert %s)\n(assert (not %s))\n(check-sat)\n" % (
            "(%s__inv %s)" % (w, " ".join(cur)) if cur else w + "__inv", preds[w]["body"])
        ans = z3_unsat(z3, script)
        ok = ans == "unsat"
        failures += not ok
        print("%s ranking decreases on its direct returns: %s" % (w, "pass" if ok else "FAIL (%s)" % ans))
        a = ["%s__a" % c for c in cur]
        b = ["%s__b" % c for c in cur]
        c3 = ["%s__c" % c for c in cur]
        decl3 = "\n".join("(declare-const %s %s)" % (v, s) for vs in (a, b, c3) for v, s in zip(vs, sorts))
        script = decls_r[0] + "\n" + decl3 + "\n(assert (R__ %s %s))\n(assert (R__ %s %s))\n(assert (not (R__ %s %s)))\n(check-sat)\n" % (
            " ".join(a), " ".join(b), " ".join(b), " ".join(c3), " ".join(a), " ".join(c3))
        ans = z3_unsat(z3, script)
        ok = ans == "unsat"
        failures += not ok
        print("%s ranking relation transitive: %s" % (w, "pass" if ok else "FAIL (%s)" % ans))
    print("DONE failures=%d" % failures)
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
