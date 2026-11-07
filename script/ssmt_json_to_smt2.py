#!/usr/bin/env python3
"""Convert a stochastic-SMT instance in the JSON form of the SSMT tool of Lin, Su, Jiang and
Unno (SAT 2026; github.com/NTU-ALComLab/SSMT, directory TB/) to the SMT-LIB form this
repository's `-p smt` reader takes, with `(random ((v (Uniform lo hi))) ...)` binders.

    script/ssmt_json_to_smt2.py convert [--encoding nested|flat] IN.json > OUT.smt2
    script/ssmt_json_to_smt2.py compare A.smt2 B.smt2 > QUERIES.smt2

The JSON gives `vars` in prefix order, `quant` (e = exists, a = forall, r = random) per variable,
`var_range` a Wolfram-syntax interval per variable (possibly depending on earlier variables, or
null), `var_dist` a `Uniform(lo,hi)` per random variable, and `condition` a list of
Wolfram-syntax formulas, conjoined.  Every variable is real.

The domains of the non-random variables are folded into the matrix: an existential variable's
domain is conjoined, a universal variable's domain is a guard.  Two encodings:

  nested (the default): the folding is scoped by the prefix, outermost variable outermost,
      D_1 op_1 (D_2 op_2 (... condition)) with op = `and` for exists and `=>` for forall.
      With sup over the empty set read as 0 and inf over the empty set read as 1, this gives
      every instance the value the JSON states, whether or not a domain is empty -- including a
      universal domain that depends on an existential variable outside its own domain.
  flat: the shape of the earlier in-house files, all universal guards disjoined at the top and
      every existential domain conjoined beside the condition.  It gives the same value only
      when every universal domain is non-empty at every value of the variables it depends on;
      it exists to compare against those files.

A random variable's `var_range` is dropped: it repeats the support of its distribution, so it
holds with probability one.  The JSON's `ranges` (the density's normaliser) is dropped too.

`compare` reads two files of this form, renames their variables by position, and prints Z3
queries: each random variable's support bounds must be equal and the two matrices equivalent
under the supports.  Each query is `(check-sat)` expected `unsat`; a `sat` names a difference.
The quantifier prefixes are compared directly and a mismatch is reported on stderr.
"""
import json
import re
import sys
from fractions import Fraction


# ---------------------------------------------------------------- Wolfram-syntax reader

TOKEN = re.compile(r"\s*(?:(\d+(?:\.\d+)?)|([A-Za-z][A-Za-z0-9_]*)|(<=|>=|==|!=|&&|\|\||[-+*/^()<>=!,]))")


def tokenize(s, varnames):
    """Tokens of a Wolfram-syntax expression.  An identifier that is not a variable is split
    into variables (`xy` is x times y, the implicit multiplication the inputs use)."""
    out, pos = [], 0
    s = s.strip()
    while pos < len(s):
        m = TOKEN.match(s, pos)
        if not m or m.end() == pos:
            raise ValueError("cannot read %r at %d" % (s, pos))
        num, ident, op = m.groups()
        if num is not None:
            out.append(("num", num))
        elif ident is not None:
            parts = split_ident(ident, varnames)
            if parts is None:
                raise ValueError("unknown identifier %r in %r" % (ident, s))
            out.extend(("var", p) for p in parts)
        else:
            out.append(("op", op))
        pos = m.end()
    return out


def split_ident(ident, varnames):
    if ident in varnames:
        return [ident]
    for v in sorted(varnames, key=len, reverse=True):
        if ident.startswith(v):
            rest = split_ident(ident[len(v):], varnames)
            if rest is not None:
                return [v] + rest
    return None


class Parser:
    """Precedence: || < && < ! < comparison chain < + - < * / (and juxtaposition) < unary - < ^."""

    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else (None, None)

    def eat(self, op=None):
        tok = self.peek()
        if op is not None and tok != ("op", op):
            raise ValueError("expected %r, got %r" % (op, tok))
        self.i += 1
        return tok

    def done(self):
        if self.i != len(self.t):
            raise ValueError("trailing tokens %r" % (self.t[self.i:],))

    def disj(self):
        xs = [self.conj()]
        while self.peek() == ("op", "||"):
            self.eat()
            xs.append(self.conj())
        return xs[0] if len(xs) == 1 else ["or"] + xs

    def conj(self):
        xs = [self.neg()]
        while self.peek() == ("op", "&&"):
            self.eat()
            xs.append(self.neg())
        return xs[0] if len(xs) == 1 else ["and"] + xs

    def neg(self):
        if self.peek() == ("op", "!"):
            self.eat()
            return ["not", self.neg()]
        return self.cmp()

    def cmp(self):
        # A parenthesised formula and a parenthesised term both start with "(": try the formula.
        if self.peek() == ("op", "("):
            save = self.i
            try:
                self.eat("(")
                f = self.disj()
                self.eat(")")
                if self.peek()[0] == "op" and self.peek()[1] in ("<", "<=", ">", ">=", "=", "==", "!="):
                    raise ValueError("a term, not a formula")
                if is_formula(f):
                    return f
            except ValueError:
                pass
            self.i = save
        terms, ops = [self.sum()], []
        while self.peek()[0] == "op" and self.peek()[1] in ("<", "<=", ">", ">=", "=", "==", "!="):
            ops.append(self.eat()[1])
            terms.append(self.sum())
        if not ops:
            return terms[0]
        atoms = []
        for k, op in enumerate(ops):
            op = {"==": "=", "!=": "distinct"}.get(op, op)
            atoms.append([op, terms[k], terms[k + 1]])
        return atoms[0] if len(atoms) == 1 else ["and"] + atoms

    def sum(self):
        x = self.prod()
        while self.peek() in (("op", "+"), ("op", "-")):
            op = self.eat()[1]
            x = [op, x, self.prod()]
        return x

    def starts_atom(self):
        k, v = self.peek()
        return k in ("num", "var") or (k, v) == ("op", "(")

    def prod(self):
        x = self.unary()
        while True:
            if self.peek() in (("op", "*"), ("op", "/")):
                op = self.eat()[1]
                x = [op, x, self.unary()]
            elif self.starts_atom():
                x = ["*", x, self.power()]
            else:
                return x

    def unary(self):
        if self.peek() == ("op", "-"):
            self.eat()
            return ["-", self.unary()]
        if self.peek() == ("op", "+"):
            self.eat()
            return self.unary()
        return self.power()

    def power(self):
        b = self.atom()
        if self.peek() == ("op", "^"):
            self.eat()
            e = self.unary()
            if not (isinstance(e, Fraction) and e.denominator == 1 and e >= 1):
                raise ValueError("only positive integer powers are supported")
            return ["*"] + [b] * int(e) if e > 1 else b
        return b

    def atom(self):
        k, v = self.eat()
        if k == "num":
            return Fraction(v)
        if k == "var":
            return ("var", v)
        if (k, v) == ("op", "("):
            x = self.sum()
            self.eat(")")
            return x
        raise ValueError("unexpected token %r" % ((k, v),))


def is_formula(x):
    return isinstance(x, list) and x[0] in ("and", "or", "not", "<", "<=", ">", ">=", "=", "distinct")


def parse_formula(s, varnames):
    p = Parser(tokenize(s, varnames))
    f = p.disj()
    p.done()
    if not is_formula(f):
        raise ValueError("not a formula: %r" % s)
    return f


def parse_term(s, varnames):
    p = Parser(tokenize(s, varnames))
    t = p.sum()
    p.done()
    return t


def fold(x):
    """Fold constant arithmetic to a Fraction, so `1/2` prints as 0.5 and `-(x+y+1/2)` keeps x, y."""
    if isinstance(x, list):
        args = [fold(a) for a in x[1:]]
        if x[0] in ("+", "-", "*", "/") and all(isinstance(a, Fraction) for a in args):
            if x[0] == "-" and len(args) == 1:
                return -args[0]
            r = args[0]
            for a in args[1:]:
                r = {"+": r + a, "-": r - a, "*": r * a, "/": r / a if a != 0 else None}[x[0]]
                if r is None:
                    raise ValueError("division by zero")
            return r
        return [x[0]] + args
    return x


def smt(x):
    if isinstance(x, Fraction):
        if x < 0:
            return "(- %s)" % smt(-x)
        if x.denominator == 1:
            return str(x.numerator)
        d = x.denominator
        while d % 2 == 0:
            d //= 2
        while d % 5 == 0:
            d //= 5
        if d == 1:  # a terminating decimal
            s = "%.20f" % (x.numerator / x.denominator)
            return s.rstrip("0")
        return "(/ %d %d)" % (x.numerator, x.denominator)
    if isinstance(x, tuple):
        return x[1]
    if x[0] == "/" and not isinstance(x[2], Fraction):
        raise ValueError("division by a non-constant is not linear arithmetic: %r" % (x,))
    return "(%s %s)" % (x[0], " ".join(smt(a) for a in x[1:]))


# ---------------------------------------------------------------- conversion

UNIFORM = re.compile(r"^\s*Uniform\s*\((.*)\)\s*$")


def split_top_comma(s):
    depth, parts, cur = 0, [], ""
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    return parts


def convert(d, encoding="nested"):
    vs, qs = d["vars"], d["quant"]
    names = set(vs)
    assert len(vs) == len(qs)
    dom = {}
    for v, q in zip(vs, qs):
        r = d["var_range"].get(v)
        if q in ("e", "a") and r is not None:
            dom[v] = fold(parse_formula(r, names))
    cond = [fold(parse_formula(c, names)) for c in d["condition"]]
    phi = cond[0] if len(cond) == 1 else ["and"] + cond
    if encoding == "nested":
        for v, q in reversed(list(zip(vs, qs))):
            if v in dom:
                phi = ["and", dom[v], phi] if q == "e" else ["=>", dom[v], phi]
    else:
        ex = [dom[v] for v, q in zip(vs, qs) if q == "e" and v in dom]
        un = [dom[v] for v, q in zip(vs, qs) if q == "a" and v in dom]
        if ex:
            phi = ["and"] + ex + [phi]
        if un:
            phi = ["or"] + [["not", g] for g in un] + [phi]
    body, indent = smt_pretty(phi, len(vs)), len(vs)
    for k in range(len(vs) - 1, -1, -1):
        v, q = vs[k], qs[k]
        pad = "    " * (k + 1)
        if q == "r":
            m = UNIFORM.match(d["var_dist"][v])
            if not m:
                raise ValueError("only Uniform distributions are supported: %r" % d["var_dist"][v])
            lo, hi = split_top_comma(m.group(1))
            binder = "(random ((%s (Uniform %s %s)))" % (
                v, smt(fold(parse_term(lo, names))), smt(fold(parse_term(hi, names))))
        else:
            binder = "(%s ((%s Real))" % ("exists" if q == "e" else "forall", v)
        body = "%s%s\n%s\n%s)" % (pad, binder, body, pad)
    return "(assert\n%s\n)\n" % body


def smt_pretty(f, depth):
    pad = "    " * (depth + 1)
    if isinstance(f, list) and f[0] in ("and", "or", "=>", "not"):
        inner = "\n".join(smt_pretty(a, depth + 1) for a in f[1:])
        return "%s(%s\n%s\n%s)" % (pad, f[0], inner, pad)
    return pad + smt(f)


# ---------------------------------------------------------------- comparison

def sexp(s):
    s = re.sub(r";[^\n]*", "", s)
    toks = re.findall(r"\(|\)|[^\s()]+", s)
    stack = [[]]
    for t in toks:
        if t == "(":
            stack.append([])
        elif t == ")":
            x = stack.pop()
            stack[-1].append(x)
        else:
            stack[-1].append(t)
    return stack[0]


def prefix_and_matrix(path):
    top = sexp(open(path).read())
    asserts = [x for x in top if isinstance(x, list) and x and x[0] == "assert"]
    assert len(asserts) == 1, path
    f, prefix = asserts[0][1], []
    while isinstance(f, list) and f and f[0] in ("exists", "forall", "random"):
        for b in f[1]:
            prefix.append((f[0], b[0], b[1]))
        f = f[2]
    return prefix, f


def rename(x, m):
    if isinstance(x, list):
        return [rename(a, m) for a in x]
    return m.get(x, x)


def show(x):
    if isinstance(x, list):
        return "(" + " ".join(show(a) for a in x) + ")"
    # `-3` is accepted by this repository's reader, not by Z3.
    if re.fullmatch(r"-\d+(\.\d+)?", x):
        return "(- %s)" % x[1:]
    return x


def compare(pa, pb):
    (xa, ma), (xb, mb) = prefix_and_matrix(pa), prefix_and_matrix(pb)
    kinds_a, kinds_b = [k for k, _, _ in xa], [k for k, _, _ in xb]
    if kinds_a != kinds_b:
        sys.stderr.write("PREFIX DIFFERS: %s vs %s\n" % (kinds_a, kinds_b))
        return 1
    va = {v: "v%d" % i for i, (_, v, _) in enumerate(xa)}
    vb = {v: "v%d" % i for i, (_, v, _) in enumerate(xb)}
    out = ["(set-logic ALL)"]
    out += ["(declare-const v%d Real)" % i for i in range(len(xa))]
    supports = []
    for i, ((k, _, da), (_, _, db)) in enumerate(zip(xa, xb)):
        if k != "random":
            continue
        assert da[0] == db[0] == "Uniform", (da, db)
        lo_a, hi_a = show(rename(da[1], va)), show(rename(da[2], va))
        lo_b, hi_b = show(rename(db[1], vb)), show(rename(db[2], vb))
        out += ["(push)", "(assert (or (distinct %s %s) (distinct %s %s)))" % (lo_a, lo_b, hi_a, hi_b),
                "(check-sat)", "(pop)"]
        supports.append("(<= %s v%d)" % (lo_a, i))
        supports.append("(<= v%d %s)" % (i, hi_a))
    out += ["(push)"] + ["(assert %s)" % s for s in supports]
    out += ["(assert (distinct %s %s))" % (show(rename(ma, va)), show(rename(mb, vb))),
            "(check-sat)", "(pop)"]
    print("\n".join(out))
    return 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "convert":
        enc = "nested"
        if len(a) > 2 and a[1] == "--encoding":
            enc, a = a[2], a[2:]
        sys.stdout.write(convert(json.load(open(a[1])), enc))
    elif a and a[0] == "compare" and len(a) == 3:
        sys.exit(compare(a[1], a[2]))
    else:
        sys.stderr.write(__doc__)
        sys.exit(2)
