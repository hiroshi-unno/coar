#!/usr/bin/env python3
"""Encode SimSat's linear reachability games (`.rg`) as muCLP, existential CHC and universal CHC.

Source: the 25 games of benchmarks/QSMT/ijcai2016/test/reachability/ (the submodule of SimSat,
github.com/zkincaid/strategy-improvement, MIT licence), the reachability-game benchmarks of Farzan and Kincaid, "Strategy
synthesis for linear arithmetic games", PACMPL 2 (POPL), article 61, 2018,
https://doi.org/10.1145/3158149.

The game, as SimSat's parser (ark/arkParse.mly, ark/arkLex.mll) and its solver (ark/game.ml,
simsat/simsat.ml) define it, and as the paper's section 3.2 states it:
  * positions are vectors over the variables of `vars:`, all of sort real (`TyReal`);
  * REACH picks the starting position, any position satisfying `init:`;
  * then SAFE and REACH alternate, SAFE first: SAFE moves from x to y when safe(x, y) holds
    (unprimed names are x, primed names are y), REACH moves from y to z when reach(y, z) holds
    (in the file, unprimed names are y and primed names are z);
  * the first player without a legal move loses, and SAFE wins every infinite play.
So REACH wins from a position x (SAFE to move) exactly when x is in the least fixpoint
      A = mu A. \\x. forall y. safe(x, y) => exists z. reach(y, z) /\\ A(z)
and SAFE wins exactly on its complement, the greatest fixpoint of the dual operator.

Three encodings are written for each game, each exact for the game over the reals:
  muCLP  OUT_HES/<name>.hes     exists x. init(x) /\\ A(x), A as above (a least fixpoint);
                                valid  iff REACH wins
  ECHC   OUT_ECHC/<name>.smt2   init(x) => Inv(x);  Inv(x) => exists y. safe(x, y) /\\ Mid(y);
                                Mid(y) /\\ reach(y, z) => Inv(z)
                                sat    iff SAFE wins
  UCHC   OUT_UCHC/<name>.smt2   reach(y, z) /\\ Att(z) => AttR(y);
                                (forall y. safe(x, y) => AttR(y)) => Att(x);
                                init(x) /\\ Att(x) => false
                                sat    iff SAFE wins (unsat iff REACH wins)

The reader follows SimSat's grammar exactly, including its two quirks: the lexer reads `-1` as one
numeral (so `x -1` does not parse, as in SimSat), and binary minus associates to the right
(`a - b + c` is `a - (b + c)`); a file whose meaning depends on the second is written as SimSat
reads it and the record says so.  A product of two non-constant terms, a division (which SimSat's
game lexer never produces), a name outside `vars:` and their primed copies, and a primed name in
`init:` are refused: nothing is written for that game.  Every atom is scaled by the least common
multiple of its denominators, so the outputs carry integer coefficients only.

The record, OUT_HES/STATUS.tsv, has one line per source:
  name  outcome  expected_winner  expected_source  hes  echc  uchc  detail
with outcome `generated` or `refused`, the expected answer of each encoding (`valid`/`invalid`,
`sat`/`unsat`, or `-`) derived from the expected winner, and the expected winner's source read
from script/rg_games_expected.txt.

Run from the repository root:
  python3 -I script/gen_rg_games.py [--src DIR] [--out-hes DIR] [--out-echc DIR] [--out-uchc DIR]
                                    [--only NAME ...]
Exit status 0 when every source has a record, 2 on a usage error.
"""

import argparse
import os
import re
import sys
from fractions import Fraction
from functools import reduce
from math import gcd


def lcm(*ns):
    """Least common multiple of positive integers (math.lcm needs Python 3.9)."""
    return reduce(lambda a, b: a * b // gcd(a, b), ns, 1)

SRC = 'benchmarks/QSMT/ijcai2016/test/reachability'
OUT_HES = 'benchmarks/muCLP/rg_games'
OUT_ECHC = 'benchmarks/ECHC/rg_games'
OUT_UCHC = 'benchmarks/UCHC/rg_games'
EXPECTED = 'script/rg_games_expected.txt'


class Refuse(Exception):
    pass


class Fatal(Refuse):
    """A refusal that no backtracking alternative can avoid (a non-linear product)."""


# ---------------------------------------------------------------- lexer (ark/arkLex.mll, game_token)
# ocamllex takes the longest match and, among equally long ones, the first rule.
TOKEN_RULES = [
    ('WS', r'[ \t]+'),
    ('NL', r'\r\n|\r|\n'),
    ('AND', r'&&'), ('OR', r'\|\|'), ('NOT', r'!'),
    ('LEQ', r'<='), ('GEQ', r'>='), ('EQ', r'='), ('LT', r'<'), ('GT', r'>'),
    ('MUL', r'\*'), ('ADD', r'\+'), ('MINUS', r'-'),
    ('LPAREN', r'\('), ('RPAREN', r'\)'), ('COMMA', r','),
    ('INIT', r'init:'), ('SAFE', r'safe:'), ('REACH', r'reach:'), ('VARS', r'vars:'),
    ('ID', r"[_a-zA-Z$?][_a-zA-Z0-9']*"),
    ('REAL', r'-?[0-9]+/?[0-9]*'),
]
TOKEN_RES = [(k, re.compile(p)) for k, p in TOKEN_RULES]


def lex(text):
    toks, i = [], 0
    while i < len(text):
        best = None
        for kind, rx in TOKEN_RES:
            m = rx.match(text, i)
            if m and m.end() > i and (best is None or m.end() > best[1]):
                best = (kind, m.end())
        if best is None:
            raise Refuse('lexing error at offset %d (%r)' % (i, text[i:i + 10]))
        kind, end = best
        lexeme = text[i:end]
        if kind not in ('WS', 'NL'):
            if kind == 'REAL':
                num, _, den = lexeme.partition('/')
                if '/' in lexeme and den == '':
                    raise Refuse('numeral %r has no denominator' % lexeme)
                if den != '' and int(den) == 0:
                    raise Refuse('numeral %r divides by zero' % lexeme)
                toks.append((kind, Fraction(int(num), int(den) if den else 1)))
            else:
                toks.append((kind, lexeme))
        i = end
    toks.append(('EOF', None))
    return toks


# ---------------------------------------------------------------- parser (ark/arkParse.mly, `game`)
class Lin:
    """A linear term: {name: coefficient} plus a constant, coefficients rational."""

    def __init__(self, coef=None, const=Fraction(0)):
        self.coef = {k: v for k, v in (coef or {}).items() if v != 0}
        self.const = Fraction(const)

    def add(self, o, sign=1):
        c = dict(self.coef)
        for k, v in o.coef.items():
            c[k] = c.get(k, Fraction(0)) + sign * v
        return Lin(c, self.const + sign * o.const)

    def scale(self, q):
        return Lin({k: v * q for k, v in self.coef.items()}, self.const * q)

    def is_const(self):
        return not self.coef


class Parser:
    def __init__(self, toks):
        self.toks, self.i = toks, 0
        self.notes = set()

    def peek(self):
        return self.toks[self.i][0]

    def take(self, kind):
        if self.peek() != kind:
            raise Refuse('parse error: expected %s, found %s %r'
                         % (kind, self.peek(), self.toks[self.i][1]))
        v = self.toks[self.i][1]
        self.i += 1
        return v

    def game(self):
        self.take('VARS')
        names = [self.take('ID')]
        while self.peek() == 'COMMA':
            self.take('COMMA')
            names.append(self.take('ID'))
        self.take('INIT')
        init = self.disj()
        self.take('SAFE')
        safe = self.disj()
        self.take('REACH')
        reach = self.disj()
        self.take('EOF')
        return names, init, safe, reach

    def disj(self):
        ds = [self.conj()]
        while self.peek() == 'OR':
            self.take('OR')
            ds.append(self.conj())
        return ds[0] if len(ds) == 1 else ('or', ds)

    def conj(self):
        cs = [self.atomf()]
        while self.peek() == 'AND':
            self.take('AND')
            cs.append(self.atomf())
        return cs[0] if len(cs) == 1 else ('and', cs)

    def atomf(self):
        if self.peek() == 'NOT':
            self.take('NOT')
            self.take('LPAREN')
            f = self.disj()
            self.take('RPAREN')
            return ('not', f)
        # `term relop term` and `( formula )` both may start with `(`; at most one parses, since a
        # term holds no relation symbol, so try the term first and fall back.
        save, saved_notes = self.i, set(self.notes)
        try:
            s, _ = self.add()
            op = self.peek()
            if op not in ('LEQ', 'GEQ', 'LT', 'GT', 'EQ'):
                raise Refuse('parse error: relation expected')
            self.take(op)
            t, _ = self.add()
            if op == 'GEQ':
                return ('atom', 'LEQ', t, s)
            if op == 'GT':
                return ('atom', 'LT', t, s)
            return ('atom', op, s, t)
        except Fatal:
            raise
        except Refuse:
            self.i, self.notes = save, saved_notes
            self.take('LPAREN')
            f = self.disj()
            self.take('RPAREN')
            return f

    # game_additive_term is right-recursive: s + t and s - t with t an additive term.
    def add(self):
        s = self.mult()
        if self.peek() in ('ADD', 'MINUS'):
            op = self.take(self.peek())
            t, t_compound = self.add()
            if op == '-':
                if t_compound:
                    self.notes.add('right-associative minus changes the meaning')
                return s.add(t, -1), True
            return s.add(t), True
        return s, False

    def mult(self):
        s = self.atomt()
        while self.peek() == 'MUL':
            self.take('MUL')
            t = self.atomt()
            if s.is_const():
                s = t.scale(s.const)
            elif t.is_const():
                s = s.scale(t.const)
            else:
                raise Fatal('non-linear product')
        return s

    def atomt(self):
        k = self.peek()
        if k == 'LPAREN':
            self.take('LPAREN')
            t, _ = self.add()
            self.take('RPAREN')
            return t
        if k == 'ID':
            return Lin({self.take('ID'): Fraction(1)})
        if k == 'REAL':
            return Lin(const=self.take('REAL'))
        raise Refuse('parse error: term expected, found %s' % k)


# ---------------------------------------------------------------- formulas
def names_of(f, acc):
    if f[0] in ('and', 'or'):
        for g in f[1]:
            names_of(g, acc)
    elif f[0] == 'not':
        names_of(f[1], acc)
    else:
        acc.update(f[2].coef)
        acc.update(f[3].coef)
    return acc


def normal_atom(op, s, t):
    """`s op t` as (op, P, N): P op N with P and N having non-negative integer coefficients."""
    d = s.add(t, -1)
    m = lcm(*([v.denominator for v in d.coef.values()] + [d.const.denominator]))
    d = d.scale(Fraction(m))
    pos = Lin({k: v for k, v in d.coef.items() if v > 0}, max(d.const, 0))
    neg = Lin({k: -v for k, v in d.coef.items() if v < 0}, max(-d.const, 0))
    return op, pos, neg


def nnf(f, neg=False):
    """Negation normal form over the ordered field: ('and'|'or', [...]) or ('atom', op, P, N)
    with op in LEQ, LT, EQ, or ('const', bool)."""
    tag = f[0]
    if tag == 'not':
        return nnf(f[1], not neg)
    if tag in ('and', 'or'):
        t = tag if not neg else ('or' if tag == 'and' else 'and')
        return (t, [nnf(g, neg) for g in f[1]])
    op, p, n = normal_atom(f[1], f[2], f[3])
    if p.is_const() and n.is_const():
        v = {'LEQ': p.const <= n.const, 'LT': p.const < n.const, 'EQ': p.const == n.const}[op]
        return ('const', v != neg)
    if not neg:
        return ('atom', op, p, n)
    if op == 'LEQ':
        return ('atom', 'LT', n, p)
    if op == 'LT':
        return ('atom', 'LEQ', n, p)
    return ('or', [('atom', 'LT', p, n), ('atom', 'LT', n, p)])


def num(q):
    assert q.denominator == 1
    return '%d.0' % q.numerator


# ---------------------------------------------------------------- printers
def hes_lin(t, ren):
    parts = []
    for k in sorted(t.coef):
        c = t.coef[k]
        parts.append(ren[k] if c == 1 else '%s * %s' % (num(c), ren[k]))
    if t.const != 0 or not parts:
        parts.append(num(t.const))
    return parts[0] if len(parts) == 1 else '(' + ' + '.join(parts) + ')'


def hes_f(f, ren):
    tag = f[0]
    if tag == 'const':
        return 'true' if f[1] else 'false'
    if tag in ('and', 'or'):
        if not f[1]:
            return 'true' if tag == 'and' else 'false'
        sep = ' /\\ ' if tag == 'and' else ' \\/ '
        return '(' + sep.join(hes_f(g, ren) for g in f[1]) + ')'
    sym = {'LEQ': '<=', 'LT': '<', 'EQ': '='}[f[1]]
    return '(%s %s %s)' % (hes_lin(f[2], ren), sym, hes_lin(f[3], ren))


def smt_lin(t, ren):
    parts = []
    for k in sorted(t.coef):
        c = t.coef[k]
        parts.append(ren[k] if c == 1 else '(* %s %s)' % (num(c), ren[k]))
    if t.const != 0 or not parts:
        parts.append(num(t.const))
    return parts[0] if len(parts) == 1 else '(+ ' + ' '.join(parts) + ')'


def smt_f(f, ren):
    tag = f[0]
    if tag == 'const':
        return 'true' if f[1] else 'false'
    if tag in ('and', 'or'):
        if not f[1]:
            return 'true' if tag == 'and' else 'false'
        return '(%s %s)' % (tag, ' '.join(smt_f(g, ren) for g in f[1]))
    sym = {'LEQ': '<=', 'LT': '<', 'EQ': '='}[f[1]]
    return '(%s %s %s)' % (sym, smt_lin(f[2], ren), smt_lin(f[3], ren))


# ---------------------------------------------------------------- one game
def load(path):
    with open(path, encoding='ascii') as fh:
        text = fh.read()
    p = Parser(lex(text))
    names, init, safe, reach = p.game()
    if len(set(names)) != len(names):
        raise Refuse('a variable is declared twice')
    for n in names:
        if not re.fullmatch(r'[_a-zA-Z][_a-zA-Z0-9]*', n):
            raise Refuse('variable name %r cannot be written in the outputs' % n)
    plain, primed = set(names), {n + "'" for n in names}
    if not names_of(init, set()) <= plain:
        raise Refuse('init mentions %s' % sorted(names_of(init, set()) - plain))
    for what, f in (('safe', safe), ('reach', reach)):
        extra = names_of(f, set()) - plain - primed
        if extra:
            raise Refuse('%s mentions undeclared %s' % (what, sorted(extra)))
    return names, nnf(init), nnf(safe), nnf(reach), nnf(('not', safe)), nnf(('not', reach)), p.notes


def renamings(names):
    x = {n: 'x_' + n for n in names}
    y = {n: 'y_' + n for n in names}
    z = {n: 'z_' + n for n in names}
    init = dict(x)
    safe = dict(x)
    safe.update({n + "'": y[n] for n in names})
    reach = dict(y)                                  # REACH moves from SAFE's target y ...
    reach.update({n + "'": z[n] for n in names})     # ... to the next position z
    return x, y, z, init, safe, reach


def header(comment, name, winner, source, answer_line):
    return [comment + ' Generated by script/gen_rg_games.py from',
            comment + ' benchmarks/QSMT/ijcai2016/test/reachability/%s.rg (SimSat, MIT licence),' % name,
            comment + ' a linear reachability game of Farzan and Kincaid, "Strategy synthesis for',
            comment + ' linear arithmetic games", POPL 2018, https://doi.org/10.1145/3158149.',
            comment + ' Rules: REACH picks a position satisfying init; SAFE moves first, then the players',
            comment + ' alternate; the first player without a legal move loses; SAFE wins every infinite play.',
            comment + ' ' + answer_line,
            comment + ' Expected winner: %s (%s).' % (winner, source)]


def write_hes(path, name, names, init, nsafe, reach, winner, source):
    x, y, z, r_init, r_safe, r_reach = renamings(names)
    xs = ' '.join('(%s: real)' % x[n] for n in names)
    ys = ' '.join('(%s: real)' % y[n] for n in names)
    zs = ' '.join('(%s: real)' % z[n] for n in names)
    lines = ['/*'] + [l[3:] for l in header(' * ', name, winner, source,
                                        'Valid iff REACH wins.  A(x): REACH wins from x with SAFE to move.')] + ['*/']
    lines.append('exists %s. %s /\\ A %s' % (xs, hes_f(init, r_init), ' '.join(x[n] for n in names)))
    lines.append('s.t.')
    lines.append('A %s: bool =mu forall %s. %s \\/ (exists %s. %s /\\ A %s);'
                 % (xs, ys, hes_f(nsafe, r_safe), zs, hes_f(reach, r_reach),
                    ' '.join(z[n] for n in names)))
    with open(path, 'w') as fh:
        fh.write('\n'.join(lines) + '\n')


def write_echc(path, name, names, init, safe, reach, winner, source):
    x, y, z, r_init, r_safe, r_reach = renamings(names)
    sort = ' '.join('Real' for _ in names)
    bx = ' '.join('(%s Real)' % x[n] for n in names)
    by = ' '.join('(%s Real)' % y[n] for n in names)
    bz = ' '.join('(%s Real)' % z[n] for n in names)
    ax, ay, az = (' '.join(v[n] for n in names) for v in (x, y, z))
    lines = header(';', name, winner, source,
                   'Sat iff SAFE wins.  Inv: SAFE to move; Mid: REACH to move.')
    lines += ['(set-logic HORN)',
              '(declare-fun Inv (%s) Bool)' % sort,
              '(declare-fun Mid (%s) Bool)' % sort,
              '(assert (forall (%s) (=> %s (Inv %s))))' % (bx, smt_f(init, r_init), ax),
              '(assert (forall (%s) (=> (Inv %s) (exists (%s) (and %s (Mid %s))))))'
              % (bx, ax, by, smt_f(safe, r_safe), ay),
              '(assert (forall (%s %s) (=> (and (Mid %s) %s) (Inv %s))))'
              % (by, bz, ay, smt_f(reach, r_reach), az),
              '(check-sat)']
    with open(path, 'w') as fh:
        fh.write('\n'.join(lines) + '\n')


def write_uchc(path, name, names, init, safe, reach, winner, source):
    x, y, z, r_init, r_safe, r_reach = renamings(names)
    sort = ' '.join('Real' for _ in names)
    bx = ' '.join('(%s Real)' % x[n] for n in names)
    by = ' '.join('(%s Real)' % y[n] for n in names)
    bz = ' '.join('(%s Real)' % z[n] for n in names)
    ax, ay, az = (' '.join(v[n] for n in names) for v in (x, y, z))
    lines = header(';', name, winner, source,
                   'Sat iff SAFE wins (unsat iff REACH wins).  Att: REACH wins, SAFE to move; '
                   'AttR: REACH wins, REACH to move.')
    lines += ['(set-logic HORN)',
              '(declare-fun Att (%s) Bool)' % sort,
              '(declare-fun AttR (%s) Bool)' % sort,
              '(assert (forall (%s %s) (=> (and %s (Att %s)) (AttR %s))))'
              % (by, bz, smt_f(reach, r_reach), az, ay),
              '(assert (forall (%s) (=> (forall (%s) (=> %s (AttR %s))) (Att %s))))'
              % (bx, by, smt_f(safe, r_safe), ay, ax),
              '(assert (forall (%s) (=> (and %s (Att %s)) false)))' % (bx, smt_f(init, r_init), ax),
              '(check-sat)']
    with open(path, 'w') as fh:
        fh.write('\n'.join(lines) + '\n')


def read_expected(path):
    table = {}
    with open(path) as fh:
        for line in fh:
            line = line.rstrip('\n')
            if not line or line.startswith('#'):
                continue
            name, winner, source = line.split('\t')
            if winner not in ('SAFE', 'REACH'):
                raise SystemExit('%s: bad winner %r for %s' % (path, winner, name))
            table[name] = (winner, source)
    return table


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--src', default=SRC)
    ap.add_argument('--out-hes', default=OUT_HES)
    ap.add_argument('--out-echc', default=OUT_ECHC)
    ap.add_argument('--out-uchc', default=OUT_UCHC)
    ap.add_argument('--expected', default=EXPECTED)
    ap.add_argument('--only', nargs='*')
    a = ap.parse_args()
    if not os.path.isdir(a.src):
        print('no source directory %s' % a.src, file=sys.stderr)
        return 2
    expected = read_expected(a.expected)
    for d in (a.out_hes, a.out_echc, a.out_uchc):
        os.makedirs(d, exist_ok=True)
    names = sorted(f[:-3] for f in os.listdir(a.src) if f.endswith('.rg'))
    if a.only:
        names = [n for n in names if n in a.only]
    rows = []
    for name in names:
        winner, source = expected.get(name, ('-', '-'))
        hes_e = {'REACH': 'valid', 'SAFE': 'invalid'}.get(winner, '-')
        chc_e = {'REACH': 'unsat', 'SAFE': 'sat'}.get(winner, '-')
        outs = [os.path.join(a.out_hes, name + '.hes'),
                os.path.join(a.out_echc, name + '.smt2'),
                os.path.join(a.out_uchc, name + '.smt2')]
        for o in outs:
            if os.path.exists(o):
                os.remove(o)
        try:
            vs, init, safe, reach, nsafe, _, notes = load(os.path.join(a.src, name + '.rg'))
            write_hes(outs[0], name, vs, init, nsafe, reach, winner, source)
            write_echc(outs[1], name, vs, init, safe, reach, winner, source)
            write_uchc(outs[2], name, vs, init, safe, reach, winner, source)
            rows.append((name, 'generated', winner, source, hes_e, chc_e, chc_e,
                         '; '.join(sorted(notes)) or '-'))
        except Refuse as e:
            rows.append((name, 'refused', winner, source, '-', '-', '-', str(e)))
    with open(os.path.join(a.out_hes, 'STATUS.tsv'), 'w') as fh:
        fh.write('name\toutcome\texpected_winner\texpected_source\thes\techc\tuchc\tdetail\n')
        for r in rows:
            fh.write('\t'.join(r) + '\n')
    gen = sum(1 for r in rows if r[1] == 'generated')
    print('%d sources, %d generated, %d refused' % (len(rows), gen, len(rows) - gen))
    return 0


if __name__ == '__main__':
    sys.exit(main())
