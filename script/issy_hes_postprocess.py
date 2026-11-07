#!/usr/bin/env python3
"""Make issy's `--encode-muclp` output readable by this tree's `.hes` reader, by a typed rewrite.

issy (github.com/phheim/issy, v3.0) writes two things this format does not admit:

  1. A dot-less integer numeral where a real is required: issy's logic lets an integer
     constant stand at sort Real (as SMT-LIB solvers do), and its printer writes it as `n`,
     e.g. its negation `(-1 * (x))` of a real `x`, or a source `(x = 0)` with `x` real.  This
     format types a dot-less numeral as `int` and has no numeral coercion, so the file is a
     type error.
  2. A space inside the names its parity encoding builds, `Pred_ 0_l0` for `Pred_0_l0`, which
     this format reads as three tokens.
  3. A negative numeral as a bare application argument, `(P_q1 -1 qvar0 x)`: issy prints an
     argument as a space and the term, and a negative constant as `-1`.  In this format, as in any
     curried application syntax, `P_q1 -1 qvar0 x` is `P_q1 - (1 qvar0 x)`, a syntax error; the
     argument is meant, and `(P_q1 (-1) qvar0 x)` says it.

The rewrite is a typed pass over the format's own grammar (the lexer and the LR(1) grammar of the
reader, transcribed rule for rule below; the grammar has no conflicts, so any derivation found is
the reader's).  Every numeral gets a sort variable of its own instead of `int`; the sorts of the
declared predicate parameters and bound variables, the operators and the comparisons then fix
what each numeral must be.  A numeral the constraints force to be real is respelled `n.0`; every
other numeral is left as written.  Contract:

  - The output is the input with exactly these edits and no other byte changed: `.0` appended to
    a dot-less numeral forced to real, the one space removed inside each broken parity name
    (every occurrence of it, definition heads, applications and the query alike), and `(` `)`
    put around a negative numeral that stands bare as an application argument: the sign adjacent
    to the digits, whitespace before the sign, at a place where the reader's grammar expects the
    next argument of a predicate application.  No rule of that grammar continues an application
    (or any formula) with `-`, so such a place exists only in an input the reader refuses, and
    the only reading that makes it an equation list is the argument.  A `-` anywhere else -- a
    subtraction `x - 1` or `x -1` inside a term, a negative numeral after a comparison or an
    operator, `a-1` with no space before the sign, `- 1` with one after it -- is left as written.
  - Exact, not a choice of meaning: an input the reader already accepts is returned byte for
    byte, since the reader's own typing (every numeral `int`) is a solution of the relaxed
    constraints, so no numeral can be forced to real.  A numeral forced to real in a rejected
    input denotes its real value, which is what issy's logic means by an integer constant at sort
    Real; over `+`, `-`, `*`, negation and comparisons this agrees with integer arithmetic on the
    embedded value.  A forced-real numeral inside a `/` or `mod` would choose between integer and
    real division, which is a decision rather than a respelling, so such an input is refused.
  - Refused, with nothing written and a non-zero exit: issy's exit status non-zero (issy prints a
    partial encoding to stdout before failing on an operator it cannot print), an input that is
    not a complete equation list in this grammar, a sort conflict no respelling resolves, an
    unbound variable or undefined predicate, and a repaired name that collides with an existing
    identifier.
  - Also refused, because the file reads but does not mean the game it encodes: a parity encoding
    whose colour groups are not listed highest colour first, and a co-Buchi encoding (see the two
    checks below for why each means another game, and how each is recognised by its shape).

Usage:
  issy_hes_postprocess.py [--issy-status N] [-o OUT] [--report] IN      (IN may be '-')
  issy_hes_postprocess.py --self-test
  issy_hes_postprocess.py --mutate-int K IN   (test instrument: also respell the K-th numeral the
                                               constraints force to be `int`; the reader must then
                                               refuse the output)
  issy_hes_postprocess.py --keep-int K IN     (test instrument: leave the K-th numeral the constraints
                                               force to be real as written; the reader must refuse)
Exit status: 0 written, 1 refused, 2 usage error.
"""

import argparse
import os
import re
import sys
import tempfile


class Refused(Exception):
    pass


# ---------------------------------------------------------------- lexer
# The rules of the reader's lexer, in its order.  ocamllex takes the longest match and, among
# matches of equal length, the earliest rule; the same choice is made here.

_ID = r"[a-zA-Z#_][a-zA-Z0-9'_#]*"
_RULES = [
    ('SKIP', r"[ \t\r]+"),
    ('SKIP', r"\n"),
    ('SKIP', r"//[^\n]*?\n"),
    ('COMMENT', r"/\*"),
    ('TT', r"tt"), ('FF', r"ff"), ('TRUE', r"true"), ('FALSE', r"false"),
    ('INT', r"int"), ('BOOL', r"bool"), ('REAL', r"real"),
    ('EQFIX', r"=mu"), ('EQFIX', r"=nu"),
    ('AND', r"/\\"), ('OR', r"\\/"), ('NOT', r"!"), ('NOT', r"not"),
    ('AND', r"and"), ('OR', r"or"), ('IFF', r"<=>"), ('IMPLY', r"=>"),
    ('RCMP', r">=\."), ('RCMP', r">\."), ('RCMP', r"<=\."), ('RCMP', r"<\."),
    ('RADD', r"\+\."), ('RMINUS', r"-\."), ('RMULT', r"\*\."), ('RDIV', r"/\."),
    ('RABS', r"abs\."),
    ('REALL', r"real\(-?[0-9]+(?:/[0-9]+)?\)"),
    ('MINUS', r"-"), ('ADD', r"\+"), ('MULT', r"\*"),
    ('DIV', r"/"), ('DIV', r"div"), ('MOD', r"%"), ('MOD', r"mod"),
    ('NCMP', r">="), ('NCMP', r">"), ('NCMP', r"<="), ('NCMP', r"<"),
    ('EQ', r"="), ('EQ', r"!="),
    ('COLON', r":"), ('SEMI', r";"),
    ('BINDER', r"forall"), ('BINDER', r"exists"),
    ('WHERE', r"s\.t\."), ('WHERE', r"where"),
    ('DOT', r"\."), ('LPAREN', r"\("), ('RPAREN', r"\)"),
    ('ID', _ID),
    ('REALL', r"(?:0|[1-9][0-9]*)\.[0-9]*"),
    ('INTL', r"0|[1-9][0-9]*"),
]
_COMPILED = [(k, re.compile(p)) for k, p in _RULES]


class Tok:
    __slots__ = ('kind', 'text', 'start', 'end')

    def __init__(self, kind, text, start, end):
        self.kind, self.text, self.start, self.end = kind, text, start, end

    def __repr__(self):
        return f'{self.kind}:{self.text!r}@{self.start}'


def lex(text):
    toks, pos, n = [], 0, len(text)
    while pos < n:
        best = None
        for kind, rx in _COMPILED:
            m = rx.match(text, pos)
            if m and m.end() > pos and (best is None or m.end() > best[1]):
                best = (kind, m.end())
        if best is None:
            raise Refused(f'offset {pos}: unexpected character {text[pos]!r}')
        kind, end = best
        if kind == 'COMMENT':
            close = text.find('*/', end)
            if close < 0:
                raise Refused(f'offset {pos}: unterminated comment')
            pos = close + 2
            continue
        if kind != 'SKIP':
            toks.append(Tok(kind, text[pos:end], pos, end))
        pos = end
    toks.append(Tok('EOF', '', n, n))
    return toks


# ---------------------------------------------------------------- parity names
# issy builds a parity predicate's name as  prefix ++ "_ " ++ show col ++ "_" ++ loc.  A name is
# taken to be broken exactly when a definition head reads  ID INTL ID '('  with the first ID ending
# in '_', one space before the numeral, the numeral and the second ID adjacent, and the second ID
# starting with '_'; every adjacent occurrence of that triple is then joined.

def _broken_triple(toks, i, text):
    if i + 2 >= len(toks):
        return None
    a, b, c = toks[i], toks[i + 1], toks[i + 2]
    if (a.kind == 'ID' and b.kind == 'INTL' and c.kind == 'ID' and a.text.endswith('_')
            and c.text.startswith('_') and text[a.end:b.start] == ' ' and b.end == c.start):
        return a.text + b.text + c.text
    return None


def repair_names(toks, text):
    """Return (tokens, edits) with every broken parity name joined into one ID token."""
    broken = set()
    for i, t in enumerate(toks):
        if i > 0 and toks[i - 1].kind in ('WHERE', 'SEMI'):
            name = _broken_triple(toks, i, text)
            if name is not None and i + 3 < len(toks) and toks[i + 3].kind in ('LPAREN', 'COLON'):
                broken.add(name)
    if not broken:
        return toks, []
    existing = {t.text for t in toks if t.kind == 'ID'}
    clash = sorted(n for n in broken if n in existing)
    if clash:
        raise Refused(f'repaired name {clash[0]} already occurs in the input')
    # If the prefix were itself a defined predicate, `Pred_ 0_l0` could be its application to
    # `0` and `_l0`, and joining would change the formula rather than respell a name.
    heads = {toks[i].text for i in range(1, len(toks))
             if toks[i - 1].kind in ('WHERE', 'SEMI') and toks[i].kind == 'ID'
             and _broken_triple(toks, i, text) not in broken}
    for i in range(len(toks)):
        name = _broken_triple(toks, i, text)
        if name in broken and toks[i].text in heads:
            raise Refused(f'{toks[i].text} is a defined predicate, so {name!r} may be its application')
    out, edits, i = [], [], 0
    while i < len(toks):
        name = _broken_triple(toks, i, text)
        if name in broken:
            a, c = toks[i], toks[i + 2]
            out.append(Tok('ID', name, a.start, c.end))
            edits.append(('del', a.end, a.end + 1))
            i += 3
        else:
            out.append(toks[i])
            i += 1
    return out, edits


# ---------------------------------------------------------------- parity equation order
# issy's parity encoding for a max-parity game (the system wins when the largest colour seen
# infinitely often is odd) defines, per location L and colour c >= 1, an alias
#     P_c_L(v1)...(vn): bool =sigma (P_{c-1}_L v1 ... vn);      sigma = nu for odd c, mu for even c
# and P_0_L as the controllable predecessor into P_{col(L)}.  In this format the first equation
# is the outermost fixpoint, so the system means the game's winning region only when the
# colour groups are listed highest colour first (the largest colour outermost, P_0 innermost).
# issy prints its equations in the order of their names as strings, which puts colour 0 first
# (and colour 10 between 1 and 2): the aliases then collapse onto P_0 and the whole system is the
# least fixpoint of the controllable predecessor, "the system can force the play to stop",
# whatever the colours, so any answer is about another game.  Such an input is refused; one whose
# chains are listed with colours non-increasing is accepted unchanged.
#
# A chain is recognised by its aliases alone (head p_c_L, body exactly the application of
# p_{c-1}_L to the head's parameters in order), so the test does not depend on how the names
# are spelled once issy's space is removed.

_COLOUR_SEP = re.compile(r'_(\d+)_')


def _name_splits(name):
    """Every (prefix, colour, location), both non-empty, with name == prefix_colour_location."""
    out = []
    for i in range(1, len(name)):
        m = _COLOUR_SEP.match(name, i)
        if m and m.end() < len(name):
            out.append((name[:i], int(m.group(1)), name[m.end():]))
    return out


def _alias_target(fun):
    """The predicate a definition is an exact alias of (same parameters, in order), or None."""
    _, bs, body = fun
    if not (isinstance(body, tuple) and body[0] == 'app') or len(body[2]) != len(bs):
        return None
    if any(not (a[0] == 'var' and a[1] == b[0]) for a, b in zip(body[2], bs)):
        return None
    return body[1]


def check_parity_order(funs):
    """Refuse a parity chain whose colour groups are not listed highest colour first."""
    chains = {}  # prefix -> colours linked by an alias step
    for f in funs:
        target = _alias_target(f)
        if target is None:
            continue
        for p, c, loc in _name_splits(f[0]):
            if c >= 1 and target == f'{p}_{c - 1}_{loc}':
                chains.setdefault(p, set()).update((c, c - 1))
    for p in sorted(chains):
        order = []
        for name, _, _ in funs:
            for q, c, _ in _name_splits(name):
                if q == p and c in chains[p]:
                    order.append((c, name))
                    break
        for (c1, n1), (c2, n2) in zip(order, order[1:]):
            if c2 > c1:
                raise Refused(f'parity equations listed lower colour first ({n1} before {n2}); the first '
                              f'equation is the outermost fixpoint here, so the system is not the '
                              f'max-parity winning region')


# issy's co-Buchi encoding (the system wins when the play eventually stays in a set S) defines per
# location L the pair  pLFP_L =mu (pGFP_L v...)  and  pGFP_L =nu CPre(L in S ? pLFP : pGFP).
# Neither order means the condition: printed in name order (GFP first, outermost) the alias
# collapses and the system is the greatest fixpoint of the controllable predecessor, "the play can
# go on forever"; with LFP outermost it is "S is visited only finitely often", the complement's
# condition, since the branches are the wrong way round.  The Buchi encoding has the alias the
# other way (pGFP_L =nu (pLFP_L v...)) and is correct with GFP first, as issy prints it, so only
# an LFP-to-GFP alias whose GFP side is not itself an alias back is refused.

def check_cobuechi(funs):
    alias = {f[0]: _alias_target(f) for f in funs}
    for f in funs:
        target = alias[f[0]]
        if target is None:
            continue
        name = f[0]
        i = name.find('LFP_')
        while i >= 0:
            # A Buchi location whose step is a bare self-loop gives the two predicates as aliases of
            # each other, so the pair is the co-Buchi shape only when the GFP side is a real step.
            if i > 0 and target == name[:i] + 'GFP_' + name[i + 4:] and alias.get(target) != name:
                raise Refused(f'{name} is an alias of {target}: issy co-Buchi encoding, which does not '
                              f'mean the co-Buchi winning region in either equation order')
            i = name.find('LFP_', i + 1)


def check_fixpoint_order(funs):
    check_parity_order(funs)
    check_cobuechi(funs)


# ---------------------------------------------------------------- parser
# Recursive descent over the reader's grammar.  Every choice point below has alternatives that
# no input satisfies both of (the grammar is LR(1) without conflicts), and each is decided by
# trying the alternative whose derivation ends in a token the other cannot have.

class _Fail(Exception):
    pass


class Parser:
    def __init__(self, toks):
        self.t = toks
        self.memo = {}

    def peek(self, i):
        return self.t[i].kind

    def expect(self, i, kind):
        if self.t[i].kind != kind:
            raise _Fail(i)
        return i + 1

    def toplevel(self):
        q, i = self.formula(0)
        i = self.expect(i, 'WHERE')
        funs = []
        while True:
            f, i = self.fun(i)
            i = self.expect(i, 'SEMI')
            funs.append(f)
            if self.peek(i) == 'EOF':
                break
        return q, funs

    def bounds(self, i):
        bs = []
        while self.peek(i) == 'LPAREN':
            j = i + 1
            if self.peek(j) != 'ID':
                break
            name = self.t[j].text
            j = self.expect(j + 1, 'COLON')
            k = self.peek(j)
            if k not in ('INT', 'BOOL', 'REAL'):
                raise _Fail(j)
            j = self.expect(j + 1, 'RPAREN')
            bs.append((name, {'INT': 'int', 'BOOL': 'bool', 'REAL': 'real'}[k]))
            i = j
        return bs, i

    def fun(self, i):
        if self.peek(i) != 'ID':
            raise _Fail(i)
        name = self.t[i].text
        bs, i = self.bounds(i + 1)
        i = self.expect(i, 'COLON')
        i = self.expect(i, 'BOOL')
        i = self.expect(i, 'EQFIX')
        body, i = self.formula(i)
        return (name, bs, body), i

    def formula(self, i):
        if self.peek(i) == 'BINDER':
            bs, j = self.bounds(i + 1)
            j = self.expect(j, 'DOT')
            body, j = self.formula(j)
            return ('bind', bs, body), j
        left, i = self.imply(i)
        if self.peek(i) == 'IFF':
            right, i = self.imply(i + 1)
            return ('conn', [left, right]), i
        return left, i

    def imply(self, i):
        left, i = self.or_(i)
        if self.peek(i) == 'IMPLY':
            right, i = self.imply(i + 1)
            return ('conn', [left, right]), i
        return left, i

    def or_(self, i):
        left, i = self.and_(i)
        if self.peek(i) == 'OR':
            right, i = self.or_(i + 1)
            return ('conn', [left, right]), i
        return left, i

    def and_(self, i):
        left, i = self.neg(i)
        if self.peek(i) == 'AND':
            right, i = self.and_(i + 1)
            return ('conn', [left, right]), i
        return left, i

    def neg(self, i):
        if self.peek(i) == 'NOT':
            return self.negparen(i + 1)
        return self.fatom(i)

    def negparen(self, i):
        if self.peek(i) == 'NOT':
            return self.negparen(i + 1)
        i = self.expect(i, 'LPAREN')
        f, i = self.formula(i)
        return f, self.expect(i, 'RPAREN')

    def fatom(self, i):
        # T_bool: T_num PREDSYM T_num -- the only atom followed by a comparison
        try:
            t1, j = self.tnum(i)
            k = self.peek(j)
            if k in ('NCMP', 'RCMP', 'EQ'):
                t2, j = self.tnum(j + 1)
                return ('cmp', {'NCMP': 'num', 'RCMP': 'real', 'EQ': 'eq'}[k], t1, t2), j
        except _Fail:
            pass
        k = self.peek(i)
        if k == 'ID':
            name, j = self.t[i].text, i + 1
            if self.peek(j) == 'LPAREN' and self.peek(j + 1) == 'RPAREN':
                return ('app', name, [], i), j + 2
            args = []
            a, j = self.argument(j)
            args.append(a)
            while True:
                try:
                    a, j2 = self.argument(j)
                except _Fail:
                    break
                args.append(a)
                j = j2
            return ('app', name, args, i), j
        if k in ('TRUE', 'FALSE'):
            return ('const',), i + 1
        i = self.expect(i, 'LPAREN')
        f, i = self.formula(i)
        return f, self.expect(i, 'RPAREN')

    def argument(self, i):
        # An application argument is a T_numatom.  Besides, a negative numeral written bare,
        # `-1` or `-0.5` with the sign adjacent to the digits and whitespace before the sign, is
        # taken as one argument: issy's printer writes a negative constant as `show n` and an
        # argument as " " ++ term, and never writes a binary `-` (its sums are `+` with negative
        # coefficients), so the sign there can only be the numeral's.  In the reader's grammar no
        # rule continues an application, or any formula, with `-`, so this alternative is reached
        # only by inputs the reader refuses; an input it accepts is parsed exactly as before.
        try:
            return self.tnumatom(i)
        except _Fail:
            pass
        if i + 1 >= len(self.t):
            raise _Fail(i)
        m, n = self.t[i], self.t[i + 1]
        if (m.kind == 'MINUS' and n.kind in ('INTL', 'REALL') and m.end == n.start and i > 0
                and self.t[i - 1].end < m.start):
            lit = ('intl', i + 1) if n.kind == 'INTL' else ('sort', 'real')
            return ('neglit', i, lit), i + 2
        raise _Fail(i)

    def tnum(self, i):
        key = i
        if key in self.memo:
            r = self.memo[key]
            if r is None:
                raise _Fail(i)
            return r
        try:
            r = self._addsub(i)
        except _Fail:
            self.memo[key] = None
            raise
        self.memo[key] = r
        return r

    def _addsub(self, i):
        t, i = self._muldiv(i)
        while self.peek(i) in ('ADD', 'MINUS', 'RADD', 'RMINUS'):
            kind = 'real' if self.peek(i) in ('RADD', 'RMINUS') else 'num'
            u, i = self._muldiv(i + 1)
            t = ('op', kind, [t, u])
        return t, i

    def _muldiv(self, i):
        t, i = self._neg(i)
        while self.peek(i) in ('MULT', 'RMULT', 'RDIV', 'DIV', 'MOD'):
            k = self.peek(i)
            kind = {'MULT': 'num', 'RMULT': 'real', 'RDIV': 'real', 'DIV': 'divmod',
                    'MOD': 'divmod'}[k]
            u, i = self._neg(i + 1)
            t = ('op', kind, [t, u])
        return t, i

    def _neg(self, i):
        k = self.peek(i)
        if k == 'MINUS':
            t, i = self._neg(i + 1)
            return ('op', 'num', [t]), i
        if k in ('RMINUS', 'RABS'):
            t, i = self._neg(i + 1)
            return ('op', 'real', [t]), i
        return self.tnumatom(i)

    def tnumatom(self, i):
        k = self.peek(i)
        if k == 'LPAREN':
            t, j = self.tnum(i + 1)
            return t, self.expect(j, 'RPAREN')
        if k == 'INTL':
            return ('intl', i), i + 1
        if k == 'REALL':
            return ('sort', 'real'), i + 1
        if k in ('TT', 'FF'):
            return ('sort', 'bool'), i + 1
        if k == 'ID':
            return ('var', self.t[i].text, i), i + 1
        raise _Fail(i)


def parse(toks, text):
    p = Parser(toks)
    try:
        return p.toplevel()
    except _Fail as e:
        i = e.args[0]
        tok = toks[i]
        line = text.count('\n', 0, tok.start) + 1
        col = tok.start - (text.rfind('\n', 0, tok.start) + 1) + 1
        what = 'end of input' if tok.kind == 'EOF' else repr(tok.text)
        raise Refused(f'{line}:{col}: syntax error at {what} (not a complete equation list)')
    except RecursionError:
        raise Refused('input nested too deeply for this checker')


# ---------------------------------------------------------------- typing

class Sorts:
    """Union-find over sort variables; a class may be fixed to int, real or bool."""

    def __init__(self):
        self.parent, self.fixed, self.numeric = [], [], []

    def fresh(self, sort=None):
        self.parent.append(len(self.parent))
        self.fixed.append(sort)
        self.numeric.append(False)
        return len(self.parent) - 1

    def find(self, v):
        while self.parent[v] != v:
            self.parent[v] = self.parent[self.parent[v]]
            v = self.parent[v]
        return v

    def unify(self, a, b, where):
        a, b = self.find(a), self.find(b)
        if a == b:
            return
        fa, fb = self.fixed[a], self.fixed[b]
        if fa and fb and fa != fb:
            raise Refused(f'{where}: sort conflict {fa} against {fb} that no respelling of a numeral resolves')
        self.parent[b] = a
        self.fixed[a] = fa or fb
        self.numeric[a] = self.numeric[a] or self.numeric[b]

    def sort_of(self, v):
        return self.fixed[self.find(v)]


def infer(query, funs, toks, text):
    S = Sorts()
    cst = {s: S.fresh(s) for s in ('int', 'real', 'bool')}
    sig = {}
    for name, bs, _ in funs:
        if name in sig:
            raise Refused(f'predicate {name} defined twice')
        sig[name] = [s for _, s in bs]
    literals = []   # (token index, sort variable)
    divmods = []    # (sort variable of the node, literal sort variables beneath it)
    neglits = []    # token index of the sign of each bare negative numeral argument

    def where(i):
        tok = toks[i]
        return f'{text.count(chr(10), 0, tok.start) + 1}:{tok.start - (text.rfind(chr(10), 0, tok.start) + 1) + 1}'

    def term(t, env, lits):
        tag = t[0]
        if tag == 'intl':
            v = S.fresh()
            literals.append((t[1], v))
            lits.append(v)
            return v
        if tag == 'sort':
            return cst[t[1]]
        if tag == 'var':
            if t[1] not in env:
                raise Refused(f'{where(t[2])}: unbound variable {t[1]}')
            return env[t[1]]
        if tag == 'neglit':
            # the argument the parentheses make of it, `(-n)`, is the reader's unary minus
            neglits.append(t[1])
            t = ('op', 'num', [t[2]])
            tag = 'op'
        if tag == 'op':
            _, kind, args = t
            v = S.fresh('real' if kind == 'real' else None)
            S.numeric[S.find(v)] = True
            sub = []
            for a in args:
                S.unify(v, term(a, env, sub), 'operator')
            if kind == 'divmod':
                divmods.append((v, sub))
            lits.extend(sub)
            return v
        raise AssertionError(t)

    def formula(f, env):
        tag = f[0]
        if tag == 'bind':
            env = dict(env)
            for name, s in f[1]:
                env[name] = cst[s]
            formula(f[2], env)
        elif tag == 'conn':
            for g in f[1]:
                formula(g, env)
        elif tag == 'const':
            pass
        elif tag == 'cmp':
            _, kind, t1, t2 = f
            a, b = term(t1, env, []), term(t2, env, [])
            S.unify(a, b, 'comparison')
            if kind == 'real':
                S.unify(a, cst['real'], 'real comparison')
            elif kind == 'num':
                S.numeric[S.find(a)] = True
        elif tag == 'app':
            _, name, args, i = f
            if name not in sig:
                raise Refused(f'{where(i)}: undefined predicate {name}')
            if len(sig[name]) != len(args):
                raise Refused(f'{where(i)}: {name} applied to {len(args)} arguments, declared with {len(sig[name])}')
            for a, s in zip(args, sig[name]):
                S.unify(term(a, env, []), cst[s], f'argument of {name}')
        else:
            raise AssertionError(f)

    formula(query, {})
    for _, bs, body in funs:
        formula(body, {n: cst[s] for n, s in bs})
    for v in range(len(S.parent)):
        r = S.find(v)
        if S.numeric[r] and S.fixed[r] == 'bool':
            raise Refused('a Boolean term under an arithmetic operator')
    for v, sub in divmods:
        if S.sort_of(v) == 'real' and any(S.sort_of(l) == 'real' for l in sub):
            raise Refused('a numeral forced to real under / or mod: respelling it would choose the division')
    to_real = [i for i, v in literals if S.sort_of(v) == 'real']
    forced_int = [i for i, v in literals if S.sort_of(v) == 'int']
    return to_real, forced_int, neglits


# ---------------------------------------------------------------- driver

def _apply(text, edits):
    out, pos = [], 0
    for kind, a, b in sorted(edits, key=lambda e: (e[1], e[0])):
        out.append(text[pos:a])
        if kind == 'ins':
            out.append(b)
            pos = a
        else:
            pos = b
    out.append(text[pos:])
    return ''.join(out)


def _check_tokens(before, after_text, retyped, joined, wrapped=()):
    """Independent check that the output's tokens are the input's with only the intended changes."""
    after = lex(after_text)
    want = []
    i = 0
    retyped = set(retyped)
    while i < len(before):
        t = before[i]
        name = None
        if i in joined:
            name = joined[i]
        if name is not None:
            want.append(('ID', name))
            i += 3
            continue
        if i in wrapped:
            want.append(('LPAREN', '('))
        if i in retyped:
            want.append(('REALL', t.text + '.0'))
        else:
            want.append((t.kind, t.text))
        if i - 1 in wrapped:
            want.append(('RPAREN', ')'))
        i += 1
    got = [(t.kind, t.text) for t in after]
    if got != want:
        raise AssertionError('internal: output tokens differ from the intended edits')


def process(text, mutate_int=None, keep_int=None):
    """Return (output text, number of numerals respelled, number of name occurrences joined)."""
    toks0 = lex(text)
    toks, name_edits = repair_names(toks0, text)
    query, funs = parse(toks, text)
    check_fixpoint_order(funs)
    to_real, forced_int, neglits = infer(query, funs, toks, text)
    if mutate_int is not None:
        if mutate_int >= len(forced_int):
            raise Refused(f'no forced-int numeral number {mutate_int} (there are {len(forced_int)})')
        to_real = to_real + [forced_int[mutate_int]]
    if keep_int is not None:
        if keep_int >= len(to_real):
            raise Refused(f'no respelled numeral number {keep_int} (there are {len(to_real)})')
        to_real = to_real[:keep_int] + to_real[keep_int + 1:]
    # The closing parenthesis goes after any `.0` at the same offset: _apply's sort is stable.
    edits = (list(name_edits) + [('ins', toks[i].end, '.0') for i in to_real]
             + [('ins', toks[i].start, '(') for i in neglits]
             + [('ins', toks[i + 1].end, ')') for i in neglits])
    out = _apply(text, edits)
    # map the retyped and joined positions back to the unjoined token list for the check
    start_index = {t.start: k for k, t in enumerate(toks0)}
    retyped0 = [start_index[toks[i].start] for i in to_real]
    joined0 = {start_index[t.start]: t.text for t in toks if t.kind == 'ID' and t.start in start_index
               and toks0[start_index[t.start]].text != t.text}
    wrapped0 = {start_index[toks[i].start] for i in neglits}
    _check_tokens(toks0, out, retyped0, joined0, wrapped0)
    return out, len(to_real), len(name_edits), len(neglits)


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('input', nargs='?')
    ap.add_argument('-o', '--output')
    ap.add_argument('--issy-status', type=int, default=0)
    ap.add_argument('--report', action='store_true')
    ap.add_argument('--self-test', action='store_true')
    ap.add_argument('--mutate-int', type=int)
    ap.add_argument('--keep-int', type=int)
    a = ap.parse_args(argv)
    if a.self_test:
        return self_test()
    if a.input is None:
        ap.print_usage(sys.stderr)
        return 2
    try:
        if a.issy_status != 0:
            raise Refused(f'issy exited with status {a.issy_status}; its output is a partial encoding')
        if a.input == '-':
            text = sys.stdin.buffer.read().decode('utf-8')
        else:
            with open(a.input, 'rb') as f:
                text = f.read().decode('utf-8')
        out, nreal, nname, nneg = process(text, a.mutate_int, a.keep_int)
    except (Refused, UnicodeDecodeError, OSError) as e:
        print(f'issy_hes_postprocess: refused {a.input}: {e}', file=sys.stderr)
        return 1
    if a.report:
        print(f'issy_hes_postprocess: {a.input}: numerals respelled {nreal}, name spaces removed {nname}, '
              f'negative arguments parenthesised {nneg}',
              file=sys.stderr)
    data = out.encode('utf-8')
    if a.output:
        d = os.path.dirname(os.path.abspath(a.output))
        fd, tmp = tempfile.mkstemp(dir=d, prefix='.issy_hes_postprocess.')
        try:
            with os.fdopen(fd, 'wb') as f:
                f.write(data)
            os.replace(tmp, a.output)
        except BaseException:
            os.unlink(tmp)
            raise
    else:
        sys.stdout.buffer.write(data)
    return 0


# ---------------------------------------------------------------- self-test

_CASES = [
    # (name, input, expected output or None for refusal)
    ('negation of a real', 'forall (x: real). P x\ns.t.\nP (x: real): bool =nu (-1 * (x)) <= 0.0 \\/ P x;\n',
     'forall (x: real). P x\ns.t.\nP (x: real): bool =nu (-1.0 * (x)) <= 0.0 \\/ P x;\n'),
    ('real equality', 'forall (x: real). P x\ns.t.\nP (x: real): bool =nu (x = 0) \\/ P x;\n',
     'forall (x: real). P x\ns.t.\nP (x: real): bool =nu (x = 0.0) \\/ P x;\n'),
    ('real sum', 'forall (x: real). P x\ns.t.\nP (x: real): bool =nu (x = (1 + (x))) \\/ P x;\n',
     'forall (x: real). P x\ns.t.\nP (x: real): bool =nu (x = (1.0 + (x))) \\/ P x;\n'),
    ('integer context untouched', 'forall (x: int). P x\ns.t.\nP (x: int): bool =nu (-1 * x) <= 0 /\\ x = 0;\n',
     'forall (x: int). P x\ns.t.\nP (x: int): bool =nu (-1 * x) <= 0 /\\ x = 0;\n'),
    ('mixed parameters', 'forall (x: real). forall (n: int). P x n\ns.t.\nP (x: real)(n: int): bool =mu x <= 3 /\\ n <= 3 /\\ P (x + 1) (n + 1);\n',
     'forall (x: real). forall (n: int). P x n\ns.t.\nP (x: real)(n: int): bool =mu x <= 3.0 /\\ n <= 3 /\\ P (x + 1.0) (n + 1);\n'),
    ('argument at a real parameter', 'forall (n: int). Q 1 n\ns.t.\nQ (r: real)(n: int): bool =nu r >= 0.5 /\\ Q 2 7;\n',
     'forall (n: int). Q 1.0 n\ns.t.\nQ (r: real)(n: int): bool =nu r >= 0.5 /\\ Q 2.0 7;\n'),
    ('literal-only comparison stays int', 'forall (x: real). P x\ns.t.\nP (x: real): bool =nu 0 = 1 \\/ x = 0.0;\n',
     'forall (x: real). P x\ns.t.\nP (x: real): bool =nu 0 = 1 \\/ x = 0.0;\n'),
    ('literal sum at real', 'forall (x: real). P x\ns.t.\nP (x: real): bool =nu 1 + 2 <= x;\n',
     'forall (x: real). P x\ns.t.\nP (x: real): bool =nu 1.0 + 2.0 <= x;\n'),
    ('binder shadows', 'forall (x: real). P x\ns.t.\nP (x: real): bool =nu x = 1 /\\ (forall (x: int). x = 1);\n',
     'forall (x: real). P x\ns.t.\nP (x: real): bool =nu x = 1.0 /\\ (forall (x: int). x = 1);\n'),
    ('exists binder and not', 'forall (x: real). P x\ns.t.\nP (x: real): bool =mu exists (y: real). not (y = 2) /\\ P (y - 1);\n',
     'forall (x: real). P x\ns.t.\nP (x: real): bool =mu exists (y: real). not (y = 2.0) /\\ P (y - 1.0);\n'),
    ('comments and spacing kept', '/* c */ forall (x: real).   P x // q\ns.t.\nP (x: real): bool =nu x = 0;\n',
     '/* c */ forall (x: real).   P x // q\ns.t.\nP (x: real): bool =nu x = 0.0;\n'),
    ('parity name space', 'forall (x: int). Pred_ 0_l0 x\ns.t.\nPred_ 0_l0 (x: int): bool =mu x >= 0 /\\ Pred_ 1_l2 x;\nPred_ 1_l2 (x: int): bool =nu Pred_ 0_l0 (x + 1);\n',
     'forall (x: int). Pred_0_l0 x\ns.t.\nPred_0_l0 (x: int): bool =mu x >= 0 /\\ Pred_1_l2 x;\nPred_1_l2 (x: int): bool =nu Pred_0_l0 (x + 1);\n'),
    ('parity name and real numeral', 'forall (x: real). Pred_ 0_l0 x\ns.t.\nPred_ 0_l0 (x: real): bool =mu x >= 0;\n',
     'forall (x: real). Pred_0_l0 x\ns.t.\nPred_0_l0 (x: real): bool =mu x >= 0.0;\n'),
    ('repaired name collides', 'forall (x: int). Pred_ 0_l0 x\ns.t.\nPred_ 0_l0 (x: int): bool =mu Pred_0_l0 x;\nPred_0_l0 (x: int): bool =mu x >= 0;\n', None),
    ('truncated', 'forall (x: real). P x\ns.t.\nP (x: real): bool =nu (x = 0) /\\ (x <=', None),
    ('no final semicolon', 'forall (x: real). P x\ns.t.\nP (x: real): bool =nu x = 0', None),
    ('real division refused', 'forall (x: real). P x\ns.t.\nP (x: real): bool =nu x / 2 = x;\n', None),
    ('integer division kept', 'forall (x: int). P x\ns.t.\nP (x: int): bool =nu x / 2 = x mod 3;\n',
     'forall (x: int). P x\ns.t.\nP (x: int): bool =nu x / 2 = x mod 3;\n'),
    ('genuine conflict refused', 'forall (x: real). P x\ns.t.\nP (x: real)(n: int): bool =nu x = n;\n', None),
    ('arity refused', 'forall (x: real). P x 1\ns.t.\nP (x: real): bool =nu x = 0;\n', None),
    ('unbound variable refused', 'forall (x: real). P x\ns.t.\nP (x: real): bool =nu y = 0;\n', None),
    ('real-only operator', 'forall (x: real). P x\ns.t.\nP (x: real): bool =nu 1 +. 2 <=. 3;\n',
     'forall (x: real). P x\ns.t.\nP (x: real): bool =nu 1.0 +. 2.0 <=. 3.0;\n'),
    ('prefix is a predicate', 'forall (x: int). Pred_ 0_l0 x\ns.t.\nPred_ 0_l0 (x: int): bool =mu x >= 0;\nPred_ (a: int)(b: int): bool =mu a = b;\n', None),
    ('parity lowest colour first refused', 'forall (x: int). Pred_ 2_l0 x\ns.t.\nPred_ 0_l0 (x: int): bool =mu x >= 0 /\\ Pred_ 1_l0 (x + 1);\nPred_ 1_l0 (x: int): bool =nu (Pred_ 0_l0 x);\nPred_ 2_l0 (x: int): bool =mu (Pred_ 1_l0 x);\n', None),
    ('parity highest colour first kept', 'forall (x: int). Pred_ 2_l0 x\ns.t.\nPred_ 2_l0 (x: int): bool =mu (Pred_ 1_l0 x);\nPred_ 1_l0 (x: int): bool =nu (Pred_ 0_l0 x);\nPred_ 0_l0 (x: int): bool =mu x >= 0 /\\ Pred_ 1_l0 (x + 1);\n',
     'forall (x: int). Pred_2_l0 x\ns.t.\nPred_2_l0 (x: int): bool =mu (Pred_1_l0 x);\nPred_1_l0 (x: int): bool =nu (Pred_0_l0 x);\nPred_0_l0 (x: int): bool =mu x >= 0 /\\ Pred_1_l0 (x + 1);\n'),
    ('parity order checked without the space', 'forall (x: int). P_2_a x\ns.t.\nP_0_a (x: int): bool =mu P_1_a (x + 1);\nP_1_a (x: int): bool =nu (P_0_a x);\nP_2_a (x: int): bool =mu (P_1_a x);\n', None),
    ('parity colour 10 in name order refused', 'forall (x: int). P_10_a x\ns.t.\nP_0_a (x: int): bool =mu P_1_a x;\nP_1_a (x: int): bool =nu (P_0_a x);\nP_10_a (x: int): bool =mu (P_9_a x);\nP_2_a (x: int): bool =mu (P_1_a x);\nP_9_a (x: int): bool =nu (P_2_a x);\n', None),
    ('parity location with digits', 'forall (x: int). P_1_q_3_b x\ns.t.\nP_0_q_3_b (x: int): bool =mu x = 0;\nP_1_q_3_b (x: int): bool =nu (P_0_q_3_b x);\n', None),
    ('alias across locations is no chain', 'forall (x: int). P_1_a x\ns.t.\nP_0_b (x: int): bool =mu x = 0;\nP_1_a (x: int): bool =nu (P_0_b x);\n',
     'forall (x: int). P_1_a x\ns.t.\nP_0_b (x: int): bool =mu x = 0;\nP_1_a (x: int): bool =nu (P_0_b x);\n'),
    ('alias with other arguments is no chain', 'forall (x: int). P_1_a x 0\ns.t.\nP_0_a (x: int)(y: int): bool =mu x = y;\nP_1_a (x: int)(y: int): bool =nu (P_0_a y x);\n',
     'forall (x: int). P_1_a x 0\ns.t.\nP_0_a (x: int)(y: int): bool =mu x = y;\nP_1_a (x: int)(y: int): bool =nu (P_0_a y x);\n'),
    ('buechi pair kept', 'forall (x: int). PredGFP_a x\ns.t.\nPredGFP_a (x: int): bool =nu (PredLFP_a x);\nPredLFP_a (x: int): bool =mu x >= 0 /\\ PredGFP_a x;\n',
     'forall (x: int). PredGFP_a x\ns.t.\nPredGFP_a (x: int): bool =nu (PredLFP_a x);\nPredLFP_a (x: int): bool =mu x >= 0 /\\ PredGFP_a x;\n'),
    ('buechi self-loop location kept', 'forall (x: int). PredGFP_a x\ns.t.\nPredGFP_a (x: int): bool =nu (PredLFP_a x);\nPredGFP_s (x: int): bool =nu (PredLFP_s x);\nPredLFP_a (x: int): bool =mu x >= 0 /\\ PredGFP_s x;\nPredLFP_s (x: int): bool =mu (PredGFP_s x);\n',
     'forall (x: int). PredGFP_a x\ns.t.\nPredGFP_a (x: int): bool =nu (PredLFP_a x);\nPredGFP_s (x: int): bool =nu (PredLFP_s x);\nPredLFP_a (x: int): bool =mu x >= 0 /\\ PredGFP_s x;\nPredLFP_s (x: int): bool =mu (PredGFP_s x);\n'),
    ('co-buechi pair refused', 'forall (x: int). PredLFP_a x\ns.t.\nPredGFP_a (x: int): bool =nu x >= 0 /\\ PredLFP_a (x + 1);\nPredLFP_a (x: int): bool =mu (PredGFP_a x);\n', None),
    ('negative numeral argument', 'forall (x: int). Q -1 x\ns.t.\nQ (a: int)(x: int): bool =nu a = x \\/ (Q -2 (x + 1));\n',
     'forall (x: int). Q (-1) x\ns.t.\nQ (a: int)(x: int): bool =nu a = x \\/ (Q (-2) (x + 1));\n'),
    ('negative numeral after a nested argument', 'forall (x: int). Q (1 + (x)) -1 (1 + (x))\ns.t.\nQ (a: int)(b: int)(c: int): bool =nu a = b + c;\n',
     'forall (x: int). Q (1 + (x)) (-1) (1 + (x))\ns.t.\nQ (a: int)(b: int)(c: int): bool =nu a = b + c;\n'),
    ('negative numeral argument after a variable', 'forall (x: int). (Q x -1 x)\ns.t.\nQ (a: int)(b: int)(c: int): bool =nu a = b;\n',
     'forall (x: int). (Q x (-1) x)\ns.t.\nQ (a: int)(b: int)(c: int): bool =nu a = b;\n'),
    ('negative numeral argument at a real parameter', 'forall (x: real). Q -1 x -0.5\ns.t.\nQ (a: real)(x: real)(c: real): bool =nu a = x;\n',
     'forall (x: real). Q (-1.0) x (-0.5)\ns.t.\nQ (a: real)(x: real)(c: real): bool =nu a = x;\n'),
    ('subtraction kept', 'forall (x: int). Q (x -1) (x - 1)\ns.t.\nQ (a: int)(b: int): bool =nu a -1 <= b /\\ a = -1 /\\ (-1 + (a)) = b;\n',
     'forall (x: int). Q (x -1) (x - 1)\ns.t.\nQ (a: int)(b: int): bool =nu a -1 <= b /\\ a = -1 /\\ (-1 + (a)) = b;\n'),
    ('sign not adjacent refused', 'forall (x: int). Q x - 1\ns.t.\nQ (a: int)(b: int): bool =nu a = b;\n', None),
    ('no space before the sign refused', 'forall (x: int). Q x-1\ns.t.\nQ (a: int)(b: int): bool =nu a = b;\n', None),
    ('negative variable argument refused', 'forall (x: int). Q -x x\ns.t.\nQ (a: int)(b: int): bool =nu a = b;\n', None),
    ('nullary application', 'forall (x: real). P ()\ns.t.\nP : bool =nu 0 = 0;\n',
     'forall (x: real). P ()\ns.t.\nP : bool =nu 0 = 0;\n'),
]


def self_test():
    failures = 0
    for name, src, want in _CASES:
        try:
            got = process(src)[0]
        except Refused as e:
            got = None
            why = str(e)
        ok = got == want
        failures += not ok
        print(f'{"ok  " if ok else "FAIL"} {name}' + ('' if ok else f': got {got!r}' + (f' ({why})' if got is None else '')))
    # mutation: respelling a numeral the constraints force to int must change a forced-int numeral,
    # which a second pass of the same typing then rejects as a conflict
    src = 'forall (x: real). forall (n: int). P x n\ns.t.\nP (x: real)(n: int): bool =mu n <= 3 /\\ x <= 3;\n'
    mutant = process(src, mutate_int=0)[0]
    try:
        process(mutant)
        mok = False
    except Refused:
        mok = True
    failures += not mok
    print(f'{"ok  " if mok else "FAIL"} mutant respelling a forced-int numeral is refused on re-reading')
    kept = process(src, keep_int=0)[0]
    kok = kept == src
    failures += not kok
    print(f'{"ok  " if kok else "FAIL"} mutant leaving the one forced-real numeral is the refused input')
    # issy's exit status
    rc = main(['--issy-status', '1', '-'])
    failures += rc != 1
    print(f'{"ok  " if rc == 1 else "FAIL"} non-zero issy status refused')
    print(f'self-test: {len(_CASES) + 3 - failures} ok, {failures} failed')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
