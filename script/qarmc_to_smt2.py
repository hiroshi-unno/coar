#!/usr/bin/env python3
"""Translate one E-HSF/QARMC `.qarmc` file into an SMT-LIB E-CHC problem, and into muCLP when exact.

The input language is the Prolog-syntax clause format read by E-HSF, the solver of Beyene, Popeea
and Rybalchenko, "Solving existentially quantified Horn clauses", CAV 2013, LNCS 8044.  A clause
of that paper is `c(v0) /\\ q1(v1) /\\ ... /\\ qn(vn) -> h(v)` with `h` a query, a constraint or an
existentially quantified conjunction of queries and constraints, or a unit clause `dwf(q)`; a
solution maps each query symbol to a relation such that every clause is valid.

Constructs and their translation (each is exact; anything not listed is refused, nothing guessed):

  % ..., /* ... */          comments; dropped
  name(X1..Xn) := F.        a macro (the transition system: init, next, dst, ...).  Parameters must
                            be distinct variables.  Every use is replaced by F with the arguments
                            substituted simultaneously.  A variable of F that is not a parameter is
                            renamed fresh; such a macro is accepted only where the fresh variable is
                            universally quantified in the clause (a positive body position), and
                            refused under \\+ or in a head.
  H :- B.                   a clause: forall (all variables). B => H.
  B: q(t1..tn)              an unknown applied to terms
     \\+ M                  negation of a predicate-free formula (a macro or a constraint); refused
                            when M contains an unknown
     t1 OP t2               OP in  = \\= =\\= =:= < > =< >= ; arithmetic + - * and unary -
     (F ; G), (F , G)       disjunction and conjunction of predicate-free formulas (a disjunction or
                            negation containing an unknown is refused)
     true, false
  H: false, a constraint, q(t..), a conjunction of these, or exists([W1..Wk], C) with C such a
     conjunction.  A conjunction in a head is the conjunction of the heads (one clause each in Horn
     form; written as one `and` here).
  exists([W..], C) :- B     with no W in B: forall v. B => exists W. C (the paper's clause).
                            When a body conjunct mentions some W (the CTL encoders put the
                            transition `next(v, w)` there), the conjunct is moved under the
                            existential: forall v. B0(v) => exists W. B1(v, W) /\\ C(v, W).  This
                            is the reading the paper's own EF encoding has
                            (inv(v) /\\ ~dst(v) -> exists v'. next(v, v') /\\ inv(v') /\\ rank(v, v'),
                            CAV 2013 section 4); a moved conjunct that contains an unknown is refused.
                            A variable that occurs only in moved conjuncts (a macro's local
                            variable, `_`, an input) is bound by the same exists, as it was
                            existential within the body; one that also occurs in the head outside
                            W is refused.
  next(V1..Vn, W1..Wn) := F the program's transition relation, made total (unless --no-stutter): a
                            state with no successor gets a self-loop, the usual reading of CTL over a
                            program whose run has ended (it stays where it is).  Every application of
                            `next` uses next(v, w) \\/ (~(exists u. next(v, u)) /\\ w = v), with V the
                            current and W the primed half of the parameters.  exists u. next(v, u) is
                            computed exactly when F is a disjunction of conjunctions of literals, each
                            fixing every primed variable by an equation: the disjunct's other literals
                            with those equations substituted, provided they mention only V.  A `next`
                            of another shape, of odd arity, or applied under an existential with the
                            bound variables off its second half is refused.  No other macro (init, dst,
                            nondet_next, step, ...) is changed.  The disjunction is not written where
                            it can be split off exactly: a body conjunct next'(c, p) makes two clauses,
                            the plain one and its stutter arm (p := c), which is dropped when its head
                            is among its body conjuncts and has a head false when that is a wf q(c, c);
                            a next' under the head's exists is decided from R(c), the rest of the head
                            at the stutter step (Problem.emit says how).
                            When every disjunct of next fixes every primed variable by an equation
                            (next = \\/_i (G_i(v) /\\ w = e_i(v))) and a clause's exists binds exactly
                            the primed arguments w of its one moved next, exists w. next'(c, w) /\\ R(w)
                            is written \\/_i (G_i(c) /\\ R(e_i(c))) (plus the stutter disjunct where it
                            was not decided): the one-point rule, exact in every interpretation of the
                            unknowns.  The head is then non-Horn, so this form is printed in the .hes
                            (a nu-body disjunction) and in the .smt2 of a file with a wf (pfwnCSP, whose
                            clauses may be arbitrary), never in an ECHC .smt2; --keep-exists keeps the
                            existential everywhere.
  wf(q/2n), wf(q(X1..X2n))  q is well-founded as a relation between its two argument halves:
                            (declare-wfp q (S..S) Bool).  The paper's unit clause is dwf(q); the
                            archive writes wf on the relation the transitive-closure clauses would
                            have been built from.
  dwf(q/2n), dwf(q(..))     the paper's unit clause: q is disjunctively well-founded (contained in a
                            finite union of well-founded relations): (declare-dwfp q (S..S) Bool).
  name(..X..X..) := F       a repeated macro parameter is head unification: the arguments at its
                            positions are equated.
  prog_rep(Vars, Init, Next) the tool's own copy of the program (initial condition and transition),
                            used by its search; it constrains no unknown and is kept as a comment.
  query_naming(..), query_finite_sorts(..), skolem_template(..)
                            search hints of the tool (display names, finite argument positions,
                            templates for a Skolem relation).  A template restricts where the tool
                            searches, not which assignments are solutions (the paper's GrdT/RelT are
                            supplied by the user and are not part of a clause's meaning), so dropping
                            them keeps the clause set's problem; they are kept verbatim as comments.
                            Not when a file has a skolem_template and an existential clause whose
                            witness no theory formula of the clause constrains (`exists([W], q(W)) :-
                            q(V)`): there the move relation may be stated only in the template, with
                            parameters that are constants chosen once, and the clause set alone is
                            a different (often trivial) problem.  Such a file is refused.

Refused (the file gets no output; the reason is printed on stderr and in the exit status 1):
  template(q, ..) when q occurs in a clause -- a template on an unknown that appears only in bodies
  restricts the solution space and is part of the problem; its semantics is not in the paper;
  id(..) in a body, a body atom q(..) or q-[..] naming a Skolem relation by the tool's own
  convention, the HSF list notation q-[..] (its identity with q(..) is not documented);
  integer division, min, max; anything not in the table.

Sorts: every variable is `Int` (the programs are C programs over int); `--sort Real` gives the
rational reading the CLP(Q) back end of the tool may have used (unverified).

muCLP: with --hes OUT, a `.hes` file is also written when every clause has at most one unknown
in its body, unknowns occur only positively in heads and no wf is declared.  Then the problem is
satisfiable iff the greatest fixpoint of the body-indexed operator satisfies the clauses without
an unknown in the body (the theorem is in the theory document of the E-CHC corpus); the `.hes`
has one =nu equation per unknown and that check as its query.  Otherwise no `.hes` is written and
the reason is printed.

Usage: qarmc_to_smt2.py IN.qarmc -o OUT.smt2 [--hes OUT.hes] [--sort Int|Real] [--info] [--no-stutter]
                        [--keep-exists]
Exit status: 0 written, 1 refused (nothing written), 2 usage error.  With --info a line
`class=<ECHC|pfwnCSP|CHC> exists=<k> wf=<k> moved=<k> hes=<written|reason> stutter=<applied|no-next|off>
hints=<..>` goes to stdout, followed by `onepoint=<k>` when k clauses have a one-point form.
"""

import argparse
import itertools
import os
import sys


class Refuse(Exception):
    pass


# ---------------------------------------------------------------- lexer

SYMCH = set('+-*/\\^<>=~:.?@#&$')


def lex(text):
    """Tokens (kind, value, ws_before).  kind: name var int str punct sym end."""
    toks = []
    i, n = 0, len(text)
    ws = True
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            ws = True
            continue
        if c == '%':
            while i < n and text[i] != '\n':
                i += 1
            ws = True
            continue
        if c == '/' and i + 1 < n and text[i + 1] == '*':
            j = text.find('*/', i + 2)
            if j < 0:
                raise Refuse('unterminated /* comment')
            i = j + 2
            ws = True
            continue
        if c.isalpha() or c == '_':
            j = i
            while j < n and (text[j].isalnum() or text[j] == '_'):
                j += 1
            w = text[i:j]
            toks.append(('var' if (w[0].isupper() or w[0] == '_') else 'name', w, ws))
            i = j
        elif c.isdigit():
            j = i
            while j < n and text[j].isdigit():
                j += 1
            if j < n and text[j] == '.' and j + 1 < n and text[j + 1].isdigit():
                raise Refuse('a non-integer numeral')
            toks.append(('int', int(text[i:j]), ws))
            i = j
        elif c == "'":
            j = i + 1
            buf = []
            while j < n and text[j] != "'":
                if text[j] == '\\' and j + 1 < n:
                    buf.append(text[j + 1])
                    j += 2
                else:
                    buf.append(text[j])
                    j += 1
            if j >= n:
                raise Refuse('unterminated quoted atom')
            toks.append(('name', ''.join(buf), ws))
            i = j + 1
        elif c in '()[],|;!':
            toks.append(('punct', c, ws))
            i += 1
        elif c in SYMCH:
            j = i
            while j < n and text[j] in SYMCH:
                j += 1
            s = text[i:j]
            if s == '.' and (j >= n or text[j].isspace() or text[j] == '%'):
                toks.append(('end', '.', ws))
            else:
                toks.append(('sym', s, ws))
            i = j
        else:
            raise Refuse('unexpected character %r' % c)
        ws = False
    return toks


# ---------------------------------------------------------------- reader (Prolog operator grammar)

INFIX = {':-': (1200, 'xfx'), ':=': (1200, 'xfx'), ';': (1100, 'xfy'), '|': (1100, 'xfy'),
         '->': (1050, 'xfy'), ',': (1000, 'xfy'),
         '=': (700, 'xfx'), '\\=': (700, 'xfx'), '==': (700, 'xfx'), '\\==': (700, 'xfx'),
         '=<': (700, 'xfx'), '>=': (700, 'xfx'), '<': (700, 'xfx'), '>': (700, 'xfx'),
         '=:=': (700, 'xfx'), '=\\=': (700, 'xfx'), 'is': (700, 'xfx'),
         '+': (500, 'yfx'), '-': (500, 'yfx'), '*': (400, 'yfx'), '/': (400, 'yfx'),
         '//': (400, 'yfx'), 'mod': (400, 'yfx')}
PREFIX = {'\\+': (900, 'fy'), '-': (200, 'fy'), ':-': (1200, 'fx')}


class Reader:
    """Terms: ('var', n) ('int', k) ('app', f, [args]) ('list', [items]); an atom is ('app', f, [])."""

    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else ('eof', None, True)

    def next(self):
        tok = self.peek()
        self.i += 1
        return tok

    def expect(self, kind, val):
        tok = self.next()
        if tok[0] != kind or tok[1] != val:
            raise Refuse('syntax: expected %r, found %r' % (val, tok[1]))

    def op_name(self, tok):
        if tok[0] in ('sym', 'name') or (tok[0] == 'punct' and tok[1] in ',|;'):
            return tok[1]
        return None

    def parse(self, maxp):
        left, lp = self.primary(maxp)
        while True:
            tok = self.peek()
            name = self.op_name(tok)
            if name not in INFIX:
                return left
            p, typ = INFIX[name]
            if p > maxp:
                return left
            lmax = p - 1 if typ[0] == 'x' else p
            if lp > lmax:
                return left
            self.next()
            rmax = p - 1 if typ[2] == 'x' else p
            right = self.parse(rmax)
            left, lp = ('app', name, [left, right]), p

    def primary(self, maxp):
        tok = self.next()
        kind, val, _ = tok
        if kind == 'int':
            return ('int', val), 0
        if kind == 'var':
            return ('var', val), 0
        if kind == 'punct' and val == '(':
            t = self.parse(1200)
            self.expect('punct', ')')
            return t, 0
        if kind == 'punct' and val == '[':
            items = []
            if self.peek()[:2] == ('punct', ']'):
                self.next()
                return ('list', items), 0
            while True:
                items.append(self.parse(999))
                tok = self.next()
                if tok[:2] == ('punct', ']'):
                    return ('list', items), 0
                if tok[:2] != ('punct', ','):
                    raise Refuse('syntax: list tail or bad list')
        if kind in ('name', 'sym'):
            nxt = self.peek()
            if nxt[:2] == ('punct', '(') and not nxt[2]:
                self.next()
                args = [self.parse(999)]
                while True:
                    tok = self.next()
                    if tok[:2] == ('punct', ')'):
                        break
                    if tok[:2] != ('punct', ','):
                        raise Refuse('syntax: bad argument list of %s' % val)
                    args.append(self.parse(999))
                return ('app', val, args), 0
            if val in PREFIX:
                # a negative numeral, or a prefix operator applied to an operand
                if val == '-' and nxt[0] == 'int' and not nxt[2]:
                    self.next()
                    return ('int', -nxt[1]), 0
                p, typ = PREFIX[val]
                if p > maxp:
                    p = 999
                starts = nxt[0] in ('int', 'var', 'name') or nxt[:2] in (('punct', '('), ('punct', '[')) \
                    or (nxt[0] == 'sym' and nxt[1] in PREFIX)
                if starts and not (nxt[0] in ('sym', 'name') and nxt[1] in INFIX and nxt[1] not in PREFIX):
                    arg = self.parse(p if typ == 'fy' else p - 1)
                    return ('app', val, [arg]), p
            return ('app', val, []), 0
        raise Refuse('syntax: unexpected %r' % (val,))

    def clauses(self):
        out = []
        while self.peek()[0] != 'eof':
            t = self.parse(1200)
            tok = self.next()
            if tok[0] != 'end':
                raise Refuse('syntax: expected end of clause, found %r' % (tok[1],))
            out.append(t)
        return out


def show(t):
    if t[0] == 'var':
        return t[1]
    if t[0] == 'int':
        return str(t[1])
    if t[0] == 'list':
        return '[' + ','.join(show(x) for x in t[1]) + ']'
    f, args = t[1], t[2]
    if not args:
        return f
    if f in INFIX and len(args) == 2:
        return '(' + show(args[0]) + f + show(args[1]) + ')'
    return f + '(' + ','.join(show(a) for a in args) + ')'


# ---------------------------------------------------------------- semantic layer

# formulas: ('true',) ('false',) ('and', [..]) ('or', [..]) ('not', f) ('cmp', op, a, b) ('pred', q, [terms])
# terms: ('var', x) ('int', k) ('add', a, b) ('sub', a, b) ('mul', a, b) ('neg', a)

CMP = {'=': '=', '=:=': '=', '\\=': '!=', '=\\=': '!=', '<': '<', '>': '>', '=<': '<=', '>=': '>='}
HINTS = {'query_naming', 'query_finite_sorts', 'skolem_template', 'prog_rep'}


def tvars(t, acc):
    if t[0] == 'var':
        acc.add(t[1])
    elif t[0] in ('add', 'sub', 'mul'):
        tvars(t[1], acc)
        tvars(t[2], acc)
    elif t[0] == 'neg':
        tvars(t[1], acc)
    return acc


def fvars(f, acc=None):
    acc = set() if acc is None else acc
    k = f[0]
    if k in ('and', 'or'):
        for g in f[1]:
            fvars(g, acc)
    elif k == 'not':
        fvars(f[1], acc)
    elif k == 'cmp':
        tvars(f[2], acc)
        tvars(f[3], acc)
    elif k == 'pred':
        for a in f[2]:
            tvars(a, acc)
    elif k == 'exists':
        inner = fvars(f[2])
        acc |= inner - set(f[1])
    return acc


def has_pred(f):
    k = f[0]
    if k == 'pred':
        return True
    if k in ('and', 'or'):
        return any(has_pred(g) for g in f[1])
    if k == 'not':
        return has_pred(f[1])
    if k == 'exists':
        return has_pred(f[2])
    return False


def preds_of(f, acc):
    k = f[0]
    if k == 'pred':
        acc.append(f)
    elif k in ('and', 'or'):
        for g in f[1]:
            preds_of(g, acc)
    elif k == 'not':
        preds_of(f[1], acc)
    elif k == 'exists':
        preds_of(f[2], acc)
    return acc


def subst_t(t, s):
    if t[0] == 'var':
        return s.get(t[1], t)
    if t[0] in ('add', 'sub', 'mul'):
        return (t[0], subst_t(t[1], s), subst_t(t[2], s))
    if t[0] == 'neg':
        return ('neg', subst_t(t[1], s))
    return t


def subst_f(f, s):
    k = f[0]
    if k in ('and', 'or'):
        return (k, [subst_f(g, s) for g in f[1]])
    if k == 'not':
        return ('not', subst_f(f[1], s))
    if k == 'cmp':
        return ('cmp', f[1], subst_t(f[2], s), subst_t(f[3], s))
    if k == 'pred':
        return ('pred', f[1], [subst_t(a, s) for a in f[2]])
    return f


DNF_LIMIT = 4096


def dnf(f):
    """The disjunctive normal form of a predicate-free formula built from and/or over literals (cmp,
    not, true, false), as a list of literal lists; None past DNF_LIMIT disjuncts.  Equivalent to f."""
    k = f[0]
    if k == 'true':
        return [[]]
    if k == 'or':
        out = []
        for g in f[1]:
            d = dnf(g)
            if d is None:
                return None
            out.extend(d)
        return out if len(out) <= DNF_LIMIT else None
    if k == 'and':
        out = [[]]
        for g in f[1]:
            d = dnf(g)
            if d is None:
                return None
            out = [a + b for a in out for b in d]
            if len(out) > DNF_LIMIT:
                return None
        return out
    return [[f]]


def bound_side(c, p, unfixed):
    """'lower', 'upper' or 'neither' when the literal c bounds the variable p alone (p OP e or e OP p
    with e free of every variable in unfixed); None otherwise."""
    if c[0] != 'cmp' or c[1] not in ('<', '<=', '>', '>=', '!='):
        return None
    op, a, b = c[1], c[2], c[3]
    if b == ('var', p) and a != ('var', p):
        a, b = b, a
        op = {'<': '>', '<=': '>=', '>': '<', '>=': '<=', '!=': '!='}[op]
    if a != ('var', p) or tvars(b, set()) & unfixed:
        return None
    return {'<': 'upper', '<=': 'upper', '>': 'lower', '>=': 'lower', '!=': 'neither'}[op]


class Problem:
    def __init__(self):
        self.macros = {}      # (name, arity) -> (params, prolog term)
        self.wf = []          # (name, arity)
        self.templates = []   # names with template/N
        self.hints = {}       # hint name -> list of source texts
        self.clauses = []     # (body conjunct list, exists vars, head conjunct list)
        self.arity = {}       # unknown -> arity
        self.fresh = itertools.count()
        self.moved = 0
        self.bare_exists = 0  # existential clauses whose witness no theory formula of the clause constrains
        self.stutter = True   # give a state without a next-successor a self-loop (stutter_next)
        self.stuttered = {}   # macro key -> its stuttered definition (a formula over its parameters)
        self.stutter_pri = {}
        self.stutter_live = None  # (current-state parameters, exists u. next(v, u)) of the stuttered next
        self.plain_next = False   # inline next as written (clause() splits the stutter off itself)
        self.split = 0            # clause arms the stutter split produced and kept
        self.dropped = 0          # stutter arms dropped as valid
        self.sealed = 0           # stutter arms whose rank(v, v) head became false
        self.next_cases = None    # (cur, pri, [(guard, {primed: e(cur)})]): next as guarded equations
        self.onepoint_on = True   # eliminate an existential successor of next by the one-point rule
        self.onepoint_alt = {}    # clause index -> its one-point form (b, [], h)

    def fresh_var(self, base):
        return '%s_m%d' % (base, next(self.fresh))

    # -- terms
    def term(self, t):
        if t[0] == 'var':
            return t
        if t[0] == 'int':
            return t
        if t[0] == 'app' and len(t[2]) == 2 and t[1] in ('+', '-', '*'):
            a, b = self.term(t[2][0]), self.term(t[2][1])
            return ({'+': 'add', '-': 'sub', '*': 'mul'}[t[1]], a, b)
        if t[0] == 'app' and len(t[2]) == 1 and t[1] == '-':
            return ('neg', self.term(t[2][0]))
        raise Refuse('unsupported arithmetic term %s' % show(t))

    # -- formulas; `where` is 'body' (positive premise), 'neg' (under negation) or 'head'
    def formula(self, t, where, allow_pred):
        if t[0] == 'app':
            f, args = t[1], t[2]
            if f == ',' and len(args) == 2:
                return ('and', [self.formula(a, where, allow_pred) for a in args])
            if f in (';', '|') and len(args) == 2:
                return ('or', [self.formula(a, where, False) for a in args])
            if f == '\\+' and len(args) == 1:
                g = self.formula(args[0], 'neg', False)
                return ('not', g)
            if f in CMP and len(args) == 2:
                return ('cmp', CMP[f], self.term(args[0]), self.term(args[1]))
            if f == 'true' and not args:
                return ('true',)
            if f in ('false', 'fail') and not args:
                return ('false',)
            if f == '-' and len(args) == 2 and args[1][0] == 'list':
                raise Refuse('HSF list notation %s-[..]: its identity with %s(..) is not documented'
                             % (show(args[0]), show(args[0])))
            if f == 'id':
                raise Refuse('id(..) in a clause: a Skolem relation named by the tool\'s convention')
            if f in ('exists', 'wf', 'template') or f in HINTS:
                raise Refuse('%s/%d inside a formula' % (f, len(args)))
            if (f, len(args)) in self.macros:
                return self.inline(f, args, where)
            if not f[0].isalpha():
                raise Refuse('unsupported operator %s' % f)
            if not allow_pred:
                raise Refuse('unknown %s/%d %s' % (f, len(args), 'inside a macro' if where == 'macro'
                                                    else 'under a disjunction or negation'))
            if f in self.templates:
                raise Refuse('template on the unknown %s, which occurs in a clause' % f)
            terms = [self.term(a) for a in args]
            if self.arity.setdefault(f, len(terms)) != len(terms):
                raise Refuse('unknown %s used at two arities' % f)
            return ('pred', f, terms)
        raise Refuse('not a formula: %s' % show(t))

    def stutter_next(self):
        """Give every state without a successor a self-loop: replace the transition macro `next`
        by next'(v, v') = next(v, v') \\/ (~(exists u. next(v, u)) /\\ v' = v).

        The transition macro is the one named `next` (the CTL encoders' name for the program's
        transition relation, the one prog_rep and query_naming describe); no other macro is
        touched.  Its 2n parameters are n current-state variables followed by their n primed
        counterparts in the same order (the encoders' convention, checked against every existential
        clause that moves `next` under its exists).  The macro body (predicate-free) is put in
        disjunctive normal form; in each disjunct D the primed variables fixed by an equation
        `p' = e`, whose right side mentions no primed variable not already fixed, are substituted
        (exact: the equations have the unique solution p' = e(v)); a primed variable no equation
        fixes may occur only in one-sided bounds on it alone, which exists p' drops; what remains
        is exists u. D(v, u), and must mention only current-state variables.  Anything else is
        refused, since the existential over a guard with a local variable, or over a variable
        bounded from both sides, is not computed here."""
        key = next((k for k in self.macros if k[0] == 'next'), None)
        if key is None:
            return
        params, body = self.macros[key]
        n = len(params)
        if n % 2:
            raise Refuse('stutter: next/%d has an odd arity, so its current and primed halves are not '
                         'determined (--no-stutter keeps the clauses as written)' % n)
        cur, pri = params[:n // 2], params[n // 2:]
        g = self.formula(body, 'macro', False)
        disjuncts = dnf(g)
        if disjuncts is None:
            raise Refuse('stutter: next has more than %d disjuncts in disjunctive normal form' % DNF_LIMIT)
        guards, cases = [], []
        for i, cs in enumerate(disjuncts):
            sub, used = {}, set()
            progress = True
            while progress:
                progress = False
                for j, c in enumerate(cs):
                    if j in used or c[0] != 'cmp' or c[1] != '=':
                        continue
                    for lhs, rhs in ((c[2], c[3]), (c[3], c[2])):
                        if lhs[0] == 'var' and lhs[1] in pri and lhs[1] not in sub \
                                and not (tvars(rhs, set()) & (set(pri) - set(sub))):
                            sub[lhs[1]] = subst_t(rhs, sub)
                            used.add(j)
                            progress = True
                            break
            grd = [subst_f(c, sub) for j, c in enumerate(cs) if j not in used]
            if cases is not None:
                ev = set()
                for e in sub.values():
                    tvars(e, ev)
                cases = cases + [(grd, dict(sub))] if len(sub) == len(pri) and ev <= set(cur) else None
            # A primed variable no equation fixes (a nondeterministic assignment) is eliminated when
            # every literal mentioning it bounds it alone from one side (p > e, p >= e, or p < e,
            # p =< e, with e free of unfixed primed variables) or excludes one value (p != e): such
            # a set of literals has a solution in p for every value of the rest, over Int and over
            # Real alike, so exists p drops them.  Bounds from both sides are refused.
            for p in sorted(set(pri) - set(sub)):
                lits = [c for c in grd if p in fvars(c)]
                sides = set()
                for c in lits:
                    side = bound_side(c, p, set(pri) - set(sub))
                    if side is None:
                        raise Refuse('stutter: disjunct %d of next constrains %s, which no equation fixes, '
                                     'other than by one-sided bounds' % (i + 1, p))
                    sides.add(side)
                if {'lower', 'upper'} <= sides:
                    raise Refuse('stutter: disjunct %d of next bounds %s, which no equation fixes, from '
                                 'both sides' % (i + 1, p))
                grd = [c for c in grd if p not in fvars(c)]
            extra = set().union(*(fvars(c) for c in grd)) - set(cur) if grd else set()
            if extra:
                raise Refuse('stutter: the guard of disjunct %d of next mentions %s, not a current-state '
                             'variable' % (i + 1, ', '.join(sorted(extra))))
            guards.append(('and', grd))
        dead = ('not', ('or', guards))
        stay = [('cmp', '=', ('var', p), ('var', c)) for c, p in zip(cur, pri)]
        self.stuttered[key] = ('or', [g, ('and', [dead] + stay)])
        self.stutter_pri = {key: pri}
        self.stutter_live = (cur, ('or', guards))
        # When every disjunct fixes every primed variable by an equation, next(v, v') is
        # \/_i (G_i(v) /\ v' = e_i(v)) exactly; onepoint() eliminates an existential successor with it.
        # (A disjunct whose primed variable is only bounded from one side has no such e_i.)
        self.next_cases = (cur, pri, cases) if cases is not None else None

    def onepoint(self, cur_terms, ws, rest):
        """exists ws. next(c, ws) /\\ R(ws), with c = cur_terms (free of ws), ws the distinct bound
        variables on next's primed half, and R = rest (a conjunct list), as the disjunction
        \\/_i (G_i(c) /\\ R(e_i(c))); None when next_cases is not computed.  Exact by the one-point
        rule: in disjunct i the equations ws = e_i(c) have the single solution e_i(c), which
        mentions no bound variable, and G_i(c) does not mention ws."""
        if self.next_cases is None:
            return None
        cur, pri, cases = self.next_cases
        sc = dict(zip(cur, cur_terms))
        out = []
        for grd, sub in cases:
            s = {w: subst_t(sub[p], sc) for w, p in zip(ws, pri)}
            out.append(('and', [subst_f(g, sc) for g in grd] + [subst_f(g, s) for g in rest]))
        return ('or', out)

    def final_clauses(self, nonhorn):
        """The clauses to print: with nonhorn, each clause that has a one-point form (emit) in that
        form, whose head is a disjunction over unknowns; otherwise the clauses as recorded."""
        return [self.onepoint_alt.get(i, c) if nonhorn else c for i, c in enumerate(self.clauses)]

    def live(self, cur_terms):
        """exists u. next(v, u) at v = cur_terms (exact, as computed by stutter_next)."""
        cur, g = self.stutter_live
        return subst_f(g, dict(zip(cur, cur_terms)))

    def inline(self, f, args, where):
        params, body = self.macros[(f, len(args))]
        s = {p: self.term(a) for p, a in zip(params, args)}
        g = (None if self.plain_next else self.stuttered.get((f, len(args)))) \
            or self.formula(body, 'macro', False)
        local = fvars(g) - set(params)
        if local:
            if where != 'body':
                raise Refuse('macro %s has variables %s outside its parameters and is used %s'
                             % (f, sorted(local), 'under negation' if where == 'neg' else 'in a head'))
            for v in sorted(local):
                s[v] = ('var', self.fresh_var(v))
        return subst_f(g, s)

    def load(self, terms):
        # pass 1: macros, directives
        rest = []
        for t in terms:
            if t[0] == 'app' and t[1] == ':=' and len(t[2]) == 2:
                lhs, rhs = t[2]
                if lhs[0] != 'app' or not lhs[2]:
                    raise Refuse('macro head %s' % show(lhs))
                # A repeated parameter is Prolog head unification: the arguments at its positions are
                # equal.  It becomes a fresh parameter and an equation conjoined to the definition.
                ps, eqs = [], []
                for a in lhs[2]:
                    if a[0] != 'var' or a[1] == '_':
                        raise Refuse('macro %s: a parameter is not a named variable' % lhs[1])
                    if a[1] in ps:
                        dup = '%s_dup%d' % (a[1], len(ps))
                        ps.append(dup)
                        eqs.append(('app', '=', [('var', dup), a]))
                    else:
                        ps.append(a[1])
                for e in eqs:
                    rhs = ('app', ',', [e, rhs])
                key = (lhs[1], len(ps))
                if key in self.macros:
                    raise Refuse('macro %s/%d defined twice' % key)
                self.macros[key] = (ps, rhs)
            elif t[0] == 'app' and t[1] in HINTS:
                self.hints.setdefault(t[1], []).append(show(t))
            elif t[0] == 'app' and t[1] == 'template':
                # template(q, Vars, Def, ParamConstraint), or template([(q, Vars, Def), ..], ParamConstraint)
                first = t[2][0] if t[2] else None
                entries = first[1] if first is not None and first[0] == 'list' else [first]
                for e in entries:
                    while e is not None and e[0] == 'app' and e[1] == ',' and len(e[2]) == 2:
                        e = e[2][0]
                    if e is None or e[0] != 'app' or e[2]:
                        raise Refuse('template without a name')
                    self.templates.append(e[1])
                self.hints.setdefault('template', []).append(show(t))
            elif t[0] == 'app' and t[1] in ('wf', 'dwf') and len(t[2]) == 1:
                # wf(q/n), dwf(q/n), or the same with q applied to n variables: dwf(q(X1..Xn))
                a = t[2][0]
                if a[0] == 'app' and a[1] == '/' and a[2][0][0] == 'app' and not a[2][0][2] \
                        and a[2][1][0] == 'int':
                    self.wf.append((a[2][0][1], a[2][1][1], t[1]))
                elif a[0] == 'app' and a[2] and all(x[0] == 'var' for x in a[2]):
                    self.wf.append((a[1], len(a[2]), t[1]))
                else:
                    raise Refuse('%s argument %s' % (t[1], show(a)))
            elif t[0] == 'app' and t[1] == ':-' and len(t[2]) == 1:
                raise Refuse('directive :- %s' % show(t[2][0]))
            else:
                rest.append(t)
        # A `next` the stutter cannot handle refuses the file, but only after the checks below, so
        # that a file refused for another reason keeps that reason in the record.
        stutter_refusal = None
        if self.stutter:
            try:
                self.stutter_next()
            except Refuse as e:
                stutter_refusal = e
        # pass 2: clauses
        for t in rest:
            if t[0] == 'app' and t[1] == ':-' and len(t[2]) == 2:
                head, body = t[2]
            else:
                head, body = t, ('app', 'true', [])
            self.clause(head, body)
        # macros used as unknowns would have been inlined; check wf targets
        for (q, n, _) in self.wf:
            if q not in self.arity:
                raise Refuse('wf(%s/%d) names no unknown of a clause' % (q, n))
            if self.arity[q] != n or n % 2:
                raise Refuse('wf(%s/%d) does not match the unknown\'s arity or is odd' % (q, n))
        if self.bare_exists and 'skolem_template' in self.hints:
            raise Refuse('%d existential clause(s) constrain the witness only through unknowns, and the file '
                         'has a skolem_template: the move relation may live only in the template, whose '
                         'parameters are constants chosen once (a judgement per file, not a translation)'
                         % self.bare_exists)
        for q in self.templates:
            if q in self.arity:
                raise Refuse('template on the unknown %s, which occurs in a clause' % q)
        if stutter_refusal is not None:
            raise stutter_refusal

    def conj(self, f):
        if f[0] == 'and':
            out = []
            for g in f[1]:
                out.extend(self.conj(g))
            return out
        if f[0] == 'true':
            return []
        return [f]

    def src_conj(self, t):
        """The top-level conjuncts of a source body, as written (macros not expanded)."""
        if t[0] == 'app' and t[1] == ',' and len(t[2]) == 2:
            return self.src_conj(t[2][0]) + self.src_conj(t[2][1])
        return [t]

    def rename_anon(self, t):
        if t[0] == 'var' and t[1] == '_':
            return ('var', self.fresh_var('Anon'))
        if t[0] == 'app':
            return ('app', t[1], [self.rename_anon(a) for a in t[2]])
        if t[0] == 'list':
            return ('list', [self.rename_anon(a) for a in t[1]])
        return t

    def clause(self, head, body):
        head, body = self.rename_anon(head), self.rename_anon(body)
        # One group per conjunct as written in the source, so that a macro application stays one
        # relation when it is moved under an existential below.  An application of the stuttered
        # `next` as a conjunct of its own is inlined as written, and its stutter arm is split off
        # below; nexts maps its index to its current and primed argument terms.
        srcs = self.src_conj(body)
        groups, nexts = [], {}
        for i, t in enumerate(srcs):
            key = (t[1], len(t[2])) if t[0] == 'app' else None
            self.plain_next = key in self.stutter_pri
            try:
                groups.append(self.conj(self.formula(t, 'body', True)))
            finally:
                self.plain_next = False
            if key in self.stutter_pri:
                k = len(t[2]) // 2
                nexts[i] = ([self.term(a) for a in t[2][:k]], [self.term(a) for a in t[2][k:]])
        b = [g for grp in groups for g in grp]
        for g in b:
            if g[0] in ('or', 'not') and has_pred(g):
                raise Refuse('unknown under a disjunction or negation in a body')
        ws = []
        if head[0] == 'app' and head[1] == 'exists' and len(head[2]) == 2:
            lst, inner = head[2]
            if lst[0] != 'list' or any(x[0] != 'var' for x in lst[1]):
                raise Refuse('exists: the bound list is not a list of variables')
            ws = [x[1] for x in lst[1]]
            if len(set(ws)) != len(ws):
                raise Refuse('exists binds a variable twice')
            head = inner
        # A head conjunct next(c, W) under the exists is the same relation as a body conjunct moved
        # there, and becomes one (a moved group), so that its stutter arm is decided below; only
        # when W are exactly its primed arguments and c mentions no bound variable, and its plain
        # definition has no variable of its own (which, in a head, is refused as before).
        h = []
        for t in self.src_conj(head):
            key = (t[1], len(t[2])) if t[0] == 'app' else None
            if ws and key in self.stutter_pri and len(groups) == len(srcs):
                k = len(t[2]) // 2
                cur, pri = [self.term(a) for a in t[2][:k]], [self.term(a) for a in t[2][k:]]
                params, mbody = self.macros[key]
                if all(a[0] == 'var' and a[1] in ws for a in pri) \
                        and len({a[1] for a in pri}) == len(pri) \
                        and not any(tvars(a, set()) & set(ws) for a in cur) \
                        and not fvars(self.formula(mbody, 'macro', False)) - set(params):
                    self.plain_next = True
                    try:
                        groups.append(self.conj(self.formula(t, 'head', True)))
                    finally:
                        self.plain_next = False
                    nexts[len(groups) - 1] = (cur, pri)
                    continue
            h.extend(self.conj(self.formula(t, 'head', True)))
        for g in h:
            if g[0] in ('or', 'not') and has_pred(g):
                raise Refuse('unknown under a disjunction or negation in a head')
        moved = set()
        if ws:
            # The unit moved is a source conjunct, not a conjunct of its expansion: a transition
            # macro `next(V, W) := G(V), U(V, W)` is the relation the paper's encoding puts under
            # the exists whole.  Moving only U would leave the guard G in the body, so a state where
            # G fails would no longer need a successor -- a weaker clause, and an EG or EF problem
            # whose path deadlocks would turn satisfiable.
            for i, grp in enumerate(groups):
                gv = set()
                for g in grp:
                    fvars(g, gv)
                if gv & set(ws):
                    moved.add(i)
                    # The stuttered `next` pairs its parameter halves as current and primed; a moved
                    # application must put the existential's variables exactly on the primed half.
                    if i in nexts:
                        cur, pri = nexts[i]
                        if any(a[0] != 'var' or a[1] not in ws for a in pri) \
                                or any(tvars(a, set()) & set(ws) for a in cur):
                            raise Refuse('stutter: next is applied under an existential with the bound '
                                         'variables not exactly on its second half of arguments')
        # A body conjunct next'(c, p) = next(c, p) \/ (dead(c) /\ p = c) that stays in the body is
        # split: (A \/ A') /\ B => H is (A /\ B => H) /\ (A' /\ B => H).  In the stutter arm the
        # primed arguments, when they are distinct variables not occurring in c (universal over the
        # clause, since they are not under the head's exists), are replaced by c: forall p.
        # (p = c /\ F(p)) => G(p) is F(c) => G(c).  Otherwise the equations stay.
        arms = [(groups, h, nexts, False)]
        for i in sorted(set(nexts) - moved):
            out = []
            for gs, hh, nx, st in arms:
                out.append((gs, hh, nx, st))
                cur, pri = nx[i]
                pv = [a[1] for a in pri if a[0] == 'var']
                cv = set()
                for a in cur:
                    tvars(a, cv)
                if len(pv) == len(pri) and len(set(pv)) == len(pv) and not set(pv) & cv:
                    s, eqs = dict(zip(pv, cur)), []
                else:
                    s, eqs = {}, [('cmp', '=', p, c) for p, c in zip(pri, cur)]
                gs2 = [[('not', self.live(cur))] + eqs if j == i else [subst_f(g, s) for g in grp]
                       for j, grp in enumerate(gs)]
                nx2 = {j: ([subst_t(a, s) for a in c], [subst_t(a, s) for a in p]) for j, (c, p) in nx.items()}
                out.append((gs2, [subst_f(g, s) for g in hh], nx2, True))
            arms = out
        for n, (gs, hh, nx, st) in enumerate(arms):
            self.emit(gs, ws, hh, nx, moved, st, n == 0, len(srcs))

    def reflexive_wf(self, g):
        """g is q(t, t) for a (d)wf unknown q of arity 2n: no well-founded relation, and no disjunctively
        well-founded one (a finite union of well-founded relations), holds of a pair (v, v), since v, v,
        v, ... would be an infinite descending chain."""
        if g[0] != 'pred':
            return False
        n = len(g[2])
        return n % 2 == 0 and any(q == g[1] and k == n for q, k, _ in self.wf) \
            and g[2][:n // 2] == g[2][n // 2:]

    def emit(self, gs, ws, h, nx, moved, st, first, nbody):
        """Record the clause whose body is the conjunct groups gs (the first nbody from the source
        body, any later one a head next made a moved group) and whose head is exists ws. h;
        nx: the groups that are a plain next application (index -> current and primed terms);
        moved: the indices of the groups over ws; st: this clause is a stutter arm of a split body;
        first: the first (plain) arm of its source clause, which alone is counted."""
        if not ws:
            b = [g for grp in gs for g in grp]
            if st:
                # A stutter arm whose head conjuncts are all body conjuncts (inv(v) => inv(v) of an
                # AG or invariant clause after p := v) is valid and dropped.  One whose head is a
                # well-founded q(v, v) (an AF rank clause) has that head false (reflexive_wf).
                if all(g in b for g in h):
                    self.dropped += 1
                    return
                if len(h) == 1 and self.reflexive_wf(h[0]):
                    h = [('false',)]
                    self.sealed += 1
                self.split += 1
            self.clauses.append((b, ws, h))
            return
        keep = [g for j, grp in enumerate(gs) if j not in moved for g in grp]
        move = [g for j, grp in enumerate(gs) if j in moved for g in grp]
        for g in move:
            if has_pred(g):
                raise Refuse('a body atom of an unknown mentions an existentially bound variable')
        # A variable of a moved conjunct that occurs nowhere else in the body (a macro's local
        # variable, an anonymous `_`, an input such as `Rho` of `next(V, Rho, W)`) is existential
        # within the body, since forall L. (B(L) => H) is (exists L. B(L)) => H.  Moved into the
        # head it keeps that quantifier, now under the head's exists: leaving it universal states
        # that every value of it has a successor, which is a stronger clause.  One that also
        # occurs in the head outside W is universal over the whole clause in the source and
        # cannot be moved under the exists without changing that; such a clause is refused.
        kept_vs, head_vs, move_vs = set(), set(), set()
        for g in keep:
            fvars(g, kept_vs)
        for g in h:
            fvars(g, head_vs)
        for g in move:
            fvars(g, move_vs)
        local = move_vs - kept_vs - set(ws)
        if local & head_vs:
            raise Refuse('variable(s) %s occur in the head and only in body conjuncts moved under '
                         'the existential' % ', '.join(sorted(local & head_vs)))
        ws = ws + sorted(local)
        if first:
            if any(j < nbody for j in moved):
                self.moved += 1
            if not any(not has_pred(g) and fvars(g) & set(ws) for g in move + h):
                self.bare_exists += 1
        if st:
            self.split += 1
        # A moved next'(c, W) puts the stutter under the exists: B(c) => exists W. (next(c, W) /\
        # R(W)) \/ (dead(c) /\ R(c)), with R the other moved conjuncts and the head.  When R(c)
        # mentions no bound variable it is decided syntactically, after dropping its body conjuncts
        # (true under B): a conjunct false or a well-founded q(c, c) makes the arm false, and the
        # clause is the plain one; nothing left makes the head (exists W. next /\ R) \/ dead(c),
        # i.e. B /\ live(c) => exists W. next /\ R, and with R empty that is valid (live(c) is
        # exists u. next(c, u) exactly) and dropped.  Otherwise next' stays as one disjunction.
        stut = [j for j in sorted(moved) if j in nx]
        plain = []
        if len(stut) == 1:
            m = stut[0]
            cur, pri = nx[m]
            s = {p[1]: c for p, c in zip(pri, cur)}
            rest = [g for j in sorted(moved) if j != m for g in gs[j]] + h
            arm = [subst_f(g, s) for g in rest]
            av = set()
            for g in arm:
                fvars(g, av)
            if not av & set(ws):
                arm = [g for g in arm if g not in keep]
                if any(g[0] == 'false' or self.reflexive_wf(g) for g in arm):
                    plain = stut
                    self.sealed += 1
                elif not arm:
                    if not rest:
                        self.dropped += 1
                        return
                    plain = stut
                    keep = keep + [self.live(cur)]
                    self.split += 1
        # The same clause with the successor eliminated (one-point rule, onepoint): when the only
        # bound variables are the primed arguments W of the one moved next (no local of a moved
        # conjunct, no other witness), exists W. next(c, W) /\ R(W) is \/_i (G_i(c) /\ R(e_i(c))),
        # and the stutter disjunct dead(c) /\ R(c), where it was not decided above, is one more
        # disjunct.  The head becomes a disjunction of conjunctions over unknowns: to_smt2 writes it
        # only into a class that admits non-Horn clauses, to_hes as a nu-body disjunction.
        if self.onepoint_on and len(stut) == 1 and set(ws) == {p[1] for p in nx[stut[0]][1]}:
            m = stut[0]
            cur, pri = nx[m]
            rest = [g for j in sorted(moved) if j != m for g in gs[j]] + h
            disj = self.onepoint(cur, [p[1] for p in pri], rest)
            if disj is not None:
                if not plain:
                    s = {p[1]: c for p, c in zip(pri, cur)}
                    disj = ('or', disj[1] + [('and', [('not', self.live(cur))] + [subst_f(g, s) for g in rest])])
                self.onepoint_alt[len(self.clauses)] = (keep, [], [disj])
        if stut and not plain:
            gs = [[('or', [('and', grp), ('and', [('not', self.live(nx[j][0]))]
                                          + [('cmp', '=', p, c) for p, c in zip(nx[j][1], nx[j][0])])])]
                  if j in stut else grp for j, grp in enumerate(gs)]
            move = [g for j, grp in enumerate(gs) if j in moved for g in grp]
        self.clauses.append((keep, ws, move + h))


# ---------------------------------------------------------------- printers

def smt_t(t):
    k = t[0]
    if k == 'var':
        return 'x_' + t[1]
    if k == 'int':
        return str(t[1]) if t[1] >= 0 else '(- %d)' % -t[1]
    if k == 'neg':
        return '(- %s)' % smt_t(t[1])
    return '(%s %s %s)' % ({'add': '+', 'sub': '-', 'mul': '*'}[k], smt_t(t[1]), smt_t(t[2]))


def smt_f(f):
    k = f[0]
    if k == 'true':
        return 'true'
    if k == 'false':
        return 'false'
    if k in ('and', 'or'):
        if not f[1]:
            return 'true' if k == 'and' else 'false'
        if len(f[1]) == 1:
            return smt_f(f[1][0])
        return '(%s %s)' % (k, ' '.join(smt_f(g) for g in f[1]))
    if k == 'not':
        return '(not %s)' % smt_f(f[1])
    if k == 'cmp':
        if f[1] == '!=':
            return '(not (= %s %s))' % (smt_t(f[2]), smt_t(f[3]))
        return '(%s %s %s)' % (f[1], smt_t(f[2]), smt_t(f[3]))
    if k == 'pred':
        if not f[2]:
            return f[1]
        return '(%s %s)' % (f[1], ' '.join(smt_t(a) for a in f[2]))
    raise AssertionError(f)


def hes_t(t):
    k = t[0]
    if k == 'var':
        return 'x_' + t[1]
    if k == 'int':
        return str(t[1]) if t[1] >= 0 else '(0 - %d)' % -t[1]
    if k == 'neg':
        return '(0 - %s)' % hes_t(t[1])
    return '(%s %s %s)' % (hes_t(t[1]), {'add': '+', 'sub': '-', 'mul': '*'}[k], hes_t(t[2]))


def hes_f(f):
    k = f[0]
    if k == 'true':
        return 'true'
    if k == 'false':
        return 'false'
    if k in ('and', 'or'):
        if not f[1]:
            return 'true' if k == 'and' else 'false'
        return '(' + (' /\\ ' if k == 'and' else ' \\/ ').join(hes_f(g) for g in f[1]) + ')'
    if k == 'not':
        return '(not %s)' % hes_f(f[1])
    if k == 'cmp':
        return '(%s %s %s)' % (hes_t(f[2]), f[1], hes_t(f[3]))
    if k == 'pred':
        if not f[2]:
            return 'P_%s ()' % f[1]
        return '(P_%s %s)' % (f[1], ' '.join('(%s)' % hes_t(a) for a in f[2]))
    if k == 'exists':
        if not f[1]:
            return hes_f(f[2])
        return '(exists %s. %s)' % (' '.join('(x_%s: %s)' % (v, f[3]) for v in f[1]), hes_f(f[2]))
    if k == 'forall':
        if not f[1]:
            return hes_f(f[2])
        return '(forall %s. %s)' % (' '.join('(x_%s: %s)' % (v, f[3]) for v in f[1]), hes_f(f[2]))
    if k == 'imp':
        return '(%s => %s)' % (hes_f(f[1]), hes_f(f[2]))
    raise AssertionError(f)


def stutter_state(pb):
    if not pb.stutter:
        return 'off'
    return 'applied' if pb.stuttered else 'no-next'


STUTTER_NOTE = ('a state without a next-successor has a self-loop: next(v, v\') is read as '
                'next(v, v\') \\/ (~(exists u. next(v, u)) /\\ v\' = v)')


ONEPOINT_NOTE = ('%d clause(s) with an existential successor exists w. next(v, w) /\\ R(w) have it eliminated '
                 'by the one-point rule: \\/_i (G_i(v) /\\ R(e_i(v))), next being \\/_i (G_i(v) /\\ w = e_i(v))')


def to_smt2(pb, sort, src, comments):
    out = ['; Generated by script/qarmc_to_smt2.py from %s' % src,
           '; E-HSF/QARMC clause format (Beyene, Popeea, Rybalchenko, CAV 2013); every variable is %s.' % sort]
    if pb.stuttered:
        out.append('; ' + STUTTER_NOTE + '.')
    if pb.moved:
        out.append('; %d clause(s) had a body conjunct over an existentially bound variable, moved under the'
                   % pb.moved)
        out.append(';   existential: forall v. B0(v) => exists w. B1(v, w) /\\ H(v, w).')
    if pb.wf and pb.onepoint_alt:
        out.append('; ' + ONEPOINT_NOTE % len(pb.onepoint_alt) + '.')
    for line in comments:
        out.append('; source: ' + line)
    for name in sorted(pb.hints):
        for h in pb.hints[name]:
            out.append('; dropped hint: ' + h)
    out.append('(set-logic HORN)')
    wf = {q: k for q, _, k in pb.wf}
    if len(wf) != len(pb.wf):
        raise Refuse('an unknown declared well-founded twice')
    for q in sorted(pb.arity):
        args = ' '.join([sort] * pb.arity[q])
        decl = {'wf': 'wfp', 'dwf': 'dwfp'}.get(wf.get(q), 'fun')
        out.append('(declare-%s %s (%s) Bool)' % (decl, q, args))
    for b, ws, h in pb.final_clauses(bool(pb.wf)):
        hf = ('and', h)
        hs = smt_f(hf)
        bound = set(ws)
        if ws:
            hs = '(exists (%s) %s)' % (' '.join('(x_%s %s)' % (w, sort) for w in ws), hs)
        bs = smt_f(('and', b))
        vs = set()
        for g in b:
            fvars(g, vs)
        for g in h:
            fvars(g, vs)
        vs -= bound
        body = '(=> %s %s)' % (bs, hs)
        if vs:
            body = '(forall (%s) %s)' % (' '.join('(x_%s %s)' % (v, sort) for v in sorted(vs)), body)
        out.append('(assert %s)' % body)
    out.append('(check-sat)')
    return '\n'.join(out) + '\n'


def hes_fragment(pb):
    """The reason the problem is outside the nu-only fragment, or None."""
    if pb.wf:
        return 'wf declared'
    for b, ws, h in pb.clauses:
        n = sum(1 for g in b if g[0] == 'pred')
        if n > 1:
            return 'a clause with %d unknowns in its body' % n
    return None


def to_hes(pb, sort, src):
    s = sort.lower()
    eqs = {q: [] for q in pb.arity}
    query = []
    for b, ws, h in pb.final_clauses(True):
        atoms = [g for g in b if g[0] == 'pred']
        rest = [g for g in b if g[0] != 'pred']
        head = ('exists', ws, ('and', h), s)
        vs = set()
        for g in b + h:
            fvars(g, vs)
        vs -= set(ws)
        if atoms:
            q, args = atoms[0][1], atoms[0][2]
            params = ['p%d' % i for i in range(len(args))]
            # An argument that is a variable of its own (not existential, not repeated) is renamed to
            # its parameter instead of being bound and equated: `forall x. p = x => ...` is equivalent,
            # but a solver that keeps the binder Skolemises it in its dual (an identity to synthesise),
            # and MuVal then did not refute a one-equation system whose fixpoint is empty.  The
            # renaming is skipped when a conjunct has a binder of its own, which subst_f does not enter.
            ren, eqsf = {}, []
            nested = any(g[0] == 'exists' for g in rest + h)
            for p, a in zip(params, args):
                if not nested and a[0] == 'var' and a[1] not in ws and a[1] not in ren:
                    ren[a[1]] = ('var', p)
                else:
                    eqsf.append(('cmp', '=', ('var', p), a))
            eqsf = [subst_f(g, ren) for g in eqsf]
            rest = [subst_f(g, ren) for g in rest]
            head = ('exists', ws, ('and', [subst_f(g, ren) for g in h]), s)
            # P(params) => forall vs. (params = args /\ rest) => head
            eqs[q].append(('forall', sorted(vs - set(ren)), ('imp', ('and', eqsf + rest), head), s))
        else:
            query.append(('forall', sorted(vs), ('imp', ('and', rest), head), s))
    lines = ['/* Generated by script/qarmc_to_smt2.py from %s: the nu-only muCLP encoding of an' % src,
             '   E-CHC whose clauses have at most one unknown in the body (greatest fixpoint of the',
             '   body-indexed operator, checked against the clauses without an unknown in the body).'
             + ('\n   ' + STUTTER_NOTE + '.' if pb.stuttered else '')
             + ('\n   ' + ONEPOINT_NOTE % len(pb.onepoint_alt) + '.' if pb.onepoint_alt else '') + ' */']
    lines.append(hes_f(('and', query)) if query else 'true')
    lines.append('s.t.')
    for q in sorted(eqs):
        n = pb.arity[q]
        params = ' '.join('(x_p%d: %s)' % (i, s) for i in range(n)) if n else '()'
        body = ('and', eqs[q])
        lines.append('P_%s %s: bool =nu %s;' % (q, params, hes_f(body)))
    return '\n'.join(lines) + '\n'


def source_comments(text):
    """The tool's own result notes at the file's end (lines starting with %)."""
    out = []
    for line in text.splitlines():
        s = line.strip()
        if s.startswith('%') and ('ctlstar' in s or 'program correct' in s or 'program is correct' in s
                                  or 'CEX' in s):
            out.append(s.lstrip('% ').rstrip())
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('src')
    ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--hes')
    ap.add_argument('--sort', choices=['Int', 'Real'], default='Int')
    ap.add_argument('--name', help='source name written into the header (default: the path)')
    ap.add_argument('--info', action='store_true')
    ap.add_argument('--no-stutter', action='store_true',
                    help='keep next as written: a state without a successor stays a deadlock')
    ap.add_argument('--keep-exists', action='store_true',
                    help='keep an existential successor of next instead of eliminating it by the one-point rule')
    a = ap.parse_args()
    with open(a.src, encoding='latin-1') as fh:
        text = fh.read()
    src = a.name or a.src
    try:
        pb = Problem()
        pb.stutter = not a.no_stutter
        pb.onepoint_on = not a.keep_exists
        pb.load(Reader(lex(text)).clauses())
        smt = to_smt2(pb, a.sort, src, source_comments(text))
    except Refuse as e:
        print('refused: %s' % e, file=sys.stderr)
        if a.info:
            print('refused\t%s' % e)
        return 1
    with open(a.out, 'w') as fh:
        fh.write(smt)
    has_e = any(ws for _, ws, _ in pb.clauses)
    cls = 'pfwnCSP' if pb.wf else ('ECHC' if has_e else 'CHC')
    why = hes_fragment(pb) or ('the muCLP printer writes Int only' if a.sort != 'Int' else None)
    hes = why or 'written'
    if a.hes:
        if why is None:
            with open(a.hes, 'w') as fh:
                fh.write(to_hes(pb, 'Int', src))
        elif os.path.exists(a.hes):
            os.remove(a.hes)
    if a.info:
            print('class=%s\texists=%d\twf=%d\tmoved=%d\thes=%s\tstutter=%s\thints=%s' % (
            cls, sum(1 for _, ws, _ in pb.clauses if ws), len(pb.wf), pb.moved, hes, stutter_state(pb),
            ','.join('%s:%d' % (k, len(v)) for k, v in sorted(pb.hints.items())) or '-')
            + ('\tonepoint=%d' % len(pb.onepoint_alt) if pb.onepoint_alt else ''))
    return 0


if __name__ == '__main__':
    sys.exit(main())
