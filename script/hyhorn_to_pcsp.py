#!/usr/bin/env python3
"""Convert HyHorn's hyperproperty benchmark suite into CoAR pCSP problems (SMT-LIB 2 with `declare-fun`).

    python3 -I script/hyhorn_to_pcsp.py --hyhorn DIR --out OUT [--z3 Z3] [--only NAME ...] [--list]

SOURCE.  HyHorn is the tool of Itzhaky, Shoham and Vizel, "Hyperproperty Verification as CHC Satisfiability",
ESOP 2024 (LNCS 14577, pp. 212-241, doi 10.1007/978-3-031-57267-8_9).  DIR is the `/hyhorn` directory of its
artifact (Zenodo record 10449234, CC-BY-4.0), taken out of the record's Docker image without running it.  Its
specifications are Python classes (`benchmarks/hypa.py`, `benchmarks/more_test_cases.py`): control-flow graphs
whose edge labels map to state transformers (`lambda s: s.assume('x < n').assign({'x': 'x + 1'})`), with the
precondition, the observation points and the observed property given as strings of Z3 Python syntax.

THE ARTIFACT'S CODE IS NEVER RUN.  The two files are parsed with Python's `ast` module and the small part of Python
they use is interpreted here: literals, comprehensions, f-strings, lambdas and the few method bodies the suite
calls (`simplified`, `global_assumptions`, the `etc` helpers), against a re-implementation of the three HyHorn
library classes they build on, read from its `lib/floyd.py` and `lib/symbolic_interp.py`: `FloydCFG` (edges, the
first edge's source is the start node), the symbolic `State` (`assign` is simultaneous, `assume` adds a path
condition, `use` adds names to the evaluation context of a string) and `TR_of_CFG` (a step is the disjunction over
edges of `pc = u /\\ path conditions /\\ V' = V after the transformer, pc' = v`).  Anything else -- another call,
statement or operator -- is refused, never approximated.  Terms are built and printed here; Z3 (the binary given by
--z3) is only asked whether a copy's transition formula is total.

WHAT IS EMITTED.  A specification is  psi -> forall pi_1 : xi_1 ... pi_l : xi_l . exists pi_l+1 : xi_l+1 ... . G phi
over k copies of a transition system (OHyperLTL with observation points xi_i; at most one existential copy in
this suite).  Two encodings, both from the paper:

  k-safety (l = k): the paper's Fig. 4a, which its Theorem 2 states is satisfiable iff the system satisfies the
  property.  Unknowns: Inv(V) and one arbiter predicate A_M(V) per non-empty schedule M of the copies.

      init_1(V_1) /\\ ... /\\ init_k(V_k) /\\ psi(V)  ->  Inv(V)
      Inv(V) /\\ xi_1(V_1) /\\ ... /\\ xi_k(V_k) /\\ ~phi(V)  ->  false
      Inv(V) /\\ A_M(V) /\\ ~valid_M(V)  ->  false                         (for every M)
      Inv(V) /\\ A_M(V) /\\ Delta_M(V, V')  ->  Inv(V')                    (for every M)
      Inv(V)  ->  \\/_M A_M(V)

  where Delta_M steps the copies in M by their transition formula and keeps the others, and valid_M says that no
  copy in M is at its observation point, or that M is every copy and all are at their points or none is (the
  paper's Definition 1: the copies synchronise at observation points).  The last clause has a disjunctive head:
  this is the pCSP the paper starts from, before its own transformation to CHCs.

  forall-exists (l = k - 1): the verification game of Beutner and Finkbeiner (CAV 2022) that the paper's Fig. 6a
  encodes, with every choice made explicit.  In a round the falsifier fixes the next state C_i of every universal
  copy (any successor its transition formula allows), the verifier answers with a schedule M -- A_M(V, C) -- and,
  when the existential copy is in M, with a successor of that copy, which is a head existential:

      Inv(V) /\\ T_1(V_1, C_1) /\\ ... /\\ T_l(V_l, C_l)  ->  \\/_M A_M(V, C)
      Inv(V) /\\ T(V, C) /\\ A_M(V, C) /\\ ~valid_M(V)  ->  false
      Inv(V) /\\ T(V, C) /\\ A_M(V, C)  ->  exists V'_k. T_k(V_k, V'_k) /\\ Inv(post_M)   (k in M)
      Inv(V) /\\ T(V, C) /\\ A_M(V, C)  ->  Inv(post_M)                                  (k not in M)

  This is the game on the system made deterministic by labelling every transition with all of its
  nondeterministic choices (the paper's Sec. 6, "we can always determinize TS by extending the set of labels"):
  the verifier sees the universal copies' moves before it moves and makes all of the existential copy's choices.
  It is exact for the game semantics with finite or infinite branching, and the paper's own encodings -- labels
  for some choices only and, for infinite branching, the "restrictions" of its Sec. 6.2 -- each ask at least as
  much.  Satisfiable implies the property (the game semantics is sound, the paper's Theorem 3); unsatisfiable
  means the verifier has no winning strategy in this game, not that the property fails.

  Totality.  The theorems assume every state has a successor (the paper's footnote 3 adds a self-loop where there
  is none).  For each copy and each node of its graph Z3 is asked whether some edge is always enabled there; where
  not, the step relation gets exactly that completion (stay put where no edge is enabled), and the file's header
  names the nodes.

  HyHorn's proof hints -- predicate abstraction (`pa`), `projections`, `restrictions` -- are not part of the
  property and are not emitted.  `global_assumptions` (one instance, squares_sum, stating facts about a
  nondeterministic value that stands for a*a) is part of HyHorn's model of the program and is conjoined to every
  step, as HyHorn does.  HyHorn's `int` is the mathematical integer and its arrays are Z3 arrays from Int.

Exit status: 0 when every selected instance was written or refused with a reason, 1 on an unexpected failure.
"""
import argparse
import ast
import itertools
import os
import re
import subprocess
import sys
import traceback


class Refused(Exception):
    pass


# ----------------------------------------------------------------------------------------------------- terms

INT, BOOL = "Int", "Bool"


def arr(elem):
    return ("Array", INT, elem)


class T:
    """A first-order term: op is 'var', 'int', 'bool' or an SMT-LIB function symbol; sort is INT, BOOL or arr(s)."""
    __slots__ = ("op", "args", "sort", "name", "val")

    def __init__(self, op, args=(), sort=None, name=None, val=None):
        self.op, self.args, self.sort, self.name, self.val = op, tuple(args), sort, name, val


def var(name, sort):
    return T("var", (), sort, name=name)


def lit(x):
    if isinstance(x, T):
        return x
    if isinstance(x, Poison):
        raise Refused(f"{x.what} is outside the supported part of the DSL")
    if isinstance(x, bool):
        return T("bool", (), BOOL, val=x)
    if isinstance(x, int):
        return T("int", (), INT, val=x)
    raise Refused(f"not a term: {x!r}")


def sort_str(s):
    if isinstance(s, tuple):
        return f"(Array {sort_str(s[1])} {sort_str(s[2])})"
    return s


ARITH = {"+", "-", "*"}
CMP = {"<", "<=", ">", ">="}


def app(op, *args):
    args = [lit(a) for a in args]
    if op in ARITH:
        if any(a.sort != INT for a in args):
            raise Refused(f"'{op}' on a non-integer")
        return T(op, args, INT)
    if op == "neg":
        if args[0].sort != INT:
            raise Refused("negation of a non-integer")
        return T("-", args, INT)
    if op in CMP:
        if any(a.sort != INT for a in args):
            raise Refused(f"'{op}' on a non-integer")
        return T(op, args, BOOL)
    if op == "=":
        if args[0].sort != args[1].sort:
            raise Refused(f"'=' between sorts {args[0].sort} and {args[1].sort}")
        return T("=", args, BOOL)
    if op in ("and", "or"):
        if any(a.sort != BOOL for a in args):
            raise Refused(f"'{op}' of a non-Boolean")
        if not args:
            return lit(op == "and")
        if len(args) == 1:
            return args[0]
        return T(op, args, BOOL)
    if op in ("not", "=>"):
        if any(a.sort != BOOL for a in args):
            raise Refused(f"'{op}' of a non-Boolean")
        return T(op, args, BOOL)
    if op == "ite":
        if args[0].sort != BOOL or args[1].sort != args[2].sort:
            raise Refused("ill-sorted if-then-else")
        return T("ite", args, args[1].sort)
    if op in ("div", "mod"):
        if any(a.sort != INT for a in args):
            raise Refused(f"'{op}' on a non-integer")
        return T(op, args, INT)
    if op == "store":
        a, i, v = args
        if not (isinstance(a.sort, tuple) and i.sort == a.sort[1] and v.sort == a.sort[2]):
            raise Refused("ill-sorted store")
        return T("store", args, a.sort)
    if op == "select":
        a, i = args
        if not (isinstance(a.sort, tuple) and i.sort == INT):
            raise Refused("indexing a non-array")
        return T("select", args, a.sort[2])
    raise Refused(f"operator {op}")


def to_smt(t):
    if t.op == "var":
        return t.name
    if t.op == "int":
        return str(t.val) if t.val >= 0 else f"(- {-t.val})"
    if t.op == "bool":
        return "true" if t.val else "false"
    if t.op == "exists":
        bs = " ".join(f"({v.name} {sort_str(v.sort)})" for v in t.val)
        return f"(exists ({bs}) {to_smt(t.args[0])})"
    return "(" + " ".join([t.op] + [to_smt(a) for a in t.args]) + ")"


def free_vars(t, acc=None, bound=frozenset()):
    if acc is None:
        acc = {}
    if t.op == "var":
        if t.name not in bound:
            acc.setdefault(t.name, t)
    elif t.op == "exists":
        free_vars(t.args[0], acc, bound | {v.name for v in t.val})
    else:
        for a in t.args:
            free_vars(a, acc, bound)
    return acc


def subst(t, m):
    if t.op == "var":
        return m.get(t.name, t)
    if not t.args:
        return t
    if t.op == "exists":
        inner = {k: v for k, v in m.items() if k not in {b.name for b in t.val}}
        return T("exists", (subst(t.args[0], inner),), BOOL, val=t.val)
    return T(t.op, [subst(a, m) for a in t.args], t.sort, t.name, t.val)


def mk_and(*xs):
    return app("and", *xs)


def mk_or(*xs):
    return app("or", *xs)


# ------------------------------------------------------------------------------- the DSL's runtime objects

class Fresh:
    n = 0

    @classmethod
    def name(cls, prefix):
        cls.n += 1
        return f"{prefix}{cls.n}"


class Edge(tuple):
    pass


class FloydCFG:
    """lib/floyd.py's FloydCFG: nodes in order of appearance, the start node is the first edge's source."""

    def __init__(self):
        self.V, self.E, self.start, self.tr = [], [], None, {}

    def edges(self, es):
        for e in es:
            e = tuple(e)
            for u in e[:2]:
                if self.start is None:
                    self.start = u
                if u not in self.V:
                    self.V.append(u)
            if len(e) == 2:
                e = e + ({},)
            if isinstance(e[2], str):
                e = e[:2] + ({"label": e[2]},)
            if len(e) != 3 or not isinstance(e[2], dict):
                raise Refused(f"edge {e!r}")
            self.E.append(e)
        return self

    def deepcopy(self):
        c = FloydCFG()
        c.V, c.start, c.tr = list(self.V), self.start, dict(self.tr)
        c.E = [(u, v, dict(l)) for (u, v, l) in self.E]
        return c


class Signature:
    def __init__(self, decls):
        self.decls = {}
        for v, ty in decls.items():
            self.decls[v] = parse_type(ty)


class Poison:
    """The value of a name outside the supported subset (a bit-vector sort, say); any use refuses."""

    def __init__(self, what):
        self.what = what


def parse_type(ty):
    if isinstance(ty, Poison):
        raise Refused(f"{ty.what} is outside the supported part of the DSL")
    if ty in (INT, BOOL) or isinstance(ty, tuple):
        return ty
    if isinstance(ty, list):
        if len(ty) != 1:
            raise Refused(f"type {ty!r}")
        return arr(parse_type(ty[0]))
    if ty is int:
        return INT
    if ty is bool:
        return BOOL
    raise Refused(f"type {ty!r}")


class State:
    """lib/symbolic_interp.py's State."""

    def __init__(self, interp, sig=None, suffix=None):
        self.interp = interp
        self.sig = sig
        self.locals = {}
        self.path = []
        self.mw = {}
        if sig is not None:
            for v, s in sig.decls.items():
                self.locals[v] = var(v + suffix, s)

    def clone(self):
        c = State(self.interp)
        c.sig, c.locals, c.path, c.mw = self.sig, dict(self.locals), list(self.path), dict(self.mw)
        return c

    def context(self):
        d = {"_": self}
        d.update(self.mw)
        d.update(self.locals)
        return d

    def eval(self, expr):
        if isinstance(expr, (PyFunction, Builtin, BoundMethod)):
            expr = self.interp.call(expr, [self], {})
        if isinstance(expr, str):
            expr = self.interp.eval_string(expr, self.context())
        return expr

    # the methods a transformer may call
    def m_assign(self, d):
        if not isinstance(d, dict):
            raise Refused("assign of a non-dict")
        new = {}
        for v, e in d.items():
            if v not in self.locals:
                raise Refused(f"assignment to undeclared {v}")
            val = lit(self.eval(e))
            if val.sort != self.sig.decls[v]:
                raise Refused(f"assignment of sort {val.sort} to {v}")
            new[v] = val
        self.locals.update(new)
        return self

    def m_assume(self, c):
        c = lit(self.eval(c))
        if c.sort != BOOL:
            raise Refused("assume of a non-Boolean")
        self.path.append(c)
        return self

    def m_use(self, d):
        if not isinstance(d, dict):
            raise Refused("use of a non-dict")
        self.mw.update(d)
        return self

    def m_clone(self):
        return self.clone()


class Compound(tuple):
    """CompoundState: `_[i]['x']` in a string is copy i's variable x."""

    def context(self):
        return {"_": tuple(s.context() for s in self)}


# --------------------------------------------------------------------------------------- the interpreter

class PyFunction:
    def __init__(self, node, params, defaults, body, env, is_lambda, name):
        self.node, self.params, self.defaults, self.body, self.env = node, params, defaults, body, env
        self.is_lambda, self.name = is_lambda, name
        self.kind = "function"


class BoundMethod:
    def __init__(self, fn, obj):
        self.fn, self.obj = fn, obj


class Builtin:
    def __init__(self, f, name):
        self.f, self.name = f, name


class PyClass:
    def __init__(self, name, bases, ns):
        self.name, self.bases, self.ns = name, bases, ns

    def mro(self):
        out = [self]
        for b in self.bases:
            for c in b.mro():
                if c not in out:
                    out.append(c)
        return out

    def lookup(self, attr):
        for c in self.mro():
            if attr in c.ns:
                return True, c.ns[attr]
        return False, None


class Instance:
    def __init__(self, cls):
        self.cls, self.d = cls, {}


class Return(Exception):
    def __init__(self, v):
        self.v = v


class Module:
    def __init__(self, name, g):
        self.name, self.g = name, g


ROOT = "benchmark"  # HyHorn's benchmark base class, given its semantics directly


class Interp:
    def __init__(self, hyhorn):
        self.dir = hyhorn
        self.modules = {}
        self.root = PyClass(ROOT, [], {
            "nondets": None, "global_assumptions": None, "qs": None, "restrictions": None,
        })

    # ---- modules
    def load(self, name):
        if name in self.modules:
            return self.modules[name]
        path = os.path.join(self.dir, "benchmarks", name + ".py")
        with open(path) as f:
            tree = ast.parse(f.read(), filename=path)
        g = {}
        mod = Module(name, g)
        self.modules[name] = mod
        for st in tree.body:
            self.module_stmt(st, g)
        return mod

    def z3_name(self, n):
        table = {
            "And": Builtin(lambda *a: mk_and(*a), "And"),
            "Or": Builtin(lambda *a: mk_or(*a), "Or"),
            "Not": Builtin(lambda a: app("not", a), "Not"),
            "Implies": Builtin(lambda a, b: app("=>", a, b), "Implies"),
            "If": Builtin(lambda c, a, b: app("ite", c, a, b), "If"),
            "Int": Builtin(lambda nm: var(nm, INT), "Int"),
        }
        return table.get(n)

    def module_stmt(self, st, g):
        if isinstance(st, ast.ImportFrom):
            for al in st.names:
                nm = al.asname or al.name
                if st.module == "z3":
                    b = self.z3_name(al.name)
                    g[nm] = b if b is not None else Builtin(self.refuser(f"z3.{al.name}"), al.name)
                elif st.module == "floyd" and al.name == "FloydCFG":
                    g[nm] = Builtin(lambda: FloydCFG(), "FloydCFG")
                elif st.module in ("floyd", "predicate_abstraction"):
                    g[nm] = Builtin(lambda *a, **k: None, al.name)  # TS_of_CFG, PredicateAbstraction: hints only
                elif st.module in ("hypa",):
                    g[nm] = self.load(st.module).g[al.name]
                else:
                    raise Refused(f"import from {st.module}")
            return
        if isinstance(st, ast.Import):
            for al in st.names:
                g[al.asname or al.name] = self.load(al.name)
            return
        if isinstance(st, ast.ClassDef):
            if st.name in ("cfgs", "meta"):
                return  # metaclass plumbing of `benchmark`
            if st.name == ROOT:
                g[ROOT] = self.root
                return
            g[st.name] = self.class_def(st, [g])
            return
        if isinstance(st, ast.Assign):
            v = self.ev(st.value, [g])
            for t in st.targets:
                self.assign(t, v, [g])
            return
        if isinstance(st, ast.Expr) and isinstance(st.value, ast.Constant):
            return
        if isinstance(st, ast.FunctionDef):
            g[st.name] = self.func_def(st, [g])
            return
        raise Refused(f"module statement {ast.dump(st)[:60]}")

    def refuser(self, what):
        # A name outside the supported subset is refused when its value is used, not when a class that some
        # other (unconverted) instance defines is created.
        return lambda *a, **k: Poison(what)

    def class_def(self, st, env):
        bases = [self.ev(b, env) for b in st.bases]
        for b in bases:
            if not isinstance(b, PyClass):
                raise Refused(f"base class {b!r}")
        ns = {}
        cenv = [ns] + env
        for s in st.body:
            if isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant):
                continue
            if isinstance(s, ast.FunctionDef):
                ns[s.name] = self.func_def(s, env)  # a method body does not see the class namespace
                continue
            if isinstance(s, ast.Assign):
                v = self.ev(s.value, cenv)
                for t in s.targets:
                    self.assign(t, v, cenv)
                continue
            if isinstance(s, ast.Pass):
                continue
            raise Refused(f"class statement {ast.dump(s)[:60]}")
        return PyClass(st.name, bases, ns)

    def func_def(self, st, env):
        a = st.args
        if a.vararg or a.kwarg or a.kwonlyargs or a.posonlyargs:
            raise Refused(f"signature of {st.name}")
        defaults = [self.ev(d, env) for d in a.defaults]
        f = PyFunction(st, [p.arg for p in a.args], defaults, st.body, env, False, st.name)
        for d in st.decorator_list:
            if isinstance(d, ast.Name) and d.id in ("staticmethod", "classmethod", "property"):
                f.kind = d.id
            else:
                raise Refused(f"decorator on {st.name}")
        return f

    # ---- calls
    def call(self, f, args, kw):
        if isinstance(f, Builtin):
            return f.f(*args, **kw)
        if isinstance(f, BoundMethod):
            return self.call(f.fn, [f.obj] + list(args), kw)
        if isinstance(f, PyClass):
            if args or kw:
                raise Refused(f"constructor arguments for {f.name}")
            return Instance(f)
        if not isinstance(f, PyFunction):
            raise Refused(f"call of {f!r}")
        if kw:
            raise Refused("keyword arguments")
        n = len(f.params)
        if len(args) > n:
            raise Refused(f"{len(args)} arguments for {f.name} ({n} parameters)")
        loc = dict(zip(f.params, args))
        missing = f.params[len(args):]
        nd = len(f.defaults)
        for i, p in enumerate(missing):
            j = len(args) + i - (n - nd)
            if j < 0:
                raise Refused(f"missing argument {p} of {f.name}")
            loc[p] = f.defaults[j]
        env = [loc] + f.env
        if f.is_lambda:
            return self.ev(f.body, env)
        try:
            for s in f.body:
                self.stmt(s, env)
        except Return as r:
            return r.v
        return None

    # ---- statements in function bodies
    def stmt(self, s, env):
        if isinstance(s, ast.Return):
            raise Return(self.ev(s.value, env) if s.value is not None else None)
        if isinstance(s, ast.Assign):
            v = self.ev(s.value, env)
            for t in s.targets:
                self.assign(t, v, env)
            return
        if isinstance(s, ast.AugAssign) and isinstance(s.op, ast.Add):
            cur = self.ev(s.target, env)
            self.assign(s.target, self.binop(ast.Add(), cur, self.ev(s.value, env)), env)
            return
        if isinstance(s, ast.Expr):
            if isinstance(s.value, ast.Constant):
                return
            self.ev(s.value, env)
            return
        if isinstance(s, ast.For):
            if s.orelse:
                raise Refused("for-else")
            for x in self.iterate(self.ev(s.iter, env)):
                self.assign(s.target, x, env)
                for b in s.body:
                    self.stmt(b, env)
            return
        if isinstance(s, ast.If):
            for b in (s.body if self.truth(self.ev(s.test, env)) else s.orelse):
                self.stmt(b, env)
            return
        if isinstance(s, ast.Import):
            for al in s.names:
                if al.name != "copy":
                    raise Refused(f"import {al.name}")
                env[0][al.asname or "copy"] = Module("copy", {"deepcopy": Builtin(self.deepcopy, "deepcopy")})
            return
        if isinstance(s, ast.Pass):
            return
        raise Refused(f"statement {ast.dump(s)[:60]}")

    def deepcopy(self, x):
        if isinstance(x, FloydCFG):
            return x.deepcopy()
        raise Refused("deepcopy of something other than a control-flow graph")

    def truth(self, x):
        if isinstance(x, T):
            raise Refused("a symbolic value used as a Python condition")
        return bool(x)

    def iterate(self, x):
        if isinstance(x, (list, tuple, set, dict, str, Compound)):
            return list(x)
        raise Refused(f"iteration over {type(x).__name__}")

    def assign(self, t, v, env):
        if isinstance(t, ast.Name):
            env[0][t.id] = v
        elif isinstance(t, ast.Tuple):
            vs = self.iterate(v)
            if len(vs) != len(t.elts):
                raise Refused("unpacking length")
            for a, b in zip(t.elts, vs):
                self.assign(a, b, env)
        elif isinstance(t, ast.Attribute):
            o = self.ev(t.value, env)
            if isinstance(o, Instance):
                o.d[t.attr] = v
            elif isinstance(o, PyClass):
                o.ns[t.attr] = v
            elif isinstance(o, FloydCFG) and t.attr == "tr":
                o.tr = v
            else:
                raise Refused(f"attribute assignment .{t.attr}")
        elif isinstance(t, ast.Subscript):
            o = self.ev(t.value, env)
            k = self.ev(t.slice, env)
            if isinstance(o, dict):
                o[k] = v
            else:
                raise Refused("item assignment")
        else:
            raise Refused("assignment target")

    # ---- names and attributes
    def lookup(self, n, env):
        for d in env:
            if n in d:
                return d[n]
        if n in ("int", "bool"):
            return {"int": int, "bool": bool}[n]
        z = self.z3_name(n)
        if z is not None:
            return z
        raise Refused(f"name {n}")

    def getattr(self, o, a):
        if isinstance(o, Module):
            if a in o.g:
                return o.g[a]
            raise Refused(f"{o.name}.{a}")
        if isinstance(o, PyClass):
            ok, v = o.lookup(a)
            if not ok:
                if a == "__name__":
                    return o.name
                raise Refused(f"{o.name}.{a}")
            if isinstance(v, PyFunction) and v.kind == "classmethod":
                return BoundMethod(v, o)
            return v
        if isinstance(o, Instance):
            if a in o.d:
                return o.d[a]
            if a == "name":
                return o.d.get("__name__", o.cls.name)
            if a == "cfgs":
                ok, v = o.cls.lookup("cfgs")
                if ok:
                    return v
                cfg = self.getattr(o, "cfg")
                return [cfg, cfg]
            ok, v = o.cls.lookup(a)
            if not ok:
                raise Refused(f"attribute {a} of {o.cls.name}")
            if isinstance(v, PyFunction):
                if v.kind == "staticmethod":
                    return v
                if v.kind == "classmethod":
                    return BoundMethod(v, o.cls)
                if v.kind == "property":
                    return self.call(v, [o], {})
                return BoundMethod(v, o)
            return v
        if isinstance(o, State):
            if a == "locals":
                return o.locals
            if hasattr(o, "m_" + a):
                return Builtin(getattr(o, "m_" + a), a)
            raise Refused(f"state method {a}")
        if isinstance(o, FloydCFG):
            if a in ("E", "V", "tr", "start"):
                return getattr(o, a)
            if a == "edges":
                return Builtin(o.edges, "edges")
            raise Refused(f"FloydCFG.{a}")
        if isinstance(o, dict) and a in ("items", "keys", "values", "get"):
            return Builtin(getattr(o, a), a)
        if isinstance(o, str) and a == "join":
            return Builtin(o.join, "join")
        if isinstance(o, str) and a == "startswith":
            return Builtin(o.startswith, "startswith")
        raise Refused(f"attribute {a} of {type(o).__name__}")

    # ---- expressions
    def ev(self, e, env):
        m = getattr(self, "e_" + type(e).__name__, None)
        if m is None:
            raise Refused(f"expression {type(e).__name__}")
        return m(e, env)

    def e_Constant(self, e, env):
        return e.value

    def e_Name(self, e, env):
        return self.lookup(e.id, env)

    def e_Attribute(self, e, env):
        return self.getattr(self.ev(e.value, env), e.attr)

    def e_JoinedStr(self, e, env):
        out = []
        for v in e.values:
            if isinstance(v, ast.Constant):
                out.append(v.value)
            elif isinstance(v, ast.FormattedValue) and v.conversion == -1 and v.format_spec is None:
                x = self.ev(v.value, env)
                if isinstance(x, (int, str)) and not isinstance(x, bool):
                    out.append(str(x))
                else:
                    raise Refused("f-string of a non-scalar")
            else:
                raise Refused("f-string form")
        return "".join(out)

    def seq(self, elts, env):
        out = []
        for x in elts:
            if isinstance(x, ast.Starred):
                out.extend(self.iterate(self.ev(x.value, env)))
            else:
                out.append(self.ev(x, env))
        return out

    def e_List(self, e, env):
        return self.seq(e.elts, env)

    def e_Tuple(self, e, env):
        return tuple(self.seq(e.elts, env))

    def e_Set(self, e, env):
        return set(self.seq(e.elts, env))

    def e_Dict(self, e, env):
        d = {}
        for k, v in zip(e.keys, e.values):
            if k is None:
                x = self.ev(v, env)
                if not isinstance(x, dict):
                    raise Refused("** of a non-dict")
                d.update(x)
            else:
                d[self.ev(k, env)] = self.ev(v, env)
        return d

    def comp(self, gens, env, emit):
        def go(i, env):
            if i == len(gens):
                emit(env)
                return
            g = gens[i]
            if g.is_async:
                raise Refused("async comprehension")
            for x in self.iterate(self.ev(g.iter, env)):
                loc = {}
                self.assign(g.target, x, [loc] + env)
                env2 = [loc] + env
                if all(self.truth(self.ev(c, env2)) for c in g.ifs):
                    go(i + 1, env2)
        go(0, env)

    def e_ListComp(self, e, env):
        out = []
        self.comp(e.generators, env, lambda en: out.append(self.ev(e.elt, en)))
        return out

    e_GeneratorExp = e_ListComp

    def e_SetComp(self, e, env):
        return set(self.e_ListComp(e, env))

    def e_DictComp(self, e, env):
        out = {}
        self.comp(e.generators, env, lambda en: out.__setitem__(self.ev(e.key, en), self.ev(e.value, en)))
        return out

    def e_Lambda(self, e, env):
        a = e.args
        if a.vararg or a.kwarg or a.kwonlyargs or a.posonlyargs:
            raise Refused("lambda signature")
        defaults = [self.ev(d, env) for d in a.defaults]
        return PyFunction(e, [p.arg for p in a.args], defaults, e.body, env, True, "<lambda>")

    def e_Call(self, e, env):
        f = self.ev(e.func, env)
        args = self.seq(e.args, env)
        kw = {k.arg: self.ev(k.value, env) for k in e.keywords}
        if any(k is None for k in kw):
            raise Refused("** arguments")
        return self.call(f, args, kw)

    def e_Subscript(self, e, env):
        o = self.ev(e.value, env)
        if isinstance(e.slice, ast.Slice):
            s = e.slice
            lo = self.ev(s.lower, env) if s.lower else None
            hi = self.ev(s.upper, env) if s.upper else None
            if s.step or not isinstance(o, (list, tuple)):
                raise Refused("slice")
            return o[lo:hi]
        k = self.ev(e.slice, env)
        if isinstance(o, T):
            return app("select", o, k)
        if isinstance(o, State):
            return o.locals[k]
        if isinstance(o, (list, tuple, dict, Compound)):
            try:
                return o[k]
            except (KeyError, IndexError, TypeError):
                raise Refused(f"subscript {k!r}")
        raise Refused(f"subscript of {type(o).__name__}")

    def binop(self, op, a, b):
        sym = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}.get(type(op))
        if isinstance(a, T) or isinstance(b, T):
            if sym is None:
                raise Refused(f"symbolic {type(op).__name__}")
            if isinstance(a, bool) or isinstance(b, bool):
                raise Refused("arithmetic on a Boolean")
            return app(sym, a, b)
        if sym == "+":
            return a + b
        if sym == "-":
            return a - b
        if sym == "*":
            return a * b
        raise Refused(f"operator {type(op).__name__}")

    def e_BinOp(self, e, env):
        return self.binop(e.op, self.ev(e.left, env), self.ev(e.right, env))

    def e_UnaryOp(self, e, env):
        x = self.ev(e.operand, env)
        if isinstance(e.op, ast.USub):
            return app("neg", x) if isinstance(x, T) else -x
        if isinstance(e.op, ast.Not):
            return not self.truth(x)
        raise Refused("unary operator")

    def e_BoolOp(self, e, env):
        if isinstance(e.op, ast.And):
            for v in e.values:
                x = self.ev(v, env)
                if not self.truth(x):
                    return x
            return x
        for v in e.values:
            x = self.ev(v, env)
            if self.truth(x):
                return x
        return x

    def e_IfExp(self, e, env):
        return self.ev(e.body if self.truth(self.ev(e.test, env)) else e.orelse, env)

    def e_Compare(self, e, env):
        left = self.ev(e.left, env)
        res = []
        for op, rhs in zip(e.ops, e.comparators):
            right = self.ev(rhs, env)
            res.append(self.cmp(op, left, right))
            left = right
        if all(not isinstance(r, T) for r in res):
            return all(res)
        return mk_and(*res)

    def cmp(self, op, a, b):
        if isinstance(op, (ast.In, ast.NotIn)):
            r = a in self.iterate(b)
            return r if isinstance(op, ast.In) else not r
        if isinstance(op, (ast.Is, ast.IsNot)):
            r = a is b
            return r if isinstance(op, ast.Is) else not r
        sym = {ast.Eq: "=", ast.NotEq: "!=", ast.Lt: "<", ast.LtE: "<=", ast.Gt: ">", ast.GtE: ">="}[type(op)]
        if isinstance(a, T) or isinstance(b, T):
            if sym == "!=":
                return app("not", app("=", a, b))
            return app(sym, a, b)
        if isinstance(a, (State, FloydCFG)) or isinstance(b, (State, FloydCFG)):
            raise Refused("comparison of states")
        return {"=": a == b, "!=": a != b, "<": a < b, "<=": a <= b, ">": a > b, ">=": a >= b}[sym]

    # a string of Z3 Python syntax, as HyHorn's State.eval evaluates it
    def eval_string(self, s, ctx):
        try:
            tree = ast.parse(s.strip(), mode="eval")
        except SyntaxError:
            raise Refused(f"cannot parse {s!r}")
        return self.ev(tree.body, [ctx])


# ------------------------------------------------------------------------------------ the specification

class Copy:
    def __init__(self, name, sig, cfg, extra_fn):
        self.name, self.sig, self.cfg, self.extra_fn = name, sig, cfg, extra_fn
        self.index = {v: j for j, v in enumerate(cfg.V)}
        self.stutter = {}  # node -> condition under which no edge is enabled (None: never)

    def pc(self, v):
        return lit(self.index[v])


class Spec:
    pass


def build_spec(interp, inst):
    obs_spec = interp.getattr(inst, "observe")
    if len(obs_spec) != 1:
        raise Refused(f"{len(obs_spec)} observation clauses")
    obs_spec = obs_spec[0]
    cfgs = interp.getattr(inst, "cfgs")
    k = len(cfgs)
    # HyHorn reads copy i's observation point from entry i and the property from the last entry, so an
    # observation tuple longer than k + 1 has entries no copy reads (p1_simple: three points, two copies).
    if len(obs_spec) < k + 1:
        raise Refused(f"observation tuple of length {len(obs_spec)} for {k} copies")
    unread = len(obs_spec) - (k + 1)
    qs = interp.getattr(inst, "qs") or "A" * k
    if qs not in ("AA", "AAA", "AE", "AAE", "AEi", "AAEi") or len(qs.rstrip("i")) != k:
        raise Refused(f"quantifier structure {qs!r} over {k} copies")
    var_decls = interp.getattr(inst, "var_decls")
    sig = Signature({"pc": INT, **{v: parse_type(t) for v, t in var_decls.items()}})
    nondets = interp.getattr(inst, "nondets")
    ga = interp.getattr(inst, "global_assumptions")
    if ga is not None and "E" in qs:
        raise Refused("global assumptions in a forall-exists property")
    if nondets is not None:
        if "E" in qs or len(nondets) != k:
            raise Refused("nondets")
        nondets = [Signature(d) for d in nondets]
    spec = Spec()
    spec.k, spec.qs, spec.sig, spec.ga, spec.nondets = k, qs, sig, ga, nondets
    spec.copies = []
    for i, (cfg, nm) in enumerate(zip(cfgs, "abc")):
        if not isinstance(cfg, FloydCFG):
            raise Refused("a copy that is not a control-flow graph")
        spec.copies.append(Copy(nm, sig, cfg, None))
    spec.obs = []
    for i, c in enumerate(spec.copies):
        b = obs_spec[i]
        pts = b if isinstance(b, set) else {b}
        for p in pts:
            if p not in c.index:
                raise Refused(f"observation point {p!r} is not a node of copy {c.name}")
        spec.obs.append(sorted(pts, key=lambda p: c.index[p]))
    spec.pre_src, spec.phi_src = interp.getattr(inst, "precond"), obs_spec[-1]
    spec.unread = unread
    return spec


def tr_edges(interp, spec, i, s0, s1, extra):
    """The step formula of copy i as a list of (node, path condition, formula) per edge."""
    c = spec.copies[i]
    out = []
    for (u, v, l) in c.cfg.E:
        s = s0.clone()
        s.path = []
        s.mw = {}
        if "label" in l:
            if l["label"] not in c.cfg.tr:
                raise Refused(f"no transformer for label {l['label']!r}")
            r = interp.call(c.cfg.tr[l["label"]], [s] + list(extra), {})
            if not isinstance(r, State):
                raise Refused(f"transformer {l['label']!r} returned no state")
        else:
            r = s
        r = r.clone()
        r.locals["pc"] = c.pc(v)
        eqs = [app("=", s1.locals[x], r.locals[x]) for x in c.sig.decls]
        guard = mk_and(app("=", s0.locals["pc"], c.pc(u)), *r.path)
        out.append((u, r.path, mk_and(guard, *eqs)))
    return out


def copy_vars(st):
    return [st.locals[v] for v in st.sig.decls]


def eq_state(a, b):
    return mk_and(*[app("=", x, y) for x, y in zip(copy_vars(a), copy_vars(b))])


def labels_for(spec, i):
    """Extra arguments HyHorn passes to copy i's transformers: a Boolean label per copy in "AE"/"AAE" (one more
    nondeterministic choice of that copy); `nondets` values per copy; nothing in the "i" variants, whose integer
    label only selects a restriction."""
    if spec.qs in ("AE", "AAE"):
        return [var(Fresh.name(f"lab_{spec.copies[i].name}_"), BOOL)]
    return []


def step(interp, spec, i, s0, s1, extra=None):
    """Copy i's completed step relation from s0 to s1; free variables other than s0's and s1's are its
    nondeterministic choices."""
    if getattr(spec, "raw", False):
        return spec.copies[i].step(s0, s1)
    if extra is None:
        extra = labels_for(spec, i)
    es = tr_edges(interp, spec, i, s0, s1, extra)
    disj = [f for (_, _, f) in es]
    c = spec.copies[i]
    for node, cond in c.stutter.items():
        disj.append(mk_and(app("=", s0.locals["pc"], c.pc(node)), subst_state(cond, c, s0), eq_state(s0, s1)))
    return mk_or(*disj)


def subst_state(t, c, s):
    return subst(t, {f"{x}__en": s.locals[x] for x in c.sig.decls})


def check_totality(interp, spec, z3bin):
    """For every copy and node: is some edge always enabled?  Where not, record the stutter condition
    `not (exists choices. guard_1) /\\ ... ` (quantifier-free when the guards mention no choice)."""
    if getattr(spec, "raw", False):
        for c in spec.copies:
            c.check_totality(z3bin)
        return
    for i, c in enumerate(spec.copies):
        s0 = State(interp, spec.sig, "__en")
        s1 = State(interp, spec.sig, "__en_next")
        extra = labels_for(spec, i)
        if spec.nondets:
            extra = list(State(interp, spec.nondets[i], f"__en_{c.name}").locals.values())
        es = tr_edges(interp, spec, i, s0, s1, extra)
        state_names = {v.name for v in copy_vars(s0)}
        for node in c.cfg.V:
            ens = []
            for (u, path, _) in es:
                if u != node:
                    continue
                g = mk_and(*path)
                choice = [v for n, v in free_vars(g).items() if n not in state_names]
                ens.append(T("exists", (g,), BOOL, val=choice) if choice else g)
            enabled = mk_or(*ens) if ens else lit(False)
            fv = free_vars(enabled)
            decls = "".join(f"(declare-const {v.name} {sort_str(v.sort)})\n" for v in fv.values())
            q = f"(set-option :timeout 20000)\n{decls}(assert (not {to_smt(enabled)}))\n(check-sat)\n"
            r = subprocess.run([z3bin, "-in"], input=q, capture_output=True, text=True, timeout=60)
            ans = r.stdout.strip().splitlines()[:1]
            if ans == ["unsat"]:
                continue
            if ans != ["sat"]:
                raise Refused(f"totality of copy {c.name} at node {node} undecided ({r.stdout.strip()[:40]})")
            c.stutter[node] = app("not", enabled)


def schedules(k):
    return [m for r in range(1, k + 1) for m in itertools.combinations(range(k), r)]


def mlabel(m, k):
    return "".join("1" if i in m else "0" for i in range(k))


def obs_at(spec, i, st):
    c = spec.copies[i]
    if getattr(spec, "raw", False):
        return c.obs(st)
    return mk_or(*[app("=", st.locals["pc"], c.pc(p)) for p in spec.obs[i]])


def valid(spec, s, m):
    obs = [obs_at(spec, i, s[i]) for i in range(spec.k)]
    none_in_m = mk_and(*[app("not", obs[i]) for i in m])
    if len(m) < spec.k:
        return none_in_m
    return mk_or(none_in_m, mk_and(*obs))


class Pred:
    def __init__(self, name, sorts):
        self.name, self.sorts = name, sorts

    def __call__(self, *args):
        if len(args) != len(self.sorts):
            raise Refused("arity")
        return T(self.name, args, BOOL)


def emit(interp, spec, name, group, table, z3bin):
    check_totality(interp, spec, z3bin)
    k = spec.k
    s0 = Compound(State(interp, spec.sig, f"_{c.name}") for c in spec.copies)
    vs0 = [v for st in s0 for v in copy_vars(st)]
    sorts = [v.sort for v in vs0]
    Inv = Pred("Inv", sorts)
    ms = schedules(k)
    if getattr(spec, "raw", False):
        pre, phi = spec.pre(s0), app("not", spec.bad(s0))
        init = mk_and(*[c.init(st) for c, st in zip(spec.copies, s0)], pre)
    else:
        pre = lit(interp.eval_string(spec.pre_src, s0.context()) if isinstance(spec.pre_src, str) else spec.pre_src)
        phi = lit(interp.eval_string(spec.phi_src, s0.context()))
        if pre.sort != BOOL or phi.sort != BOOL:
            raise Refused("precondition or property is not Boolean")
        init = mk_and(*[app("=", st.locals["pc"], c.pc(c.cfg.start)) for c, st in zip(spec.copies, s0)], pre)
    bad = mk_and(*[obs_at(spec, i, s0[i]) for i in range(k)], app("not", phi))
    F = lit(False)
    clauses = []
    preds = [Inv]
    ex = spec.qs.rstrip("i").find("E")
    if ex < 0:
        A = {m: Pred("A_" + mlabel(m, k), sorts) for m in ms}
        preds += [A[m] for m in ms]
        s1 = Compound(State(interp, spec.sig, f"_{c.name}_next") for c in spec.copies)
        nd = None
        ga = []
        if spec.nondets:
            nd = [State(interp, spec.nondets[i], f"_{c.name}") for i, c in enumerate(spec.copies)]
            if spec.ga is not None:
                ga = interp.call(spec.ga, [s0, Compound(nd)], {})
                ga = [lit(x) for x in ga]
        elif spec.ga is not None:
            raise Refused("global assumptions without nondets")
        clauses.append((init, Inv(*vs0), []))
        clauses.append((mk_and(Inv(*vs0), bad), F, []))
        for m in ms:
            clauses.append((mk_and(Inv(*vs0), A[m](*vs0), app("not", valid(spec, s0, m))), F, []))
        for m in ms:
            parts = []
            for i in range(k):
                if i in m:
                    extra = list(nd[i].locals.values()) if nd else None
                    parts.append(step(interp, spec, i, s0[i], s1[i], extra))
                else:
                    parts.append(eq_state(s0[i], s1[i]))
            vs1 = [v for st in s1 for v in copy_vars(st)]
            clauses.append((mk_and(Inv(*vs0), A[m](*vs0), *parts, *ga), Inv(*vs1), []))
        clauses.append((Inv(*vs0), mk_or(*[A[m](*vs0) for m in ms]), []))
        enc = "k-safety, the paper's Fig. 4a"
    else:
        if ex != k - 1:
            raise Refused("the existential copy is not the last one")
        fa = list(range(k - 1))
        cand = Compound(State(interp, spec.sig, f"_{c.name}_next") for c in spec.copies)
        cvars = [v for i in fa for v in copy_vars(cand[i])]
        asorts = sorts + [v.sort for v in cvars]
        A = {m: Pred("A_" + mlabel(m, k), asorts) for m in ms}
        preds += [A[m] for m in ms]
        moves = [step(interp, spec, i, s0[i], cand[i]) for i in fa]
        base = mk_and(Inv(*vs0), *moves)
        clauses.append((init, Inv(*vs0), []))
        clauses.append((mk_and(Inv(*vs0), bad), F, []))
        clauses.append((base, mk_or(*[A[m](*vs0, *cvars) for m in ms]), []))
        e = k - 1
        for m in ms:
            clauses.append((mk_and(base, A[m](*vs0, *cvars), app("not", valid(spec, s0, m))), F, []))
        for m in ms:
            post = []
            for i in fa:
                post += copy_vars(cand[i]) if i in m else copy_vars(s0[i])
            body = mk_and(base, A[m](*vs0, *cvars))
            if e in m:
                te = step(interp, spec, e, s0[e], cand[e])
                keep = {v.name for v in vs0}
                evs = [v for n, v in free_vars(te).items() if n not in keep]
                evs += [v for v in copy_vars(cand[e]) if v.name not in {x.name for x in evs}]
                post += copy_vars(cand[e])
                clauses.append((body, mk_and(te, Inv(*post)), evs))
            else:
                post += copy_vars(s0[e])
                clauses.append((body, Inv(*post), []))
        enc = "forall-exists game (the paper's Fig. 6a with every choice explicit)"
    stut = [f"{c.name}:{','.join(str(n) for n in c.stutter)}" for c in spec.copies if c.stutter]
    if getattr(spec, "raw", False):
        stut = [f"{c.name}:any" for c in spec.copies if c.stutter_cond is not None]
    hdr = [
        f"; HyHorn benchmark {name} ({group}, {table}); converted by script/hyhorn_to_pcsp.py",
        "; source: Itzhaky, Shoham, Vizel, ESOP 2024, artifact Zenodo 10449234 (CC-BY-4.0)",
        f"; quantifier prefix {spec.qs}, {k} copies; encoding: {enc}",
        "; nodes where no edge is always enabled (completed by a stutter step): " + (" ".join(stut) or "none"),
    ] + ([f"; the observation tuple has {spec.unread} entries no copy reads (HyHorn ignores them too)"]
         if getattr(spec, "unread", 0) else [])
    info = f"copies={k} qs={spec.qs} schedules={len(ms)} stutter={' '.join(stut) or '-'}"
    return render(preds, clauses, hdr), info


def render(preds, clauses, hdr):
    out = hdr + ["(set-logic HORN)"]
    for p in preds:
        out.append(f"(declare-fun {p.name} ({' '.join(sort_str(s) for s in p.sorts)}) Bool)")
    for body, head, evs in clauses:
        h = T("exists", (head,), BOOL, val=evs) if evs else head
        cl = T("=>", (body, h), BOOL)
        fv = list(free_vars(cl).values())
        s = to_smt(cl)
        if fv:
            s = f"(forall ({' '.join(f'({v.name} {sort_str(v.sort)})' for v in fv)}) {s})"
        out.append(f"(assert {s})")
    out.append("(check-sat)")
    return "\n".join(out) + "\n"


# ------------------------------------------- the Pdsc comparators, from script/hyhorn_pdsc_dump.py's JSON

class Names:
    """SMT-LIB names of the dump (Pdsc's carry `@`, `%`, `.`) mapped injectively to plain identifiers."""

    def __init__(self):
        self.m, self.used = {}, set()

    def __call__(self, n):
        if n not in self.m:
            b = SAFE.sub("_", n.replace("'", "_p")) or "v"
            if b[0].isdigit():
                b = "v_" + b
            c, j = b, 0
            while c in self.used:
                j += 1
                c = f"{b}_{j}"
            self.used.add(c)
            self.m[n] = c
        return self.m[n]


SAFE = re.compile(r"[^A-Za-z0-9_]")


def sexp_tokens(s):
    toks, i, n = [], 0, len(s)
    while i < n:
        ch = s[i]
        if ch.isspace():
            i += 1
        elif ch in "()":
            toks.append(ch)
            i += 1
        elif ch == "|":
            j = s.index("|", i + 1)
            toks.append(("sym", s[i + 1:j]))
            i = j + 1
        elif ch == ";":
            while i < n and s[i] != "\n":
                i += 1
        else:
            j = i
            while j < n and not s[j].isspace() and s[j] not in "()":
                j += 1
            toks.append(("sym", s[i:j]))
            i = j
    return toks


def sexp_parse(s):
    toks = sexp_tokens(s)
    pos = 0

    def go():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t == "(":
            out = []
            while toks[pos] != ")":
                out.append(go())
            pos += 1
            return out
        if t == ")":
            raise Refused("unbalanced s-expression")
        return t[1]
    e = go()
    if pos != len(toks):
        raise Refused("trailing s-expression text")
    return e


def sort_of_sexp(e):
    if e in (INT, BOOL):
        return e
    if isinstance(e, list) and len(e) == 3 and e[0] == "Array":
        return ("Array", sort_of_sexp(e[1]), sort_of_sexp(e[2]))
    raise Refused(f"sort {e!r}")


OPS = {"and": "and", "or": "or", "not": "not", "=>": "=>", "ite": "ite", "*": "*", "<": "<", "<=": "<=",
       ">": ">", ">=": ">=", "select": "select", "store": "store", "div": "div", "mod": "mod"}


def term_of_sexp(e, consts, names, env=None):
    env = env or {}
    if isinstance(e, str):
        if e in env:
            return env[e]
        if e == "true" or e == "false":
            return lit(e == "true")
        if e in ("and", "or"):  # Z3 prints an empty conjunction or disjunction as the bare operator
            return lit(e == "and")
        if re.fullmatch(r"[0-9]+", e):
            return lit(int(e))
        if e in consts:
            return var(names(e), consts[e])
        raise Refused(f"unknown symbol {e}")
    if not e:
        raise Refused("empty application")
    h = e[0]
    if h == "let":
        env2 = dict(env)
        for b in e[1]:
            env2[b[0]] = term_of_sexp(b[1], consts, names, env)
        return term_of_sexp(e[2], consts, names, env2)
    if not isinstance(h, str):
        raise Refused(f"application head {h!r}")
    args = [term_of_sexp(x, consts, names, env) for x in e[1:]]
    if h == "+":
        return T("+", args, INT) if len(args) > 1 and all(a.sort == INT for a in args) else app("+", *args)
    if h == "-":
        return app("neg", args[0]) if len(args) == 1 else app("-", *args)
    if h == "=":
        return mk_and(*[app("=", a, b) for a, b in zip(args, args[1:])])
    if h == "xor":
        if any(a.sort != BOOL for a in args):
            raise Refused("xor of a non-Boolean")
        out = args[0]
        for b in args[1:]:
            out = app("not", app("=", out, b))
        return out
    if h == "distinct":
        return mk_and(*[app("not", app("=", a, b)) for a, b in itertools.combinations(args, 2)])
    if h == "*" and len(args) > 2:
        return T("*", args, INT)
    if h in OPS:
        return app(OPS[h], *args)
    raise Refused(f"operator {h}")


class RawCopy:
    """A copy given by formulas over `<v>__c<j>` (current) and `<v>__c<j>n` (next)."""

    def __init__(self, j, d, consts, names):
        self.j, self.name = j, d["name"]
        self.base = [(v, SAFE.sub("_", v), sort_of_sexp(sexp_parse(srt) if srt.startswith("(") else srt))
                     for v, srt in d["vars"]]
        if len({b for _, b, _ in self.base}) != len(self.base):
            raise Refused("two state variables with the same plain name")
        self.sig = Signature({b: s for _, b, s in self.base})
        self.names = names
        self.tr_t = term_of_sexp(sexp_parse(d["tr"]), consts, names)
        self.init_t = term_of_sexp(sexp_parse(d["init"]), consts, names)
        self.obs_t = term_of_sexp(sexp_parse(d["obs"]), consts, names)
        self.cur = {names(f"{v}__c{j}") for v, _, _ in self.base}
        self.nxt = {names(f"{v}__c{j}n") for v, _, _ in self.base}
        self.stutter_cond = None
        self.stutter = {}

    def cmap(self, s):
        return {self.names(f"{v}__c{self.j}"): s.locals[b] for v, b, _ in self.base}

    def nmap(self, s):
        return {self.names(f"{v}__c{self.j}n"): s.locals[b] for v, b, _ in self.base}

    def init(self, s):
        return subst(self.init_t, self.cmap(s))

    def obs(self, s):
        return subst(self.obs_t, self.cmap(s))

    def choices(self):
        return [v for n, v in free_vars(self.tr_t).items() if n not in self.cur and n not in self.nxt]

    def step(self, s0, s1):
        m = {**self.cmap(s0), **self.nmap(s1)}
        for v in self.choices():  # fresh per use, so two uses in one clause do not share a choice
            m[v.name] = var(Fresh.name(v.name + "_ch"), v.sort)
        t = subst(self.tr_t, m)
        if self.stutter_cond is not None:
            t = mk_or(t, mk_and(subst(self.stutter_cond, self.cmap(s0)), eq_state(s0, s1)))
        return t

    def check_totality(self, z3bin):
        bound = [v for n, v in free_vars(self.tr_t).items() if n not in self.cur]
        enabled = T("exists", (self.tr_t,), BOOL, val=bound) if bound else self.tr_t
        fv = free_vars(enabled)
        decls = "".join(f"(declare-const {v.name} {sort_str(v.sort)})\n" for v in fv.values())
        q = f"(set-option :timeout 20000)\n{decls}(assert (not {to_smt(enabled)}))\n(check-sat)\n"
        r = subprocess.run([z3bin, "-in"], input=q, capture_output=True, text=True, timeout=60)
        ans = r.stdout.strip().splitlines()[:1]
        if ans == ["unsat"]:
            return
        if ans != ["sat"]:
            raise Refused(f"totality of copy {self.name} undecided ({r.stdout.strip()[:40]})")
        self.stutter_cond = app("not", enabled)


def raw_spec(d, names):
    consts = {}
    for n, srt in d["consts"].items():
        consts[n] = sort_of_sexp(sexp_parse(srt) if srt.startswith("(") else srt)
    copies = [RawCopy(j, c, consts, names) for j, c in enumerate(d["copies"])]
    if not copies or any(c.sig.decls != copies[0].sig.decls for c in copies):
        raise Refused("copies with different state variables")
    spec = Spec()
    spec.raw = True
    spec.k = len(copies)
    spec.qs = "A" * spec.k
    spec.sig = copies[0].sig
    spec.copies = copies
    spec.nondets, spec.ga = None, None
    pre_t = term_of_sexp(sexp_parse(d["pre"]), consts, names)
    bad_t = term_of_sexp(sexp_parse(d["bad"]), consts, names)

    def allmap(s):
        m = {}
        for c, st in zip(copies, s):
            m.update(c.cmap(st))
        return m
    spec.pre = lambda s: subst(pre_t, allmap(s))
    spec.bad = lambda s: subst(bad_t, allmap(s))
    return spec


# ------------------------------------------------------------------------------------------ the suite

def suite(interp):
    """What the paper's Table 1 ran (the artifact's benchmarks/zee_paper.py: hypa.K_SAFETY and
    more_test_cases.K_SAFETY, each followed by its `simplified()` variant, then hypa.BEYOND), plus
    more_test_cases.BEYOND.  hypa.BEYOND has 16 entries; Table 1 shows 15 (not counter_negate)."""
    hypa = interp.load("hypa")
    more = interp.load("more_test_cases")
    out = []
    for cls in hypa.g["K_SAFETY"] + more.g["K_SAFETY"]:
        out.append(("ksafety", cls.name, cls, False, "table1a"))
        if cls.lookup("simplified")[0]:
            out.append(("ksafety", cls.name + "_simpl", cls, True, "table1a"))
    for cls in hypa.g["BEYOND"]:
        out.append(("forall_exists", cls.name, cls, False,
                    "extra" if cls.name == "counter_negate" else "table1b"))
    for cls in more.g["BEYOND"]:
        out.append(("forall_exists", cls.name, cls, False, "extra"))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hyhorn", required=True, help="the artifact's /hyhorn directory")
    ap.add_argument("--out", help="output directory (one subdirectory per group)")
    ap.add_argument("--z3", default="z3", help="the z3 binary, for the totality checks")
    ap.add_argument("--only", nargs="*", help="instance names to convert")
    ap.add_argument("--list", action="store_true", help="list the suite and exit")
    ap.add_argument("--pdsc-json", help="also convert the comparators from script/hyhorn_pdsc_dump.py's output")
    a = ap.parse_args()
    interp = Interp(os.path.abspath(a.hyhorn))
    items = suite(interp)
    if a.only:
        items = [it for it in items if it[1] in a.only]
    if a.list:
        for g, n, _, _, t in items:
            print(f"{g}\t{n}\t{t}")
        return 0
    if not a.out:
        print("--out is required", file=sys.stderr)
        return 2
    rows, rc = [], 0
    for group, name, cls, simpl, table in items:
        try:
            inst = Instance(cls)
            if simpl:
                inst = interp.call(interp.getattr(inst, "simplified"), [], {})
                if not isinstance(inst, Instance):
                    raise Refused("simplified() returned no instance")
            spec = build_spec(interp, inst)
            text, info = emit(interp, spec, name, group, table, a.z3)
            d = os.path.join(a.out, group)
            os.makedirs(d, exist_ok=True)
            with open(os.path.join(d, name + ".smt2"), "w") as f:
                f.write(text)
            rows.append((group, name, table, "written", info))
            print(f"written  {group}/{name}.smt2  {info}", file=sys.stderr)
        except Refused as e:
            rows.append((group, name, table, "refused", str(e)))
            print(f"refused  {group}/{name}: {e}", file=sys.stderr)
        except Exception:
            rc = 1
            rows.append((group, name, table, "error", traceback.format_exc().strip().splitlines()[-1]))
            print(f"ERROR    {group}/{name}", file=sys.stderr)
            traceback.print_exc()
    if a.pdsc_json:
        import json
        with open(a.pdsc_json) as f:
            dumps = json.load(f)
        for d in dumps:
            name, group = d["name"], "comparators"
            if a.only and name not in a.only:
                continue
            try:
                if d.get("status") != "dumped":
                    raise Refused(f"the front end failed: {d.get('error')}")
                spec = raw_spec(d, Names())
                text, info = emit(interp, spec, name, group, "annexA", a.z3)
                dd = os.path.join(a.out, group)
                os.makedirs(dd, exist_ok=True)
                with open(os.path.join(dd, name + ".smt2"), "w") as f:
                    f.write(text)
                rows.append((group, name, "annexA", "written", info))
                print(f"written  {group}/{name}.smt2  {info}", file=sys.stderr)
            except Refused as e:
                rows.append((group, name, "annexA", "refused", str(e)))
                print(f"refused  {group}/{name}: {e}", file=sys.stderr)
            except Exception:
                rc = 1
                rows.append((group, name, "annexA", "error", traceback.format_exc().strip().splitlines()[-1]))
                print(f"ERROR    {group}/{name}", file=sys.stderr)
                traceback.print_exc()
    os.makedirs(a.out, exist_ok=True)
    with open(os.path.join(a.out, "conversion_dsl.tsv"), "w") as f:
        f.write("group\tname\ttable\tstatus\tinfo\n")
        for r in rows:
            f.write("\t".join(r) + "\n")
    w = sum(1 for r in rows if r[3] == "written")
    print(f"DONE {w} written, {sum(1 for r in rows if r[3] == 'refused')} refused, "
          f"{sum(1 for r in rows if r[3] == 'error')} errors", file=sys.stderr)
    return rc


if __name__ == "__main__":
    sys.exit(main())
