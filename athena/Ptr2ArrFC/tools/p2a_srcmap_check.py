#!/usr/bin/env python3
"""Check the source map of a ptr2arr record against the files it describes.

usage: p2a_srcmap_check.py [--expect FILE] IN.c OUT.c OUT.p2a.json

Every entry of source_map.statements is checked:

  output  the position is inside OUT.c, on the first character of a token
          that starts a statement: the text before it on its line is blank
          or ends with "{", "}", ";", ")", ":", "*/" (an annotation) or
          "else"; a loop-head is
          printed "while", a branch "if" or "while", a target and a call as
          a call ("name(" or "x = name(" ... ), and the line above a
          statement of an output written with --line-directives is the
          #line line that names its input line (or the output's next line);
  input   when not null, the position is inside IN.c on a character that is
          not blank and starts a token; a loop-head points to "for" or
          "while", a branch to "if", "while", "for" or "do", an unreach-call
          target to "reach_error"; any target to the first character of a
          statement or full expression (the text before it on its line is
          blank or ends with one of "{", "}", ";", ")", ":", "(", ",", "=",
          "else", "return", "do", or a for header's "("). A statement inside
          a macro's expansion is placed at the macro's name, which must be a
          macro the input defines.

The order of the entries must be the order of their output positions.

--expect FILE: lines "ROLE PROPERTY LINE COLUMN [COUNT]" (PROPERTY "-" when
none, LINE and COLUMN "null" for no input position; COUNT, default 1, the
number of entries expected with that role, property and input position)
that the map must contain, and "no ROLE PROPERTY" for a role and property
it must not contain; "#" starts a comment.

Prints one line per problem and ends with "OK n" (n entries checked) or
"FAIL n"; exits 1 on a problem.
"""
import json
import re
import sys

IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9]*")


def lines_of(path):
    with open(path, "rb") as f:
        return [l.rstrip(b"\r\n").decode("latin-1") for l in f.read().split(b"\n")]


def at(lines, line, col):
    if line < 1 or line > len(lines):
        return None
    text = lines[line - 1]
    if col < 1 or col > len(text):
        return None
    return text, col - 1


def token_start(text, i):
    if text[i].isspace():
        return False
    if i > 0 and (text[i - 1].isalnum() or text[i - 1] == "_") and (text[i].isalnum() or text[i] == "_"):
        return False
    return True


OUT_BEFORE = re.compile(r"(^|[{};):]|\*/|\belse)\s*$")
IN_BEFORE = re.compile(r"(^|[{};):(,=?]|\belse|\breturn|\bdo|\bcase\s+[^:]*:|\bdefault\s*:)\s*$")
CALL = re.compile(r"(?:[^;]*?[^=!<>]=(?!=)\s*)?(?:\([^()]*\)\s*)?[A-Za-z_]\w*\s*\(")


def check(inp, out, rec, expect):
    problems = []
    ilines, olines = lines_of(inp), lines_of(out)
    macros = set(re.findall(r"^\s*#\s*define\s+([A-Za-z_]\w*)", "\n".join(ilines), re.M))
    record = json.load(open(rec))
    sm = record.get("source_map")
    if sm is None:
        return ["no source_map"], 0
    if sm.get("input_file") != record["input"]["path"]:
        problems.append("input_file %r differs from input.path %r" % (sm.get("input_file"), record["input"]["path"]))
    entries = sm["statements"]
    directives = any(l.startswith("#line ") for l in olines)
    prev = (0, 0)
    for e in entries:
        ol, oc, role = e["output_line"], e["output_column"], e["role"]
        where = "output %d:%d (%s)" % (ol, oc, role)
        if (ol, oc) < prev:
            problems.append("%s: out of order" % where)
        prev = (ol, oc)
        a = at(olines, ol, oc)
        if a is None:
            problems.append("%s: outside the output" % where)
            continue
        text, i = a
        rest = text[i:]
        if not token_start(text, i) or not OUT_BEFORE.search(text[:i]):
            problems.append("%s: not the start of a statement: %r" % (where, text))
        if role == "loop-head" and not rest.startswith("while"):
            problems.append("%s: a loop-head printed as %r" % (where, rest[:20]))
        if role == "branch" and not (rest.startswith("if") or rest.startswith("while")):
            problems.append("%s: a branch printed as %r" % (where, rest[:20]))
        if role in ("target", "call") and not CALL.match(rest):
            problems.append("%s: not a call: %r" % (where, rest[:40]))
        if (role == "branch") != (e["cond_negated"] is not None):
            problems.append("%s: cond_negated %r" % (where, e["cond_negated"]))
        if (role == "target") != (e["property"] is not None):
            problems.append("%s: property %r" % (where, e["property"]))
        if role == "branch" and e["cond_negated"] is not None and e["input"]:
            # an input if or while: the printed condition starts with a
            # negation exactly when the input's does or cond_negated says so
            src = at(ilines, e["input"]["line"], e["input"]["column"])
            m = src and re.match(r"(if|while)\s*\(\s*(!?)", src[0][src[1]:])
            if m:
                printed = re.match(r"(if|while) \(! ", rest) is not None
                if printed != ((m.group(2) == "!") != e["cond_negated"]):
                    problems.append("%s: cond_negated %r, printed %r, input %r"
                                    % (where, e["cond_negated"], rest[:30], src[0][src[1]:][:30]))
        if directives and not text[:i].strip():
            above = olines[ol - 2] if ol >= 2 else ""
            inp_ = e["input"]
            want = ('#line %d "%s"' % (inp_["line"], sm["input_file"]) if inp_
                    else '#line %d "' % ol)
            if not above.startswith(want):
                problems.append("%s: line above is %r, expected %r" % (where, above, want))
        inp_ = e["input"]
        if inp_ is None:
            continue
        il, ic = inp_["line"], inp_["column"]
        iwhere = "%s -> input %d:%d" % (where, il, ic)
        b = at(ilines, il, ic)
        if b is None:
            problems.append("%s: outside the input" % iwhere)
            continue
        itext, j = b
        irest = itext[j:]
        if not token_start(itext, j):
            problems.append("%s: not the start of a token: %r" % (iwhere, itext))
        m = IDENT.match(irest)
        in_macro = m is not None and m.group(0) in macros
        if role == "loop-head" and not in_macro and not re.match(r"(for|while)\b", irest):
            problems.append("%s: a loop-head at %r" % (iwhere, irest[:20]))
        if role == "branch" and not in_macro and not re.match(r"(if|while|for|do)\b", irest):
            problems.append("%s: a branch at %r" % (iwhere, irest[:20]))
        if role == "target" and not in_macro:
            if e["property"] == "unreach-call" and not irest.startswith("reach_error"):
                problems.append("%s: an unreach-call target at %r" % (iwhere, irest[:20]))
            if not IN_BEFORE.search(itext[:j]) and not re.search(r"\bfor\s*\([^;]*;[^;]*;?\s*$", itext[:j]):
                problems.append("%s: not the start of a statement or full expression: %r" % (iwhere, itext))
    for line in expect:
        f = line.split()
        if f[0] == "no":
            role, prop = f[1], (None if f[2] == "-" else f[2])
            n = sum(1 for e in entries if e["role"] == role and e["property"] == prop)
            if n:
                problems.append("expected no %s %s, found %d" % (role, f[2], n))
            continue
        role, prop = f[0], (None if f[1] == "-" else f[1])
        pos = None if f[2] == "null" else (int(f[2]), int(f[3]))
        count = int(f[4]) if len(f) > 4 else 1
        n = sum(1 for e in entries
                if e["role"] == role and e["property"] == prop
                and (None if e["input"] is None else (e["input"]["line"], e["input"]["column"])) == pos)
        if n != count:
            problems.append("expected %d %s %s at input %s, found %d" % (count, role, f[1], pos, n))
    return problems, len(entries)


def main():
    args = sys.argv[1:]
    expect = []
    if args and args[0] == "--expect":
        with open(args[1]) as f:
            expect = [l.split("#")[0].strip() for l in f]
            expect = [l for l in expect if l]
        args = args[2:]
    if len(args) != 3:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    problems, n = check(*args, expect)
    for p in problems:
        print(p)
    print("%s %d" % ("FAIL" if problems else "OK", n))
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
