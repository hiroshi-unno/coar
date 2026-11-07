#!/usr/bin/env python3
"""Join ranking-function counts with MuValPPM (SCC & AD) results; tabulate time by count.

  rankcount.py --prepare ROOT [--timeout T]   write ROOT/results/rankcount/<corpus>.csv and print
                                              one `<figure suffix> <seconds>` line per corpus
  rankcount.py --table ROOT [--timeout T] [--latex]
                                              print the distribution of solving times by the number
                                              of ranking functions, as text or as a LaTeX table

The counts are ROOT/results/rankcount/<corpus>.stats (rankcount.sh), one line per benchmark and side:
`<benchmark>\treduction-stats: side=S ... ranking_functions=N ranking_function_args=M ...`.  The results
are ROOT/results/<corpus>/muval_ppm_popl27.csv (runall.sh; muval_ppm_scc_ad.csv, its name before
2026-11-03, is read too).  A three-field timeout row records the run's time limit
as its time; results written by an older runner record none and are read at --timeout (default 300).

Each joined row is `name, verdict, time, primal ranking functions, dual ranking functions, primal
arguments, dual arguments`, with a count left empty when that side printed no line (no reduction within
the counting run's limit).  A side is counted where it could have answered: the primal (the ranking
functions of the least fixed points) over the valid instances and the timeouts, the dual over the
invalid instances and the timeouts.
"""

import argparse
import csv
from pathlib import Path
import sys

from summarize_results import PRIMARY, labelled_path, read_records, timeout_seconds, figure_limit, fill_blank_timeouts

CORPORA = (("term25its", "its", "ITS"), ("popl2023mod", "popl23", "POPL'23"))
ALIASES = {"yes": "valid", "no": "invalid", "maybe": "unknown"}
SIDES = (("primal", "valid", 3, 5), ("dual", "invalid", 4, 6))
COUNT_ROWS = ("0", "1", "2", "3", "4", ">=5")


def read_stats(path):
    stats = {}
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            if not line.strip():
                continue
            name, separator, rest = line.rstrip("\n").partition("\t")
            parts = rest.split()
            if not separator or not name.strip() or not parts or parts[0] != "reduction-stats:":
                raise ValueError(f"{path}:{line_number}: invalid reduction statistics")
            fields = dict(kv.split("=", 1) for kv in parts[1:] if "=" in kv)
            if fields.get("side") not in ("primal", "dual"):
                raise ValueError(f"{path}:{line_number}: invalid reduction side")
            for key in ("ranking_functions", "ranking_function_args"):
                value = fields.get(key, "")
                if not value.isascii() or not value.isdecimal():
                    raise ValueError(f"{path}:{line_number}: invalid {key} {value!r}")
                try:
                    int(value)
                except ValueError as error:
                    raise ValueError(f"{path}:{line_number}: invalid {key}: {error}") from None
            # The first reduction of each side is the one the solving run uses.
            stats.setdefault(name, {}).setdefault(fields["side"], fields)
    return stats


def prepare(root, corpus, default_timeout):
    """Write the joined CSV of CORPUS; return its rows and the time limit they record."""
    try:
        results = labelled_path(root / "results" / corpus, PRIMARY)
    except ValueError as error:
        raise SystemExit(str(error)) from None
    stats = read_stats(root / "results" / "rankcount" / f"{corpus}.stats")
    rows = []
    records = read_records(results, plotting=True)
    limit = figure_limit((records.values(),), default_timeout, str(results))
    for name, verdict, time in fill_blank_timeouts(records.values(), limit):
        by = stats.get(name, {})
        get = lambda side, key: by[side][key] if side in by else ""
        rows.append([name, verdict, time,
                     get("primal", "ranking_functions"), get("dual", "ranking_functions"),
                     get("primal", "ranking_function_args"), get("dual", "ranking_function_args")])
    return rows, float(limit)


def bucket(verdict, time, limit):
    if verdict == "timeout":
        return 4
    t = float(time)
    return 0 if t < 1 else 1 if t < 10 else 2


def distribution(rows, side, limit):
    """{count row: [instances, <1 s, 1-10 s, 10 s-limit, timeout]} and the instances with no count."""
    _, answer, column, _ = next(s for s in SIDES if s[0] == side)
    table, missing = {}, 0
    for row in rows:
        if row[1] not in (answer, "timeout"):
            continue
        if row[column] == "":
            missing += 1
            continue
        n = int(row[column])
        key = COUNT_ROWS[min(n, 5)]
        cells = table.setdefault(key, [0, 0, 0, 0, 0])
        cells[0] += 1
        cells[1 + {0: 0, 1: 1, 2: 2, 4: 3}[bucket(row[1], row[2], limit)]] += 1
    return {k: table[k] for k in COUNT_ROWS if k in table}, missing


def fmt_limit(limit):
    return f"{limit:g}"


def cell(k, n):
    return f"{k} ({round(100 * k / n)}%)" if n else str(k)


def text_table(blocks, limit, key="#RF"):
    head = ["", key, "#inst.", "<1 s", "1-10 s", f"10-{fmt_limit(limit)} s", "timeout"]
    lines = []
    for label, table, missing in blocks:
        body = [[k] + [str(c[0])] + [cell(x, c[0]) for x in c[1:]] for k, c in table.items()]
        if len(table) > 1:
            total = [sum(c[i] for c in table.values()) for i in range(5)]
            body.append(["total", str(total[0])] + [cell(x, total[0]) for x in total[1:]])
        for i, r in enumerate(body):
            lines.append([label if i == 0 else ""] + r)
        if missing:
            lines.append([label if not body else "", f"({missing} without a count)", "", "", "", "", ""])
        elif not body:
            lines.append([label, "(no eligible instances)", "0", "", "", "", ""])
        lines.append(None)
    widths = [max([len(head[i])] + [len(r[i]) for r in lines if r]) for i in range(len(head))]
    out = ["  ".join(h.ljust(w) if i < 2 else h.rjust(w) for i, (h, w) in enumerate(zip(head, widths)))]
    for r in lines[:-1]:
        if r is None:
            out.append("-" * len(out[0]))
        else:
            out.append("  ".join(c.ljust(w) if i < 2 else c.rjust(w)
                                 for i, (c, w) in enumerate(zip(r, widths))))
    return "\n".join(out)


RF_CAPTION = (r"MuValPPM (SCC \& AD): solving time by the number of ranking functions",
              r"in the reduced problem. The primal side is counted over the \emph{valid} instances",
              r"and the timeouts, the dual side over the \emph{invalid} instances and the timeouts;",
              r"percentages are of the row.")


def latex_table(blocks, limit, key=r"\#RF", caption=RF_CAPTION, label="tab:rf-time"):
    lim = fmt_limit(limit)
    pct = lambda k, n: f"{k} ({round(100 * k / n)}\\%)"
    out = [r"\begin{table}[t]", r"  \centering", "  \\caption{" + caption[0]]
    out += ["    " + line for line in caption[1:]]
    out[-1] += "}"
    out += [f"  \\label{{{label}}}", r"  \small", r"  \begin{tabular}{llrrrrr}", r"    \toprule",
            f"    & {key} & \\#inst. & $<$1\\,s & 1--10\\,s & 10--{lim}\\,s & timeout \\\\"]
    for label, table, missing in blocks:
        out.append(r"    \midrule")
        rows = [(k.replace(">=", r"$\geq$"), c) for k, c in table.items()]
        if len(table) > 1:
            rows.append(("total", [sum(c[i] for c in table.values()) for i in range(5)]))
        corpus, side = label.split()
        name = f"\\shortstack[l]{{{corpus}\\\\{side}}}"
        if not rows:
            message = f"{missing} without a count" if missing else "no eligible instances"
            out.append(f"    {name} & \\multicolumn{{6}}{{l}}{{{message}}}" + r" \\")
            continue
        out.append(f"    \\multirow{{{len(rows)}}}{{*}}{{{name}}}" if len(rows) > 1 else f"    {name}")
        for k, c in rows:
            out.append(f"    & {k} & {c[0]} & " + " & ".join(pct(x, c[0]) for x in c[1:]) + r" \\")
        if missing:
            out.append(f"    & \\multicolumn{{6}}{{l}}{{{missing} without a count}}" + r" \\")
    out += [r"    \bottomrule", r"  \end{tabular}", r"\end{table}"]
    return "\n".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", metavar="ROOT", type=Path)
    mode.add_argument("--table", metavar="ROOT", type=Path)
    parser.add_argument("--timeout", type=timeout_seconds, default=None, help="the limit of timeout rows that record none (default: recorded limit or 300)")
    parser.add_argument("--latex", action="store_true")
    args = parser.parse_args()
    root = args.prepare or args.table
    blocks, limits = [], set()
    prepared = []
    try:
        for corpus, suffix, label in CORPORA:
            rows, limit = prepare(root, corpus, args.timeout)
            prepared.append((corpus, suffix, label, rows, limit))
    except (OSError, ValueError, csv.Error) as error:
        parser.exit(1, f"error: {error}\n")
    for corpus, suffix, label, rows, limit in prepared:
        limits.add(limit)
        if args.prepare:
            with (root / "results" / "rankcount" / f"{corpus}.csv").open("w", newline="") as stream:
                csv.writer(stream).writerows(rows)
            print(suffix, fmt_limit(limit))
        else:
            for side, *_ in SIDES:
                table, missing = distribution(rows, side, limit)
                blocks.append((f"{label} {side}", table, missing))
    if args.table:
        if len(limits) > 1:
            print(f"note: the corpora were run with different limits {sorted(limits)}", file=sys.stderr)
            for _, suffix, label, _, limit in prepared:
                selected = [block for block in blocks if block[0].split()[0] == label]
                print(latex_table(selected, limit, label=f"tab:rf-time-{suffix}")
                      if args.latex else text_table(selected, limit))
        else:
            print((latex_table if args.latex else text_table)(blocks, max(limits)))


if __name__ == "__main__":
    main()
