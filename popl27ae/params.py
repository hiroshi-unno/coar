#!/usr/bin/env python3
"""Characterise the benchmarks by three parameters and relate each to MuValPPM's (SCC & AD) solving time.

  params.py --prepare ROOT [--timeout T]   write ROOT/results/params/<corpus>.csv and print one
                                           `<figure suffix> <seconds>` line per corpus
  params.py --table ROOT [--timeout T] [--latex]
                                           print the summary, the distributions and the time tables

The parameters are read from the `reduction-stats:` lines that rankcount.sh counts
(ROOT/results/rankcount/<corpus>.stats), one per side (primal, dual) of a benchmark, and joined with
ROOT/results/<corpus>/muval_ppm_popl27.csv (runall.sh), as rankcount.py joins them:

  AD    `alternation_depth`: the largest alternation depth of a predicate of the problem the reduction
        receives, each computed within its strongly connected component (1 when no fixed-point
        alternation is nested in a cycle; 0 when the preprocessing left no predicate); a predicate whose
        fixed-point kind is left open (`mu_or_nu`, which the ITS translation produces) adds no
        alternation
  SCC   `nontrivial_sccs`: the strongly connected components of that problem's call graph (an edge from
        P to Q when Q occurs in the body of P) that have a cycle -- two or more predicates, or one that
        calls itself; an acyclic single predicate is not counted (the line's `sccs` counts it)
  RF    the ranking functions of the reduced problems, primal and dual together (`ranking_functions`
        of both lines)

AD and SCC are read from the primal line (the dual line when the primal one is missing).  The dual
problem has the same call graph and swaps every least and greatest fixed point, which leaves the
alternation depth unchanged; the number of benchmarks whose two sides nevertheless differ is printed.
(The line's `alternation_depth_as_nu` reads a `mu_or_nu` predicate as a greatest fixed point instead,
the reading MuValPPM assigns priorities from; it is not used here.)  A benchmark contributes to a
parameter when its line carries the field.

For each corpus and parameter it prints the distribution of the benchmarks over the values (counts
per value or bucket, minimum, median, maximum), the table of solving times by value or bucket in the
format of rankcount.py's table (over the valid and invalid answers and the timeouts), and Spearman's
rank correlation between the parameter and the solving time, a timeout taken at the time limit
(solving time is censored at the limit, so only its order is used), over all those benchmarks and
over the answered ones only.  A compact table, corpus by parameter, gives the minimum, median and
maximum and both correlations.  --prepare writes one row per benchmark, `name, verdict, time, AD,
SCC, RF, sccs, predicates, AD of the dual side`, with a timeout's time at the limit, which the figures
results/fig/{ad,scc,rf}_vs_time_{popl23,its}.pdf draw.
"""

import argparse
import csv
from pathlib import Path
import statistics
import sys

from summarize_results import PRIMARY, labelled_path, read_records, timeout_seconds, figure_limit, fill_blank_timeouts
from rankcount import CORPORA, read_stats, fmt_limit, text_table, latex_table

# (key, heading, LaTeX heading, buckets: (label, low, high or None))
PARAMETERS = (
    ("ad", "AD", "AD", (("0", 0, 0), ("1", 1, 1), ("2", 2, 2), ("3", 3, 3), (">=4", 4, None))),
    ("scc", "#SCC", r"\#SCC", (("0", 0, 0), ("1", 1, 1), ("2", 2, 2), ("3", 3, 3), ("4-7", 4, 7),
                               (">=8", 8, None))),
    ("rf", "#RF", r"\#RF", (("0", 0, 0), ("1", 1, 1), ("2", 2, 2), ("3", 3, 3), ("4", 4, 4),
                            (">=5", 5, None))),
)
NAMES = {"ad": "alternation depth", "scc": "nontrivial SCCs", "rf": "ranking functions"}
ANSWERS = ("valid", "invalid")


def parameter_values(by_side):
    """{ad, scc, rf, sccs, predicates} of one benchmark's stats lines; a value is None when absent."""
    def field(key, sides=("primal", "dual")):
        for side in sides:
            value = by_side.get(side, {}).get(key, "")
            if value.isascii() and value.isdecimal():
                return int(value)
        return None
    rf = None
    if "primal" in by_side and "dual" in by_side:
        rf = int(by_side["primal"]["ranking_functions"]) + int(by_side["dual"]["ranking_functions"])
    return {"ad": field("alternation_depth"), "scc": field("nontrivial_sccs"), "rf": rf,
            "sccs": field("sccs"), "predicates": field("predicates"),
            "ad_dual": field("alternation_depth", ("dual",))}


def prepare(root, corpus, default_timeout):
    """The joined rows of CORPUS -- [name, verdict, time, values] -- and the time limit."""
    try:
        results = labelled_path(root / "results" / corpus, PRIMARY)
    except ValueError as error:
        raise SystemExit(str(error)) from None
    stats = read_stats(root / "results" / "rankcount" / f"{corpus}.stats")
    records = read_records(results, plotting=True)
    limit = figure_limit((records.values(),), default_timeout, str(results))
    rows = []
    for name, verdict, time in fill_blank_timeouts(records.values(), limit):
        rows.append([name, verdict, float(time), parameter_values(stats.get(name, {}))])
    return rows, float(limit)


def bucket_of(buckets, value):
    for label, low, high in buckets:
        if value >= low and (high is None or value <= high):
            return label
    return None


def ranks(xs):
    """Average ranks (1-based) of xs, ties sharing the mean of their positions."""
    order = sorted(range(len(xs)), key=lambda i: xs[i])
    r = [0.0] * len(xs)
    i = 0
    while i < len(order):
        j = i
        while j + 1 < len(order) and xs[order[j + 1]] == xs[order[i]]:
            j += 1
        for k in range(i, j + 1):
            r[order[k]] = (i + j) / 2 + 1
        i = j + 1
    return r


def spearman(pairs):
    """Spearman's rho of [(x, y)] (Pearson's correlation of the average ranks); None when undefined."""
    if len(pairs) < 3:
        return None
    rx, ry = ranks([x for x, _ in pairs]), ranks([y for _, y in pairs])
    mx, my = statistics.fmean(rx), statistics.fmean(ry)
    sxy = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    sxx = sum((a - mx) ** 2 for a in rx)
    syy = sum((b - my) ** 2 for b in ry)
    if sxx == 0 or syy == 0:
        return None
    return sxy / (sxx * syy) ** 0.5


def fmt_rho(rho):
    return "-" if rho is None else f"{rho:+.2f}"


def fmt_median(values):
    m = statistics.median(values)
    return str(int(m)) if m == int(m) else f"{m:g}"


def analyse(rows, limit, key, buckets):
    """The figures of one corpus and parameter."""
    timed = [r for r in rows if r[1] in ANSWERS or r[1] == "timeout"]
    have = [r for r in timed if r[3][key] is not None]
    values = [r[3][key] for r in have]
    counts = {label: 0 for label, _, _ in buckets}
    table = {}
    for r in have:
        label = bucket_of(buckets, r[3][key])
        counts[label] += 1
        cells = table.setdefault(label, [0, 0, 0, 0, 0])
        cells[0] += 1
        if r[1] == "timeout":
            cells[4] += 1
        else:
            cells[1 if r[2] < 1 else 2 if r[2] < 10 else 3] += 1
    all_pairs = [(r[3][key], limit if r[1] == "timeout" else r[2]) for r in have]
    answered = [(r[3][key], r[2]) for r in have if r[1] in ANSWERS]
    return {
        "n": len(have), "missing": len(timed) - len(have), "other": len(rows) - len(timed),
        "counts": counts,
        "min": min(values) if values else None, "median": fmt_median(values) if values else "-",
        "max": max(values) if values else None,
        "table": {label: table[label] for label, _, _ in buckets if label in table},
        "rho_all": spearman(all_pairs), "n_all": len(all_pairs),
        "rho_answered": spearman(answered), "n_answered": len(answered),
    }


def summary_text(results):
    head = ["corpus", "parameter", "min", "median", "max", "rho (all)", "n", "rho (answered)", "n"]
    body = [[label, NAMES[key], str(a["min"]), a["median"], str(a["max"]),
             fmt_rho(a["rho_all"]), str(a["n_all"]), fmt_rho(a["rho_answered"]), str(a["n_answered"])]
            for label, key, a in results]
    widths = [max(len(r[i]) for r in [head] + body) for i in range(len(head))]
    fmt = lambda r: "  ".join(c.ljust(w) if i < 2 else c.rjust(w) for i, (c, w) in enumerate(zip(r, widths)))
    return "\n".join([fmt(head), "-" * len(fmt(head))] + [fmt(r) for r in body])


def summary_latex(results, limit, corpus_limits=None):
    time_limits = f"the time limit ({fmt_limit(limit)}\\,s)"
    if corpus_limits and len({cap for _, cap in corpus_limits}) > 1:
        shown = "; ".join(f"{label}: {fmt_limit(cap)}\\,s" for label, cap in corpus_limits)
        time_limits = f"its corpus's time limit ({shown})"
    out = [r"\begin{table}[t]", r"  \centering",
           r"  \caption{The benchmarks by alternation depth (AD), number of nontrivial strongly connected",
           r"    components (\#SCC) and number of ranking functions of the reduced problems (\#RF), and",
           r"    Spearman's rank correlation $\rho$ of each with the solving time of MuValPPM (SCC \& AD),",
           f"    a timeout taken at {time_limits}, over all benchmarks and over",
           r"    the answered ones.}",
           r"  \label{tab:params}", r"  \small", r"  \begin{tabular}{llrrrrrrr}", r"    \toprule",
           r"    & & min & median & max & $\rho$ (all) & $n$ & $\rho$ (answered) & $n$ \\"]
    previous = None
    heading = {key: tex for key, _, tex, _ in PARAMETERS}
    for label, key, a in results:
        if label != previous:
            out.append(r"    \midrule")
        name = label if label != previous else ""
        previous = label
        out.append(f"    {name} & {heading[key]} & {a['min']} & {a['median']} & {a['max']} & "
                   f"${fmt_rho(a['rho_all'])}$ & {a['n_all']} & ${fmt_rho(a['rho_answered'])}$ & "
                   f"{a['n_answered']} \\\\")
    out += [r"    \bottomrule", r"  \end{tabular}", r"\end{table}"]
    return "\n".join(out).replace("$-$", "--")


def distribution_text(label, key, buckets, a):
    heading = next(h for k, h, _, _ in PARAMETERS if k == key)
    cells = "  ".join(f"{b}: {a['counts'][b]}" for b, _, _ in buckets)
    notes = []
    if a["missing"]:
        notes.append(f"{a['missing']} without a value")
    if a["other"]:
        notes.append(f"{a['other']} neither answered nor timed out")
    note = f" ({'; '.join(notes)})" if notes else ""
    return (f"{label} {heading}: n={a['n']}  min={a['min']}  median={a['median']}  max={a['max']}"
            f"  |  {cells}{note}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", metavar="ROOT", type=Path)
    mode.add_argument("--table", metavar="ROOT", type=Path)
    parser.add_argument("--timeout", type=timeout_seconds, default=None, help="the limit of timeout rows that record none (default: recorded limit or 300)")
    parser.add_argument("--latex", action="store_true")
    args = parser.parse_args()
    root = args.prepare or args.table
    prepared = []
    try:
        # the POPL'23 corpus first, as in Table 1
        for corpus, suffix, label in sorted(CORPORA, key=lambda c: c[0] != "popl2023mod"):
            rows, limit = prepare(root, corpus, args.timeout)
            prepared.append((corpus, suffix, label, rows, limit))
    except (OSError, ValueError, csv.Error) as error:
        parser.exit(1, f"error: {error}\n")
    if args.prepare:
        out = root / "results" / "params"
        out.mkdir(parents=True, exist_ok=True)
        for corpus, suffix, label, rows, limit in prepared:
            with (out / f"{corpus}.csv").open("w", newline="") as stream:
                writer = csv.writer(stream)
                for name, verdict, time, v in rows:
                    t = limit if verdict == "timeout" else time
                    writer.writerow([name, verdict, f"{t:g}"] + ["" if v[k] is None else v[k]
                                                                 for k in ("ad", "scc", "rf", "sccs", "predicates", "ad_dual")])
            print(suffix, fmt_limit(limit))
        return
    limits = {limit for *_, limit in prepared}
    if len(limits) > 1:
        print(f"note: the corpora were run with different limits {sorted(limits)}", file=sys.stderr)
    summary, blocks, distributions = [], {key: [] for key, *_ in PARAMETERS}, []
    for corpus, suffix, label, rows, limit in prepared:
        for key, heading, _, buckets in PARAMETERS:
            a = analyse(rows, limit, key, buckets)
            summary.append((label, key, a))
            blocks[key].append((f"{label} all", a["table"], a["missing"]))
            distributions.append(distribution_text(label, key, buckets, a))
        differ = sum(1 for r in rows if None not in (r[3]["ad"], r[3]["ad_dual"]) and r[3]["ad"] != r[3]["ad_dual"])
        if differ:
            distributions.append(f"{label}: the dual side's alternation depth differs on {differ} benchmarks")
    limit = max(limits)
    groups = [("", limit, range(len(prepared)))]
    if len(limits) > 1:
        groups = [(suffix, cap, [index])
                  for index, (_, suffix, _, _, cap) in enumerate(prepared)]
    if args.latex:
        print(summary_latex(summary, limit, [(label, cap) for _, _, label, _, cap in prepared]))
        for key, heading, tex, _ in PARAMETERS:
            for suffix, cap, indices in groups:
                print()
                label = f"tab:{key}-time" + (f"-{suffix}" if suffix else "")
                print(latex_table([blocks[key][i] for i in indices], cap, key=tex, label=label, caption=(
                    f"MuValPPM (SCC \\& AD): solving time by {NAMES[key]}, over the valid and invalid",
                    r"instances and the timeouts; percentages are of the row.")))
        return
    print("Summary: Spearman's rank correlation with MuValPPM (SCC & AD) solving time, timeouts at the limit")
    print(summary_text(summary))
    print()
    print("Distributions")
    for line in distributions:
        print("  " + line)
    for key, heading, _, _ in PARAMETERS:
        for _, cap, indices in groups:
            print()
            print(f"Solving time by {NAMES[key]}")
            print(text_table([blocks[key][i] for i in indices], cap, key=heading))


if __name__ == "__main__":
    main()
