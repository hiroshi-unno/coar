#!/usr/bin/env python3
"""Validate benchmark CSVs, display matched counts, or prepare plotting data."""

import argparse
import csv
from decimal import Decimal, DecimalException
import math
import os
import re
import tempfile
from collections import Counter
from pathlib import Path
import sys


ROWS = ("valid", "invalid", "timeout", "abort")
# Shown only when some file has them, so a table without them prints as before;
# `refused` is the runner's row for a run the tool declined (status 1, an `error:` line).
EXTRA_ROWS = ("unknown", "refused")
ALIASES = {"yes": "valid", "no": "invalid", "maybe": "unknown"}
# Result labels (CSV stems and run names) that were renamed together with the configurations they
# ran, old -> new.  Results written under an old label are read under its new one; this table is the
# one place the readers (this module, rankcount.py) map them, so stored results are never rewritten.
RENAMED_LABELS = {
    "muval_ppm_scc_ad": "muval_ppm_popl27",
    "muval_ppm_ad": "muval_ppm_popl27_no_scc",
    "muval_ppm_scc": "muval_ppm_popl27_no_ad",
    "muval_ppm_noopt": "muval_ppm_popl27_no_scc_ad",
    "muval_ppm_woerq": "muval_ppm_no_erasure",
    "muval_ppm_scc_woerq": "muval_ppm_no_ad_erasure",
    "muval_ppm_noopt_woerq": "muval_ppm_no_scc_ad_erasure",
    "muval_woerq": "muval_no_erasure",
    "muval_noopt_woerq": "muval_no_cycle_restriction_erasure",
}
# MuValPPM with SCC and AD, the configuration every figure compares against.
PRIMARY = "muval_ppm_popl27"
DECIMAL_TIME = re.compile(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?")


def canonical_label(stem):
    """The current label of a result named `stem` (an old label maps to its new one)."""
    return RENAMED_LABELS.get(stem, stem)


def labelled_records(paths, **options):
    """Read each CSV of `paths` into a map from its current label to its records.

    Refuses two files that carry one label (an old and a new name side by side), since which
    of them is the result would otherwise depend on the order they are read in.
    """
    records, sources = {}, {}
    for path in paths:
        label = canonical_label(path.stem)
        if label in records:
            raise ValueError(f"{path} and {sources[label]} both hold the results labelled {label!r}")
        records[label], sources[label] = read_records(path, **options), path
    return records


def labelled_path(directory, label):
    """The CSV in `directory` holding the results labelled `label`, under its new or an old name.

    Returns the new name's path when no file holds the label, so a caller's error names the file
    a current run writes; refuses two files that hold it.
    """
    names = [label] + [old for old, new in RENAMED_LABELS.items() if new == label]
    found = [directory / f"{name}.csv" for name in names if (directory / f"{name}.csv").exists()]
    if len(found) > 1:
        raise ValueError(f"{found[0]} and {found[1]} both hold the results labelled {label!r}")
    return found[0] if found else directory / f"{label}.csv"


def timeout_seconds(value):
    unit = value[-1:] if value[-1:] in ("s", "m", "h", "d") else ""
    number = value[:-1] if unit else value
    if DECIMAL_TIME.fullmatch(number) is None:
        raise argparse.ArgumentTypeError("timeout must be a positive duration, e.g. 300 or 5m")
    try:
        seconds = Decimal(number) * {"": 1, "s": 1, "m": 60, "h": 3600, "d": 86400}[unit]
    except DecimalException:
        raise argparse.ArgumentTypeError("timeout must be finite and positive") from None
    numeric_seconds = float(seconds)
    if not math.isfinite(numeric_seconds) or numeric_seconds <= 0:
        raise argparse.ArgumentTypeError("timeout must be finite and positive")
    return format(seconds, "f")


def read_records(path, *, plotting=False, timeout=None):
    records = {}
    with path.open(newline="", encoding="utf-8-sig") as stream:
        reader = csv.reader(stream, strict=True)
        for record in reader:
            if not record or all(not cell.strip() for cell in record):
                continue
            if not (3 if plotting else 2) <= len(record) <= 5:
                raise ValueError(f"{path}:{reader.line_num}: unexpected CSV column count")
            name = record[0]
            if not name.strip() or any(char in name for char in "\r\n"):
                raise ValueError(f"{path}:{reader.line_num}: missing or multiline benchmark name")
            if name in records:
                raise ValueError(f"{path}:{reader.line_num}: duplicate benchmark {name!r}")
            verdict = ALIASES.get(record[1].strip().lower(), record[1].strip().lower())
            if verdict not in (*ROWS, *EXTRA_ROWS):
                raise ValueError(f"{path}:{reader.line_num}: unsupported verdict {record[1]!r}")
            if plotting:
                elapsed = record[2].strip()
                # Deadline rows have three columns and carry the configured cap.
                # A solver-owned timeout keeps a fourth (possibly empty) metadata
                # field, and its time is measured runtime, not a plotting limit.
                solver_timeout = verdict == "timeout" and len(record) >= 4
                if verdict == "timeout" and not solver_timeout and elapsed:
                    # A recorded timeout time is the run's limit and becomes a plot bound.
                    try:
                        positive_limit = (DECIMAL_TIME.fullmatch(elapsed) is not None
                                          and Decimal(elapsed) > 0)
                    except DecimalException:
                        positive_limit = False
                    if not positive_limit:
                        raise ValueError(f"{path}:{reader.line_num}: invalid time limit {elapsed!r}")
                if elapsed:
                    if DECIMAL_TIME.fullmatch(elapsed) is None:
                        raise ValueError(f"{path}:{reader.line_num}: invalid elapsed time {elapsed!r}")
                    try:
                        seconds = float(elapsed)
                    except ValueError:
                        raise ValueError(f"{path}:{reader.line_num}: invalid elapsed time {elapsed!r}") from None
                    if verdict == "timeout" and not solver_timeout and seconds <= 0:
                        raise ValueError(f"{path}:{reader.line_num}: invalid time limit {elapsed!r}")
                    if not math.isfinite(seconds) or seconds < 0:
                        raise ValueError(f"{path}:{reader.line_num}: invalid elapsed time {elapsed!r}")
                elif verdict != "timeout":
                    raise ValueError(f"{path}:{reader.line_num}: missing elapsed time")
                if solver_timeout:
                    elapsed = ""
                if verdict == "timeout" and not elapsed and timeout is not None:
                    elapsed = timeout
                records[name] = [name, verdict, elapsed]
            else:
                records[name] = verdict
    if not records:
        raise ValueError(f"{path}: no benchmark records")
    return records


def require_same_names(left, right, label):
    if left.keys() != right.keys():
        missing = sorted(left.keys() - right.keys())
        extra = sorted(right.keys() - left.keys())
        raise ValueError(f"{label}: benchmark sets differ (missing={missing!r}, extra={extra!r})")


def figure_limit(tables, timeout, label):
    """The time limit a figure's timeout points are drawn at.

    Every timeout row with a recorded time in `tables` (lists of
    [name, verdict, elapsed] rows) must name the same limit, compared as a
    decimal number; that limit is returned in plain decimal notation. A blank
    timeout time (older output or a solver-owned timeout) carries no limit of its own: it
    takes the recorded one, or `timeout` when that was given explicitly, in
    which case `timeout` must agree with the recorded limit too. With nothing
    recorded the result is `timeout`, or 300 seconds when it is None.
    Disagreeing limits raise ValueError, since one figure cannot place its
    timeout points at two marks.
    """
    limits = {}
    blank = False
    for rows in tables:
        for row in rows:
            if row[1] == "timeout":
                if row[2]:
                    limits.setdefault(Decimal(row[2]), row[2])
                else:
                    blank = True
    if blank and timeout is not None:
        limits.setdefault(Decimal(timeout), f"{timeout} (--timeout, for blank timeout rows)")
    if len(limits) > 1:
        shown = ", ".join(limits[key] for key in sorted(limits))
        raise ValueError(f"{label}: timeout rows record different time limits ({shown}); "
                         "plot results of one time limit together")
    if not limits:
        return timeout if timeout is not None else "300"
    return format(next(iter(limits)).normalize(), "f")


def fill_blank_timeouts(rows, limit):
    """Copy `rows`, giving each timeout row without a time the time `limit`."""
    return [row[:2] + [limit] if row[1] == "timeout" and not row[2] else list(row)
            for row in rows]


def prepare_plots(root, timeout=None):
    """Write the joined comparison CSVs and return each figure's time limit.

    The result maps each comparison CSV's stem (the figure's data name, e.g.
    `pr_vs_dwf_its`) to the limit its timeout points are drawn at: the limit
    the inputs' timeout rows record, or `timeout` (300 seconds when None) when
    none records one; `figure_limit` states the rule. Blank timeout times in
    the derived CSVs are filled with that limit. Nothing is written unless
    every input validates.
    """
    # Join by benchmark identity; successful plotting cannot certify positional correspondence.
    comparisons = (("mustrat", "dwf", "1a"), ("muval", "wf", "1b"),
                   ("muval_ppm_popl27_no_scc", "wo_scc", "2a"),
                   ("muval_ppm_popl27_no_ad", "wo_ad", "2b"),
                   ("muval_ppm_popl27_no_scc_ad", "wo_ad_scc", "2c"))
    outputs = {}
    limits = {}
    for family, suffix in (("popl2023mod", "popl23"), ("term25its", "its")):
        directory = root / "results" / family
        paths = sorted(path for path in directory.glob("*.csv")
                       if not path.stem.endswith("_3cols"))
        records = labelled_records(paths, plotting=True)
        primary = records.get(PRIMARY)
        if primary is None:
            raise ValueError(f"{directory}: missing {PRIMARY}.csv")
        for competitor, label, _ in comparisons:
            if competitor not in records:
                raise ValueError(f"{directory}: missing {competitor}.csv")
            other = records[competitor]
            require_same_names(primary, other, f"{directory}: {competitor}")
            for name in primary:
                left_verdict = primary[name][1]
                right_verdict = other[name][1]
                if {left_verdict, right_verdict} == {"valid", "invalid"}:
                    raise ValueError(
                        f"{directory}: opposing verdicts for {name!r}: "
                        f"{PRIMARY}={left_verdict}, {competitor}={right_verdict}")
            stem = f"pr_vs_{label}_{suffix}"
            limit = figure_limit((primary.values(), other.values()), timeout,
                                 f"{directory}: {PRIMARY}.csv and {competitor}.csv")
            limits[stem] = limit
            left = fill_blank_timeouts(primary.values(), limit)
            right = fill_blank_timeouts([other[name] for name in primary], limit)
            outputs[root / "results" / "comparison" / f"{stem}.csv"] = [
                l + r for l, r in zip(left, right)]
        for stem, rows in records.items():
            limit = figure_limit((rows.values(),), timeout, f"{directory}/{stem}.csv")
            outputs[directory / f"{stem}_3cols.csv"] = fill_blank_timeouts(rows.values(), limit)
    # Validate the entire input set before replacing any derived CSV.
    for path, rows in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(mode="w", newline="", encoding="utf-8",
                                             dir=path.parent, delete=False) as stream:
                temporary = stream.name
                csv.writer(stream, lineterminator="\n").writerows(rows)
            os.replace(temporary, path)
        finally:
            if temporary and os.path.exists(temporary):
                os.unlink(temporary)
    return limits


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-plots", type=Path, metavar="ROOT")
    parser.add_argument("--timeout", type=timeout_seconds, default=None,
                        help="time limit of results whose timeout rows record no time (older "
                             "runner output or solver-owned timeout); a recorded limit is used otherwise (default: 300 seconds)")
    parser.add_argument("--validate-times", action="store_true",
                        help="require complete finite nonnegative elapsed times")
    parser.add_argument("csv_files", type=Path, nargs="*", help="CSV files, in display order")
    args = parser.parse_args()
    try:
        if args.prepare_plots is not None:
            if args.csv_files:
                parser.error("--prepare-plots does not accept CSV arguments")
            limits = prepare_plots(args.prepare_plots, args.timeout)
            # One line per figure, `<data name> <limit seconds>`, for the plotting driver.
            for stem, limit in limits.items():
                print(stem, limit)
            return 0
        if not args.csv_files:
            parser.error("at least one CSV file is required")
        records = list(labelled_records(args.csv_files, plotting=args.validate_times).values())
        for path, result in zip(args.csv_files[1:], records[1:]):
            require_same_names(records[0], result, str(path))
        counts = [Counter(row[1] for row in result.values()) if args.validate_times
                  else Counter(result.values()) for result in records]
    except (OSError, ValueError, csv.Error) as error:
        parser.exit(1, f"error: {error}\n")

    rows = list(ROWS)
    rows.extend(verdict for verdict in EXTRA_ROWS if any(result[verdict] for result in counts))
    # A column is headed by its result's current label, so old and new result files print alike.
    table = [["result", *(canonical_label(path.stem) + path.suffix for path in args.csv_files)]]
    table.extend([verdict, *(str(result[verdict]) for result in counts)] for verdict in rows)
    widths = [max(len(row[column]) for row in table) for column in range(len(table[0]))]
    for index, row in enumerate(table):
        print(" | ".join(cell.ljust(widths[column]) if column == 0 or index == 0
                         else cell.rjust(widths[column]) for column, cell in enumerate(row)))
        if index == 0:
            print("-+-".join("-" * width for width in widths))
    return 0


if __name__ == "__main__":
    sys.exit(main())
