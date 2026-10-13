#!/usr/bin/env python3
"""Validate benchmark CSVs, display matched counts, or prepare plotting data."""

import argparse
import csv
import math
import os
import re
import tempfile
from collections import Counter
from pathlib import Path
import sys


ROWS = ("valid", "invalid", "timeout", "abort")
ALIASES = {"yes": "valid", "no": "invalid", "maybe": "unknown"}
DECIMAL_TIME = re.compile(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?")


def read_records(path, *, plotting=False):
    records = {}
    with path.open(newline="", encoding="utf-8-sig") as stream:
        reader = csv.reader(stream, strict=True)
        for record in reader:
            if not record or all(not cell.strip() for cell in record):
                continue
            if not (3 if plotting else 2) <= len(record) <= 4:
                raise ValueError(f"{path}:{reader.line_num}: unexpected CSV column count")
            name = record[0]
            if not name.strip() or any(char in name for char in "\r\n"):
                raise ValueError(f"{path}:{reader.line_num}: missing or multiline benchmark name")
            if name in records:
                raise ValueError(f"{path}:{reader.line_num}: duplicate benchmark {name!r}")
            verdict = ALIASES.get(record[1].strip().lower(), record[1].strip().lower())
            if verdict not in (*ROWS, "unknown"):
                raise ValueError(f"{path}:{reader.line_num}: unsupported verdict {record[1]!r}")
            if plotting:
                elapsed = record[2].strip()
                if elapsed:
                    if DECIMAL_TIME.fullmatch(elapsed) is None:
                        raise ValueError(f"{path}:{reader.line_num}: invalid elapsed time {elapsed!r}")
                    try:
                        seconds = float(elapsed)
                    except ValueError:
                        raise ValueError(f"{path}:{reader.line_num}: invalid elapsed time {elapsed!r}") from None
                    if not math.isfinite(seconds) or seconds < 0:
                        raise ValueError(f"{path}:{reader.line_num}: invalid elapsed time {elapsed!r}")
                elif verdict != "timeout":
                    raise ValueError(f"{path}:{reader.line_num}: missing elapsed time")
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


def prepare_plots(root):
    # Join by benchmark identity; successful plotting cannot certify positional correspondence.
    comparisons = (("mustrat", "dwf", "1a"), ("muval", "wf", "1b"),
                   ("muval_ppm_ad", "wo_scc", "2a"),
                   ("muval_ppm_scc", "wo_ad", "2b"),
                   ("muval_ppm_noopt", "wo_ad_scc", "2c"))
    outputs = {}
    for family, suffix in (("popl2023mod", "popl23"), ("term25its", "its")):
        directory = root / "results" / family
        paths = sorted(path for path in directory.glob("*.csv")
                       if not path.stem.endswith("_3cols"))
        records = {path.stem: read_records(path, plotting=True) for path in paths}
        primary = records.get("muval_ppm_scc_ad")
        if primary is None:
            raise ValueError(f"{directory}: missing muval_ppm_scc_ad.csv")
        for competitor, label, _ in comparisons:
            if competitor not in records:
                raise ValueError(f"{directory}: missing {competitor}.csv")
            other = records[competitor]
            require_same_names(primary, other, f"{directory}: {competitor}")
            outputs[root / "results" / "comparison" / f"pr_vs_{label}_{suffix}.csv"] = [
                primary[name] + other[name] for name in primary]
        for stem, rows in records.items():
            outputs[directory / f"{stem}_3cols.csv"] = list(rows.values())
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-plots", type=Path, metavar="ROOT")
    parser.add_argument("--validate-times", action="store_true",
                        help="require complete finite nonnegative elapsed times")
    parser.add_argument("csv_files", type=Path, nargs="*", help="CSV files, in display order")
    args = parser.parse_args()
    try:
        if args.prepare_plots is not None:
            if args.csv_files:
                parser.error("--prepare-plots does not accept CSV arguments")
            prepare_plots(args.prepare_plots)
            return 0
        if not args.csv_files:
            parser.error("at least one CSV file is required")
        records = [read_records(path, plotting=args.validate_times) for path in args.csv_files]
        for path, result in zip(args.csv_files[1:], records[1:]):
            require_same_names(records[0], result, str(path))
        counts = [Counter(row[1] for row in result.values()) if args.validate_times
                  else Counter(result.values()) for result in records]
    except (OSError, ValueError, csv.Error) as error:
        parser.exit(1, f"error: {error}\n")

    rows = list(ROWS)
    if any(result["unknown"] for result in counts):
        rows.append("unknown")
    table = [["result", *(path.name for path in args.csv_files)]]
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
