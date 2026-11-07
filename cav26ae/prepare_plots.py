#!/usr/bin/env python3
"""Validate and join scatter-plot inputs by benchmark identity."""

import argparse
import csv
from decimal import Decimal
import math
import os
import re
from pathlib import Path
import tempfile


DECIMAL_TIME = re.compile(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?")

def read_records(path):
    records = {}
    with path.open(newline='', encoding='utf-8-sig') as stream:
        reader = csv.reader(stream, strict=True)
        for row in reader:
            if not row or all(not cell.strip() for cell in row):
                continue
            if len(row) not in (3, 4):
                raise ValueError(f'{path}:{reader.line_num}: expected three or four columns')
            name, verdict, elapsed = row[:3]
            if (not name.strip() or any(c in name for c in ',"\r\n')
                    or name.lstrip().startswith('#') or name in records):
                raise ValueError(f'{path}:{reader.line_num}: unsupported or duplicate benchmark name')
            if verdict not in ('sat', 'unsat', 'unknown', 'timeout', 'abort', 'refused'):
                raise ValueError(f'{path}:{reader.line_num}: unsupported verdict {verdict!r}')
            # The shared runner uses three fields for an enforced deadline,
            # four for a solver-owned timeout with measured runtime/metadata.
            solver_timeout = verdict == 'timeout' and len(row) == 4
            if elapsed:
                if DECIMAL_TIME.fullmatch(elapsed) is None:
                    raise ValueError(f'{path}:{reader.line_num}: invalid elapsed time')
                seconds = float(elapsed)
                if not math.isfinite(seconds) or seconds < 0:
                    raise ValueError(f'{path}:{reader.line_num}: invalid elapsed time')
                if verdict == 'timeout' and not solver_timeout and seconds == 0:
                    # A recorded timeout time is the run's limit and becomes a plot bound.
                    raise ValueError(f'{path}:{reader.line_num}: invalid time limit')
            elif verdict != 'timeout':
                raise ValueError(f'{path}:{reader.line_num}: missing elapsed time')
            if solver_timeout:
                elapsed = ''
            records[name] = [name, verdict, elapsed]
    if not records:
        raise ValueError(f'{path}: no benchmark records')
    return records


def figure_limit(tables, timeout, label):
    """The time limit a figure's timeout points are drawn at.

    Every timeout row with a recorded time in `tables` (iterables of
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
            if row[1] == 'timeout':
                if row[2]:
                    limits.setdefault(Decimal(row[2]), row[2])
                else:
                    blank = True
    if blank and timeout is not None:
        limits.setdefault(Decimal(timeout), f'{timeout} (--timeout, for blank timeout rows)')
    if len(limits) > 1:
        shown = ', '.join(limits[key] for key in sorted(limits))
        raise ValueError(f'{label}: timeout rows record different time limits ({shown}); '
                         'plot results of one time limit together')
    if not limits:
        return timeout if timeout is not None else '300'
    return format(next(iter(limits)).normalize(), 'f')


# The arms, named by their configurations (config/solver/<arm>.json): the approach with the
# progress property, compared against the return without it and against Z3.
PRIMARY = 'mucyc_qsat_deepest_own_projected_repeatedly'
COMPETITORS = ('mucyc_qsat_deepest_own', 'z3_smt')

def filled(row, limit):
    """Copy a [name, verdict, elapsed] row, a blank timeout time becoming `limit`."""
    return [row[0], row[1], limit] if row[1] == 'timeout' and not row[2] else list(row)


def prepare(root, family, timeout=None):
    """Write the joined comparison CSVs and return each figure's time limit.

    The result maps each comparison's name (`<family>_<PRIMARY>_vs_<competitor>`,
    the stem of its CSV, PDF and gnuplot script) to the limit its timeout
    points are drawn at, by `figure_limit`'s rule. Blank timeout times in the
    derived CSVs are filled with that limit. Nothing is written unless every
    comparison validates.
    """
    primary = read_records(root / f'{family}_{PRIMARY}.csv')
    outputs = {}
    limits = {}
    for competitor in COMPETITORS:
        other = read_records(root / f'{family}_{competitor}.csv')
        if primary.keys() != other.keys():
            raise ValueError(f'{family}_{competitor}: benchmark sets differ')
        stem = f'{family}_{PRIMARY}_vs_{competitor}'
        limit = figure_limit((primary.values(), other.values()), timeout,
                             f'{family}_{PRIMARY}.csv and {family}_{competitor}.csv')
        limits[stem] = limit
        rows = []
        for name in sorted(primary):
            left, right = primary[name], other[name]
            if left[1] in ('sat', 'unsat') and right[1] in ('sat', 'unsat') and left[1] != right[1]:
                raise ValueError(f'{name}: contradictory decided verdicts')
            rows.append(filled(left, limit) + filled(right, limit))
        outputs[root / f'{stem}.csv'] = rows
    # Validate every comparison before replacing derived files. Raw results stay intact.
    for path, rows in outputs.items():
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(mode='w', newline='', encoding='utf-8', dir=root,
                                             delete=False) as stream:
                temporary = stream.name
                csv.writer(stream, lineterminator='\n').writerows(rows)
            os.replace(temporary, path)
        finally:
            if temporary and os.path.exists(temporary):
                os.unlink(temporary)
    return limits


def positive_seconds(value):
    if DECIMAL_TIME.fullmatch(value) is None or not math.isfinite(float(value)) or float(value) <= 0:
        raise argparse.ArgumentTypeError('timeout must be a finite positive number of seconds')
    return format(Decimal(value).normalize(), 'f')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('family', choices=('LIA', 'LRA'))
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--timeout', type=positive_seconds, default=None,
                        help='time limit of results whose timeout rows record no time (older '
                             'runner output); a recorded limit is used otherwise (default: 300)')
    args = parser.parse_args()
    try:
        limits = prepare(args.root, args.family, args.timeout)
        # One line per figure, `<name> <limit seconds>`, for the plotting driver.
        for stem, limit in limits.items():
            print(stem, limit)
    except (OSError, ValueError, csv.Error) as error:
        parser.exit(1, f'error: {error}\n')


if __name__ == '__main__':
    main()
