#!/usr/bin/env python3
"""Validate memory manifests and completed evaluation rows before publication."""

import csv
from decimal import Decimal
import math
from pathlib import Path
import re
import sys

NUMBER = re.compile(r'[+]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?')
ARMS = ('spacer', 'pcsat', 'cps')


def number(text, label):
    text = text.strip()
    if NUMBER.fullmatch(text) is None:
        raise ValueError(f'{label}: expected a finite nonnegative number')
    result = Decimal(text)
    if not math.isfinite(float(result)):
        raise ValueError(f'{label}: expected a finite nonnegative number')
    return result


def read_manifest(path):
    rows = []
    seen = set()
    with path.open(newline='', encoding='utf-8-sig') as stream:
        reader = csv.reader(stream, strict=True)
        for row in reader:
            if len(row) != 2:
                raise ValueError(f'{path}:{reader.line_num}: expected two columns')
            name = row[0]
            if not name.strip() or any(c in name for c in ',"\r\n') or name in seen:
                raise ValueError(f'{path}:{reader.line_num}: invalid or duplicate benchmark name')
            if not Path(name).is_file():
                raise ValueError(f'{path}:{reader.line_num}: missing benchmark {name!r}')
            seen.add(name)
            rows.append((name, number(row[1], f'{path}:{reader.line_num}')))
    if not rows:
        raise ValueError(f'{path}: empty memory manifest')
    return rows


def prepare(artifact, stage, limit):
    threshold = number(limit, 'memory limit') * 1024 * 1024
    manifests = {arm: read_manifest(artifact / f'memusage_{arm}.csv') for arm in ARMS}
    for arm, rows in manifests.items():
        selected = [name for name, memory in rows if memory <= threshold]
        (stage / f'{arm}.paths').write_bytes(b''.join(name.encode() + b'\0' for name in selected))
        with (stage / f'{arm}.excluded').open('w', newline='') as stream:
            csv.writer(stream, lineterminator='\n').writerows(
                (name, '(excluded)') for name, memory in rows if memory > threshold)


def validate(artifact, stage):
    for arm in ARMS:
        selected = set((stage / f'{arm}.paths').read_bytes().decode().split('\0')[:-1])
        with (stage / f'{arm}.excluded').open(newline='') as stream:
            excluded = {row[0] for row in csv.reader(stream)}
        expected = selected | excluded
        seen = set()
        with (stage / f'results_{arm}.csv').open(newline='') as stream:
            reader = csv.reader(stream, strict=True)
            for row in reader:
                if len(row) < 2 or row[0] not in expected or row[0] in seen:
                    raise ValueError(f'{arm}:{reader.line_num}: unexpected or duplicate result')
                seen.add(row[0])
                verdict = row[1]
                if verdict == '(excluded)':
                    if len(row) != 2 or row[0] not in excluded:
                        raise ValueError(f'{arm}: malformed exclusion row')
                elif verdict in ('sat', 'unsat', 'unknown', 'abort', 'refused', 'timeout'):
                    if len(row) not in (3, 4) or row[0] not in selected:
                        raise ValueError(f'{arm}: malformed result row')
                    if row[2] or verdict != 'timeout':
                        number(row[2], f'{arm}: elapsed time')
                else:
                    raise ValueError(f'{arm}: unsupported verdict {verdict!r}')
        if seen != expected:
            raise ValueError(f'{arm}: missing benchmark results')


def main():
    try:
        operation, artifact, stage, *extra = sys.argv[1:]
        if operation == 'prepare':
            prepare(Path(artifact), Path(stage), extra[0])
        elif operation == 'validate':
            validate(Path(artifact), Path(stage))
        else:
            raise ValueError('invalid operation')
    except (OSError, ValueError, csv.Error, ArithmeticError) as error:
        sys.exit(f'error: {error}')


if __name__ == '__main__':
    main()
