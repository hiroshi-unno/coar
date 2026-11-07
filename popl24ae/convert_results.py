#!/usr/bin/env python3
"""Validate artifact CSVs and derive tables using benchmark identities."""

import csv
import os
from pathlib import Path
import re
import sys
import tempfile

from evaluation_inputs import number


def records(path):
    result = {}
    with path.open(newline='', encoding='utf-8-sig') as stream:
        reader = csv.reader(stream, strict=True)
        for row in reader:
            if len(row) < 2:
                raise ValueError(f'{path}:{reader.line_num}: malformed row')
            name, verdict = row[:2]
            if not name.strip() or any(c in name for c in ',"\r\n') or name in result:
                raise ValueError(f'{path}:{reader.line_num}: invalid or duplicate name')
            if verdict == '(excluded)':
                if len(row) != 2:
                    raise ValueError(f'{path}:{reader.line_num}: malformed exclusion')
                elapsed = ''
            elif verdict in ('sat', 'unsat', 'unknown', 'abort', 'refused', 'timeout'):
                if len(row) not in (3, 4):
                    raise ValueError(f'{path}:{reader.line_num}: malformed result')
                elapsed = row[2]
                if elapsed or verdict != 'timeout':
                    number(elapsed, f'{path}:{reader.line_num}: elapsed time')
            else:
                raise ValueError(f'{path}:{reader.line_num}: unsupported verdict {verdict!r}')
            result[name] = (verdict, elapsed)
    if not result:
        raise ValueError(f'{path}: no benchmark records')
    return result


def table1(rows, label):
    output = [['file name', f'[{label}] result correct?', f'[{label}] time']]
    names = set()
    for name in sorted(rows):
        basename = Path(name).name
        if basename in names:
            raise ValueError(f'{label}: ambiguous basename {basename!r}')
        names.add(basename)
        verdict, elapsed = rows[name]
        if verdict == 'timeout':
            answer, elapsed = '-', 'timeout'
        elif verdict == '(excluded)':
            answer, elapsed = '(excluded)', '-'
        elif verdict in ('unknown', 'abort'):
            answer, elapsed = 'abort', '-'
        elif verdict == 'refused':
            # The tool declined the input (status 1, an `error:` line): neither an
            # answer nor a crash, so it keeps its own word.
            answer, elapsed = 'refused', '-'
        else:
            match = re.search(r'-(SAT|UNSAT)\.ml$', basename)
            if match is None:
                raise ValueError(f'{label}: missing expected-verdict suffix: {name!r}')
            answer = 'Yes' if verdict.upper() == match[1] else 'No'
        output.append([basename, answer, elapsed])
    return output


def table2(rows):
    groups = {}
    displayed = {}
    for name, record in rows.items():
        path = Path(name)
        match = re.fullmatch(r'(.+)_(DS|CPS|CPS_opt)\.ml', path.name)
        if match is None:
            raise ValueError(f'missing transformation suffix: {name!r}')
        program, role = match.groups()
        key = (str(path.parent), program)
        if program in displayed and displayed[program] != key:
            raise ValueError(f'ambiguous program basename: {program!r}')
        displayed[program] = key
        group = groups.setdefault(key, {})
        if role in group:
            raise ValueError(f'duplicate transformation role: {name!r}')
        group[role] = record
    output = [['program', '[DS] verified?', '[DS] time', '[CPS] verified?',
               '[CPS] time', '[CPS opt] verified?', '[CPS opt] time']]
    for (_, program), group in sorted(groups.items()):
        if group.keys() != {'DS', 'CPS', 'CPS_opt'}:
            raise ValueError(f'incomplete transformation group: {program!r}')
        row = [program]
        for role in ('DS', 'CPS', 'CPS_opt'):
            verdict, elapsed = group[role]
            row.extend([{'sat': 'Yes', 'unsat': 'No'}.get(verdict, verdict), elapsed])
        output.append(row)
    return output


def convert(root):
    inputs = {arm: records(root / f'results_{arm}.csv') for arm in ('spacer', 'pcsat', 'cps')}
    if inputs['spacer'].keys() != inputs['pcsat'].keys():
        raise ValueError('Spacer and PCSat benchmark sets differ')
    outputs = {'spacer': table1(inputs['spacer'], 'Spacer'),
               'pcsat': table1(inputs['pcsat'], 'PCSat'), 'cps': table2(inputs['cps'])}
    # Build every table before publishing. Each replacement is atomic, but the
    # complete set of table replacements is not a filesystem transaction.
    for arm, rows in outputs.items():
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(mode='w', newline='', encoding='utf-8',
                                             dir=root, delete=False) as stream:
                temporary = stream.name
                csv.writer(stream, lineterminator='\n').writerows(rows)
            os.replace(temporary, root / f'table_{arm}.csv')
        finally:
            if temporary and os.path.exists(temporary):
                os.unlink(temporary)


if __name__ == '__main__':
    try:
        convert(Path(__file__).resolve().parent)
    except (OSError, ValueError, csv.Error, ArithmeticError) as error:
        sys.exit(f'error: {error}')
