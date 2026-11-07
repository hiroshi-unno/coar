#!/usr/bin/env python3
"""Generate the muCLP (`.hes`) inputs of the infinite-state reactive-synthesis benchmarks.

The games of github.com/phheim/infinite-state-reactive-synthesis-benchmarks are kept as sources
(`.rpg`, `.issy`, `.tslmt`) in the submodule benchmarks/infinite-state-reactive-synthesis-benchmarks;
this repository stores no `.hes` made from them.  This script makes one `.hes` per source in an
ignored directory (default benchmarks/muCLP/issy), with the generator the source's format asks for:

  .rpg    rpgencode muclp < SRC                (rpglib 2ddb0a8: the tool that made the POPL 2024
                                                artifact's .hes files, reproduced byte for byte);
          issy --encode-muclp --rpg SRC         only when rpgencode is absent or fails
  .issy   issy --encode-muclp --caller-aut LTL2TGBA SRC
  .tslmt  issy --encode-muclp --tslmt --caller-aut LTL2TGBA SRC

Every output then goes through script/issy_hes_postprocess.py, given the generator's exit status.
That pass returns a file this tree already reads byte for byte, respells the integer numerals
issy writes at real positions, joins the parity names issy writes with a space, and refuses --
writing nothing -- a partial output (the generator failed after printing part of an encoding),
a parity encoding not listed highest colour first and a co-Buchi encoding (both read, but mean
another game than the source).  A file is kept only when the post-processor writes it.

The record, OUT/STATUS.tsv, has one line per source:

  source  family  generator  gen_status  outcome  expected  seconds  bytes  detail

where `outcome` is one of
  generated          OUT/<name>.hes exists
  refused-parity     the parity encoding lists a lower colour first (issy v3.0 does, always)
  refused-cobuechi   a co-Buchi encoding
  refused-truncated  the generator exited non-zero after writing part of an encoding
  refused-other      the post-processor refused for another reason (named in `detail`)
  gen-failed         the generator exited non-zero and wrote nothing
  gen-timeout        the generator ran past --timeout (killed, with its process group)
  gen-killed         the generator was killed by a signal from outside (a memory cap, typically)
  no-generator       a tool the source needs is not installed
`expected` is REAL (realizable: a correct MuVal answer is `valid`), UNREAL (`invalid`), `-` when
no artifact annotates the source, and `disputed` when the two artifacts that annotate it disagree
(script/issy_expected.txt holds both).  `gen_status` is the generator's exit status (124 on a
timeout).  Raw generator outputs and their stderr are kept under OUT/raw/ for diagnosis.

Tools are looked up in the repository root first (the names are in .gitignore, linked in as the
solvers are) and then on PATH.  Run from the repository root:

  script/gen_issy_hes.py [--out DIR] [--jobs N] [--timeout SECONDS] [--only NAME ...]

Nothing outside OUT is written.  An existing OUT/<name>.hes is regenerated, so re-running the script
gives the record of the run that wrote it.  Exit status 0 when every source has a record (whatever
its outcome), 2 on a usage error.
"""

import argparse
import concurrent.futures
import os
import shutil
import signal
import subprocess
import sys
import time

SUBMODULE = 'benchmarks/infinite-state-reactive-synthesis-benchmarks/benchmarks'
EXPECTED = 'script/issy_expected.txt'
POSTPROCESS = 'script/issy_hes_postprocess.py'


def find_tool(name):
    local = os.path.join('.', name)
    if os.path.isfile(local) and os.access(local, os.X_OK):
        return os.path.abspath(local)
    return shutil.which(name)


def read_expected(path):
    table = {}
    with open(path, encoding='utf-8') as f:
        for line in f:
            if line.startswith('#') or not line.strip():
                continue
            src, thesis, tacas = (line.rstrip('\n').split('\t') + ['-', '-'])[:3]
            labels = {v for v in (thesis, tacas) if v != '-'}
            table[src] = labels.pop() if len(labels) == 1 else ('disputed' if labels else '-')
    return table


def run(cmd, stdin_path, out_path, err_path, timeout):
    """Run cmd with stdout/stderr to files; kill its whole process group on a timeout.
    Returns (status, seconds), status 124 for a timeout as timeout(1) reports it."""
    t0 = time.monotonic()
    with open(out_path, 'wb') as out, open(err_path, 'wb') as err:
        stdin = open(stdin_path, 'rb') if stdin_path else subprocess.DEVNULL
        try:
            p = subprocess.Popen(cmd, stdin=stdin, stdout=out, stderr=err, start_new_session=True)
            try:
                status = p.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                p.wait()
                status = 124
        finally:
            if stdin_path:
                stdin.close()
    return status, time.monotonic() - t0


def classify_refusal(msg):
    if 'parity equations listed lower colour first' in msg:
        return 'refused-parity'
    if 'co-Buchi' in msg:
        return 'refused-cobuechi'
    if 'partial encoding' in msg:
        return 'refused-truncated'
    return 'refused-other'


def generate(src, tools, out_dir, timeout):
    name, ext = os.path.splitext(src)
    path = os.path.join(SUBMODULE, src)
    raw = os.path.join(out_dir, 'raw', name + '.raw.hes')
    err = os.path.join(out_dir, 'raw', name + '.err')
    final = os.path.join(out_dir, name + '.hes')
    if os.path.exists(final):
        os.unlink(final)
    issy, ltl2tgba, rpgencode = tools['issy'], tools['ltl2tgba'], tools['rpgencode']
    attempts = []
    if ext == '.rpg':
        if rpgencode:
            attempts.append(('rpgencode', [rpgencode, 'muclp'], path))
        if issy:
            attempts.append(('issy-rpg', [issy, '--quiet', '--encode-muclp', '--rpg', path], None))
    elif ext in ('.issy', '.tslmt') and issy and ltl2tgba:
        cmd = [issy, '--quiet', '--encode-muclp'] + (['--tslmt'] if ext == '.tslmt' else [])
        attempts.append(('issy', cmd + ['--caller-aut', ltl2tgba, path], None))
    if not attempts:
        return name, 'none', '-', 'no-generator', 0.0, 0, f'no tool for {ext}'
    seconds = 0.0
    for gen, cmd, stdin_path in attempts:
        status, dt = run(cmd, stdin_path, raw, err, timeout)
        seconds += dt
        # rpgencode is tried first for .rpg; issy is the fallback only when rpgencode fails.
        if status == 0 or gen != 'rpgencode':
            break
    size = os.path.getsize(raw)
    if status == 124:
        return name, gen, status, 'gen-timeout', seconds, size, f'killed after {timeout} s'
    reason = ''
    if status != 0:
        # issy reports an unsupported construct as `issy: <message>` followed by a Haskell call
        # stack, so that line is the reason; otherwise the last line of stderr.
        with open(err, encoding='utf-8', errors='replace') as f:
            lines = [l.strip() for l in f.read().splitlines() if l.strip()]
        reason = next((l for l in lines if l.startswith('issy:')), lines[-1] if lines else '(no stderr)')
    if status < 0:
        # killed by a signal from outside, typically a memory cap around the run (SIGKILL)
        return name, gen, status, 'gen-killed', seconds, size, f'signal {-status}'
    if status != 0 and size == 0:
        return name, gen, status, 'gen-failed', seconds, size, reason
    pp = subprocess.run([sys.executable, '-I', POSTPROCESS, '--issy-status', str(status), '--report',
                         '-o', final, raw], capture_output=True, text=True)
    msg = ' '.join(pp.stderr.split())
    msg = msg.split(raw + ': ', 1)[-1]
    if pp.returncode == 0:
        return name, gen, status, 'generated', seconds, os.path.getsize(final), msg
    return name, gen, status, classify_refusal(msg), seconds, size, msg + (f' ({reason})' if reason else '')


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--out', default='benchmarks/muCLP/issy')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--timeout', type=float, default=1800.0,
                    help='seconds per generator call (a .tslmt source can take over ten minutes)')
    ap.add_argument('--only', nargs='*', help='source file names (with extension) to generate')
    a = ap.parse_args(argv)
    if not os.path.isdir(SUBMODULE):
        print(f'gen_issy_hes: {SUBMODULE} is missing: git submodule update --init '
              f'{os.path.dirname(SUBMODULE)}', file=sys.stderr)
        return 2
    tools = {t: find_tool(t) for t in ('issy', 'ltl2tgba', 'rpgencode')}
    for t, p in tools.items():
        print(f'gen_issy_hes: {t} = {p or "(absent)"}', file=sys.stderr)
    expected = read_expected(EXPECTED)
    sources = sorted(f for f in os.listdir(SUBMODULE) if f.endswith(('.rpg', '.issy', '.tslmt')))
    if a.only:
        missing = sorted(set(a.only) - set(sources))
        if missing:
            print(f'gen_issy_hes: not sources: {" ".join(missing)}', file=sys.stderr)
            return 2
        sources = [s for s in sources if s in a.only]
    os.makedirs(os.path.join(a.out, 'raw'), exist_ok=True)
    rows = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as ex:
        futs = {ex.submit(generate, s, tools, a.out, a.timeout): s for s in sources}
        for fut in concurrent.futures.as_completed(futs):
            src = futs[fut]
            name, gen, status, outcome, secs, size, detail = fut.result()
            rows[src] = (src, src.split('-', 1)[0], gen, str(status), outcome, expected.get(src, '-'),
                         f'{secs:.1f}', str(size), detail)
            print(f'gen_issy_hes: {src}\t{outcome}', file=sys.stderr, flush=True)
    status_path = os.path.join(a.out, 'STATUS.tsv')
    if a.only and os.path.exists(status_path):
        with open(status_path, encoding='utf-8') as f:
            for line in f:
                if not line.startswith('#'):
                    cols = line.rstrip('\n').split('\t')
                    rows.setdefault(cols[0], tuple(cols))
    with open(status_path + '.tmp', 'w', encoding='utf-8') as f:
        f.write('# source\tfamily\tgenerator\tgen_status\toutcome\texpected\tseconds\tbytes\tdetail\n')
        for src in sorted(rows):
            f.write('\t'.join(rows[src]) + '\n')
    os.replace(status_path + '.tmp', status_path)
    counts = {}
    for r in rows.values():
        counts[r[4]] = counts.get(r[4], 0) + 1
    print('gen_issy_hes: ' + ', '.join(f'{k} {v}' for k, v in sorted(counts.items())) + f', total {len(rows)}')
    print('DONE')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
