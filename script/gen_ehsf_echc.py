#!/usr/bin/env python3
"""Generate SMT-LIB (and, where exact, muCLP) inputs from the E-HSF benchmark archive.

The archive `hsf-Benchmarks.zip` holds the `.qarmc` inputs of E-HSF (Beyene, Popeea and
Rybalchenko, "Solving existentially quantified Horn clauses", CAV 2013): CTL properties of the
industrial examples of Cook and Koskinen (PLDI 2013) and CTL* instances over Windows drivers.  It
has no public upstream this repository knows of, and its licence is not stated, so it is neither
tracked nor redistributed: it is read where it lies (by default benchmarks/ECHC/hsf-Benchmarks.zip,
untracked) and checked against the SHA-256 below, and every output goes to an ignored directory.

A larger tree of the same tool's inputs (ConSynth's, which grew out of E-HSF: the CAV 2013 sets
in four versions, CTL+FO, the POPL 2014 games, ConSynth's development games, unit tests) is in
github.com/stanlysamuel/gensys, branch gensys-ltl, under tools/consynth/Benchmarks/; its licence
is not stated either.  `--fetch` downloads the `.qarmc` files listed in script/fetch/consynth.manifest
at the pinned commit into the ignored benchmarks/ECHC/consynth-src/, checking each file's git blob
hash; the families of 1-9 MB procedural driver files (rec-synth, pldi14-sub, vstte15,
ctlstar-pldi2014sub) are left out.

Each `.qarmc` file is translated by script/qarmc_to_smt2.py and placed in the corpus of its least
class (a predicate kind -- wf -- makes it pfwnCSP, an existential head without a kind ECHC,
neither CHC):

  benchmarks/<CLASS>/ehsf/<src>/<dir>/<stem>.smt2   CLASS in ECHC, pfwnCSP, CHC
  benchmarks/muCLP/ehsf/<src>/<dir>/<stem>.hes      only when the nu-only muCLP encoding is exact

with <src> `zip` (the archive; <dir> one of ctlstar-cav13, ctlstar-cav13-template,
ctlstar-pldi2014sub) or `consynth` (<dir> the path below Benchmarks/).  The record,
benchmarks/ECHC/ehsf/STATUS.tsv, has one line per source:

  src  dir  stem  outcome  class  expected  hes  detail

`outcome` is `converted`, `refused`, or `duplicate` (an archive file byte-identical to the fetched
ConSynth file of the same path, converted once from there); `expected` is `sat` for a `-succeed` file, `unsat` for a
`-fail` file and `-` otherwise (the archive's own naming; a muCLP answer `valid` corresponds to
`sat`); `hes` is `written` or the reason the file is outside the fragment; `detail` is the refusal
or the converter's feature line.  Beside it, NOTES.md is a copy of script/fetch/ehsf.notes.md: the
files whose name states a verdict that is wrong, against the source paper, or undecided.

Run from the repository root:

  script/gen_ehsf_echc.py [--fetch] [--zip PATH] [--consynth DIR] [--sort Int|Real] [--no-stutter]
                          [--keep-exists]

--consynth reads the ConSynth tree from DIR instead of benchmarks/ECHC/consynth-src (each file is still
checked against the manifest).  By default the converter makes the transition relation `next` total by
giving a state without a successor a self-loop (an ended run stays where it is, the usual reading of
CTL over a program); --no-stutter keeps the clauses as written, where such a state is a deadlock that
falsifies EG and needs no rank for AF.  The record's detail column says which (`stutter=`).
Where every disjunct of the stuttered `next` fixes all primed variables by equations, an existential
successor `exists w. next(v, w) /\\ R(w)` is eliminated by the one-point rule in the `.hes` (a nu-body
disjunction) and in a pfwnCSP `.smt2` (a disjunctive head; an ECHC `.smt2` keeps the existential, the
form its class is about); --keep-exists keeps it everywhere (`onepoint=<k>` in the detail column).

A missing archive or a missing consynth-src skips that source with a line on stderr.

Existing outputs under the four ehsf directories are removed first, so the directories hold
exactly the last run.  Exit status 0 when every source has a record, 1 when the archive's digest differs or a fetched file
does not match the manifest, 2 on a usage error.
"""

import argparse
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
import urllib.request
import zipfile

ZIP_DEFAULT = 'benchmarks/ECHC/hsf-Benchmarks.zip'
ZIP_SHA256 = 'f4be99ddc16110f3b6a3ddd7b55b59d9424013e09440721a1dd209a59939bb8d'
ZIP_DIRS = {'Benchmarks/ctlstar-cav13/': 'ctlstar-cav13',
            'Benchmarks/ctl/ctlstar-cav13-template/': 'ctlstar-cav13-template',
            'Benchmarks/ctlstar-pldi2014sub/': 'ctlstar-pldi2014sub'}
GENSYS_COMMIT = '1c80c45f34a8462d7e93de68daebec7140d5ee62'
NOTES = 'script/fetch/ehsf.notes.md'
GENSYS_RAW = 'https://raw.githubusercontent.com/stanlysamuel/gensys/%s/tools/consynth/Benchmarks/%s'
MANIFEST = 'script/fetch/consynth.manifest'
CONSYNTH_DIR = 'benchmarks/ECHC/consynth-src'
CLASSES = ('ECHC', 'pfwnCSP', 'CHC')
CONVERTER = 'script/qarmc_to_smt2.py'


def blob_sha1(data):
    return hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()


def manifest():
    out = []
    with open(MANIFEST) as fh:
        for line in fh:
            if line.startswith('#') or not line.strip():
                continue
            path, sha, size = line.rstrip('\n').split('\t')
            out.append((path, sha, int(size)))
    return out


def fetch():
    bad = 0
    for path, sha, _ in manifest():
        dst = os.path.join(CONSYNTH_DIR, path)
        if os.path.isfile(dst):
            with open(dst, 'rb') as fh:
                if blob_sha1(fh.read()) == sha:
                    continue
        with urllib.request.urlopen(GENSYS_RAW % (GENSYS_COMMIT, path), timeout=60) as r:
            data = r.read()
        if blob_sha1(data) != sha:
            print('fetched %s does not match the manifest' % path, file=sys.stderr)
            bad += 1
            continue
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(dst, 'wb') as fh:
            fh.write(data)
    return bad


def expected_of(stem):
    if stem.endswith('-succeed'):
        return 'sat'
    if stem.endswith('-fail'):
        return 'unsat'
    return '-'


def sources(zpath, consynth_dir=CONSYNTH_DIR):
    """(src, dir, stem, bytes) of every input present."""
    out = []
    if os.path.isfile(zpath):
        with open(zpath, 'rb') as fh:
            digest = hashlib.sha256(fh.read()).hexdigest()
        if digest != ZIP_SHA256:
            raise SystemExit('archive digest %s differs from the pinned %s' % (digest, ZIP_SHA256))
        with zipfile.ZipFile(zpath) as z:
            for info in z.infolist():
                for prefix, dname in ZIP_DIRS.items():
                    rest = info.filename[len(prefix):]
                    if info.filename.startswith(prefix) and rest.endswith('.qarmc') and '/' not in rest:
                        out.append(('zip', dname, rest[:-len('.qarmc')], z.read(info)))
    else:
        print('archive not found, skipped: %s' % zpath, file=sys.stderr)
    if os.path.isdir(consynth_dir):
        for path, sha, _ in manifest():
            p = os.path.join(consynth_dir, path)
            if not os.path.isfile(p):
                print('missing, skipped: %s' % p, file=sys.stderr)
                continue
            with open(p, 'rb') as fh:
                data = fh.read()
            if blob_sha1(data) != sha:
                raise SystemExit('%s does not match the manifest' % p)
            d, f = os.path.split(path)
            out.append(('consynth', d, f[:-len('.qarmc')], data))
    else:
        print('%s absent (run with --fetch), skipped' % consynth_dir, file=sys.stderr)
    # The archive's ctlstar-cav13 and ctl/ctlstar-cav13-template are ConSynth's directories of the
    # same names; a file byte-identical to its fetched counterpart is converted once, from there.
    fetched = {(d, stem): data for src, d, stem, data in out if src == 'consynth'}
    zip_rel = {v: k[len('Benchmarks/'):-1] for k, v in ZIP_DIRS.items()}
    kept = []
    for m in out:
        if m[0] == 'zip' and fetched.get((zip_rel[m[1]], m[2])) == m[3]:
            kept.append(('dup', m[1], m[2], None))
        else:
            kept.append(m)
    return sorted(kept, key=lambda m: m[:3])


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--zip', default=ZIP_DEFAULT)
    ap.add_argument('--fetch', action='store_true')
    ap.add_argument('--consynth', default=CONSYNTH_DIR)
    ap.add_argument('--sort', choices=['Int', 'Real'], default='Int')
    ap.add_argument('--no-stutter', action='store_true')
    ap.add_argument('--keep-exists', action='store_true')
    a = ap.parse_args()
    if not os.path.isfile(CONVERTER):
        print('run from the repository root', file=sys.stderr)
        return 2
    if a.fetch and a.consynth != CONSYNTH_DIR:
        print('--fetch writes to %s; it does not combine with --consynth' % CONSYNTH_DIR, file=sys.stderr)
        return 2
    if a.fetch and fetch():
        return 1
    srcs = sources(a.zip, a.consynth)
    outs = ['benchmarks/%s/ehsf' % c for c in CLASSES] + ['benchmarks/muCLP/ehsf']
    for d in outs:
        shutil.rmtree(d, ignore_errors=True)
    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        for src, dname, stem, data in srcs:
            if src == 'dup':
                rows.append(('zip', dname, stem, 'duplicate', '-', expected_of(stem), '-',
                             'byte-identical to the fetched ConSynth file of the same path'))
                continue
            inp = os.path.join(tmp, 'src.qarmc')
            with open(inp, 'wb') as fh:
                fh.write(data)
            smt = os.path.join(tmp, 'out.smt2')
            hes = os.path.join(tmp, 'out.hes')
            for p in (smt, hes):
                if os.path.exists(p):
                    os.remove(p)
            name = ('hsf-Benchmarks.zip:%s' % next(k for k, v in ZIP_DIRS.items() if v == dname)
                    if src == 'zip' else 'gensys@%s:tools/consynth/Benchmarks/%s/' % (GENSYS_COMMIT[:8], dname))
            r = subprocess.run([sys.executable, '-I', CONVERTER, inp, '-o', smt, '--hes', hes,
                                '--sort', a.sort, '--info', '--name', name + stem + '.qarmc']
                               + (['--no-stutter'] if a.no_stutter else [])
                               + (['--keep-exists'] if a.keep_exists else []),
                               capture_output=True, text=True)
            line = r.stdout.strip()
            exp = expected_of(stem)
            if r.returncode != 0:
                rows.append((src, dname, stem, 'refused', '-', exp, '-', line.split('\t', 1)[-1]))
                continue
            feats = dict(kv.split('=', 1) for kv in line.split('\t'))
            cls = feats['class']
            dst = 'benchmarks/%s/ehsf/%s/%s' % (cls, src, dname)
            os.makedirs(dst, exist_ok=True)
            shutil.move(smt, os.path.join(dst, stem + '.smt2'))
            if feats['hes'] == 'written':
                hd = 'benchmarks/muCLP/ehsf/%s/%s' % (src, dname)
                os.makedirs(hd, exist_ok=True)
                shutil.move(hes, os.path.join(hd, stem + '.hes'))
            rows.append((src, dname, stem, 'converted', cls, exp, feats['hes'], line))
    os.makedirs('benchmarks/ECHC/ehsf', exist_ok=True)
    with open('benchmarks/ECHC/ehsf/STATUS.tsv', 'w') as fh:
        fh.write('src\tdir\tstem\toutcome\tclass\texpected\thes\tdetail\n')
        for row in rows:
            fh.write('\t'.join(row) + '\n')
    # The note on file names that state a wrong or doubtful verdict travels with the generated
    # corpus, which is untracked and rebuilt from scratch on every run.
    shutil.copyfile(NOTES, 'benchmarks/ECHC/ehsf/NOTES.md')
    conv = [r for r in rows if r[3] == 'converted']
    print('%d sources: %d duplicates skipped, %d converted (%s), %d refused, %d .hes' % (
        len(rows), sum(1 for r in rows if r[3] == 'duplicate'), len(conv),
        ', '.join('%s %d' % (c, sum(1 for r in conv if r[4] == c)) for c in CLASSES),
        sum(1 for r in rows if r[3] == 'refused'), sum(1 for r in conv if r[6] == 'written')))
    return 0


if __name__ == '__main__':
    sys.exit(main())
