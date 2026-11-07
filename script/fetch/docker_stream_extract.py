#!/usr/bin/env python3
"""Extract a few directories from a `docker save` image archive read as a stream, never stored.

    curl -sSL URL | python3 -I docker_stream_extract.py --prefix home/opam/sprout/ \
        --take 'examples/' --take 'query-generator/[^/]*$' --out DIR \
        [--md5 HEX] [--size BYTES] [--listing FILE] [--gunzip]

WHY A STREAM.  An image archive is a tar of layer tarballs (each possibly gzip-compressed) plus a
manifest.json naming the layers in order.  The archive this was written for is 2.7 GB and only a
few hundred kilobytes of it are wanted, so it is read once from standard input: each outer member
that is a tarball is opened as a nested stream, and the members under PREFIX that match a --take
pattern (a regular expression matched at the start of the path relative to PREFIX) are kept in
memory, per layer.  Nothing of the archive is written to disk.

LAYER ORDER.  manifest.json may come after the layers in the stream, so the kept members are
applied only at the end, in the manifest's order, with the overlay rules of the image format: a
later layer replaces a path, a whiteout `.wh.NAME` deletes NAME (and everything below it) from the
layers beneath, and `.wh..wh..opq` empties its directory of what the layers beneath put there.

GZIP.  With --gunzip the archive on standard input is gzip-compressed (a `docker save | gzip`), and it is
decompressed as it is read; the checksum and the size are then those of the compressed bytes, which is what a
record publishes for such a file.

CHECKSUM.  The whole of standard input is hashed (md5, the checksum Zenodo publishes) and counted,
the rest after the tar's end included; a mismatch with --md5 or --size exits 1 after reporting,
and then DIR is not written.

LISTING.  With --listing, every regular file under PREFIX in the final image (all paths, not only
the taken ones) is written with its size and sha256, so what the image carries besides the taken
files is on record without being stored.  A path containing `/_build/` is left out of the listing.

Exit 0 on success, 1 on a checksum or structure failure, 2 on a usage error.
"""
import argparse
import gzip
import hashlib
import json
import os
import re
import sys
import tarfile


class HashingReader:
    """A read-only file object over another that hashes and counts every byte read through it."""

    def __init__(self, raw):
        self.raw = raw
        self.md5 = hashlib.md5()
        self.n = 0

    def read(self, size=-1):
        b = self.raw.read(size)
        self.md5.update(b)
        self.n += len(b)
        return b

    def drain(self):
        while True:
            b = self.read(1 << 20)
            if not b:
                return


def norm(name):
    while name.startswith("./"):
        name = name[2:]
    return name.lstrip("/")


def read_layer(f, prefix, takes, events):
    """Read one layer tarball as a stream.  Returns the list of this layer's events under PREFIX:
    ('file', rel, bytes_or_None, size, sha256), ('dir', rel), ('symlink', rel, target),
    ('whiteout', rel) and ('opaque', reldir).  Content is kept only for taken paths."""
    hard = {}
    with tarfile.open(fileobj=f, mode="r|*") as t:
        for m in t:
            name = norm(m.name)
            if not name.startswith(prefix):
                if m.isfile():
                    hard[name] = None
                continue
            rel = name[len(prefix):].rstrip("/")
            base = os.path.basename(rel)
            parent = os.path.dirname(rel)
            if base == ".wh..wh..opq":
                events.append(("opaque", parent))
                continue
            if base.startswith(".wh."):
                events.append(("whiteout", os.path.join(parent, base[4:])))
                continue
            taken = any(r.match(rel) for r in takes)
            if m.isdir():
                events.append(("dir", rel))
            elif m.issym():
                events.append(("symlink", rel, m.linkname))
            elif m.islnk():
                src = norm(m.linkname)
                got = hard.get(src)
                if got is None or (taken and got[0] is None):
                    events.append(("file", rel, None, -1, "hardlink-unresolved:" + src))
                else:
                    events.append(("file", rel, got[0] if taken else None, got[1], got[2]))
            elif m.isfile():
                g = t.extractfile(m)
                hs = hashlib.sha256()
                chunks = []
                while True:
                    b = g.read(1 << 20)
                    if not b:
                        break
                    hs.update(b)
                    if taken:
                        chunks.append(b)
                data = b"".join(chunks) if taken else None
                hard[name] = (data, m.size, hs.hexdigest())
                events.append(("file", rel, data, m.size, hs.hexdigest()))
    return events


def under(path, d):
    return path == d or path.startswith(d + "/")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prefix", required=True)
    ap.add_argument("--take", action="append", default=[])
    ap.add_argument("--out", required=True)
    ap.add_argument("--md5")
    ap.add_argument("--size", type=int)
    ap.add_argument("--listing")
    ap.add_argument("--gunzip", action="store_true")
    a = ap.parse_args()
    prefix = norm(a.prefix)
    if not prefix.endswith("/"):
        prefix += "/"
    takes = [re.compile(p) for p in a.take]
    if os.path.exists(a.out):
        print(f"refusing: {a.out} exists", file=sys.stderr)
        return 2

    src = HashingReader(sys.stdin.buffer)
    layers = {}
    manifest = None
    outer_names = []
    stream = gzip.GzipFile(fileobj=src, mode="rb") if a.gunzip else src
    with tarfile.open(fileobj=stream, mode="r|") as outer:
        for m in outer:
            name = norm(m.name)
            outer_names.append(name)
            if not m.isfile():
                continue
            f = outer.extractfile(m)
            if name == "manifest.json":
                manifest = json.loads(f.read())
                continue
            if name.endswith(".json"):
                continue
            try:
                ev = read_layer(f, prefix, takes, [])
            except (tarfile.ReadError, EOFError, OSError):
                continue  # a blob that is not a tarball (an image config or an index)
            layers[name] = ev
            n = sum(1 for e in ev if e[0] == "file" and e[2] is not None)
            print(f"   layer {name}: {len(ev)} entries under the prefix, {n} taken", file=sys.stderr)
    if a.gunzip:
        while stream.read(1 << 20):
            pass
    src.drain()
    print(f"   read {src.n} bytes, md5 {src.md5.hexdigest()}", file=sys.stderr)
    bad = False
    if a.md5 and src.md5.hexdigest() != a.md5:
        print(f"   CHECKSUM MISMATCH: md5 {src.md5.hexdigest()}, expected {a.md5}", file=sys.stderr)
        bad = True
    if a.size is not None and src.n != a.size:
        print(f"   SIZE MISMATCH: {src.n} bytes, expected {a.size}", file=sys.stderr)
        bad = True
    if manifest is None or not isinstance(manifest, list) or len(manifest) != 1:
        print("   no single-image manifest.json in the archive", file=sys.stderr)
        bad = True
    if bad:
        return 1
    order = [norm(x) for x in manifest[0]["Layers"]]
    missing = [x for x in order if x not in layers and x in outer_names]
    absent = [x for x in order if x not in outer_names]
    if absent:
        print(f"   manifest names layers absent from the archive: {absent}", file=sys.stderr)
        return 1
    for x in missing:  # in the archive but not readable as a tarball: an empty layer or a failure
        layers[x] = []

    # Apply the layers in order.  state: path -> event.
    state = {}
    for x in order:
        for e in layers[x]:
            kind, rel = e[0], e[1]
            if kind == "whiteout":
                for p in [p for p in state if under(p, rel)]:
                    del state[p]
            elif kind == "opaque":
                for p in [p for p in state if p != rel and under(p, rel)]:
                    del state[p]
        for e in layers[x]:
            if e[0] in ("file", "dir", "symlink"):
                for p in [p for p in state if p != e[1] and under(p, e[1]) and e[0] != "dir"]:
                    del state[p]
                state[e[1]] = e

    tmp = a.out + ".partial"
    if os.path.exists(tmp):
        print(f"refusing: {tmp} exists", file=sys.stderr)
        return 2
    nfiles = 0
    for rel, e in sorted(state.items()):
        if e[0] == "file" and e[2] is not None:
            p = os.path.join(tmp, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "wb") as g:
                g.write(e[2])
            nfiles += 1
        elif e[0] == "symlink" and any(r.match(rel) for r in takes):
            p = os.path.join(tmp, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            os.symlink(e[2], p)
            nfiles += 1
    os.makedirs(tmp, exist_ok=True)
    if a.listing:
        with open(a.listing, "w") as g:
            g.write("# every regular file under " + prefix + " in the image (paths with /_build/ omitted)\n")
            g.write("# path <TAB> size <TAB> sha256 ; symlinks as path <TAB> -> <TAB> target\n")
            for rel, e in sorted(state.items()):
                if "/_build/" in "/" + rel + "/":
                    continue
                if e[0] == "file":
                    g.write(f"{rel}\t{e[3]}\t{e[4]}\n")
                elif e[0] == "symlink":
                    g.write(f"{rel}\t->\t{e[2]}\n")
    os.rename(tmp, a.out)
    print(f"   wrote {nfiles} files to {a.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
