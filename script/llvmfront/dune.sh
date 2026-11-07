#!/usr/bin/env bash
# Runs dune on CoAR with the direct LLVM frontend (lib/LLVMFront) inside the
# development image that holds both CoAR's opam dependencies and LLVM 19.1.7
# with its OCaml bindings (opam llvm.19-static); the host has no LLVM 19.
#
#   script/llvmfront/dune.sh            build main.exe
#   script/llvmfront/dune.sh ARGS...    any other dune arguments
#
# The build directory is _build_llvmfront, apart from the host's _build, whose
# objects come from a different OCaml installation.  The container gets two
# CPUs and 4 GB, runs as the calling user, and is removed when dune exits.
# LLVMFRONT_IMAGE overrides the image (LLVM 19.1.7 with its OCaml bindings and
# CoAR.opam's dependencies in one opam switch).
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
image=${LLVMFRONT_IMAGE:-coar-llvm-dev:20261022}

case "${1:-}" in
  "") set -- build main.exe ;;
esac
case "$1" in
  build|runtest|test) set -- "$@" -j 2 ;;
esac

exec docker run --rm --cpus=2 --memory=4g \
  --user "$(id -u):$(id -g)" -e HOME=/tmp -e DUNE_BUILD_DIR=_build_llvmfront \
  -e PATH=/opt/opam/5.4.0/bin:/usr/local/bin:/usr/bin:/bin \
  -e OPAMROOT=/opt/opam -e OPAM_SWITCH_PREFIX=/opt/opam/5.4.0 \
  -e CAML_LD_LIBRARY_PATH=/opt/opam/5.4.0/lib/stublibs:/opt/opam/5.4.0/lib/ocaml/stublibs:/opt/opam/5.4.0/lib/ocaml \
  -e OCAMLPATH=/opt/opam/5.4.0/lib \
  -v "$root":/w -w /w "$image" \
  dune "$@"
