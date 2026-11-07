#!/usr/bin/env bash
# Runs dune on the llvm2lts package inside the image that holds LLVM 19.1.7
# and its OCaml bindings (opam llvm.19-static), which the host does not have.
#
#   script/llvm2lts/dune.sh            build the package
#   script/llvm2lts/dune.sh runtest    build and run its tests
#   script/llvm2lts/dune.sh runtest --auto-promote
#                                      ... and accept the tests' new output
#                                      (`dune promote` cannot be pointed at
#                                      this build directory)
#   script/llvm2lts/dune.sh ARGS...    any other dune arguments
#
# The build directory is _build_llvm2lts, apart from the host's _build, whose
# objects come from a different OCaml installation.  The container gets two
# CPUs and 4 GB, runs as the calling user, and is removed when dune exits.
# LLVM2LTS_IMAGE overrides the image.
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
image=${LLVM2LTS_IMAGE:-llvm19-pin:19.1.7}

case "${1:-}" in
  "") set -- build @athena/llvm2lts/all ;;
  runtest) shift; set -- runtest athena/llvm2lts "$@" ;;
esac
# Only the commands that build take these; `dune promote` refuses them.
case "$1" in
  build|runtest|test) set -- "$@" --only-packages llvm2lts -j 2 ;;
esac

exec docker run --rm --cpus=2 --memory=4g \
  --user "$(id -u):$(id -g)" -e HOME=/tmp -e DUNE_BUILD_DIR=_build_llvm2lts -e LLVM2LTS_BUILD=1 \
  -e PATH=/opt/opam/5.4.0/bin:/usr/local/bin:/usr/bin:/bin \
  -v "$root":/w -w /w "$image" \
  dune "$@"
