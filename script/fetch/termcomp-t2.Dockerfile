# The image script/gen_termcomp_t2.sh translates C programs in: CoAR's main.exe with its Athena route built in
# (Ptr2ArrFC on Frama-C 33.0, clang 19, llvm2lts), on Ubuntu 24.04's clang-19 and llvm-19-dev (19.1.1) and opam's
# llvm.19-shared bindings.  The build context is made by the generator: CoAR.opam and src/, a `git archive` of the
# sources main.exe needs, with the commit it came from in src/COAR_COMMIT.  About 35 minutes on 8 vCPUs without a
# cache (CoAR's opam dependencies most of it); the image is about 8 GB.
FROM ocaml/opam:ubuntu-24.04-ocaml-5.4
USER opam:opam
RUN sudo apt-get update && sudo apt-get install -y \
      autoconf cmake graphviz libblas-dev libffi-dev libglpk-dev libgmp-dev liblapack-dev libmpfr-dev \
      libxml2-dev libzstd-dev pkg-config python3 zlib1g-dev clang-19 llvm-19-dev libc6-dev-i386 \
 && sudo rm -rf /var/lib/apt/lists/*
RUN sudo ln -f /usr/bin/opam-2.3 /usr/bin/opam || true
ARG OPAMJOBS=4
ENV OPAMJOBS=${OPAMJOBS}
COPY --chown=opam:opam CoAR.opam /home/opam/coar/CoAR.opam
WORKDIR /home/opam/coar
RUN opam update && opam install -y . --deps-only
RUN opam install -y frama-c.33.0
RUN opam install -y --no-depexts llvm.19-shared
COPY --chown=opam:opam src /home/opam/coar
RUN eval $(opam env) && dune build main.exe 2>&1 | tail -30 && ls -la _build/default/main.exe
