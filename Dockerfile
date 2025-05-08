# syntax=docker/dockerfile:1
# building coar
FROM ocaml/opam:ubuntu-24.10-ocaml-5.3 AS builder
USER opam:opam
RUN sudo apt update && sudo apt install -y \
        libblas-dev \
        libffi-dev \
        libglpk-dev \
        libgmp-dev \
        liblapack-dev \
        libmpfr-dev \
        pkg-config \
        python3 \
 && sudo apt clean \
 && sudo rm -rf /var/lib/apt/lists/*
RUN sudo ln -f /usr/bin/opam-2.3 /usr/bin/opam
# RUN opam repo add alpha git+https://github.com/kit-ty-kate/opam-alpha-repository.git
COPY --chown=opam:opam ./CoAR.opam /home/opam/coar/CoAR.opam
WORKDIR /home/opam/coar
# build libraries
RUN opam update \
 && opam install . --deps-only \
 && opam install dune
# build coar
COPY --chown=opam:opam . /home/opam/coar/
RUN eval $(opam env) && dune build main.exe

FROM ubuntu:24.10
RUN apt update \
 && apt install -y \
        libblas-dev \
        libffi-dev \
        libglpk-dev \
        libgmp-dev \
        liblapack-dev \
        libmpfr-dev \
        pkg-config \
 && apt clean \
 && rm -rf /var/lib/apt/lists/*
# Copy the stub library to call libz3 from coar
COPY --from=builder /home/opam/.opam/5.3/lib/stublibs/libz3.so /usr/lib/x86_64-linux-gnu/
COPY --from=builder /home/opam/.opam/5.3/lib/stublibs/libz3.so /usr/lib/aarch64-linux-gnu/
# Copy coar
COPY --from=builder /home/opam/coar/_build/default/main.exe /root/coar/
COPY README.md LICENSE CoAR.opam /root/coar/
COPY config /root/coar/config
# Copy ocaml library for ocaml program verification
COPY --from=builder /home/opam/.opam/5.3/lib/ocaml /home/opam/.opam/5.3/lib/ocaml

ENV PATH="${PATH}:/root/coar"
CMD ["/bin/bash"]
