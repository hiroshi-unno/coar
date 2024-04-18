# syntax=docker/dockerfile:1
# building fptprove 
FROM ocaml/opam:ubuntu-22.04-ocaml-5.1 AS builder
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
# RUN opam repo add alpha git+https://github.com/kit-ty-kate/opam-alpha-repository.git
COPY --chown=opam:opam ./CoAR.opam /home/opam/fptprove/CoAR.opam
WORKDIR /home/opam/fptprove
# build libraries
RUN opam update \
 && opam install . --deps-only \
 && opam install dune
# build fptprove
COPY --chown=opam:opam . /home/opam/fptprove/
RUN eval $(opam env) && dune build main.exe

FROM ubuntu:22.04
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
# Copy a stub library to call libz3 from a ocaml program
COPY --from=builder /home/opam/.opam/5.1/lib/stublibs/libz3.so /usr/lib/x86_64-linux-gnu/
COPY --from=builder /home/opam/.opam/5.1/lib/stublibs/libz3.so /usr/lib/aarch64-linux-gnu/
# Copy fptprove
COPY --from=builder /home/opam/fptprove/_build/default/main.exe /root/fptprove/
COPY README.md LICENSE CoAR.opam /root/fptprove/
COPY config /root/fptprove/config

CMD ["/bin/bash"]
