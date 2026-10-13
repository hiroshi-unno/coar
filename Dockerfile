# syntax=docker/dockerfile:1
# building coar
FROM ocaml/opam:ubuntu-25.10-ocaml-5.4 AS builder
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
 && opam install . --deps-only
# build coar
COPY --chown=opam:opam . /home/opam/coar/
RUN eval $(opam env) && dune build main.exe

FROM ubuntu:25.10
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
COPY --from=builder /home/opam/.opam/5.4/lib/stublibs/libz3.so /usr/lib/x86_64-linux-gnu/
COPY --from=builder /home/opam/.opam/5.4/lib/stublibs/libz3.so /usr/lib/aarch64-linux-gnu/
# Copy the stub library to call apron from coar
COPY --from=builder /home/opam/.opam/5.4/share/apron/lib/*.so /usr/lib/x86_64-linux-gnu/
COPY --from=builder /home/opam/.opam/5.4/share/apron/lib/*.so /usr/lib/aarch64-linux-gnu/
# Copy coar
COPY --from=builder /home/opam/coar/_build/default/main.exe /root/coar/
COPY README.md LICENSE CoAR.opam /root/coar/
COPY config /root/coar/config
# Copy ocaml library for ocaml program verification
COPY --from=builder /home/opam/.opam/5.4/lib/ocaml /home/opam/.opam/5.4/lib/ocaml

# Prepare another copies for redistribution with self-contained zip file
COPY --from=builder /home/opam/.opam/5.4/share/apron/lib/*.so /opt/apron/lib/

# Optional cvc5 (off by default): some solver paths call `cvc5` from PATH or as `./cvc5` from the
# working directory, so the static release binary is placed in /root/coar, which is on PATH.
#   docker build --build-arg WITH_CVC5=1 [--build-arg CVC5_VERSION=1.4.1] .
ARG WITH_CVC5=0
ARG CVC5_VERSION=1.4.1
ARG TARGETARCH
RUN if [ "$WITH_CVC5" = "1" ]; then \
      case "${TARGETARCH:-amd64}" in amd64) a=x86_64 ;; arm64) a=arm64 ;; *) echo "no cvc5 build for ${TARGETARCH}" >&2; exit 1 ;; esac \
   && apt update && apt install -y curl unzip ca-certificates \
   && curl -fsSL -o /tmp/cvc5.zip "https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VERSION}/cvc5-Linux-${a}-static.zip" \
   && unzip -q /tmp/cvc5.zip -d /tmp/cvc5 \
   && install -m 755 "$(find /tmp/cvc5 -type f -path '*/bin/cvc5' | head -1)" /root/coar/cvc5 \
   && rm -rf /tmp/cvc5 /tmp/cvc5.zip \
   && apt purge -y curl unzip && apt autoremove -y && apt clean && rm -rf /var/lib/apt/lists/* \
   && /root/coar/cvc5 --version ; \
    fi

ENV PATH="${PATH}:/root/coar"
WORKDIR /root/coar
CMD ["/bin/bash"]
