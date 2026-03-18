#! /bin/bash
apt update

apt install -y \
        libblas-dev \
        libffi-dev \
        libglpk-dev \
        libgmp-dev \
        liblapack-dev \
        libmpfr-dev \
        pkg-config \
	opam

apt clean &&  rm -rf /var/lib/apt/lists/*

opam update
opam init -y && opam switch create 5.4.0
opam install --deps-only -y .
opam install dune

eval $(opam env) && dune build main.exe
