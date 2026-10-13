# CAV 2021 artifact (MuVal, decision-tree termination) built from the CURRENT tree.
#
# Until 2026-09-13 this file cloned github.com/hiroshi-unno/coar at the tag
# CAV21AE, so the image contained the 2021 snapshot: the runner scripts in that
# snapshot name configs that were renamed away years ago, while the maintained
# copies in this repository (script/muval_dt_*_term_comp_20*) name configs that
# exist, and its .gitmodules still called the benchmark submodule
# `benchmarks/term-comp20`, a name this repository dropped in 2022.  None of the
# maintained files reached the image.  The decision of 2026-09-13 is that the
# permanent version of each artifact lives on Zenodo, and that the copy in this
# repository builds the latest source even if the numbers then differ from the
# paper's.
#
# Build (context is the repository root):
#   sudo docker build -f cav21ae_dt/Dockerfile -t cav21ae .
#   sudo docker run --rm -it cav21ae:latest /bin/bash --login
#
# `Dockerfile.dockerignore` beside this file is what keeps `cav21ae_dt/` and the
# needed parts of `script/` in the build context; the repository's root
# `.dockerignore` excludes both, for the released image's benefit.

# ---------------------------------------------------------------------------
# Stage 1: llvm2kittel, and the clang whose bitcode it can read.
#
# llvm2kittel links against LLVM 3.6.2 and reads LLVM 3.6 bitcode, so the C
# benchmarks have to be compiled by a clang of that vintage; neither builds with
# a current toolchain, which is why this stays on the era's base image and only
# the two binaries are carried forward.  Ubuntu 18.04 left standard support in
# 2023, so its archive now answers from old-releases.ubuntu.com.
# ---------------------------------------------------------------------------
FROM ubuntu:18.04 AS llvm2kittel

RUN sed -i 's|http://archive.ubuntu.com/ubuntu/|http://old-releases.ubuntu.com/ubuntu/|g; s|http://security.ubuntu.com/ubuntu/|http://old-releases.ubuntu.com/ubuntu/|g' /etc/apt/sources.list \
 && apt-get update \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y tzdata \
 && apt-get install -y build-essential gcc-4.8 g++-4.8 python cmake wget git

WORKDIR /root
RUN wget -O - https://releases.llvm.org/3.6.2/llvm-3.6.2.src.tar.xz | tar Jxf - \
 && wget -O - https://releases.llvm.org/3.6.2/cfe-3.6.2.src.tar.xz | tar Jxf - -C /root/llvm-3.6.2.src/tools \
 && mv /root/llvm-3.6.2.src/tools/cfe-3.6.2.src /root/llvm-3.6.2.src/tools/clang

WORKDIR /root/llvm-3.6.2.src/build
RUN CC=gcc-4.8 CXX=g++-4.8 ../configure --enable-optimized \
 && make -j"$(nproc)" \
 && make install

WORKDIR /root
RUN git clone https://github.com/gyggg/llvm2kittel.git -b kou \
 && cd llvm2kittel \
 && git checkout d4f243d \
 && mkdir build \
 && cd build \
 && CC=gcc-4.8 CXX=g++-4.8 cmake -DCMAKE_PREFIX_PATH=/root/llvm-3.6.2.src/build ../ \
 && make -j"$(nproc)"

# ---------------------------------------------------------------------------
# Stage 2: the artifact, from this repository's working tree.
# ---------------------------------------------------------------------------
FROM ocaml/opam:ubuntu-25.10-ocaml-5.4

WORKDIR /home/opam/coar
USER opam:opam

RUN sudo apt update \
	&& sudo apt install -y \
	gnuplot \
	libblas-dev \
	libffi-dev \
	libglpk-dev \
	libgmp-dev \
	liblapack-dev \
	libmpfr-dev \
	pkg-config \
	python3 \
	wget

RUN sudo ln -f /usr/bin/opam-2.5 /usr/bin/opam

# LLVM 3.6.2 with its clang, then llvm2kittel where the runner expects it
COPY --from=llvm2kittel /usr/local /usr/local
COPY --from=llvm2kittel /root/llvm2kittel/build/llvm2kittel /home/opam/llvm2kittel/build/llvm2kittel
RUN sudo ldconfig

COPY --chown=opam:opam . /home/opam/coar/

RUN sudo chown -R opam:opam /home/opam/coar && \
	rm -rf /home/opam/coar/_build && \
	opam update \
	&& opam install . --deps-only -j 4 \
	&& opam install dune \
	&& eval $(opam env) \
	&& dune build main.exe

# The benchmarks: the artifact reads only TPDB's C_Integer category, and this
# repository tracks it as the submodule `benchmarks/term-comp`, whose content
# `COPY` cannot bring in (the root context filter drops `.git`, so a submodule
# checkout cannot be completed inside the image).  Fetch that one category
# instead -- it is byte-identical to the revision the 2020 competition used.
RUN if [ ! -e benchmarks/term-comp/C_Integer ]; then \
	git clone --depth 1 --filter=blob:none --sparse https://github.com/TermCOMP/TPDB.git /tmp/tpdb \
	&& git -C /tmp/tpdb sparse-checkout set C_Integer \
	&& mkdir -p benchmarks/term-comp \
	&& cp -r /tmp/tpdb/C_Integer benchmarks/term-comp/ \
	&& rm -rf /tmp/tpdb; \
	fi

RUN wget -q -P /home/opam https://arxiv.org/pdf/2104.11463.pdf || \
	echo "could not download the paper; see https://arxiv.org/abs/2104.11463"

# Reproduce the experiments (inside the container)
#
# cd /home/opam/coar
# script/muval_dt_eager_term_comp_20.sh | tee result_eager.csv
# script/muval_dt_lazy_term_comp_20.sh  | tee result_lazy.csv
# script/muval_dt_eager_term_comp_20_compare.sh result_eager.csv
