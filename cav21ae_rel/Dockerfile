# CAV 2021 artifact (PCSat, relational verification) built from the CURRENT tree.
#
# Until 2026-09-13 this file cloned github.com/hiroshi-unno/coar at the tag
# CAV21AE, so the image contained the 2021 snapshot and none of the maintained
# copies of this artifact's own files -- `exp.sh` beside this Dockerfile names
# configs (config/solver/pcsat_tb*.json) that exist here and not in that tag.
# The decision of 2026-09-13 is that the permanent version of each artifact lives
# on Zenodo, and that the copy in this repository builds the latest source even
# if the numbers then differ from the paper's.
#
# Build (context is the repository root):
#   sudo docker build -f cav21ae_rel/Dockerfile -t cav21ae_pcsat .
#   sudo docker run --rm -it cav21ae_pcsat:latest /bin/bash --login
#
# `Dockerfile.dockerignore` beside this file is what keeps `cav21ae_rel/` in the
# build context; the repository's root `.dockerignore` excludes it, for the
# released image's benefit.

FROM ocaml/opam:ubuntu-25.10-ocaml-5.4

WORKDIR /home/opam/coar
USER opam:opam

RUN sudo apt update \
	&& sudo apt install -y \
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

COPY --chown=opam:opam . /home/opam/coar/

RUN sudo chown -R opam:opam /home/opam/coar && \
	rm -rf /home/opam/coar/_build && \
	opam update \
	&& opam install . --deps-only -j 4 \
	&& opam install dune \
	&& eval $(opam env) \
	&& dune build main.exe

# the paper, for the reader's convenience
RUN wget -q -P /home/opam https://www.riec.tohoku.ac.jp/~unno/papers/cav2021rel.pdf || \
	echo "could not download the paper; see https://www.riec.tohoku.ac.jp/~unno/papers/cav2021rel.pdf"

# Reproduce Table 1 (inside the container)
#
# cd /home/opam/coar/cav21ae_rel
# ./exp.sh
