FROM ocaml/opam:ubuntu-25.10-ocaml-5.4

WORKDIR /home/opam/coar
USER opam:opam

RUN sudo apt update \
	&& sudo apt install -y \
	gnuplot \
	zstd \
	libblas-dev \
	libffi-dev \
	libglpk-dev \
	libgmp-dev \
	liblapack-dev \
	libmpfr-dev \
	pkg-config \
	python3

RUN sudo ln -f /usr/bin/opam-2.5 /usr/bin/opam

COPY --chown=opam:opam . /home/opam/coar/

RUN sudo chown -R opam:opam /home/opam/coar && \
	rm -rf /home/opam/coar/_build && \
	opam update \
	&& opam install . --deps-only -j 4 \
	&& opam install dune \
	&& eval $(opam env) \
	&& dune build main.exe

# Build & run the image
# sudo docker build -f cav26ae/Dockerfile -t mucyc-cav26ae .
# sudo docker run --rm -it mucyc-cav26ae:latest /bin/bash --login

# Reproduce LRA (inside container)
#
# wget https://zenodo.org/records/16740866/files/LRA.tar.zst
# tar --zstd -xf LRA.tar.zst
# mkdir -p benchmarks/QSMT/LRA
# cp -r non-incremental/LRA/* benchmarks/QSMT/LRA/
#
# cd cav26ae
# ./LRA_mucyc.sh > LRA_mucyc.csv
# ./LRA_mucyc_np.sh > LRA_mucyc_np.csv
# ./LRA_z3.sh > LRA_z3.csv
# ./gen_figs_LRA.sh
