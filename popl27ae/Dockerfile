FROM ocaml/opam:ubuntu-26.04-ocaml-5.4

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
	gnuplot
# RUN sudo ln -f /usr/bin/opam-2.6 /usr/bin/opam
COPY --chown=opam:opam . /home/opam/coar/
RUN opam update \
	&& opam install . --deps-only -j 4 \
	# && opam install . --deps-only \
	&& opam install dune \
	&& eval $(opam env) \
	&& dune build main.exe

# Build & run the image
# sudo docker build -f Dockerfile -t popl27ae ../
# sudo docker run --rm -it popl27ae:latest /bin/bash --login

# save
# sudo docker save popl27ae:latest -o popl27ae.tar
