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
	python3.13-venv
RUN sudo ln -f /usr/bin/opam-2.5 /usr/bin/opam
COPY --chown=opam:opam . /home/opam/coar/
RUN opam update \
	&& opam install . --deps-only -j 4 \
	# && opam install . --deps-only \
	&& opam install dune \
	&& eval $(opam env) \
	&& dune build main.exe

# PolyQEnt on zenodo: https://doi.org/10.5281/zenodo.13960405
RUN git clone https://github.com/ChatterjeeGroup-ISTA/polyqent.git -b v0.0.15
RUN python3 -m venv .venv && . .venv/bin/activate && cd polyqent && pip install .

# Build & run the image
# sudo docker build -f Dockerfile -t muval-pldi26ae ../
# sudo docker run --rm -it muval-pldi26ae:latest /bin/bash --login

# save
# sudo docker save muval-pldi26ae:latest -o muval-pldi26ae.tar
