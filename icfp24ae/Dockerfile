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
	python3
RUN sudo ln -f /usr/bin/opam-2.3 /usr/bin/opam
COPY --chown=opam:opam . /home/opam/coar/
RUN opam update \
	&& opam install . --deps-only -j 4 \
	# && opam install . --deps-only \
	&& opam install dune \
	&& eval $(opam env) \
	&& dune build main.exe

# Build & run the image
# sudo docker build -f Dockerfile -t coar-icfp24ae ../
# sudo docker run --rm -it coar-icfp24ae:latest /bin/bash --login

# save
# sudo docker save coar-icfp24ae:latest -o coar-icfp24ae.tar