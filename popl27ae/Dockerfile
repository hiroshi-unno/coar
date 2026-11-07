FROM ocaml/opam:ubuntu-26.04-ocaml-5.4

WORKDIR /home/opam/coar
USER opam:opam
RUN sudo apt update \
	&& sudo apt install -y \
	ca-certificates \
	curl \
	libblas-dev \
	libffi-dev \
	libglpk-dev \
	libgmp-dev \
	liblapack-dev \
	libmpfr-dev \
	pkg-config \
	unzip \
	gnuplot
# RUN sudo ln -f /usr/bin/opam-2.6 /usr/bin/opam
# cvc5: PCSat asks cvc5 by default (a time-limited retry when Z3 leaves a validity query
# undecided), resolving it as ./cvc5 in the working directory or else `cvc5` on PATH; without it
# those retries prove nothing, so runs could answer less than in the development environment.
# The official static Linux release of cvc5, checksum-verified against the release's digests.
ARG CVC5_VERSION=1.4.2
ARG TARGETARCH
RUN case "${TARGETARCH:-amd64}" in \
	amd64) arch=x86_64; sum=7eb18f8c814c36a46c5a7d003983e9cfbc4b0a9828d6dd596239291bd4cc61d8 ;; \
	arm64) arch=arm64; sum=765ebee59d9e5efccb60a445fa66fbddfb07a8de9fe7a5b6d128e5c2aafec974 ;; \
	*) echo "no cvc5 release for ${TARGETARCH}" >&2; exit 1 ;; \
	esac \
	&& curl -fsSL -o /tmp/cvc5.zip "https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VERSION}/cvc5-Linux-${arch}-static.zip" \
	&& echo "${sum}  /tmp/cvc5.zip" | sha256sum -c - \
	&& unzip -q /tmp/cvc5.zip -d /tmp/cvc5 \
	&& sudo install -m 755 "/tmp/cvc5/cvc5-Linux-${arch}-static/bin/cvc5" /usr/local/bin/cvc5 \
	&& rm -rf /tmp/cvc5 /tmp/cvc5.zip \
	&& cvc5 --version
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
