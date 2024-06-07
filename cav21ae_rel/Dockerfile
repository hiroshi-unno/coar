FROM ubuntu:18.04

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y tzdata
RUN apt-get install -y build-essential gcc-4.8 g++-4.8 python cmake wget git software-properties-common groff sudo
RUN add-apt-repository ppa:avsm/ppa
RUN apt-get update
RUN apt-get install -y opam libffi-dev libgmp-dev libblas-dev liblapack-dev pkg-config
# dpkg-reconfigure tzdata

# Add user and allow sudo without password
RUN useradd -m pcsat
#RUN chsh pcsat -s /bin/bash
RUN echo "pcsat ALL=NOPASSWD: ALL" > /etc/sudoers.d/pcsat
RUN chmod 0440 /etc/sudoers.d/pcsat

USER pcsat

RUN opam init --shell=bash --shell-setup --disable-sandboxing

# Download paper, artifact, llvm, and llvm2kittel
WORKDIR /home/pcsat
RUN git clone https://github.com/hiroshi-unno/coar.git -b CAV21AE
#RUN git clone https://<USER>:<PASSWORD>@bitbucket.org/uhiro/fptprove.git -b cav21ae coar
RUN wget --user-agent="Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/90.0.4430.85 Safari/537.36" https://www.riec.tohoku.ac.jp/~unno/papers/cav2021rel.pdf

# Build artifact
WORKDIR /home/pcsat/coar
RUN eval $(opam env) && opam install . --deps-only -y && dune build main.exe

WORKDIR /home/pcsat

# Build & run the image
# sudo docker build -t cav21ae_pcsat .
# sudo docker run --rm -it cav21ae_pcsat:latest /bin/bash --login
