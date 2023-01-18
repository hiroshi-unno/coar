FROM ubuntu:18.04

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y tzdata
RUN apt-get install -y build-essential gcc-4.8 g++-4.8 python cmake wget git software-properties-common groff sudo gnuplot
RUN add-apt-repository ppa:avsm/ppa
RUN apt-get update
RUN apt-get install -y opam libffi-dev libgmp-dev libblas-dev liblapack-dev pkg-config
# dpkg-reconfigure tzdata

# Add user and allow sudo without password
RUN useradd -m muval
#RUN chsh muval -s /bin/bash
RUN echo "muval ALL=NOPASSWD: ALL" > /etc/sudoers.d/muval
RUN chmod 0440 /etc/sudoers.d/muval

USER muval

RUN opam init --shell=bash --shell-setup --disable-sandboxing

# Download paper, artifact, llvm, and llvm2kittel
WORKDIR /home/muval
RUN git clone https://github.com/hiroshi-unno/coar.git -b CAV21AE
#RUN git clone https://<USER>:<PASSWORD>@bitbucket.org/uhiro/fptprove.git -b cav21ae coar
RUN wget --user-agent="Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/90.0.4430.85 Safari/537.36" https://arxiv.org/pdf/2104.11463.pdf
RUN wget -O - https://releases.llvm.org/3.6.2/llvm-3.6.2.src.tar.xz | tar Jxf -
RUN wget -O - https://releases.llvm.org/3.6.2/cfe-3.6.2.src.tar.xz | tar Jxf - -C /home/muval/llvm-3.6.2.src/tools
RUN mv /home/muval/llvm-3.6.2.src/tools/cfe-3.6.2.src /home/muval/llvm-3.6.2.src/tools/clang
RUN git clone https://github.com/gyggg/llvm2kittel.git -b kou

# Build artifact
WORKDIR /home/muval/coar
RUN eval $(opam env) && opam install . --deps-only -y && dune build main.exe
RUN git submodule init && git submodule update benchmarks/term-comp20

# Build & install llvm
WORKDIR /home/muval/llvm-3.6.2.src
RUN mkdir build
WORKDIR /home/muval/llvm-3.6.2.src/build
RUN CC=gcc-4.8 CXX=g++-4.8 ../configure --enable-optimized
RUN make -j4
USER root
RUN make install
USER muval

# Build llvm2kittel
WORKDIR /home/muval/llvm2kittel
RUN git checkout d4f243d
RUN mkdir build
WORKDIR /home/muval/llvm2kittel/build
RUN CC=gcc-4.8 CXX=g++-4.8 cmake -DCMAKE_PREFIX_PATH=/home/muval/llvm-3.6.2.src/build ../ && make -j4

WORKDIR /home/muval
# RUN rm -r llvm-3.6.2.src

# Build & run the image
# sudo docker build -t cav21ae .
# sudo docker run --rm -it cav21ae:latest /bin/bash --login
