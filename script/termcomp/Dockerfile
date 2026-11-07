# Dockerfile for termcomp
# Participation tracks: C, Integer_Transition_Systems
# - coar (with its direct LLVM frontend), its-conversion, llvm2kittel, the new Ptr2Arr and clang 19.1.7 available
# - For termCOMP, the `solver` command can be used to invoke MuVal for (non-)termination verification

# - In the referenced `cav21ae_dt/Dockerfile`, llvm-3.6.2 was built from source code, but using a prebuilt binary also seems to be fine.

FROM ubuntu:18.04 AS llvm2kittel-builder

# Install dependencies for llvm and llvm2kittel
RUN apt update && apt install -y \
        build-essential \
        git \
        wget \
        xz-utils \
        gcc-4.8 \
        g++-4.8 \
        cmake \
        libgmp-dev

RUN apt clean \
        && rm -rf /var/lib/apt/lists/*

WORKDIR /root

# Download prebuilt-binary of its-conversion v0.0.2
RUN mkdir -p /root/its-conversion && \
    cd /root/its-conversion && \
    wget -O its-conversion-static https://github.com/TermCOMP/its-conversion/releases/download/v0.0.2/its-conversion-static

# Download and extract prebuilt-binary of llvm-3.6.2
RUN mkdir -p /root/llvm-3.6.2 && \
    wget -O - https://releases.llvm.org/3.6.2/clang+llvm-3.6.2-x86_64-linux-gnu-ubuntu-15.04.tar.xz \
    | tar Jxf - --strip-components=1 -C /root/llvm-3.6.2
ENV PATH="/root/llvm-3.6.2/bin:$PATH"

# Copy and Build llvm2kittel
COPY athena/llvm2kittel /root/llvm2kittel
WORKDIR /root/llvm2kittel/build
RUN CC=gcc-4.8 CXX=g++-4.8 cmake -DCMAKE_PREFIX_PATH=/root/llvm-3.6.2.src/build .. && \
    make -j $(nproc)


# ---- Ptr2Arr builder ----
FROM ubuntu:22.04 AS ptr2arr-builder
RUN apt-get update && apt-get install -y \
    build-essential git wget \
    zlib1g-dev libffi-dev libxml2-dev libedit-dev \
    libclang-14-dev clang-14 llvm-14-dev

RUN apt clean \
        && rm -rf /var/lib/apt/lists/*

RUN wget https://github.com/Kitware/CMake/releases/download/v3.27.8/cmake-3.27.8-linux-x86_64.tar.gz \
 && tar -xzf cmake-3.27.8-linux-x86_64.tar.gz -C /opt \
 && ln -s /opt/cmake-3.27.8-linux-x86_64/bin/cmake /usr/local/bin/cmake


# Clone and build dg repository
WORKDIR /root
RUN git clone https://github.com/mchalupa/dg
WORKDIR /root/dg
RUN mkdir build
WORKDIR /root/dg/build
RUN cmake .. && make -j $(nproc)

# Copy and build Ptr2Arr
WORKDIR /root
COPY athena/Ptr2Arr /root/Ptr2Arr
RUN cd /root/Ptr2Arr \
 && mkdir build && cd build \
    && CLANG_RESOURCE_DIR=$(clang-14 -print-resource-dir) && \
       cmake .. -DCMAKE_C_COMPILER=clang-14 -DCMAKE_CXX_COMPILER=clang++-14 \
       -DCMAKE_CXX_FLAGS="-I${CLANG_RESOURCE_DIR}/include" \
       -DCMAKE_C_FLAGS="-I${CLANG_RESOURCE_DIR}/include" \
       && make -j $(nproc)

# Copy and build SemanticAugmentor
WORKDIR /root
COPY athena/SemanticAugmentor /root/SemanticAugmentor
RUN cd /root/SemanticAugmentor \
 && mkdir build && cd build \
    && CLANG_RESOURCE_DIR=$(clang-14 -print-resource-dir) && \
       cmake .. -DCMAKE_C_COMPILER=clang-14 -DCMAKE_CXX_COMPILER=clang++-14 \
       -DCMAKE_CXX_FLAGS="-I${CLANG_RESOURCE_DIR}/include" \
       -DCMAKE_C_FLAGS="-I${CLANG_RESOURCE_DIR}/include" \
       && make -j $(nproc)

# Copy and build TypeAnnotator
WORKDIR /root
COPY athena/TypeAnnotator /root/TypeAnnotator
RUN cd /root/TypeAnnotator \
 && mkdir build && cd build \
    && CLANG_RESOURCE_DIR=$(clang-14 -print-resource-dir) && \
       cmake .. -DCMAKE_C_COMPILER=clang-14 -DCMAKE_CXX_COMPILER=clang++-14 \
       -DCMAKE_CXX_FLAGS="-I${CLANG_RESOURCE_DIR}/include" \
       -DCMAKE_C_FLAGS="-I${CLANG_RESOURCE_DIR}/include" \
       && make -j $(nproc)

# ---- LLVM 19.1.7 release ----
# The official prebuilt release: its clang-19 compiles the output of the new Ptr2Arr to LLVM IR for
# CoAR's direct LLVM frontend, and its static libraries are what that frontend links (as in
# script/svcomp/Dockerfile).
FROM ubuntu:25.10 AS llvm19-release
RUN apt-get update && apt-get install -y curl xz-utils ca-certificates
ARG LLVM19_SHA256=4a5ec53951a584ed36f80240f6fbf8fdd46b4cf6c7ee87cc2d5018dc37caf679
RUN curl -fsSL -o /tmp/llvm.tar.xz \
      https://github.com/llvm/llvm-project/releases/download/llvmorg-19.1.7/LLVM-19.1.7-Linux-X64.tar.xz \
 && echo "${LLVM19_SHA256}  /tmp/llvm.tar.xz" | sha256sum -c - \
 && mkdir -p /opt/llvm-19.1.7 \
 && tar xJf /tmp/llvm.tar.xz --strip-components=1 -C /opt/llvm-19.1.7 \
 && rm /tmp/llvm.tar.xz

# ---- Ptr2ArrFC builder (the new Ptr2Arr, on Frama-C 33.0) ----
# The executable links the Frama-C kernel statically; at run time it needs Frama-C's share
# directory, copied beside it, and gcc as the C preprocessor.
FROM ocaml/opam:ubuntu-24.04-ocaml-5.4 AS ptr2arrfc-builder
USER opam:opam
RUN sudo apt-get update && sudo apt-get install -y \
        autoconf graphviz libgmp-dev pkg-config zlib1g-dev \
 && sudo rm -rf /var/lib/apt/lists/*
RUN sudo ln -f /usr/bin/opam-2.3 /usr/bin/opam
ENV OPAMJOBS=2
RUN opam update && opam install -y frama-c.33.0
COPY --chown=opam:opam athena/Ptr2ArrFC /home/opam/Ptr2ArrFC
WORKDIR /home/opam/Ptr2ArrFC
RUN eval $(opam env) \
 && dune build --root . bin/ptr2arr.exe \
 && mkdir -p /home/opam/out \
 && cp _build/default/bin/ptr2arr.exe /home/opam/out/ptr2arr_fc \
 && cp -r "$(opam var share)/frama-c" /home/opam/out/frama-c-share

# ---- CoAR with the direct LLVM frontend ----
# coar:latest is built without the LLVM 19 OCaml bindings, so the optional library lib/LLVMFront
# (-p llvm*) is not in it.  This builds coar again on the same system as coar:latest (Ubuntu 25.10)
# with llvm.19-static against the release's static libraries.  Those are LLVM bitcode for ThinLTO;
# the release's lld cannot start on Ubuntu 25.10 (it needs libxml2.so.2), so Ubuntu's lld-19, the
# same LLVM version, links them.
FROM ocaml/opam:ubuntu-25.10-ocaml-5.4 AS coar-llvm-builder
USER opam:opam
RUN sudo apt update && sudo apt install -y \
        cmake \
        libblas-dev \
        libffi-dev \
        libglpk-dev \
        libgmp-dev \
        liblapack-dev \
        libmpfr-dev \
        libxml2-dev \
        libzstd-dev \
        lld-19 \
        pkg-config \
        python3 \
        zlib1g-dev \
 && sudo apt clean \
 && sudo rm -rf /var/lib/apt/lists/*
RUN sudo ln -f /usr/bin/opam-2.3 /usr/bin/opam
COPY --from=llvm19-release /opt/llvm-19.1.7/bin/llvm-config /opt/llvm-19.1.7/bin/
COPY --from=llvm19-release /opt/llvm-19.1.7/include /opt/llvm-19.1.7/include
COPY --from=llvm19-release /opt/llvm-19.1.7/lib /opt/llvm-19.1.7/lib
RUN sudo ln -s /usr/lib/llvm-19/bin/ld.lld /opt/llvm-19.1.7/bin/ld.lld \
 && sudo ln -s /opt/llvm-19.1.7/bin/llvm-config /usr/local/bin/llvm-config-19
COPY --chown=opam:opam ./CoAR.opam /home/opam/coar/CoAR.opam
WORKDIR /home/opam/coar
# The LLVM above is not a system package, so the depext check is skipped for
# the bindings (conf-llvm-static finds it through llvm-config-19).
RUN opam update \
 && opam install . --deps-only \
 && opam install --no-depexts llvm.19-static
COPY --chown=opam:opam dune dune-project main.ml /home/opam/coar/
COPY --chown=opam:opam lib /home/opam/coar/lib
RUN eval $(opam env) \
 && PATH="$PATH:/opt/llvm-19.1.7/bin" OCAMLPARAM="_,ccopt=-fuse-ld=lld" dune build main.exe


# ---- final runtime ----
FROM coar:latest

# Without `--no-install-recommends`, apt installs `libz3-4` and coar will not run correctly.
# gcc is the new Ptr2Arr's C preprocessor (Frama-C runs `gcc -E`).
RUN apt-get update && apt-get install -y --no-install-recommends clang-14 gcc libc6-dev

RUN apt clean \
&& rm -rf /var/lib/apt/lists/*

# Copy binaries of its-conversion, llvm-3.6.2, and llvm2kittel from builder
COPY --chmod=755 --from=llvm2kittel-builder /root/its-conversion/its-conversion-static /usr/local/bin/its-conversion-static
COPY --chmod=755 --from=llvm2kittel-builder /root/llvm-3.6.2 /opt/llvm-3.6.2
COPY --chmod=755 --from=llvm2kittel-builder /root/llvm2kittel/build/llvm2kittel /usr/local/bin/llvm2kittel

# Copy Ptr2Arr and dg binaries
COPY --chmod=755 --from=ptr2arr-builder /root/Ptr2Arr/build/Ptr2Arr /usr/local/bin/Ptr2Arr
COPY --chmod=644 --from=ptr2arr-builder /root/Ptr2Arr/ptr2arr_runtime_stubs.h /usr/local/bin/ptr2arr_runtime_stubs.h
COPY --chmod=755 --from=ptr2arr-builder /root/dg/build /usr/local/bin/dg

# Copy SemanticAugmentor binaries
COPY --chmod=755 --from=ptr2arr-builder /root/SemanticAugmentor/build/SemanticAugmentor /usr/local/bin/SemanticAugmentor

# Copy TypeAnnotator binaries
COPY --chmod=755 --from=ptr2arr-builder /root/TypeAnnotator/build/TypeAnnotator /usr/local/bin/TypeAnnotator

# Copy shared libraries
COPY --from=ptr2arr-builder /usr/lib/llvm-14/lib/libLLVM-14.so.1 /usr/lib/x86_64-linux-gnu/
COPY --from=ptr2arr-builder /usr/lib/x86_64-linux-gnu/libedit.so.2 /usr/lib/x86_64-linux-gnu/
COPY --from=ptr2arr-builder /usr/lib/x86_64-linux-gnu/libxml2.so.2 /usr/lib/x86_64-linux-gnu/
COPY --from=ptr2arr-builder /usr/lib/x86_64-linux-gnu/libicuuc.so.70 /usr/lib/x86_64-linux-gnu/
COPY --from=ptr2arr-builder /usr/lib/x86_64-linux-gnu/libicudata.so.70 /usr/lib/x86_64-linux-gnu/

COPY --from=ptr2arr-builder /root/dg/build/tools/. /usr/lib/x86_64-linux-gnu/
COPY --from=ptr2arr-builder /root/dg/build/lib/. /usr/lib/x86_64-linux-gnu/

ENV PATH="/usr/local/bin/dg/tools:/opt/llvm-3.6.2/bin:/opt:${PATH}"

# When executed with apptainer exec --fakeroot, there is a risk that /root inside the container will be overwritten, so move the files under /root to /opt/coar.
RUN mv /root/coar/main.exe /usr/local/bin/coar
# The build with the direct LLVM frontend replaces it, with the libz3 and Apron stub libraries it
# was linked with (see coar-llvm-builder).
COPY --chmod=755 --from=coar-llvm-builder /home/opam/coar/_build/default/main.exe /usr/local/bin/coar
COPY --from=coar-llvm-builder /home/opam/.opam/5.4/lib/stublibs/libz3.so /usr/lib/x86_64-linux-gnu/
COPY --from=coar-llvm-builder /home/opam/.opam/5.4/share/apron/lib/ /usr/lib/x86_64-linux-gnu/

# The direct route of solver.sh (C, C_Mod, C_BV): the new Ptr2Arr with Frama-C's share directory
# (solver.sh sets DUNE_DIR_LOCATIONS to it), and clang 19.1.7 with its own headers, found relative
# to the binary.
RUN mkdir -p /opt/coar/bin /opt/coar/share
COPY --chmod=755 --from=ptr2arrfc-builder /home/opam/out/ptr2arr_fc /opt/coar/bin/ptr2arr_fc
COPY --from=ptr2arrfc-builder /home/opam/out/frama-c-share /opt/coar/share/frama-c
COPY --chmod=755 --from=llvm19-release /opt/llvm-19.1.7/bin/clang-19 /opt/coar/bin/llvm-19.1.7/bin/clang-19
COPY --from=llvm19-release /opt/llvm-19.1.7/lib/clang /opt/coar/bin/llvm-19.1.7/lib/clang
RUN mkdir -p /opt/coar/config && mv /root/coar/config /opt/coar
RUN chmod a+rw /opt/coar

# Test user for testing under a different user account
# RUN useradd -m testuser

COPY --chmod=755 script/termcomp/solver.sh /usr/bin/solver

WORKDIR /root/coar