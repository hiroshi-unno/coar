# Dockerfile for termcomp
# Participation tracks: C, Integer_Transition_Systems
# - coar, its-conversion, and llvm2kittel available
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

# ---- final runtime ----
FROM coar:latest

# Without `--no-install-recommends`, apt installs `libz3-4` and coar will not run correctly.
RUN apt-get update && apt-get install -y --no-install-recommends clang-14

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
RUN mkdir -p /opt/coar/config && mv /root/coar/config /opt/coar
RUN chmod a+rw /opt/coar

# Test user for testing under a different user account
# RUN useradd -m testuser

COPY --chmod=755 script/termcomp/solver.sh /usr/bin/solver

WORKDIR /root/coar