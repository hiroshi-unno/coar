FROM coar:latest

# Without `--no-install-recommends`, apt installs `libz3-4` and coar will not run correctly.
RUN apt-get update && apt-get install -y --no-install-recommends wget zip ca-certificates

RUN apt clean \
&& rm -rf /var/lib/apt/lists/*

# Install APRON build dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential m4 ocaml ocaml-findlib git libgmp-dev libmpfr-dev

# Build APRON from source
RUN git clone https://github.com/antoinemine/apron.git /tmp/apron \
 && cd /tmp/apron \
 && ./configure -prefix /opt/apron \
 && make -j$(nproc) \
 && make install \
 && rm -rf /tmp/apron

# Copy shared libraries
RUN mkdir -p /root/coar/lib

RUN cp -r /usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2 /root/coar/lib
RUN cp /usr/lib/x86_64-linux-gnu/libz3.so /root/coar/lib
RUN cp -r /opt/apron/lib /root/coar/lib/apron
RUN cp -r /usr/lib/x86_64-linux-gnu/libmpfr.so /root/coar/lib/apron

ENV LD_LIBRARY_PATH="/root/coar/lib/apron:/root/coar/lib"

# Consolidate license files for dependencies
COPY script/chccomp2026/self_contained_zip.license /root/coar/LICENSE
RUN mkdir -p /root/coar/THIRD_PARTY_LICENSE
RUN wget -O /root/coar/THIRD_PARTY_LICENSE/z3.license https://raw.githubusercontent.com/Z3Prover/z3/refs/heads/master/LICENSE.txt
RUN wget -O /root/coar/THIRD_PARTY_LICENSE/apron.license https://raw.githubusercontent.com/antoinemine/apron/refs/heads/master/COPYING

# Test user for testing under a different user account
# RUN useradd -m testuser

# Copy only gather_dependencies.sh first (for caching purposes)
COPY --chmod=755 script/chccomp2026/gather_dependencies.sh /root/coar/helpers/gather_dependencies.sh

# Copy libraries and corresponding license files from apt packages
RUN /root/coar/helpers/gather_dependencies.sh --output=/root/coar/LICENSE\
        /root/coar/main.exe\
        2>&1 | tee /root/coar/gather_dependencies.log

RUN ln -s /root/coar/main.exe /usr/local/bin/coar

# Copy the wrapper script for running main.exe with the correct environment variables
COPY --chmod=755 script/chccomp2026/coar.sh /root/coar/coar.sh

WORKDIR /root/coar
