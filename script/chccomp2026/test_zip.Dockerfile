# Test self-contained zip file for submission to CHC-COMP206.
FROM ubuntu:24.04

RUN apt update \
 && apt install -y \
        gdb \
        unzip

RUN apt clean \
&& rm -rf /var/lib/apt/lists/*

WORKDIR /root
COPY --chmod=755 ./script/chccomp2026/coar.zip .
RUN unzip coar

WORKDIR /root/coar
