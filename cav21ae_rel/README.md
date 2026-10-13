# CAV21 Artifact Evaluation: PCSat

We explain how to use PCSat, a pfwCSP constraint solver.
Technical details are explained in the following paper.

Hiroshi Unno, Tachio Terauchi, and Eric Koskinen. Constraint-based Relational Verification. CAV 2021.

## Getting Started

### Using Dockerfile

1. Clone this repository (the image is built from the current source; the
   permanent version of this artifact is on Zenodo)

    ```bash
    git clone <this repository> coar
    cd coar
    ```

2. Build a docker image (about 30 min)

    ```bash
    sudo docker build -f cav21ae_rel/Dockerfile -t cav21ae_pcsat .
    ```
    The build context is the repository root, not this directory, and BuildKit
    (the default since Docker 23.0) is required: `cav21ae_rel/Dockerfile.dockerignore`
    beside the Dockerfile is what keeps this directory in the context.
    This will make a docker image tagged with `cav21ae_pcsat:latest`.

3. Run the image
    ```bash
    sudo docker run --rm -it cav21ae_pcsat:latest /bin/bash --login
    ```
    Now, you are ready to conduct experiments.

## Reproducing Experimental Results

The artifact is at `/home/opam/coar` in the container, and the paper is
`/home/opam/cav2021rel.pdf` (downloaded from
[here](https://www.riec.tohoku.ac.jp/~unno/papers/cav2021rel.pdf)).

Please run the following command.
```bash
cd /home/opam/coar/cav21ae_rel
./exp.sh
```

The image is built from the current source rather than from the 2021 revision
the paper used, so the numbers may differ from Table 1; that is intended.
This will reproduce the experimental results shown in Table 1 in the paper.
