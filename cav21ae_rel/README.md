# CAV21 Artifact Evaluation: PCSat

We explain how to use PCSat, a pfwCSP constraint solver.
Technical details are explained in the following paper.

Hiroshi Unno, Tachio Terauchi, and Eric Koskinen. Constraint-based Relational Verification. CAV 2021.

The paper-time configuration and tool are in the Zenodo archive; this directory is kept current: it runs today's strongest version of the paper's own method, constraint-based relational verification by pfwCSP solving with PCSat, run under `config/solver/pcsat.json`, PCSat's default, and follows CoAR's current defaults in everything that is not that method.

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

This runs every benchmark of Table 1 in the paper
(`benchmarks/pfwnCSP/cav2021rel/`) under PCSat's default configuration,
`config/solver/pcsat.json`, with a time limit of 1200 seconds each, one at a time, and
prints one CSV row per benchmark, `file,verdict,seconds,iterations` (redirect it to keep it:
`./exp.sh > results.csv`). The run is `pcsat_1200` of corpus `cav21ae_rel` in the repository's
table of runs, `script/bench_runs.txt`, which `script/run_corpus.sh` runs through the shared runner
`script/run_bench.sh`; `script/run_corpus.sh --dry-run cav21ae_rel pcsat_1200` prints the command,
and `timeout=60 ./exp.sh` shortens the limit.

The image is built from the current source rather than from the 2021 revision
the paper used, so the numbers differ from Table 1, and the configuration does
too:

- **The `_hint` files.** For `TS_GNI hFT`, `TS_GNI hTT`, `TI_GNI hFT` and
  `SquareSum` (marked † in Table 1) the paper ran a variant of the benchmark
  with a small hint for invariant synthesis: `TS_GNI_hFT_hint.clp`,
  `TS_GNI_hTT_hint.clp`, `TI_GNI_hFT_hint.clp`, `SquareSum_hint.clp`. For the
  GNI files the hint is one extra clause stating a non-relational fact the
  invariant must imply (`x1 >= low1`); `SquareSum_hint.clp` adds a weak
  relational fact and also replaces the sum of squares by a plain sum, so it
  is a different, linear program. `TI_GNI_hTT_hint.clp` is a hinted variant
  the paper did not use. `exp.sh` runs both the plain files and the `_hint`
  files.
- **Special configurations.** The paper ran the benchmarks under
  configurations chosen per benchmark (`config/solver/pcsat_tb.json` and
  `config/solver/pcsat_tb_hyperprop{2,3,4}.json`, which start the predicate
  template at a hand-chosen size and coefficient bound; ‡ in Table 1 marks
  `ArrayInsert` and `SquareSum`, whose initial parameters were chosen by hand).
  Those configurations were deleted on 2026-11-03 (`pcsat_tb.json` stays for other users); restore the three
  hand-chosen ones with `git checkout c487f5553c -- config/solver/pcsat_tb_hyperprop{2,3,4}.json
  config/solver/dbg_pcsat_tb_hyperprop{2,3,4}.json`.

The default configuration now needs neither the hints nor hand-chosen
parameters: it answers the plain files as well as the `_hint` ones.
