# CAV21 Artifact Evaluation: MuVal

We explain how to use MuVal, a termination analyzer.
Technical details are explained in the following paper.

Satoshi Kura, Hiroshi Unno, and Ichiro Hasuo. Decision Tree Learning in CEGIS-Based Termination Analysis. CAV 2021.

The paper-time configuration and tool are in the Zenodo archive; this directory is kept current: it runs today's strongest version of the paper's own method, MuVal's termination analysis with decision-tree learning in its CEGIS loop (the eager and the lazy strategy, with the paper's `Nu` quantifier elimination and the prove/disprove race), whose PCSat parts under the decision-tree synthesizer are today's, and follows CoAR's current defaults in everything that is not that method.

## Getting Started

### Using Dockerfile

1. Clone this repository (the image is built from the current source; the
   permanent version of this artifact is on Zenodo)

    ```bash
    git clone <this repository> coar
    cd coar
    ```

2. Build a docker image (about 50 min; most of it is LLVM 3.6.2, which
   `llvm2kittel` needs and which is built in a separate stage)

    ```bash
    sudo docker build -f cav21ae_dt/Dockerfile -t cav21ae .
    ```
    The build context is the repository root, not this directory, and BuildKit
    (the default since Docker 23.0) is required: `cav21ae_dt/Dockerfile.dockerignore`
    beside the Dockerfile is what keeps this directory and the two files under
    `script/` its runner reads (`run_corpus.sh`, `bench_runs.txt`) in the context.
    This will make a docker image tagged with `cav21ae:latest`.

3. Run the image
    ```bash
    sudo docker run --rm -it cav21ae:latest /bin/bash --login
    ```
    The artifact is at `/home/opam/coar`, and TPDB's `C_Integer` category — the
    335 benchmarks this experiment uses — is at
    `/home/opam/coar/benchmarks/term-comp/C_Integer`, fetched during the build.
    The image is built from the current source rather than from the 2021
    revision the paper used, so the numbers may differ from
    `cav21ae_dt/term-comp20.csv`; that is intended.
    Now, you are ready to conduct experiments.

## Verifying Experimental Results on the Paper

The process of verification consists of two steps.
The first step is to reproduce our experimental results (raw data) on your local computer.
The second step is to make sure that scatter plots in the paper can be made from our experimental results.

### Reproducing Experimental Results

Since there are quite a few benchmarks, conducting experiments for all benchmarks may take much time.
So, we provide another way to reduce time.

Our experiments were conducted on [StarExec](https://www.starexec.org/starexec/secure/index.jsp), and the results are saved in `cav21ae_dt/term-comp20.csv`.
The aim here is to verify that the results in `cav21ae_dt/term-comp20.csv` can be reproduced on your computer.

Instead of using all benchmarks, you can select as many benchmarks as you want and conduct experiments on them.
You can increase the number of benchmarks until you are convinced that the results in `cav21ae_dt/term-comp20.csv` are valid and reproducible.

Before proceeding, make sure that the following files and directories are in the home directory of the docker container.

- `2104.11463.pdf`: our paper (downloaded from [arxiv](https://arxiv.org/abs/2104.11463))
- `coar`: directory of our artifact
- `llvm2kittel`: directory of llvm2kittel

1. Select which benchmarks to use

    `cav21ae_dt/run.sh` runs all 335 inputs. To run a selection, print the full command and call the loop on the
    files you want:
    ```bash
    cd /home/opam/coar
    script/run_corpus.sh --dry-run cav21ae_dt dt_eager_300
    timeout=300 options='-p ltsterm' \
      prove_config=./config/solver/muval_dt_prove_nu_eager_yesno.json \
      disprove_config=./config/solver/muval_dt_disprove_nu_eager_yesno.json \
      cav21ae_dt/prove_disprove_bench.sh benchmarks/term-comp/C_Integer/Stroeder_15/A*.c | tee result_eager.csv
    ```

2. Conduct experiments

    `cav21ae_dt/run.sh eager` solves the termination problem and the non-termination problem in parallel using the
    eager strategy described in the paper, and `cav21ae_dt/run.sh lazy` does the same with the lazy strategy.
    Each is a run of the repository's table of runs, `script/bench_runs.txt` (corpus `cav21ae_dt`, runs
    `dt_eager_300` and `dt_lazy_300`: the strategy's prove and disprove configurations, the 300-second limit, the
    inputs `benchmarks/term-comp/C_Integer/{Stroeder_15,Ton_Chanh_15}/*.c`), which `script/run_corpus.sh` runs
    through the loop `cav21ae_dt/prove_disprove_bench.sh`; the race of the two configurations on one input is
    `cav21ae_dt/para_muval_prove_disprove.sh`, which first translates the C file with clang and llvm2kittel.

    To conduct experiments with the eager strategy, run the following command.
    ```bash
    cav21ae_dt/run.sh eager | tee result_eager.csv
    ```
    This will output a csv file `result_eager.csv` where each line corresponds to one benchmark.

    For the lazy strategy, replace `eager` with `lazy` and do the same thing.

3. Compare the results with `cav21ae_dt/term-comp20.csv`

    Assume that the results obtained from the artifact are saved in `result_eager.csv`.

    `result_eager.csv` has 3 or 4 columns.

    - Column 1 contains file names of benchmarks.
    - Column 2 contains answers (YES/NO/timeout) for the termination problems.
    - Column 3 contains elapsed time to solve.

    The data in `cav21ae_dt/term-comp20.csv` include our experimental results on [StarExec](https://www.starexec.org/starexec/secure/index.jsp) and the results of [TermComp 2020: C Integer](https://termcomp.github.io/Y2020/job_41519.html).

    `cav21ae_dt/term-comp20.csv` has 11 columns.

    - Column 1 contains names of benchmarks.
    - Column 2-6 contain elapsed time to solve, by AProve/irankfinder v1.3.2/Ultimate Automizer/Muval (eager)/Muval (lazy), respectively.
    - Column 7-11 contain answers (YES/NO/MAYBE) for the termination problems. The order of solvers is the same as Column 2-6.

    For example, to compare the elapsed time for "`C_Integer/Ton_Chanh_15/2Nested_false-termination.c`", you should compare Column 3 of `result_eager.csv` and Column 5 of `cav21ae_dt/term-comp20.csv`.
    ```bash
    grep "C_Integer/Ton_Chanh_15/2Nested_false-termination.c" result_eager.csv | cut -d , -f 3
    grep "C_Integer/Ton_Chanh_15/2Nested_false-termination.c" cav21ae_dt/term-comp20.csv | cut -d , -f 5
    ```

    We provide a script to make such comparisons easy.
    ```bash
    cav21ae_dt/compare.sh eager result_eager.csv
    ```
    This script compares the results of our experiments on StarExec (`cav21ae_dt/term-comp20.csv`) and the results on your computer (`result_eager.csv`).
    The script checks whether answers (YES/NO/MAYBE) are the same and generates a scatter plot `compare_eager.eps` for comparing elapsed time to solve
    (`cav21ae_dt/compare.sh lazy result_lazy.csv` for the lazy strategy).
    Note that results may be slightly different due to the difference in environments.

    Make sure that answers (YES/NO/MAYBE) on your local computer are consistent with those on StarExec except for a small amount of difference caused by environmental difference.
    Also, make sure that points in the scatter plot `compare_eager.eps` are (almost) on the diagonal line, which means that elapsed time is (almost) the same.

### Making scatter plots
The aim here is to make scatter plots in the paper from `cav21ae_dt/term-comp20.csv`.

```bash
cd cav21ae_dt
gnuplot aprove.plt
gnuplot irankfinder.plt
gnuplot ultimate.plt
```
These commands generate scatter plots `aprove.eps`, `irankfinder.eps`, and `ultimate.eps` using the data in `term-comp20.csv`.

- `aprove.eps`: AProve vs MuVal (eager)
- `irankfinder.eps`: irankfinder v1.3.2 vs MuVal (eager)
- `ultimate.eps`: Ultimate Automizer vs MuVal (eager)

Make sure that these scatter plots are the same as those in our paper.


## Using MuVal for new benchmarks

Assume that we want to solve the termination (or non-termination) problem for `INPUT.c`.

(Note that you can use [docker cp](https://docs.docker.com/engine/reference/commandline/cp/) to copy files between the host and the container.)

1. Convert `INPUT.c` to `INPUT.t2` by [llvm2kittel](https://github.com/gyggg/llvm2kittel/tree/kou)
    ```bash
    clang -Wall -Wextra -c -emit-llvm -O0 INPUT -o INPUT.bc
    ~/llvm2kittel/build/llvm2kittel --dump-ll --no-slicing --eager-inline --t2 INPUT.bc > INPUT.t2
    ```

2. Solve the problem by MuVal
    ```bash
    cd /home/opam/coar
    dune exec main -- -c CONFIG.json -p ltsterm INPUT.t2
    ```
    Possible choices for `CONFIG.json` are as follows.

    - `./config/solver/muval_dt_prove_nu_eager_yesno.json` for the termination problem with the eager strategy
    - `./config/solver/muval_dt_disprove_nu_eager_yesno.json` for eager non-termination
    - `./config/solver/muval_dt_prove_nu_lazy_yesno.json` for lazy termination
    - `./config/solver/muval_dt_disprove_nu_lazy_yesno.json` for lazy non-termination

    (the configurations `cav21ae_dt/run.sh eager|lazy` runs; the lazy ones with threshold templates,
    `muval_term_comp_{prove,disprove}_dt_lazy_thr.json`, were deleted on 2026-11-03 and are restored with
    `git checkout 2b2bc865cc -- config/solver/muval_term_comp_{prove,disprove}_dt_lazy_thr.json`)

## On StarExec

If you have a [StarExec](https://www.starexec.org/starexec/secure/index.jsp) account, you can use MuVal on StarExec.
MuVal is available from [this link](https://www.starexec.org/starexec/secure/details/solver.jsp?anonId=8afa72c8-96f1-4594-94dc-73118165a74e).

Use the following configurations.

- muval_dt_eager_nu_parallel_from_c: for the eager strategy
- muval_dt_lazy_parallel_thr_from_c: for the lazy strategy