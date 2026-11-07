CAV 2026 Artifact
=======================================
Paper title: Lagrangian-Based Duality for Quantified SMT Algorithms


Claimed badges: Available + Functional + Reusable

Justification for the badges:

  * Functional: The artifact replicates the results of the paper (see below for details). It compiles MuCyc and executes the benchmarks on our approach and the tools we compare with. The source code is included in the artifact.
      - replicated:
          * Figure 1, plot left
          * Figure 1, plot right

  * Reusable:
      - The artifact's license allows its reuse and repurposing. Source code is provided and the artifact allows several different configuration options. Namely, the benchmarks are evaluated using the approach which satisfies the progress property, as well as an approach where the progress property is not ensured. Moreover, the timeout for the execution of the benchmarks can be adjusted if needed.
      - All dependencies and used libraries are well documented and up to date. Our tool depends on the solver `Z3` and the SMT-LIB2 benchmarks. The remaining dependencies are documented in the README file in the root directory of the repository.

Requirements:

  * RAM: 32 GB
  * CPU cores: Single core
  * Time (smoke test): ~1h for setup, max. 300s for single benchmark
  * Time (full review): ~1h for setup, ~15h to run all the benchmarks

External connectivity: YES

Internet connection is needed to download the SMT-LIB2 benchmark collection.

-------------------------------------------------------------------------------
**                                SETUP                                 **
-------------------------------------------------------------------------------

### Option 1: Loading Docker Image (Recommended)
To load the docker image, run the following command:
```bash
sudo docker load -i mucyc_cav26ae.tar
```
As a final step, benchmarks need to be downloaded (see below).

### Option 2: Building Docker Image
Run the following commands:
```bash
# Unzip the source code
unzip mucyc_cav26ae_src.zip

# Go to the source code directory
cd mucyc_cav26ae_src

# Build the Docker image
cd cav26ae
sudo docker build -f Dockerfile -t mucyc_cav26ae ../
```
As a final step, benchmarks need to be downloaded (see below).

### Option 3: Manual Setup
See `README.md` in the top directory and follow the instructions to build CoAR. MuCyc is included as part of CoAR.
As a final step, benchmarks need to be downloaded (see below).

### Last step: Download benchmarks
After the setup, the SMT-LIB2 benchmarks need to be downloaded from the link below. The contents of the directory `non-incremental/LRA` (5 directories) need to be copied to `benchmarks/QSMT/LRA`.

[https://zenodo.org/records/16740866/files/LRA.tar.zst](https://zenodo.org/records/16740866/files/LRA.tar.zst)


-------------------------------------------------------------------------------
**                                SMOKE TEST                                 **
-------------------------------------------------------------------------------

To quickly verify that the setup is working correctly and to demonstrate how to run the experiments, we perform smoke tests on individual benchmarks as described below.

Start a shell inside the container:

```
sudo docker run --rm -it mucyc_cav26ae:latest /bin/bash --login
```

We can run individual benchmarks as follows:

```
timeout 300 ./_build/default/main.exe -c ./config/solver/mucyc_qsat_deepest_own_projected_repeatedly.json -p smt ./benchmarks/QSMT/LRA/2010-Monniaux-QE/mjollnir1/formula_001.smt2
```

The expected output for this particular benchmark is:
```
unsat
```

In general, the output could also be `sat`, `unsat`, `unknown`, or timeout.

The above command executes the approach in which the progress property is ensured: after learning a lemma, the search returns to the level of the lemma's deepest variable of the losing player, and projects away the variables below that level repeatedly until the level no longer changes. Here, `./config/solver/mucyc_qsat_deepest_own_projected_repeatedly.json` can be replaced by `./config/solver/mucyc_qsat_deepest_own.json` for executing the approach in which the progress property is not ensured (the return of Bjorner and Janota's algorithm, without the projection). Similarly, `./config/solver/z3_smt.json` can be used to check the `Z3` approach.

Moreover, `2010-Monniaux-QE/mjollnir1/formula_001.smt2` can be replaced with any other benchmark from the benchmark collection.


-------------------------------------------------------------------------------
**                               FULL REVIEW                                 **
-------------------------------------------------------------------------------

Start a shell inside the container:

```
sudo docker run --rm -it mucyc_cav26ae:latest /bin/bash --login
```

Inside the container, move to the artifact folder and run the LRA experiments:

```
cd /home/opam/coar/cav26ae
./run.sh LRA
```
This writes `LRA_mucyc_qsat_deepest_own_projected_repeatedly.csv`, `LRA_mucyc_qsat_deepest_own.csv` and `LRA_z3_smt.csv` beside the script, one per arm, each arm named by
its configuration `config/solver/<arm>.json` (`./run.sh LRA z3_smt`
runs one arm; `./run.sh LIA` runs the LIA experiments). Each arm is a row of the repository's table of runs,
`script/bench_runs.txt` (corpus `cav26ae`, runs `LRA_mucyc_qsat_deepest_own_projected_repeatedly_300`, `LRA_mucyc_qsat_deepest_own_300`, `LRA_z3_smt_300` and their `LIA_`
counterparts), which `script/run_corpus.sh` runs; `script/run_corpus.sh --dry-run cav26ae LRA_z3_smt_300` prints the
command a run issues.
It will take around 15 hours to run the full set of benchmarks.

Finally, generate the plots (Python 3 and gnuplot are required):
```
./gen_figs_LRA.sh
```

The following `csv` files are generated:
- `LRA_mucyc_qsat_deepest_own.csv`: results of execution time of all benchmarks when using the approach in which the progress property is not ensured.
- `LRA_mucyc_qsat_deepest_own_projected_repeatedly.csv`: results of execution time of all benchmarks when using the approach in which the progress property is ensured.
- `LRA_z3_smt.csv`: results of execution time of all benchmarks when using the SMT solver `Z3`.

These files are then used to generate the plots depicted in Figure 1:
- `LRA_mucyc_qsat_deepest_own_projected_repeatedly_vs_mucyc_qsat_deepest_own.pdf`: plot comparing approach with and without progress property
- `LRA_mucyc_qsat_deepest_own_projected_repeatedly_vs_z3_smt.pdf`: plot comparing approach with progress property and `Z3` solver.

Plot preparation validates nonempty input CSVs and joins comparisons by benchmark
name. Missing or duplicate names, unequal benchmark sets, invalid elapsed times,
and contradictory `sat`/`unsat` answers stop plotting. The generated
`LRA_mucyc_qsat_deepest_own_projected_repeatedly_vs_mucyc_qsat_deepest_own.csv` and `LRA_mucyc_qsat_deepest_own_projected_repeatedly_vs_z3_smt.csv` contain six columns
(name, verdict, time for each approach); raw result CSVs are preserved. A
enforced-timeout row records the run's time limit in seconds as its time (300 for the
runs above), and each figure draws its timeouts at that limit, with axes
ending just past it, so a run with a shorter `timeout` needs no further
option. The results compared in one figure must record one limit; different
limits stop plotting. A blank timeout time, as written by older versions of
the runner, takes the limit recorded beside it, or 300 seconds when no row
records one (`./gen_figs_LRA.sh --timeout 60` gives another value for such
results). The LIA plotting entry point applies the same checks.

Benchmark identities must follow the producer's plain-field CSV contract: no
commas, quotation marks or line breaks. Identities whose first nonwhitespace
character is `#` are also refused, because GNUplot treats their unquoted rows
as comments. A native toy check confirms that a combined quote/comma identity
can shift GNUplot's fields despite valid RFC CSV quoting. Comma-only and
quote-only toy identities worked, but preparation conservatively rejects both
to retain the producer's domain. Validation completes before derived comparison
files are replaced; malformed inputs produce an error diagnostic.

To check plotting preparation on small fixtures without running solvers:
```bash
python3 script/check_cav26ae_plots.py
```

The six runs go through the repository's shared runner `script/run_bench.sh`
(`run.sh` changes to the repository root first, so it can be started from any
directory). The runner discovers every input before launching workers, preserves
spaces in benchmark paths, and refuses names containing CSV delimiters, quotes
or line breaks. Discovery failures propagate through `run.sh`.
Only a zero-exit, single-line recognized verdict is recorded as an answer.
Other process/output failures receive one retry, then an `abort` row, except
that a run which exits 1 after a last standard-error line `error: <reason>` (the
tool declining the input) gets a `refused` row with that reason in the fourth
field; neither is plotted, and neither fails the batch. GNU timeout exit
124 produces a three-column timeout row whose third field is the time limit in
seconds (`timeout=2m` gives `120`); decided/abort/refused rows retain four columns. A
limit of 0 means no deadline, so exit 124 is then an ordinary failure. Progress
lines go to standard error; an input list that names no files writes nothing
and exits 0.
The `cmd` and `options` environment variables retain their whitespace-tokenized
command interface; quoting characters inside their values are not shell syntax.

Check these boundaries without running benchmarks:
```bash
python3 script/check_cav26ae_runner.py
```

The unquoted iteration field must also contain no comma, quotation mark or
carriage return. Malformed metadata follows the retry/abort policy, and abort
rows leave that field empty instead of copying failed output into the CSV.
This preserves four columns even when a process emits extra comma fields.

The shared runner uses three fields for an enforced timeout and its configured limit; a solver-owned timeout has four fields and a measured runtime, which is validated but is not a plot limit. Such rows use a recorded deadline in the figure, or the explicit plotting limit or 300-second fallback when none is recorded. Source CSVs are unchanged. Imported files with padded or removed fields must be converted using their producer's documented format; column count alone cannot recover lost provenance.
