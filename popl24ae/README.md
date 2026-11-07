# POPL24 Artifact Evaluation

The paper-time configuration and tool are in the Zenodo archive; this directory is kept current: it runs today's strongest version of the paper's own method, the refinement type system with answer refinement modification for algebraic effects, inferred by RCaml at its default settings (`config/solver/rcaml.json`) and, for the paper's Spacer column, `rcaml_wopp_spacer.json`, and follows CoAR's current defaults in everything that is not that method.

We explain how to reproduce the evaluation results shown in Table 1 and 2 in the following paper:

Fuga Kawamata, Hiroshi Unno, Taro Sekiyama, and Tachio Terauchi. Answer Refinement Modification: Refinement Type System for Algebraic Effects and Handlers. POPL 2024.

## Installation from Source Code

* Install opam2 (see [the official webpage](https://opam.ocaml.org/doc/Install.html)).
* Install ocaml-5.4.0:
  ```bash
  opam switch create 5.4.0
  ```
* Install dune:
  ```bash
  opam install dune
  ```
* Clone this repository:
  ```bash
  git clone https://github.com/hiroshi-unno/coar.git -b POPL24AE
  ```
* Move to the directory:
  ```bash
  cd coar
  ```
* Install required packages:
  ```bash
  opam install . --deps-only
  ```
  (You may also need to install `libblas-dev`, `liblapack-dev`, `libmpfr-dev`, `libgmp-dev`, `libglpk-dev`, `libffi-dev`, and `pkg-config`)
* Build:
  ```bash
  dune build main.exe
  ```

Now you can run a sanity test by the following command:
```bash
./_build/default/main.exe -c ./config/solver/rcaml.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```
(or also you can build and run sequentially by the following command:)
```bash
dune exec main -- -c ./config/solver/rcaml.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```
If the installation has been done successfully, you will see the output similar to below:
```
unsat,0         @assert type_of(sum) <: ($x208:int) -> {$v212: int | $v212 >_#svar13 $x208} [#1]
sat,9           @assert type_of(sum) <: ($x219:{$v224: int | $v224 >_#svar15 1}) -> {$v223: int | $v223 >_#svar18 $x219} [#2]
sat,3           @assert type_of(sum) <: ($x230:int) -> {$v234: int | $v234 >=_#svar21 $x230} [#3]
```

## Run the Evaluation
```bash
cd popl24ae
./exp.sh
```

This will reproduce the results shown in Table 1 and 2 in the paper. It takes about 60 minutes to be completed.

Python 3 is required for input and result validation. Before executing any family,
`exp.sh` validates all three nonempty memory manifests, unique benchmark names,
existing files and finite nonnegative memory values. Spaces in filenames are
preserved; CSV delimiter, quote and line-break characters are refused. The
memory threshold is an exclusion filter based on the supplied measurements,
not an enforced process-memory limit. A fully excluded family starts no worker.

All three result files are staged and checked for complete benchmark identities
before publication. A failed runner or malformed/missing result preserves the
previous published files and reports the staging directory containing partial
results. Each final file replacement is atomic; replacement of all three files
is not a filesystem transaction. `abort`, `refused`, `unknown` and `timeout` remain recorded
outcomes (`refused` is a run the tool declined: status 1 with an `error:` line, shown
as `refused` in the tables), rather than infrastructure failures. These checks do not establish
verdict correctness or reproduce the paper's measurements.

Run the small mock-process checks without executing benchmarks:
```bash
python3 script/check_popl24_evaluation.py
```

* The results corresponding to the "Spacer" column in Table 1 will be output in `results_spacer.csv`.
* The results corresponding to the "PCSat" column in Table 1 will be output in `results_pcsat.csv`.
* The results corresponding to Table 2 will be output in `results_cps.csv`.

(At the same time, log messages will appear in the standard output.) In each CSV file, the first column contains the program file names, the second one contains the verification results, and the third one contains the evaluation time (in seconds).

For each line `results_spacer.csv` and `results_pcsat.csv`, if the result is "sat" or "unsat" and it matches the prefix of the file name ("`-SAT`" or "`-UNSAT`"), we put "Yes" in the "result correct?" column in Table 1, and "No" if it does not match. Also, the evaluation time is put in the "time" column in Table 1. If the result is "timeout", we put "timeout" in the "time" column in Table 1. If the result is "unknown", it indicates that some error occurs and we put "Abort" in the "result correct?" column in Table 1.

In `results_cps.csv`, we have three kinds of the suffix of the file names: `_DS`, `_CPS`, and `_CPS_opt`. They correspond to the column "DS", "CPS", and "CPS (optimized)" in Table 2 respectively. (e.g., the result of the file `choose-easy_CPS.ml` is written at the "`choose-easy`" row and the "CPS" column in Table 2.) For each result, if the result is "sat", we put "Yes" in the "verified?" column in Table 2, and "No" if "unsat". Also, the evaluation time is put in the "time" column in Table 2.

We provide a script to convert the CSV files into new CSV files
that have almost the same structure as the tables in the paper.
```bash
./convert.sh
```
The converter validates all three nonempty result files before replacing any
table. Spacer and PCSat must contain identical full benchmark identity sets,
including exclusions. Matching sets do not establish corpus completeness or
that files came from the same run; no source-file existence or run provenance
check is inferred from conversion. It rejects duplicate identities, unsupported verdicts, malformed
exclusions and nonfinite or negative elapsed times. Table 1 compares decided
answers with the terminal `-SAT.ml` or `-UNSAT.ml` filename tag; this is a
comparison with the artifact's expected label, not an independent correctness
proof. Table 2 groups by program identity and the terminal `_DS.ml`, `_CPS.ml`
and `_CPS_opt.ml` roles, requiring exactly one of each. Input order does not
determine column placement. Different source directories with the same displayed
program name are refused as ambiguous.

Malformed or missing input preserves all existing tables. Final replacements
are atomic individually, but are not a transaction across all three files.
Raw result CSVs are never rewritten by conversion.

Check conversion with small fixtures:
```bash
python3 script/check_popl24_conversion.py
```

This produces three CSV files: `table_spacer.csv`, `table_pcsat.csv`, and `table_cps.csv`.
The first two files correspond to Table 1 in the paper,
and the third one corresponds to Table 2 in the paper.

### Note
- Depending on machine performance, some results may differ from the ones in the paper since they require a lot of resources. For example, the evaluation of `amb-3-SAT.ml` in the "PCSat" configuration may time out, or the evaluation of `distribution-SAT.ml` in the "PCSat" configuration may be out of memory (which will show "abort" as the result).
- You can change some parameters by editing the variables declared at the beginning of the script `exp.sh`:
  - `timeout`: Time limit in seconds.
  - `para`: The number of parallel executions. You can disable parallelism by setting this variable to `1`.
  - `memlimit`: Memory limit in GB. By changing this variable, you can exclude benchmarks that require more than `memlimit` GB of memory. The amount of required memory for each benchmark is based on a measurement of memory usage  performed on our machine, which is listed in `memusage_spacer.csv`, `memusage_pcsat.csv`, and `memusage_cps.csv`.
- The paper's numbers were obtained with Z3 4.12.x (OCaml 5.0). The "Spacer" configuration depends on the Z3 version: with Z3 5.1.0, `bfs-UNSAT.ml` and `choose-max-UNSAT.ml` are not answered and the other `choose-*` benchmarks are several times slower (for example `choose-max-SAT.ml` takes minutes rather than seconds). This is a change in Z3's Spacer between 4.12.2 and 4.13.3, not in the benchmarks or their encoding: the same Horn clauses are solved by Z3 4.12.2 and not by Z3 5.1.0.

## Additional Artifact Description
- The benchmark program files are located at `<porject root>/benchmarks/OCaml/popl24/arm/` (for Table 1) and `<porject root>/benchmarks/OCaml/popl24/cps/` (for Table 2).
- You can verify your program written in (subset of) OCaml (maybe with algebraic effects and handlers) by the following command (at the project root directory):
  ```bash
  ./_build/default/main.exe -c <config file> -p ml ./path/to/program.ml
  ```
  The `<config file>` can be either
  - `./config/solver/rcaml.json`: RCaml at its default settings, which `exp.sh` uses for the "PCSat" column of
    Table 1 (the paper's numbers were taken with `rcaml_pcsat_tb_ar.json`, deleted on 2026-11-03), or
  - `./config/solver/rcaml_wopp_spacer.json`: which is used in the "Spacer" configuration in Table 1 and Table 2.