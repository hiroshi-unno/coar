# POPL 2027 Artifact Evaluation

## Basic Information

- Artifact URL: The artifact is available at [Zenodo](https://doi.org/10.5281/zenodo.23232542).
- Paper: Solving First-Order Fixed-Point Logics via a Least-to-Greatest Transformation Based on Game Semantics

## Setup

### Option 1: Loading Docker Image (Recommended)
To load the docker image, run the following command:
```bash
# linux/amd64 platform
sudo docker load -i popl27ae_linux_amd64.tar

# linux/arm64 platform
# sudo docker load -i popl27ae_linux_arm64.tar
```

### Option 2: Building Docker Image
Run the following commands:
```bash
# Unzip the source code
unzip popl27ae_src.zip

# Go to the source code directory
cd popl27ae_src

# Build the Docker image
cd popl27ae
sudo docker build -f Dockerfile -t popl27ae ../
```

### Option 3: Manual Setup
See `README.md` in the top directory and follow the instructions to build CoAR. MuVal is included as part of CoAR.

`git submodule update --init benchmarks/term-comp`

## Instructions for Experiments

First, open a bash shell in a Docker container:
```bash
sudo docker run --name popl27ae_container -it popl27ae:latest /bin/bash --login
```

Then run the following commands inside the container:

```bash
./popl27ae/runall.sh
```

While a script runs, it prints its progress to standard error: `[i/N] running <benchmark> (elapsed hh:mm:ss)` when a benchmark starts and `[done k/N, elapsed hh:mm:ss] <benchmark>: <answer>` when it finishes. The results go to standard output, one CSV line per benchmark (`<benchmark>,<answer>,<seconds>,<iterations>`), sorted by name at the end.

The experiments require several hours (300s timeout * (202 + 1222) benchmarks * 6 configurations).

After running the script, you will find csv files in `results/{popl2023mod,term25its}`.

Check that `runall.sh` exits successfully before using the results. It stages
all twelve families, checks nonempty CSVs with matching benchmark identities
and valid elapsed times within each corpus, then publishes them. If collection
or validation fails, existing result CSVs remain intact and the error reports
where the unpublished data were retained. Publication itself is not a transaction
across all files; a filesystem failure during publication must still be treated
as a failed run. Abnormally terminated solver runs are retried once and then
recorded as abort; ordinary timeout outcomes remain timeout.

CSV names containing commas, double quotes or line breaks are refused before
benchmark execution. Empty, duplicate or mismatched benchmark sets are rejected
by the summarizer. Plotting joins the two configurations by benchmark name,
validates the inputs before replacing derived CSVs, and can be repeated without
creating further generations of helper CSVs. These checks do not establish that
the selected set is the expected complete corpus or that preexisting CSVs came
from the same run.

### Table 1

To reproduce Table 1, run the following commands.

```bash
# POPL23 benchmarks
python3 popl27ae/summarize_results.py results/popl2023mod/{muval_ppm_scc_ad,muval_ppm_ad,muval_ppm_scc,muval_ppm_noopt,muval,mustrat}.csv

# TermCOMP ITS benchmarks
python3 popl27ae/summarize_results.py results/term25its/{muval_ppm_scc_ad,muval_ppm_ad,muval_ppm_scc,muval_ppm_noopt,muval,mustrat}.csv
```

### Figures 1 and 2

To reproduce Fig. 1 and Fig. 2, run the following commands.

```bash
./popl27ae/plot.sh
```

Then, you will find pdf files in `results/fig`.
`*_popl23.pdf` are scatter plots for POPL23 benchmarks.
`*_its.pdf` are scatter plots for TermCOMP ITS benchmarks.

To open the pdf files, you may need to use `docker cp`.
```bash
sudo docker cp popl27ae_container:/home/opam/coar/results ./results
```


### (Optional) Running the Tool on a Single Benchmark

It is also possible to run MuVal on a single benchmark.

```bash
# POPL 2023 benchmarks (.hes files)
./_build/default/main.exe -c ./config/solver/muval_parallel_exc_ppm_tbq_ar.json -p muclp benchmarks/muCLP/popl2023mod/sas2019_simple-nest.hes

# TermCOMP ITS benchmarks (.smt2 files)
./_build/default/main.exe -c ./config/solver/muval_parallel_exc_ppm_tbq_ar.json -p pltsterm benchmarks/term-comp/Integer_Transition_Systems/From_AProVE_2014/AProVE12-cyclic-Iterate.jar-obl-9.smt2
```


## Additional Description

### Input Format

#### `.hes` Files

The POPL23 benchmarks in `benchmarks/muCLP/popl2023mod/` use the `.hes`
format. Each file describes a μCLP with a query defined in Section 2.1 of our paper:
a query followed by an ordered sequence of recursive Boolean predicate
definitions. The tool checks whether the query is true under these definitions.

The general structure is:

```text
<query>
s.t.
P (x: int) ... : bool =mu <formula>;
Q (y: int) ... : bool =nu <formula>;
...
```

The keyword `s.t.` separates the query from the
definitions. Each definition declares a predicate name, typed arguments, a type of fixed-point operator (`=mu` denotes a **least fixed point** and `=nu` denotes a **greatest fixed point**), and a defining formula, and ends
with a semicolon. Predicate applications use space-separated arguments, such
as `P x` or `P (x + 1)`.

Predicates may refer to themselves and to other predicates. Definition order
is part of the HES semantics: when least and greatest fixed points depend on
one another, reordering definitions can change the meaning of the query.

For example, `benchmarks/muCLP/popl2023mod/sas2019_simple-nest.hes` contains:

```text
forall (n: int). X n \/ n >= 0
s.t.
X (x: int): bool =mu X (x + 1) \/ Y x;
Y (y: int): bool =nu y != 0 /\ Y (y - 1);
```

The query asks whether every integer `n` satisfies `X n` or `n >= 0`.
`X` and `Y` are predicates over `int` and defined as a least fixed point and a greatest fixed point, respectively.

The main syntax used in the benchmark files is summarized below.

| Construct | Syntax |
| --- | --- |
| Argument types | `int`, `bool` |
| Universal / existential quantification | `forall (x: int). ...`, `exists (x: int). ...` |
| Conjunction / disjunction | `/\`, `\/` (also `and`, `or`) |
| Implication / equivalence | `=>`, `<=>` |
| Negation | `not (...)` or `!(...)` |
| Comparisons | `=`, `!=`, `<`, `<=`, `>`, `>=` |
| Integer arithmetic | `+`, `-`, `*`, `/`, `%` (also `div`, `mod`) |
| Logical constants | `true`, `false` |
| Comments | `// ...` and `/* ... */` |

Parentheses group formulas and arithmetic expressions. For the complete
syntax, see [`lib/muCLP/parser.mly`](../lib/muCLP/parser.mly) and
[`lib/muCLP/lexer.mll`](../lib/muCLP/lexer.mll).

#### `.smt2` Files

The TermCOMP ITS benchmarks in `benchmarks/` use the `.smt2` format.
See [TermComp Proposal: Pushdown Systems as a Model for Programs with Procedures](https://www.microsoft.com/en-us/research/publication/termcomp-proposal-pushdown-systems-as-a-model-for-programs-with-procedures/) for details.