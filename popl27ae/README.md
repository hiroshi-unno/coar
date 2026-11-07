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
`popl27ae_src.zip` already contains the TermCOMP ITS benchmarks (`benchmarks/term-comp/Integer_Transition_Systems/`, 1,222 files), which the Docker build copies into the image.
The zip has no `.git` directory, so the `git submodule` command of Option 3 is neither needed nor possible there.
(When building the image from a git clone instead, run that command first, so that `benchmarks/term-comp` is populated in the build context.)

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
The experiments also use [cvc5](https://github.com/cvc5/cvc5) (1.4.2), which must be on `PATH` (or placed as `./cvc5` in the top directory); the Docker image installs it.
Summarizing and plotting the results (`popl27ae/summarize_results.py`, `popl27ae/plot.sh`) needs `python3`, and `popl27ae/plot.sh` also needs [gnuplot](http://www.gnuplot.info/); the Docker image provides both.

The TermCOMP ITS benchmarks are a git submodule; in a git clone, fetch them with:

```bash
git submodule update --init benchmarks/term-comp
```

## Instructions for Experiments

For Options 1 and 2, open a bash shell in a Docker container:
```bash
sudo docker run --name popl27ae_container -it popl27ae:latest /bin/bash --login
```

Then run the following commands inside the container:

```bash
./popl27ae/runall.sh
```

While a script runs, it prints its progress to standard error: `[i/N] running <benchmark> (elapsed hh:mm:ss)` when a benchmark starts and `[done k/N, elapsed hh:mm:ss] <benchmark>: <answer>` when it finishes. The results go to standard output, one CSV line per benchmark (`<benchmark>,<answer>,<seconds>,<iterations>`), sorted by name at the end; a run that hits the time limit is written as `<benchmark>,timeout,<time limit in seconds>`.

The experiments require about two days.
In our first full run (300-second time limit), the solver time summed over the twelve runs was about 99.5 hours (POPL23 benchmarks 6.9 hours, TermCOMP ITS benchmarks 92.6 hours); since each run executes two to four benchmarks in parallel, `runall.sh` needs about 47 hours of wall-clock time on one machine with 8 vCPUs.
In the worst case, where every benchmark times out, it would take about 14 days (300s timeout * (202 + 1222) benchmarks * 6 configurations, run two at a time for MuVal and MuValPPM and four at a time for MuStrat).
You can also set a shorter timeout to complete the experiment more quickly by the following command (with a 60-second limit, the worst case is about 3 days).
However, this will affect the experimental results.

```bash
BENCH_TIMEOUT=60 ./popl27ae/runall.sh
```

After running the script, you will find csv files in `results/{popl2023mod,term25its}`.

The MuValPPM files are named after their configurations: `muval_ppm_popl27.csv` is MuValPPM with SCC & AD (Table 1's first column), and `muval_ppm_popl27_no_scc.csv`, `muval_ppm_popl27_no_ad.csv` and `muval_ppm_popl27_no_scc_ad.csv` are the ablations without SCC, without AD and without both.
Results written by an earlier version of this artifact name them `muval_ppm_scc_ad.csv`, `muval_ppm_ad.csv`, `muval_ppm_scc.csv` and `muval_ppm_noopt.csv`; `plot.sh` and `rankcount.sh` read either name, and `summarize_results.py` given the old file names prints the new ones as column headings.

### Table 1

To reproduce Table 1, run the following commands.
Note that experimental results may slightly vary depending on the environment.

```bash
# POPL23 benchmarks
python3 popl27ae/summarize_results.py results/popl2023mod/{muval_ppm_popl27,muval_ppm_popl27_no_scc,muval_ppm_popl27_no_ad,muval_ppm_popl27_no_scc_ad,muval,mustrat}.csv

# TermCOMP ITS benchmarks
python3 popl27ae/summarize_results.py results/term25its/{muval_ppm_popl27,muval_ppm_popl27_no_scc,muval_ppm_popl27_no_ad,muval_ppm_popl27_no_scc_ad,muval,mustrat}.csv
```

The table counts `valid`, `invalid`, `timeout` and `abort` rows; an `unknown` row and a `refused` row (a run the tool declined: status 1 with an `error:` line) appear only when some result has them.

### Figures 1 and 2

To reproduce Fig. 1 and Fig. 2, run the following commands.

```bash
./popl27ae/plot.sh
```

Then, you will find pdf files in `results/fig`.
Each figure draws a timeout at the time limit its results record (300 seconds by default, 60 after `BENCH_TIMEOUT=60 ./popl27ae/runall.sh`), and its axes end just past that limit; no option is needed.
Plotting stops with an error when the results compared in one figure were run with different time limits.
The shared runner uses three fields for an enforced timeout and its configured limit; a solver-owned timeout has four fields (five with MuVal exchange counts) and a measured runtime, which is validated but is not a plot limit. Such rows use a recorded deadline in the figure, or the explicit plotting limit or 300-second fallback when none is recorded. Source CSVs are unchanged. Imported files with padded or removed fields must be converted using their producer's documented format; column count alone cannot recover lost provenance.
Results written by an older version of the runner record no time for a timeout; they are drawn at 300 seconds, or at the limit given as `./popl27ae/plot.sh --timeout 60`.
`*_popl23.pdf` are scatter plots for POPL23 benchmarks.
`*_its.pdf` are scatter plots for TermCOMP ITS benchmarks.

To open the pdf files, you may need to use `docker cp`.
```bash
sudo docker cp popl27ae_container:/home/opam/coar/results ./results
```

### Ranking functions and their arguments against solving time

To relate MuValPPM's (SCC & AD) solving time to the number of ranking functions in the reduced problem (a table) and to the number of their arguments (scatter plots), run the following command after `runall.sh` (it reads `results/{popl2023mod,term25its}/muval_ppm_scc_ad.csv`).

```bash
./popl27ae/rankcount.sh
```

The script first runs MuValPPM (SCC & AD) once more on every benchmark, with one extra configuration field, `output_reduction_stats`, which prints a line counting the ranking functions of each side (primal and dual) as soon as that side has been reduced to a pfwCSP, before any solving.
Each run is stopped once both lines are printed, so the counting takes about one hour (36 minutes for us with three runs in parallel); a run that has not reduced both sides within `RANKCOUNT_TIMEOUT` seconds (default 300) is stopped there and its missing side is reported as without a count.
The counts are written to `results/rankcount/{popl2023mod,term25its}.stats`, joined with the solving times in `results/rankcount/{popl2023mod,term25its}.csv`. A failed counting process aborts collection, displays its diagnostic and preserves the affected corpus's existing statistics file.

The script then prints a table of the solving times by the number of ranking functions (0, 1, 2, 3, 4, 5 or more), with the columns under 1 s, 1-10 s, 10 s to the time limit, and timeout.
The primal side is counted over the `valid` benchmarks and the timeouts, the dual side over the `invalid` benchmarks and the timeouts, since each side's ranking functions matter only where that side can answer.
It also draws the number of arguments of the ranking functions (each ranking function weighted by its predicate's arity) against the solving time, `results/fig/rfargs_vs_time_popl23.pdf` and `results/fig/rfargs_vs_time_its.pdf`: blue filled points are `valid` answers at the primal's argument count, red circles `invalid` answers at the dual's argument count, and a timeout is drawn at the time limit once for each side; an argument count of 0 is drawn at the tick labelled 0.
On the TermCOMP ITS benchmarks the dual (non-termination) side has no ranking function, so every `invalid` answer has 0 ranking functions and an argument count of 0.
The summarizer rejects duplicate benchmarks, invalid verdicts or times, and invalid counts before replacing derived CSVs; empty populations and missing counts retain their corpus and side labels in both text and LaTeX tables.

To print the table again, or as LaTeX, without counting again:

```bash
./popl27ae/rankcount.sh --no-count            # table and figures from results/rankcount
python3 popl27ae/rankcount.py --table . --latex
```


### Alternation depth, strongly connected components and ranking functions

The same counting run also characterises every benchmark by three parameters and relates each to MuValPPM's (SCC & AD) solving time; `./popl27ae/rankcount.sh` prints these tables after the ranking-function table (`./popl27ae/rankcount.sh --no-count` prints them again from `results/rankcount`).
Each `reduction-stats:` line also describes the problem that side's reduction received, that is, after the preprocessing every solving run applies:

- `alternation_depth` (AD): the largest alternation depth of a predicate. The alternation depth of a predicate X_i is 1, or the largest of alpha_j (X_j of the same fixed-point kind) and alpha_j + 1 (of the other kind) over the later predicates X_j (j > i) that lie on a common cycle with X_i through predicates after X_i only; it is computed within the strongly connected component of X_i, where MuValPPM assigns its priorities from it. AD 1 means that no alternation of least and greatest fixed points is nested in a cycle.
- `sccs`: the number of strongly connected components of the call graph (an edge from P to Q when Q occurs in the definition of P), a single predicate on no cycle included; `nontrivial_sccs` (#SCC): those with a cycle, that is, with two or more predicates or one that calls itself; `ranked_sccs`: the nontrivial ones holding a least fixed point on that side, which the reduction gives a ranking family; `ad_per_scc`: the AD of each nontrivial component, `/`-separated; `predicates`: the number of predicates.

The number of ranking functions (#RF) of a benchmark is that of the primal and the dual reduced problems together.
AD and #SCC are read from the primal side. The dual problem has the same call graph, and the same alternation depths unless it has predicates whose fixed-point kind is left open (`mu_or_nu`, which the translation of an ITS produces): the alternation depth reads such a predicate as a greatest fixed point, so a least fixed point that calls one alternates on the primal side and not on the dual one. The CSV below keeps the dual side's value too, and the summary says on how many benchmarks the two differ.

`popl27ae/params.py` joins the counts with `results/{popl2023mod,term25its}/muval_ppm_popl27.csv` into `results/params/{popl2023mod,term25its}.csv` (`benchmark, verdict, time, AD, #SCC, #RF, sccs, predicates, dual AD`, a timeout's time at the time limit) and prints, per corpus:

- a summary table, corpus by parameter: the minimum, median and maximum, and Spearman's rank correlation rho of the parameter with the solving time, a timeout taken at the time limit, over all benchmarks (`valid`, `invalid` and `timeout`) and over the answered ones only, each with its number of benchmarks n. A rank correlation is used because the solving time is censored at the limit;
- the distribution of the benchmarks over each parameter's values: AD 0 (the preprocessing left no predicate), 1, 2, 3, >=4; #SCC 0, 1, 2, 3, 4-7, >=8; #RF 0, 1, 2, 3, 4, >=5;
- for each parameter, the table of solving times by those values, in the format of the ranking-function table.

It also draws the solving time against each parameter, `results/fig/{ad,scc,rf}_vs_time_{popl23,its}.pdf`: blue filled points are `valid` answers, red circles `invalid` ones, black crosses timeouts at the time limit, each point spread sideways around its integer value.

To print the tables as LaTeX, the summary table first:

```bash
python3 popl27ae/params.py --table . --latex
```

### (Optional) Running the Tool on a Single Benchmark

It is also possible to run MuVal on a single benchmark.

```bash
# POPL 2023 benchmarks (.hes files)
./_build/default/main.exe -c ./config/solver/muval_ppm_popl27.json -p muclp benchmarks/muCLP/popl2023mod/sas2019_simple-nest.hes

# TermCOMP ITS benchmarks (.smt2 files)
./_build/default/main.exe -c ./config/solver/muval_ppm_popl27.json -p pltsterm benchmarks/term-comp/Integer_Transition_Systems/From_AProVE_2014/AProVE12-cyclic-Iterate.jar-obl-9.smt2
```

Expected output: the first command prints a line starting with `valid`, the second prints `YES` (the numbers after the verdict vary between runs).


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
