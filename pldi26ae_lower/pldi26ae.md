# PLDI 2026 Artifact Evaluation

## Basic Information

- Artifact URL: The artifact is available at [Zenodo](https://doi.org/10.5281/zenodo.19068567).
- Paper: Supermartingales for Unique Fixed Points: A Unified Approach to Lower Bound Verification

## Setup

### Option 1: Loading Docker Image (Recommended)
To load the docker image, run:
```bash
sudo docker load -i muval_pldi26ae_lower.tar
```

The file `muval_pldi26ae_lower.tar` is a Docker image for the `linux/arm64` platform.
If you are using the `linux/amd64` platform, please use `muval_pldi26ae_lower_linux_amd64.tar` instead.

### Option 2: Building Docker Image
Run the following commands:
```bash
# Unzip the source code
unzip muval_pldi26ae_lower_src.zip

# Go to the the source code directory
cd muval_pldi26ae_lower_src

# Copy the experiment script to the top directory
cp script/prob_bounds/run.sh .

# Build the Docker image
cd pldi26ae_lower
sudo docker build -f Dockerfile -t muval_pldi26ae_lower ../
```

### Option 3: Manual Setup
See `README.md` in the top directory and follow the instruction to build CoAR. MuVal is included as part of CoAR.
You also need to install [PolyQEnt](https://github.com/ChatterjeeGroup-ISTA/polyqent) to run the experiments described below.

## Instruction for Experiments

First, open a bash shell in a Docker container:
```bash
sudo docker run --rm -it muval_pldi26ae_lower:latest /bin/bash --login
```

Then run the following commands inside the container:

```bash
# Activate the Python virtual environment for PolyQEnt
source .venv/bin/activate

# Run the experiment script
./run.sh
```
This command reproduces the results in Table 2 in the paper.

### (Optional) Running the Tool on a Single Benchmark

If you want to run the tool on a single benchmark, use the following command.
```bash
# Activate the Python virtual environment for PolyQEnt
source .venv/bin/activate

# Run the tool on ./benchmarks/QFL/ert_random_walk_2nd_lb.qhes
./_build/default/main.exe -c ./config/solver/muval_quant_polyqent_deg3.json -p qfl ./benchmarks/QFL/ert_random_walk_2nd_lb.qhes
```
Here, `./config/solver/muval_quant_polyqent_deg3.json` is a configuration file.

If you would like to see debug output (including synthesized certificates), use a debug configuration:
```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_quant_polyqent_deg3.json -p qfl ./benchmarks/QFL/ert_random_walk_2nd_lb.qhes
```

After the (potentially long) debug output, the synthesized certificates (cf. Theorem 4.1 in the paper) appear at the very end of the output:
```
underapproximated:
X1 (x:real) : real =mu if (<x >. real(0)>) then real(2) /. real(3) *. \X1 (x -. real(1)) +. real(1) /. real(3) *. \X1 (x +. real(1)) +. real(1) else real(0);
X2 (x:real) : real =mu if (<x >. real(0)>) then real(2) /. real(3) *. \X2 (x -. real(1)) +. real(1) /. real(3) *. \X2 (x +. real(1)) +. real(2) *. (real(2) /. real(3) *. \X1 (x -. real(1)) +. real(1) /. real(3) *. \X1 (x +. real(1))) +. real(1) else real(0);

synthesized prefixpoint:
X1 (x:real) |-> if (<x >. real(0)>) then real(3) +. real(3) *. x else real(0)
X2 (x:real) |-> if (<x >. real(0)>) then real(42) +. real(42) *. x +. real(9) *. (x *. x) else real(0)

synthesized ranking supermartingales:
X1 (x:real) |-> if (<x >. real(0)>) then real(99/4) +. real(45/2) *. x +. real(9/2) *. (x *. x) else real(0)
X2 (x:real) |-> if (<x >. real(0)>) then real(1170) +. real(846) *. x +. real(405/2) *. (x *. x) +. real(18) *. (x *. x *. x) else real(0)

synthesized postfixpoint:
X1 (x:real) |-> if (<x >. real(0)>) then real(3) *. x else real(0)
X2 (x:real) |-> if (<x >. real(0)>) then real(24) *. x +. real(9) *. (x *. x) else real(0)
=========================
valid, 0.704716s, X1 (x:real) |-> if (<x >. real(0)>) then real(3) *. x else real(0), X2 (x:real) |-> if (<x >. real(0)>) then real(24) *. x +. real(9) *. (x *. x) else real(0)
```

Note that conditionals in the debug output are enclosed by `(<` and `>)`.

## Expected Results

For each benchmark file, `run.sh` prints output of the following form.
```
./benchmarks/QFL/ert_coin_flip_lb.qhes
Config A
valid, 1.045869s, P  |-> real(1)

real	0m0.209s
user	0m1.066s
sys	0m0.077s
```

The correspondence to Table 2 in the paper is as follows.
- The first line shows the name of the benchmark file. File names with suffix `_lb` correspond to lower-bound verification, while `_ub` corresponds to upper-bound verification.
- The second line corresponds to the "Config" column in Table 2.
- The third line corresponds to the "Result" column in Table 2: `valid` indicates that the tool successfully verified the specified lower / upper bound.
- The remaining lines are produced by the `time` command. The `real` time corresponds to the "Time (sec)" column in Table 2.


The benchmark
`benchmarks/QFL/chatterjee22_fig23_lb.qhes`
raises the following exception:
`Uncaught exception: "failed to solve Problem 1"`.
This is indicated as "unknown" in Table 2.


## Additional Description

### Input Format

As we explained in Section 5 of the paper, the input of our tool is a queried equation system.
Accordingly, each benchmark file (`benchmarks/QFL/*.qhes`) consists of a query followed by a list of least-fixed-point equations.

For example, in `benchmarks/QFL/ert_random_walk_2nd_lb.qhes` (shown below), the query is `X2 1.0 >= 33.0`, and there are two least-fixed-point equations.
The query and the equations are separated by `s.t.`.

Each least fixed-point equation defines a quantitative predicate variable, declared on the left-hand side.
The right-hand side is an expression that is monotone with respect to quantitative predicate variables.
Its least fixed point determines the interpretation of the variable.

```
X2 1.0 >= 33.0
s.t.
X1 (x : real) : real =mu
  if x > 0.0 then (2.0 / 3.0) * X1 (x - 1.0) + (1.0 / 3.0) * X1 (x + 1.0) + 1.0 else 0.0;
X2 (x : real) : real =mu
  if x > 0.0 then (2.0 / 3.0) * X2 (x - 1.0) + (1.0 / 3.0) * X2 (x + 1.0) +
                  2.0 * ((2.0 / 3.0) * X1 (x - 1.0) + (1.0 / 3.0) * X1 (x + 1.0)) + 1.0 else 0.0;
```

In Section 2.3 and [Appendix A](https://arxiv.org/abs/2504.04132), we present translations of several properties of probabilistic programs into least fixed-point equation systems, including:
- weakest preexpectation
- expected runtime
- higher moments of runtime
- conditional weakest preexpectation

### Project Structure

The core implementation of **MuVal<sup>QFL</sup>** is located under the `lib/` directory. The relevant subdirectories are:

- `lib/ast`
  Definitions of abstract syntax trees for logical formulas.

- `lib/QFL`
  Definitions of *quantitative queried fixed-point equation systems* (referred to as QFL in the code).

- `lib/MuVal`
  Contains the implementation of **MuVal<sup>QFL</sup>**, the tool introduced in the paper.

- `lib/PolyQEnt`
  OCaml bindings for the solver **PolyQEnt**, used to solve polynomial quantified entailment problems arising in bounds checking.

#### Code Relevant to the Paper

The core functionality corresponding to the paper is implemented in:

- `lib/MuVal/solver.ml`

In particular:

- `check_bounds`
  Implements **lower and upper bound checking**, which is the main verification task considered in the paper.

- `solve_qfl` (in `lib/MuVal/solver.ml`)
  Dispatches different types of queries on quantitative fixed-point equation systems. Among the supported query types, bounds checking queries are handled by `check_bounds`.

The call structure is as follows:

- `main.ml`
  Entry point of the tool. It parses the problem type specified by `-p`. For `-p qfl`, it invokes the parser for quantitative queried fixed-point equation systems and then calls `solve_qfl` in `lib/solver.ml`.

- `lib/solver.ml`
  Provides `solve_qfl`, which constructs a solver module according to the configuration file specified by `-c` and then calls its `solve_qfl` function. In this artifact, that is `MuVal.solve_qfl`.

- `lib/MuVal/solver.ml`
  Defines `solve_qfl` for MuVal<sup>QFL</sup>, corresponding to `MuVal.solve_qfl` called from `lib/solver.ml`. This function implements the solving procedure for quantitative queried fixed-point equation systems.

During bounds checking, MuVal<sup>QFL</sup> generates polynomial quantified entailment problems, which are delegated to PolyQEnt via the bindings in `lib/PolyQEnt`.

### Configuration Files

Configuration files are located in:

```
config/solver/
```

For the experiments in this artifact, only the following configuration files are relevant:

- `config/solver/muval*.json`
- `config/solver/dbg_muval*.json`

The `dbg_` variants enable debug output, while the others correspond to the configurations used for reproducing the results in the paper.

These configuration files control how templates and constraints are generated and solved.

#### Options Relevant to the Paper

The following parameters are directly related to the techniques described in the paper.

##### Template for prefixed point $u$

- `quant_prefp_templ_use_orig_ite`
  Whether to reuse the branching structure of the original fixed-point equations.

- `quant_prefp_templ_num_conds`
  Number of additional conditional branches.

- `quant_prefp_templ_cond_degree`
  Degree of polynomials used in branch conditions.

- `quant_prefp_templ_term_degree`
  Degree of polynomials used in branch expressions.

##### Template for $u$-ranking supermartingale $r$

- `quant_rank_templ_use_orig_ite`
  Whether to reuse the original branching structure.

- `quant_rank_templ_num_conds`
  Number of additional conditional branches.

- `quant_rank_templ_cond_degree`
  Degree of condition polynomials.

- `quant_rank_templ_term_degree`
  Degree of branch polynomials.

##### Template for post-fixed point (invariant) $\eta'$

- `quant_postfp_templ_use_orig_ite`
  Whether to reuse the original branching structure.

- `quant_postfp_templ_num_conds`
  Number of additional conditional branches.

- `quant_postfp_templ_cond_degree`
  Degree of condition polynomials.

- `quant_postfp_templ_term_degree`
  Degree of branch polynomials.

- `quant_postfp_force_non_const`
  Whether to enforce the invariant to be non-constant.

##### Under-approximation (Section 5.2.2)

- `quant_underapprox_templ_cond_degree`
  Degree of polynomials used in guard strengthening.

- `quant_underapprox_templ_term_degree`
  Degree of polynomials used in weight subtraction.
