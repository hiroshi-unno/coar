# PLDI 2026 Artifact Evaluation

## Basic Information

- Artifact URL: The artifact is available at [Zenodo](https://doi.org/10.5281/zenodo.19068497).
- Paper: A Hierarchy of Supermartingales for $\omega$-Regular Verification

## Setup

### Option 1: Loading Docker Image (Recommended)
To load the docker image, run the following command:
```bash
sudo docker load -i muval_pldi26ae_omega.tar
```

### Option 2: Building Docker Image
Run the following commands:
```bash
# Unzip the source code
unzip muval_pldi26ae_omega_src.zip

# Go to the the source code directory
cd muval_pldi26ae_omega_src

# Copy the experiment script to the top directory
cp script/prob_omega_reg/run.sh .

# Build the Docker image
cd pldi26ae_omega
sudo docker build -f Dockerfile -t muval_pldi26ae_omega ../
```

### Option 3: Manual Setup
See `README.md` in the top directory and follow the instruction to build CoAR. MuVal is included as part of CoAR.
You also need to install [PolyQEnt](https://github.com/ChatterjeeGroup-ISTA/polyqent) to run the experiments described below.

## Instruction for Experiments

First, open a bash shell in a Docker container:
```bash
sudo docker run --rm -it muval_pldi26ae_omega:latest /bin/bash --login
```

Then run the following commands inside the container:

```bash
# Activate the Python virtual environment for PolyQEnt
source .venv/bin/activate

# Run the experiment script
./run.sh
```
This command reproduces the results in Table 1 in the paper.

### (Optional) Running a Single Benchmark

If you want to run the solver on an individual benchmark file, use the following commands:
```bash
# activate python venv for PolyQEnt
source .venv/bin/activate

# with debug output
./_build/default/main.exe -c ./config/solver/dbg_muval_quant_polyqent_deg1.json -p qfl benchmarks/QFL/omega_regular/ex3_9.qhes

# without debug output
./_build/default/main.exe -c ./config/solver/muval_quant_polyqent_deg1.json -p qfl benchmarks/QFL/omega_regular/ex3_9.qhes
```
Here, `./config/solver/muval_quant_polyqent_deg1.json` is a configuration file.


## Expected Results

The output of `run.sh` consists of five sections for LexPMSM, LexGSSM, PMSM, GSSM, and SSM.

For each benchmark file, `run.sh` prints output of the following form.
```
./benchmarks/QFL/omega_regular/EvenOrNegative.qhes
sat

real	0m0.881s
user	0m4.262s
sys	0m0.101s
```

The correspondence to Table 1 in the paper is as follows.
- The first line shows the name of the benchmark file.
- The second line shows the result (`sat` or `unknown`).
- The remaining lines are produced by the `time` command. The `real` time corresponds to the "time (sec)" column in Table 1.

## Additional Description

### Input Format

As mentioned in Section 7 of the paper, our tool takes fixed-point equation systems as input.
Most of the theoretical development in the paper, however, is presented using parity / Streett Markov chains, which are typically induced by probabilistic control-flow graphs (pCFGs).


#### Fixed-point equation systems (FES)

A fixed-point equation system is a list of equations of the following form.

$$ X_1(x) =_{\eta_1} F_1(X_1, \dots, X_n)(x);\\ X_2(x) =_{\eta_2} F_2(X_1, \dots, X_n)(x);\\ \vdots\\ X_n(x) =_{\eta_n} F_n(X_1, \dots, X_n)(x) $$

- LHS
  + Each $X_i$ is a $[0, 1]$-valued predicate variable, which we want to define as a fixed point.
  + $x$ denote the arguments for $X_i$. The arguments may consist of multiple variables, and they may differ for different predicate variables.
- $\eta_i \in \{ \mu, \nu \}$ indicate whether the equation defines a least fixed point ($\eta_i = \mu$) or a greatest fixed point ($\eta_i = \nu$).
- RHS
  $F_i(X_1, \dots, X_n)(x)$ is an expression that may contain the predicate variables $X_1, \dots, X_n$ and the arguments $x$.

The solution of the equation system depends on the order of the equations.

Benchmark example:
```
ASAT s.t.
X2 (m : real) (n : real) : real =nu X3 n n;
X3 (m : real) (n : real) : real =mu
  if m > 0.0 then (2.0 / 3.0) * X3 (m - 1.0) n + (1.0 / 3.0) * X3 (m + 1.0) n else X2 m (n + 1.0);
```

This file contains two fixed point equations: one defines `X2` as a greatest fixed point and the other defines `X3` as a least fixed point.

Both `X2` and `X3` take two arguments `m` and `n` of type `real`.
Currently, the only supported argument type is `real`.

The right-hand side of each equation specifies how the predicate variable is defined.

In the input file, the problem type is specified as `ASAT s.t.` where ASAT stands for "almost-sure satisfaction" problems.
In other words, the task is to verify whether the solution is 1 for all predicate variables and all possible values of their arguments.


#### pCFGs

In short, a pCFG is a Markov chain whose set of states is $\{ 1, \dots, L\} \times \mathbb{R}^n$.
Intuitively, a pCFG models an imperative probabilistic program with L locations and n real-valued variables.

We also consider a priority function $p$ defined on the pCFG.
In general, $p : \{ 1, \dots, L\} \times \mathbb{R}^n \to \{ 1, \dots, d \}$ is a function that maps a configuration $(l, v)$ to its priority.
However, without loss of generality, we assume that the priority depends only on the location.
Specifically, if a location has different priorities depending on the valuation $v \in \mathbb{R}^n$, we can duplicate the location and assign the corresponding priorities to the duplicated locations.
Therefore, we use $p : \{ 1, \dots, L\} \to \{ 1, \dots, d \}$ as a priority function.

We say that a trace satisfies the parity condition if the minimum priority that occurs infinitely often is even.

#### Correspondence between pCFGs and fixed-point equation systems
Fixed-point equation systems correspond to pCFGs with parity conditions (priority functions) as follows.

- Predicate variables in a FES correspond to locations in a pCFG.
- Arguments of predicate variables correspond to program variables in the pCFG.
- Predicate variables appearing earlier correspond to locations with smaller priorities. Furthermore, $\mu$ and $\nu$ correspond to odd and even priority, respectively.
- Probabilistic transitions in a pCFG correspond to unfolding fixed-point equations from the left-hand side to the right-hand side. The coefficient of each predicate variable corresponds to the probability of taking the corresponding branch.

For example, the benchmark file shown above corresponds to the pCFG with two locations (`X2` and `X3`) and 2 real-valued variables (`m` and `n`).
The priorities are assigned as follows:
- `X2` has priority 2 (the smallest even priority),
- `X3` has priority 3 (an odd priority greater than or equal to 2).
The transitions are given as follows.
- If the current state is (`X2`, (`m`, `n`)), the next state is (`X3`, (`n`, `n`)) with probability 1.
- If the current state is (`X3`, (`m`, `n`)):
  + if `m > 0.0`, then the next state is (`X3`, (`m - 1.0`, `n`)) with probability `2.0 / 3.0` and (`X3`, (`m + 1.0`, `n`)) with probability `1.0 / 3.0`;
  + otherwise the next state is (`X2`, (`m`, `n + 1.0`)).

In C-style code, this pCFG corresponds to the following probabilistic program.

```
X2: while (true) {
  m = n;
  X3: while (m > 0.0) {
    if (prob(2.0 / 3.0)) {
      m = m - 1;
    } else {
      m = m + 1;
    }
    n = n + 1;
  }
}
```

#### Invariant

We do not provide a dedicated syntax for specifying invariants.
However, invariants can be encoded by introducing a *dummy predicate variable* and redirecting all states outside the invariant to this variable.
The dummy predicate variable is defined by the greatest-fixed-point equation `Y =nu Y` and is placed as the last equation in the system.
Consequently, `Y` has the largest odd priority.


**Example**:
The following example specifies the invariant `m > -1.0 and n >= 0.0` for both `X2` and `X3`.
`Y` is the dummy predicate variable.
```
ASAT s.t.
X2 (m : real) (n : real) : real =nu
  if m > -1.0 and n >= 0.0 then X3 n n else Y;
X3 (m : real) (n : real) : real =mu
  if m > -1.0 and n >= 0.0 then if m > 0.0 then (2.0 / 3.0) * X3 (m - 1.0) n + (1.0 / 3.0) * X3 (m + 1.0) n else X2 m (n + 1.0) else Y;
Y : real =nu Y;
```
