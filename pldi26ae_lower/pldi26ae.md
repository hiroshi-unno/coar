# PLDI 2026 Artifact Evaluation

## Basic Information

- Artifact URL: The artifact is available at [Zenodo](https://doi.org/10.5281/zenodo.19068568).
- Paper: Supermartingales for Unique Fixed Points: A Unified Approach to Lower Bound Verification

## Setup

### Option 1: Loading Docker Image (Recommended)
To load the docker image, run the following command:
```bash
sudo docker load -i muval_pldi26ae_lower.tar
```

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
The meaning of each least-fixed-point equation is self-explanatory.

```
X2 1.0 >= 33.0
s.t.
X1 (x : real) : real =mu
  if x > 0.0 then (2.0 / 3.0) * X1 (x - 1.0) + (1.0 / 3.0) * X1 (x + 1.0) + 1.0 else 0.0;
X2 (x : real) : real =mu
  if x > 0.0 then (2.0 / 3.0) * X2 (x - 1.0) + (1.0 / 3.0) * X2 (x + 1.0) +
                  2.0 * ((2.0 / 3.0) * X1 (x - 1.0) + (1.0 / 3.0) * X1 (x + 1.0)) + 1.0 else 0.0;
```
