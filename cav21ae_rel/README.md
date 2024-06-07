# CAV21 Artifact Evaluation: PCSat

We explain how to use PCSat, a pfwCSP constraint solver.
Technical details are explained in the following paper.

Hiroshi Unno, Tachio Terauchi, and Eric Koskinen. Constraint-based Relational Verification. CAV 2021.

## Getting Started

### Using Dockerfile

1. Download `cav21ae_rel/Dockerfile` from [the repository](https://github.com/hiroshi-unno/coar)

2. Build a docker image (about 30 min)
    
    ```bash
    cd /path/to/Dockerfile
    sudo docker build -t cav21ae_pcsat .
    ```
    This will make a docker image tagged with `cav21ae_pcsat:latest`.

3. Run the image
    ```bash
    sudo docker run -it cav21ae_pcsat:latest /bin/bash --login
    ```
    Now, you are ready to conduct experiments.

## Reproducing Experimental Results

Before proceeding, make sure that the following file and directory are in the home directory of the docker container.

- `cav2021rel.pdf`: our paper (downloaded from [here](https://www.riec.tohoku.ac.jp/~unno/papers/cav2021rel.pdf))
- `coar`: directory of our artifact

Please run the following command.
```bash
cd ~/coar/cav21ae_rel
./exp.sh
```
This will reproduce the experimental results shown in Table 1 in the paper.
