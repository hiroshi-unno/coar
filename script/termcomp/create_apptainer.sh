#!/bin/bash
# Conversion from a Docker image to an Apptainer image and functional testing of the converted image

# strict mode
set -euo pipefail
IFS=$'\n\t'

SCRIPT_DIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)
# If the path contains “..”, Apptainer binding will not work correctly
REPO_ROOT_DIR=$(cd "$SCRIPT_DIR/../.." && pwd)

# Convert existing docker image into apptainer image
sif_filepath="$SCRIPT_DIR/coar.sif"
apptainer build -F $sif_filepath docker-daemon://termcomp:latest

# test for solver command in apptainer image
echo "Test of \`solver --name\`..."
apptainer exec $sif_filepath solver --name

echo "Test for Integer_Transition_Systems category..."
apptainer exec --writable-tmpfs -C \
    --bind $REPO_ROOT_DIR/benchmarks/term-comp-ari:$REPO_ROOT_DIR/benchmarks/term-comp-ari \
    $sif_filepath \
    solver --timeout=60 --category=Integer_Transition_Systems \
    $REPO_ROOT_DIR/benchmarks/term-comp-ari/Integer_Transition_Systems/From_AProVE_2014/Velroyen08-alternDiv.jar-obl-8.ari 2> /dev/null
printf "\n"

echo "Test for C category..."
apptainer exec --writable-tmpfs -C \
    --bind $REPO_ROOT_DIR/benchmarks/term-comp:$REPO_ROOT_DIR/benchmarks/term-comp \
    $sif_filepath \
    solver --timeout=60 --category=C \
    $REPO_ROOT_DIR/benchmarks/term-comp/C/AProVE_memory_alloca/svcomp_a.04-alloca.c 2> /dev/null
printf "\n"

# echo "Test for different user and working directory..."
# apptainer exec --writable-tmpfs -C -u --fakeroot \
#     --bind $REPO_ROOT_DIR/benchmarks/term-comp:$REPO_ROOT_DIR/benchmarks/term-comp \
#     $sif_filepath \
#     su -s /bin/bash -c "cd .. && echo \"pwd: \$(pwd)\" && echo \"whoami: \$(whoami)\" && solver --timeout=60 --category=Integer_Transition_Systems \
#     $REPO_ROOT_DIR/benchmarks/term-comp/Integer_Transition_Systems/From_AProVE_2014/Velroyen08-alternDiv.jar-obl-8.smt2" testuser