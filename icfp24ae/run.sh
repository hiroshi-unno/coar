#!/bin/bash


TIMELIMIT=300
OUTPUTFILE="result.txt"
BENCHMARKPATH="./benchmarks/OCaml/probabilistic"
BENCHMARKS=(
	"lics16_rec3.ml"
	"lics16_rec3_ghost.ml"
	"lics16_coins.ml"
	"random_walk.ml"
	"random_walk_unif.ml"
	"coin_flip.ml"
	"coin_flip_unif.ml"
	"icfp21_walk.ml"
	"icfp21_coupons.ml"
	"lics16_fact.ml"
	"coin_flip_ord2.ml"
	"coin_flip_ord3.ml"
	"toplas18_ex4.4.ml"
	"two_coin_conditioning.ml"
)

# Ctrl-C
trap signalExit 2

function signalExit() {
	echo "Interrupted"
	exit 2
}

# VERIFIER="dune exec main --"
VERIFIER="./_build/default/main.exe"

function run_benchmark() {
	basename $1
	timeout $TIMELIMIT $VERIFIER -c ./config/solver/rcaml_pcsat_tb_ar.json -p ml $1
	if [ $? -eq 124 ]; then
		echo "TIMEOUT"
	fi
}

export TIMEFORMAT="%Es"
for bench in "${BENCHMARKS[@]}"
do
	(time run_benchmark $BENCHMARKPATH/$bench) 2>&1
	echo
done | tee $OUTPUTFILE
