#!/bin/bash
# Ranking functions and their arguments against solving time, for MuValPPM (SCC & AD).
#
#   ./popl27ae/rankcount.sh            count, then tabulate and plot
#   ./popl27ae/rankcount.sh --no-count tabulate and plot from the counts already in results/rankcount
#
# Counting runs the tool once per benchmark of the two corpora with the SCC & AD configuration and its
# `output_reduction_stats` switch on, which prints one `reduction-stats:` line per side (primal, dual)
# as soon as that side has been reduced to a pfwCSP, before any solving.  A run is stopped once both
# lines are printed, or at the time limit (RANKCOUNT_TIMEOUT, default 300 seconds), so most runs take a
# second or two.  The counts go to results/rankcount/{popl2023mod,term25its}.stats.
#
# Tabulating joins those counts with the SCC & AD results of runall.sh
# (results/{popl2023mod,term25its}/muval_ppm_popl27.csv), prints the distribution of solving times by the
# number of ranking functions, and draws the number of their arguments against the solving time
# (results/fig/rfargs_vs_time_{popl23,its}.pdf).  It then does the same for the alternation depth, the
# number of nontrivial strongly connected components and the number of ranking functions, with their
# distributions and rank correlations with the solving time (params.py).  Further arguments (`--latex`,
# `--timeout 60`) go to rankcount.py and params.py.
set -e
set -o pipefail

artifact_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd -- "$artifact_dir/.."

count=1
if [ "${1-}" = --no-count ]; then
  count=0
  shift
fi

out=results/rankcount
mkdir -p "$out" results/fig

# count_one PROBLEM FILE: the input's reduction-stats lines, each prefixed by FILE and a tab.
count_one() {
  local p=$1 f=$2 err pid line status=0 stopped=0
  err=$(mktemp "$RC_TMP/run.XXXXXX") || return 1
  # -k: a count still alive 30 s after the TERM is killed (status 137), so a run that
  # cannot act on TERM (its host out of memory) does not hold the count open
  timeout -s TERM -k 30 "$RC_LIMIT" ./_build/default/main.exe -c "$RC_CONFIG" -p "$p" "$f" > /dev/null 2> "$err" &
  pid=$!
  while kill -0 "$pid" 2> /dev/null; do
    if [ "$(grep -c '^reduction-stats:' "$err")" -ge 2 ]; then
      # timeout passes the signal on to the tool
      if kill -TERM "$pid" 2> /dev/null; then
        stopped=1
      fi
      break
    fi
    sleep 0.2
  done
  wait "$pid" 2> /dev/null || status=$?
  if [ "$status" -eq 137 ]; then
    # killed after the grace or by the kernel's OOM killer: its printed lines still count
    printf 'Counting %s: killed (exit 137); using the lines it printed\n' "$f" >&2
  elif [ "$status" -ne 0 ] && [ "$status" -ne 124 ] &&
     ! { [ "$stopped" = 1 ] && [ "$status" -eq 143 ]; }; then
    printf 'Counting %s failed (exit %s):\n' "$f" "$status" >&2
    cat -- "$err" >&2
    rm -f -- "$err"
    return "$status"
  fi
  while IFS= read -r line; do
    case "$line" in
      reduction-stats:*) printf '%s\t%s\n' "$f" "$line" ;;
    esac
  done < "$err"
  rm -f -- "$err"
}

# count_corpus NAME PROBLEM GLOB...: counts every input of the corpus into results/rankcount/NAME.stats.
count_corpus() (
  local name=$1 p=$2 temporary output counted
  shift 2
  output=$out/$name.stats
  if [ -d "$output" ]; then
    echo "rankcount.sh: output is a directory: $output" >&2
    return 2
  fi
  temporary=$(mktemp -- "$output.tmp.XXXXXX") || return $?
  trap 'rm -f -- "$temporary"' EXIT
  echo "=== counting $name ($# benchmarks) ===" >&2
  if ! printf '%s\0' "$@" | xargs -0 -n 1 -P "${para:-2}" bash -c 'count_one "$0" "$1"' "$p" \
    | LC_ALL=C sort > "$temporary"; then
    return 1
  fi
  # Do not let mv interpret an existing destination directory as a container.
  if [ -d "$output" ]; then
    echo "rankcount.sh: output is a directory: $output" >&2
    return 2
  fi
  counted=$(cut -f1 "$temporary" | sort -u | wc -l) || return $?
  mv -f -- "$temporary" "$output" || return $?
  echo "$name: $counted of $# benchmarks counted" >&2
)

if [ "$count" = 1 ]; then
  RC_LIMIT=${RANKCOUNT_TIMEOUT:-300}
  RC_LIMIT=$(python3 - "$artifact_dir" "$RC_LIMIT" << 'EOF'
import argparse, sys
sys.path.insert(0, sys.argv[1])
from summarize_results import timeout_seconds
try:
    print(timeout_seconds(sys.argv[2]))
except argparse.ArgumentTypeError as error:
    sys.exit(f"Invalid RANKCOUNT_TIMEOUT: {error}")
EOF
  )
  RC_TMP=$(mktemp -d)
  trap 'rm -rf -- "$RC_TMP"' EXIT
  RC_CONFIG=$RC_TMP/muval_ppm_scc_ad_stats.json
  # The SCC & AD configuration of runall.sh, with the one switch that prints the counts.
  python3 - config/solver/muval_ppm_popl27.json "$RC_CONFIG" << 'EOF'
import json, sys
cfg = json.load(open(sys.argv[1]))
cfg[1]["output_reduction_stats"] = True
json.dump(cfg, open(sys.argv[2], "w"), indent=1)
EOF
  export RC_TMP RC_CONFIG RC_LIMIT
  export -f count_one
  # The inputs of the SCC & AD runs (script/bench_runs.txt).
  count_corpus popl2023mod muclp benchmarks/muCLP/popl2023mod/*.hes benchmarks/muCLP/popl2023mod/*/*/*.hes
  count_corpus term25its pltsterm \
    benchmarks/term-comp/Integer_Transition_Systems/From_AProVE_2014/*.smt2 \
    benchmarks/term-comp/Integer_Transition_Systems/From_T2/*.smt2
fi

# One `<corpus> <seconds>` line per corpus: the time limit its results record.
limits=$(python3 "$artifact_dir/rankcount.py" --prepare "$PWD" "$@")
while read -r name seconds; do
  gnuplot -e "TO=$seconds" "$artifact_dir/fig/rf/rfargs_vs_time_$name.plt"
done <<< "$limits"
python3 "$artifact_dir/rankcount.py" --table "$PWD" "$@"

# The same counts characterise the benchmarks by alternation depth, nontrivial SCCs and ranking
# functions (params.py): the joined rows go to results/params/{popl2023mod,term25its}.csv, a figure per
# parameter and corpus to results/fig/{ad,scc,rf}_vs_time_{popl23,its}.pdf.
limits=$(python3 "$artifact_dir/params.py" --prepare "$PWD" "$@")
while read -r name seconds; do
  case "$name" in popl23) corpus=popl2023mod ;; its) corpus=term25its ;; esac
  for spec in "ad 4 0 alternation depth" "scc 5 1 #nontrivial SCCs" "rf 6 1 #ranking functions"; do
    read -r param col logx label <<< "$spec"
    gnuplot -e "TO=$seconds; CSV='results/params/$corpus.csv'; OUT='results/fig/${param}_vs_time_$name.pdf'; COL=$col; LOGX=$logx; XLABEL='$label'" \
      "$artifact_dir/fig/params/param_vs_time.plt"
  done
done <<< "$limits"
echo
python3 "$artifact_dir/params.py" --table "$PWD" "$@"
