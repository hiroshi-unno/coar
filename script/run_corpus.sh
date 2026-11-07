#!/bin/bash
# Runs a named benchmark run: one configuration of the tool (or of a foreign solver) over
# one input set, as a row of the tables of runs beside this script describes it.
#
#   run_corpus.sh CORPUS RUN              run it; the CSV of the runner, sorted, on stdout
#   run_corpus.sh --dry-run CORPUS RUN    print the command instead of running it
#   run_corpus.sh CORPUS                  list the runs of CORPUS
#   run_corpus.sh CORPUS --all [--out DIR]
#                                         run every run of CORPUS in table order, writing
#                                         DIR/RUN.csv (DIR defaults to the working directory)
#   run_corpus.sh --list                  list the corpora
#
# The tables are bench_runs.txt and, where it exists, bench_runs_private.txt, both beside
# this script; a run is looked up in both.  Each holds tab-separated rows
#
#   corpus  run  runner  timeout  para  env  options  inputs
#
# where `runner` is a path relative to this directory (normally run_bench.sh or one of its
# thin wrappers, or a race driver), `para` and `env` are `-` when unset, `env` holds extra
# NAME=VALUE assignments separated by spaces, `options` is passed verbatim, and `inputs`
# holds the input globs separated by spaces.  A run may have several rows; they are run in
# order, each one's output sorted on its own.  Lines starting with `#` are comments.
#
# A row is run exactly as the corpus wrapper it replaces ran it: from the working directory
# (normally the repository root), with the globs expanded there, as
#   timeout=T options=O [para=P] [ENV...] RUNNER INPUTS... | LC_ALL=C sort
# The environment variables `timeout` (or `BENCH_TIMEOUT`), `para` and `cmd` override a
# row's value, so a run can be repeated with a shorter limit, another degree of parallelism
# or another binary.
#
# Exit status: the first runner, sort or publication failure; 2 for a usage error
# or an unknown run.
set -u
set -o pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd) || exit 2
tables=()
for t in bench_runs.txt bench_runs_private.txt; do
	[ -f "$script_dir/$t" ] && tables+=("$script_dir/$t")
done

usage() {
	sed -n '2,13p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//' >&2
	exit 2
}

# rows: the table rows, comments and blank lines removed, in file order.
rows() {
	local t
	for t in "${tables[@]}"; do
		grep -v -e '^#' -e '^[[:space:]]*$' -- "$t"
	done
}

override_timeout=${timeout-${BENCH_TIMEOUT-}}
override_para=${para-}
override_cmd=${cmd-}
unset timeout para BENCH_TIMEOUT

# run_row DRY ROW: run (or print) one row.
run_row() {
	local dry=$1 row=$2
	local corpus run runner rtimeout rpara renv options inputs
	IFS=$'\t' read -r corpus run runner rtimeout rpara renv options inputs <<<"$row"
	local -a assign=("timeout=${override_timeout:-$rtimeout}" "options=$options")
	if [ -n "$override_para" ]; then
		assign+=("para=$override_para")
	elif [ "$rpara" != - ]; then
		assign+=("para=$rpara")
	fi
	if [ "$renv" != - ]; then
		local -a extra
		read -r -a extra <<<"$renv"
		assign+=("${extra[@]}")
	fi
	[ -n "$override_cmd" ] && assign+=("cmd=$override_cmd")
	# The globs are expanded here, in the working directory, as the wrapper's shell did.
	local -a args
	set +f
	# shellcheck disable=SC2206
	args=($inputs)
	if [ "$dry" = 1 ]; then
		printf 'env'
		printf ' %q' "${assign[@]}" "$script_dir/$runner" "${args[@]}"
		printf ' | LC_ALL=C sort\n'
		return 0
	fi
	env "${assign[@]}" "$script_dir/$runner" "${args[@]}" | LC_ALL=C sort
}

# run_named DRY CORPUS RUN: every row of the run, in order.
run_named() {
	local dry=$1 corpus=$2 run=$3 row c r status=0 rc
	local -a matched=()
	# Collected first, so that no runner inherits the table as its standard input.
	while IFS= read -r row; do
		IFS=$'\t' read -r c r _ <<<"$row"
		[ "$c" = "$corpus" ] && [ "$r" = "$run" ] && matched+=("$row")
	done < <(rows)
	if [ "${#matched[@]}" -eq 0 ]; then
		echo "run_corpus.sh: no run $run in corpus $corpus" >&2
		return 2
	fi
	for row in "${matched[@]}"; do
		run_row "$dry" "$row"
		rc=$?
		[ "$status" -eq 0 ] && status=$rc
	done
	return "$status"
}

runs_of() {
	rows | awk -F'\t' -v c="$1" '$1 == c && !seen[$2]++ { print $2 }'
}

# Publish one complete run, preserving the previous CSV on runner/sort failure.
# Staging beside the destination permits a rename without a cross-device copy.
publish_run() (
	local corpus=$1 run=$2 output=$3 temporary rc
	if [ -d "$output" ]; then
		echo "run_corpus.sh: output is a directory: $output" >&2
		return 2
	fi
	temporary=$(mktemp -- "$output.tmp.XXXXXX") || return $?
	trap 'rm -f -- "$temporary"' EXIT
	run_named 0 "$corpus" "$run" >"$temporary"
	rc=$?
	[ "$rc" -eq 0 ] || return "$rc"
	# Do not let mv interpret an existing destination directory as a container.
	if [ -d "$output" ]; then
		echo "run_corpus.sh: output is a directory: $output" >&2
		return 2
	fi
	mv -f -- "$temporary" "$output"
)

dry=0
if [ "${1-}" = --dry-run ]; then
	dry=1
	shift
fi
case $# in
0) usage ;;
esac
if [ "$1" = --list ]; then
	rows | awk -F'\t' '!seen[$1]++ { print $1 }'
	exit 0
fi
corpus=$1
shift
if [ $# -eq 0 ]; then
	list=$(runs_of "$corpus")
	[ -n "$list" ] || { echo "run_corpus.sh: no corpus $corpus" >&2; exit 2; }
	printf '%s\n' "$list"
	exit 0
fi
if [ "$1" = --all ]; then
	shift
	out=.
	if [ "${1-}" = --out ]; then
		[ $# -ge 2 ] || usage
		out=$2
		shift 2
	fi
	[ $# -eq 0 ] || usage
	list=$(runs_of "$corpus")
	[ -n "$list" ] || { echo "run_corpus.sh: no corpus $corpus" >&2; exit 2; }
	mkdir -p -- "$out" || exit 2
	status=0
	mapfile -t names <<<"$list"
	for run in "${names[@]}"; do
		echo "run_corpus.sh: $corpus $run" >&2
		if [ "$dry" = 1 ]; then
			run_named 1 "$corpus" "$run"
		else
			publish_run "$corpus" "$run" "$out/$run.csv"
		fi
		rc=$?
		[ "$status" -eq 0 ] && status=$rc
	done
	exit "$status"
fi
[ $# -eq 1 ] || usage
run_named "$dry" "$corpus" "$1"
