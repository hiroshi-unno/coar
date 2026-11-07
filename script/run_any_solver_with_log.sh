#!/bin/bash
# A foreign solver over a corpus, keeping each run's stdout and stderr in the working
# directory as NAME.log and NAME.err: `options` is the whole command, the solver and its flags.
# Three runs at a time, no restart.
[ -n "${timeout-}" ] || { echo "e.g., timeout=10 ... $0" >&2; exit 2; }
[ -n "${options-}" ] || { echo "e.g., options='hoice [OPTIONs of hoice]' ... $0" >&2; exit 2; }
read -r -a words <<<"$options"
# A solver given without flags gets the options " ", which run_bench.sh accepts as set and
# which expands to no word.
rest="${words[*]:1}"
exec env cmd="${words[0]}" options="${rest:- }" para="${para:-3}" retries=0 logdir=. \
	"$(dirname -- "$0")/run_bench.sh" "$@"
