# Refusing to sweep over inputs that are not there.  Source this:
#   . "$(dirname "$0")/../inputs_present.sh"
#
# A list of inputs is a claim about the disk only when it was made by reading the disk.  `git
# ls-files` reads the index, so in a sparse worktree it lists files that are absent; a fixed list
# names files that a move or an uninitialised submodule took away.  The tool answers an absent
# input with `cannot read <file>: no such file` and exit 1, and a comparison of two runs then sees
# the same crash on both sides and calls the file "identical" -- a sweep over a tree where most of
# the corpus was absent would report full agreement without having solved anything.  So a sweep
# counts what it could not read before it runs, and refuses unless told to go on without it.
#
# present_inputs <list> <out> <what>
#   Copies the paths of <list> (one per line, blank lines ignored) that are readable regular files
#   to <out>, and reports the rest on stderr.  Returns 1 when some path is absent or unreadable,
#   unless ALLOW_MISSING=1, under which it returns 0 and the sweep runs over <out> alone; and
#   returns 1 when <out> is empty, since a sweep over no file agrees with everything.
present_inputs() {
  local list=$1 out=$2 what=$3 f n m
  : > "$out"; m=0
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    if [ -f "$f" ] && [ -r "$f" ]; then printf '%s\n' "$f" >> "$out"
    else
      m=$((m + 1))
      [ "$m" -le 5 ] && echo "    absent or unreadable: $f" >&2
    fi
  done < "$list"
  n=$(grep -c . "$out")
  if [ "$m" -gt 0 ]; then
    echo "MISSING: $m of $((n + m)) listed inputs of $what are not on the disk or not readable" >&2
    if [ "${ALLOW_MISSING:-0}" != 1 ]; then
      echo "    (a sparse worktree or an uninitialised submodule?)  Run in a full checkout, or set" >&2
      echo "    ALLOW_MISSING=1 to sweep over the $n that are present." >&2
      return 1
    fi
    echo "    ALLOW_MISSING=1: sweeping over the $n that are present" >&2
  fi
  [ "$n" -gt 0 ] || { echo "NO INPUTS: the list of $what is empty" >&2; return 1; }
  return 0
}
