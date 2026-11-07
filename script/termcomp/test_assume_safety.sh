#! /bin/bash

# Test script for Ptr2Arr's --assume-safety mode in the termcomp Docker container (the repository
# mounted at /root/coar, as compose.yaml does).
#
# Each program under assume_safety/ goes through the C_assume category of this directory's
# solver.sh, and the verdict must be the one its `EXPECT:` comment states. Besides, Ptr2Arr must
# refuse --memory-safety and --assume-safety together.
#
# PTR2ARR_DIR=<dir> tests another build: a directory holding `Ptr2Arr` and
# `ptr2arr_runtime_stubs.h`, which Ptr2Arr copies next to its output. The default is the image's
# own. The last two lines are a count and DONE, and the exit status is 0 only when every check passed.

set -u

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
inputs="$script_dir/assume_safety"
ptr2arr_dir=${PTR2ARR_DIR:-/usr/local/bin}

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

pass=0
fail=0
report() {
    if [ "$1" -eq 0 ]; then
        pass=$((pass + 1))
        echo "PASS $2"
    else
        fail=$((fail + 1))
        echo "FAIL $2"
    fi
}

cd "$work" || exit 1
"$ptr2arr_dir/Ptr2Arr" --memory-safety --assume-safety "$inputs/scan.c" > refused.log 2>&1
rc=$?
# The message, not only the status: a Ptr2Arr without --assume-safety also exits 1, on the
# unknown option.
[ "$rc" -ne 0 ] && grep -q "cannot be combined" refused.log
report $? "--memory-safety with --assume-safety is refused (exit status $rc)"

for src in "$inputs"/*.c; do
    name=$(basename "$src" .c)
    expect=$(sed -n 's/.*EXPECT: \([A-Z]*\).*/\1/p' "$src" | head -n 1)
    PATH="$ptr2arr_dir:$PATH" timeout 600 bash "$script_dir/solver.sh" --category=C_assume "$src" \
        > "$work/$name.out" 2> "$work/$name.err"
    rc=$?
    verdict=$(tail -n 1 "$work/$name.out")
    [ -n "$expect" ] && [ "$verdict" = "$expect" ]
    report $? "$name: expected ${expect:-<no EXPECT line>}, got ${verdict:-no answer} (exit status $rc)"
done

echo "$pass passed, $fail failed"
echo DONE
[ "$fail" -eq 0 ]
