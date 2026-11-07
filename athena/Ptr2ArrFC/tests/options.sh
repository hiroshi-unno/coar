#!/bin/bash
# Which combinations of options the executable and the plugin accept.
#
# usage: tests/options.sh [WORKDIR]
#
# Every case runs ptr2arr, or the plugin with Frama-C's own command line (the
# executable's Frama-C child, PTR2ARR_FRAMAC_CHILD=1), and compares the exit
# status with the expected one: 1 for a combination the options exclude (an
# option given with an action that does not use it, two actions, two modes,
# an option given twice with different values in one run, an invalid value,
# two input files), 0 for one they allow. A refused case also names a
# fragment of the message it must be refused with, so that a case refused for
# another reason fails. An option counts as given whatever its value, its
# default included. One line per case (ok or FAIL, status got/expected, the
# command); the script ends with the counts and the line DONE, and exits 1 if
# a case failed.
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
exe="$here/_build/default/bin/ptr2arr.exe"
[ -x "$exe" ] || { echo "missing $exe; build with: dune build --root $here"; exit 1; }
work=${1:-$(mktemp -d)}
mkdir -p "$work"
work=$(cd "$work" && pwd)
in="$here/tests/cases/c01_addr_of_local.c"
in2="$here/tests/cases/c03_global.c"
# the executable's front-end settings, for the plugin cases
fe=(-machdep gcc_x86_64 -no-frama-c-stdlib -kernel-warn-key CERT:MSC:38=active
    -no-variadic-translation -no-autoload-plugins -cpp-extra-args=-std=gnu11,-m64)
fe_no_machdep=(-no-frama-c-stdlib -kernel-warn-key CERT:MSC:38=active
               -no-variadic-translation -no-autoload-plugins -cpp-extra-args=-std=gnu11)

pass=0; fail=0
# run WANT WHY COMMAND...: WANT the exit status; WHY, for a refusal, a
# fragment of the message it must print
run() {
  local want=$1 why=$2; shift 2
  (cd "$work" && "$@") > "$work/last.log" 2>&1
  local got=$?
  local r=ok
  if [ "$got" != "$want" ]; then r=FAIL
  elif [ -n "$why" ] && ! grep -qF -- "$why" "$work/last.log"; then r=FAIL
  fi
  if [ $r = ok ]; then pass=$((pass + 1)); else fail=$((fail + 1)); fi
  printf '%s\t%s/%s\t%s\n' "$r" "$got" "$want" "$*" \
    | sed "s#$exe#ptr2arr#g; s#$in#IN#g; s#$in2#IN2#g; s#${fe[*]}#FE#; s#${fe_no_machdep[*]}#FE-without-machdep#"
  if [ "$got" = 1 ]; then
    grep -m1 -E '^ptr2arr: |User Error' "$work/last.log" | sed 's/^/    /'
  fi
  if [ $r = FAIL ]; then
    [ -n "$why" ] && echo "    expected a message with: $why"
    sed 's/^/    /' "$work/last.log" | tail -3
  fi
}
# the executable
x() { local want=$1 why=$2; shift 2; run "$want" "$why" "$exe" "$@"; }
# the plugin, with the executable's front-end settings
p() { local want=$1 why=$2; shift 2; run "$want" "$why" env PTR2ARR_FRAMAC_CHILD=1 "$exe" "${fe[@]}" "$@"; }
# the plugin without -machdep
q() { local want=$1 why=$2; shift 2; run "$want" "$why" env PTR2ARR_FRAMAC_CHILD=1 "$exe" "${fe_no_machdep[@]}" "$@"; }

echo "== inputs for the actions that read an output"
x 0 "" -o out.c "$in"
x 0 "" --wrap-integers -o wout.c "$in"
x 0 "" --data-model=ILP32 -o out32.c "$in"
x 0 "" --data-model=ILP32 --wrap-integers -o wout32.c "$in"

echo "== executable: excluded"
x 1 "exclude each other" --memory-safety --assume-safety -o e.c "$in"
x 1 "used only with --memory-safety" --violation-markers=split -o e.c "$in"
x 1 "used only with --memory-safety" --assume-safety --violation-markers=reach-error -o e.c "$in"
x 1 "invalid --violation-markers" --memory-safety --violation-markers=bogus -o e.c "$in"
x 1 "invalid --data-model" --data-model=X32 -o e.c "$in"
x 1 "invalid --unsupported" --unsupported=bogus -o e.c "$in"
x 1 "invalid --points-to" --points-to=bogus -o e.c "$in"
x 1 "invalid --region-size" --region-size=ten -o e.c "$in"
x 1 "--region-size must be at least 2" --region-size=1 -o e.c "$in"
x 1 "--allow-pointers is not used with the transformation" --allow-pointers -o e.c "$in"
x 1 "--check and --identity exclude each other" --check --identity out.c
x 1 "--check and --monitor exclude each other" --check --monitor out.c
x 1 "--check and --z-reading exclude each other" --check --z-reading out.c
x 1 "--identity and --monitor exclude each other" --identity --monitor -o e.c "$in"
x 1 "--identity and --z-reading exclude each other" --identity --z-reading -o e.c "$in"
x 1 "--monitor and --z-reading exclude each other" --monitor --z-reading -o e.c "$in"
# the modes
x 1 "--memory-safety and --memory-cleanup exclude each other" --memory-safety --memory-cleanup -o e.c "$in"
x 1 "--memory-cleanup and --assume-safety exclude each other" --memory-cleanup --assume-safety -o e.c "$in"
x 1 "--memory-cleanup and --memory-safety exclude each other" --memory-cleanup --memory-safety -o e.c "$in"
x 1 "--violation-markers is used only with --memory-safety or --memory-cleanup" \
    --violation-markers=reach-error -o e.c "$in"
x 1 "--memtrack-check is used only with --memory-safety" --memtrack-check=guess -o e.c "$in"
x 1 "--memtrack-check is used only with --memory-safety" --memory-cleanup --memtrack-check=fixpoint -o e.c "$in"
x 1 "--memtrack-check is used only with --memory-safety" --assume-safety --memtrack-check=guess -o e.c "$in"
x 1 "invalid --memtrack-check" --memory-safety --memtrack-check=bogus -o e.c "$in"
x 1 "--memtrack-check given twice" --memory-safety --memtrack-check=guess \
    --memtrack-check=fixpoint -o e.c "$in"
x 1 "--memtrack-nonterminating is used only with --memory-safety or --memory-cleanup" \
    --memtrack-nonterminating -o e.c "$in"
x 1 "--memtrack-nonterminating is used only with --memory-safety or --memory-cleanup" \
    --assume-safety --memtrack-nonterminating -o e.c "$in"
x 1 "--memtrack-check is used only with --memory-safety, or --memory-cleanup and --memtrack-nonterminating" \
    --memory-cleanup --memtrack-check=guess -o e.c "$in"
for o in --memory-safety --memory-cleanup --assume-safety --wrap-integers -o --record=e.json \
         --unsupported=warn --region-size=10 --points-to=steens --violation-markers=split \
         --memtrack-check=guess --memtrack-nonterminating; do
  if [ "$o" = -o ]; then x 1 "-o is not used with --check" --check -o e.c out.c; continue; fi
  x 1 "${o%%=*} is not used with --check" --check "$o" out.c
done
for a in --identity --monitor --z-reading; do
  for o in --memory-safety --memory-cleanup --assume-safety --wrap-integers --region-size=10 \
           --violation-markers=split --memtrack-check=fixpoint --memtrack-nonterminating \
           --allow-pointers; do
    x 1 "${o%%=*} is not used with $a" $a "$o" -o e.c "$in"
  done
done
x 1 "--points-to is not used with --identity" --identity --points-to=steens -o e.c "$in"
x 1 "--points-to is not used with --z-reading" --z-reading --points-to=steens -o e.c wout.c
x 1 "-o given twice" -o a.c -o b.c "$in"
x 1 "--record given twice" --record=a.json --record=b.json -o e.c "$in"
x 1 "--unsupported given twice" --unsupported=error --unsupported=warn -o e.c "$in"
x 1 "--region-size given twice" --region-size=10 --region-size=20 -o e.c "$in"
x 1 "--points-to given twice" --points-to=steens --points-to=alias -o e.c "$in"
x 1 "--violation-markers given twice" --memory-safety --violation-markers=split \
    --violation-markers=reach-error -o e.c "$in"
x 1 "--data-model given twice" --data-model=LP64 --data-model=ILP32 -o e.c "$in"
x 1 "--frama-c given twice" --frama-c=-kernel-verbose=0 --frama-c=-kernel-verbose=1 -o e.c "$in"
x 1 "--clang given twice" --clang=clang-19 --clang=clang-18 -o e.c "$in"
x 1 "--clang and --gcc exclude each other" --clang=clang-19 --gcc -o e.c "$in"
x 1 "exactly one input file" -o e.c "$in" "$in2"
x 1 "exactly one input file" --check out.c out32.c
# a front-end setting given through --frama-c may not contradict the data model
x 1 "reads the input with -machdep gcc_x86_64" "--frama-c=-machdep gcc_x86_32" -o e.c "$in"
x 1 "reads the input with -machdep gcc_x86_64" --data-model=LP64 "--frama-c=-machdep gcc_x86_32" -o e.c "$in"
x 1 "preprocesses with -m32" --data-model=ILP32 --frama-c=-cpp-extra-args=-m64 -o e.c "$in"

echo "== executable: allowed"
x 0 "" -o a0.c "$in"
# the preprocessor: clang-19 from PATH by default, the one --clang names, or
# gcc with --gcc; an input including glibc's headers reads in each, in both
# data models, the check of an output too, and a clang that cannot be run
# leaves the input unreadable
x 0 "" -o c0.c "$here/tests/cases/c02_malloc_array.c"
x 0 "" --clang=clang-19 --data-model=ILP32 -o c1.c "$here/tests/cases/c02_malloc_array.c"
x 0 "" --gcc -o c2.c "$here/tests/cases/c02_malloc_array.c"
x 0 "" --gcc --data-model=ILP32 -o c3.c "$here/tests/cases/c02_malloc_array.c"
x 0 "" --check --clang=clang-19 c0.c
x 0 "" --check --gcc c0.c
x 0 "" --identity --gcc -o c4.c "$in"
x 1 "" --clang=/nonexistent/clang -o e.c "$in"
x 0 "" --memory-safety -o a1.c "$in"
x 0 "" --assume-safety -o a2.c "$in"
x 0 "" --memory-safety --violation-markers=split -o a3.c "$in"
x 0 "" --memory-safety --violation-markers=reach-error -o a4.c "$in"
x 0 "" --wrap-integers --record=a5.json --unsupported=warn --region-size=1000 \
    --points-to=steens --data-model=LP64 --frama-c=-kernel-verbose=0 -o a5.c "$in"
x 0 "" --data-model=ILP32 -o a6.c "$in"
x 0 "" --memory-safety --memory-safety -o a7.c -o a7.c --data-model=ILP32 --data-model=ILP32 "$in"
x 0 "" --region-size=100 --region-size=0100 -o a8.c "$in"
x 0 "" --assume-safety --data-model=ILP32 -o a9.c "$in"
x 0 "" --memory-safety --violation-markers=reach-error --wrap-integers --data-model=ILP32 \
    --region-size=50 --points-to=steens --unsupported=warn --record=a10.json -o a10.c "$in"
x 0 "" --data-model=ILP32 "--frama-c=-machdep gcc_x86_32" -o a11.c "$in"
x 0 "" --memory-cleanup -o a18.c "$in"
x 0 "" --memory-cleanup --violation-markers=reach-error --data-model=ILP32 -o a19.c "$in"
x 0 "" --memory-safety --memtrack-check=fixpoint -o a20.c "$in"
x 0 "" --memory-safety --memtrack-check=guess --violation-markers=reach-error -o a21.c "$in"
x 0 "" --memtrack-check=fixpoint --memory-safety --memtrack-check=fixpoint -o a22.c "$in"
x 0 "" --memory-safety --memtrack-nonterminating -o a23.c "$in"
x 0 "" --memory-cleanup --memtrack-nonterminating --memtrack-check=fixpoint -o a24.c "$in"
x 0 "" --memory-cleanup --memtrack-nonterminating --memtrack-nonterminating --data-model=ILP32 -o a25.c "$in"
x 0 "" --check out.c
x 0 "" --check --allow-pointers --data-model=LP64 --frama-c=-kernel-verbose=0 out.c
x 0 "" --check --data-model=ILP32 out32.c
x 0 "" --identity -o a12.c --record=a12.json --unsupported=warn --data-model=LP64 \
    --frama-c=-kernel-verbose=0 "$in"
x 0 "" --identity --data-model=ILP32 -o a13.c "$in"
x 0 "" --monitor --points-to=steens -o a14.c --record=a14.json --unsupported=warn --data-model=LP64 "$in"
x 0 "" --monitor --data-model=ILP32 -o a15.c "$in"
x 0 "" --z-reading -o a16.c --record=a16.json --unsupported=warn --data-model=LP64 wout.c
x 0 "" --z-reading --data-model=ILP32 -o a17.c wout32.c

echo "== plugin: excluded"
p 1 "-ptr2arr-mode given twice" "$in" -ptr2arr -ptr2arr-mode memory-safety -ptr2arr-mode assume-safety
p 1 "-ptr2arr-mode given twice" "$in" -ptr2arr -ptr2arr-mode normal -ptr2arr-mode memory-safety
p 1 "used only with -ptr2arr-mode memory-safety" "$in" -ptr2arr -ptr2arr-violation-markers split
p 1 "used only with -ptr2arr-mode memory-safety" "$in" -ptr2arr -ptr2arr-mode normal \
    -ptr2arr-violation-markers split
p 1 "used only with -ptr2arr-mode memory-safety" "$in" -ptr2arr -ptr2arr-mode assume-safety \
    -ptr2arr-violation-markers reach-error
p 1 "invalid -ptr2arr-violation-markers" "$in" -ptr2arr -ptr2arr-mode memory-safety \
    -ptr2arr-violation-markers bogus
p 1 "invalid -ptr2arr-mode" "$in" -ptr2arr -ptr2arr-mode bogus
p 1 "-ptr2arr-mode given twice" "$in" -ptr2arr -ptr2arr-mode memory-safety -ptr2arr-mode memory-cleanup
p 1 "-ptr2arr-memtrack-check is used only with -ptr2arr-mode memory-safety" "$in" -ptr2arr \
    -ptr2arr-memtrack-check guess
p 1 "-ptr2arr-memtrack-check is used only with -ptr2arr-mode memory-safety" "$in" -ptr2arr \
    -ptr2arr-mode memory-cleanup -ptr2arr-memtrack-check fixpoint
p 1 "-ptr2arr-memtrack-check is used only with -ptr2arr-mode memory-safety" "$in" -ptr2arr \
    -ptr2arr-mode assume-safety -ptr2arr-memtrack-check guess
p 1 "invalid -ptr2arr-memtrack-check" "$in" -ptr2arr -ptr2arr-mode memory-safety \
    -ptr2arr-memtrack-check bogus
p 1 "-ptr2arr-memtrack-check given twice" "$in" -ptr2arr -ptr2arr-mode memory-safety \
    -ptr2arr-memtrack-check guess -ptr2arr-memtrack-check fixpoint -ptr2arr-output e.c
p 1 "used only with -ptr2arr-mode memory-safety or memory-cleanup" "$in" -ptr2arr \
    -ptr2arr-mode assume-safety -ptr2arr-violation-markers split
p 1 "-ptr2arr-memtrack-nonterminating is used only with -ptr2arr-mode memory-safety or memory-cleanup" \
    "$in" -ptr2arr -ptr2arr-memtrack-nonterminating
p 1 "-ptr2arr-memtrack-nonterminating given twice" "$in" -ptr2arr -ptr2arr-mode memory-safety \
    -ptr2arr-memtrack-nonterminating -ptr2arr-no-memtrack-nonterminating -ptr2arr-output e.c
p 1 "invalid -ptr2arr-data-model" "$in" -ptr2arr -ptr2arr-data-model X32
p 1 "reads the input with -machdep gcc_x86_32" "$in" -ptr2arr -ptr2arr-data-model ILP32
p 1 "-ptr2arr-check-allow-pointers is not used with the transformation" "$in" -ptr2arr \
    -ptr2arr-check-allow-pointers
p 1 "-ptr2arr is not used with -ptr2arr-check" out.c -ptr2arr -ptr2arr-check
p 1 "-ptr2arr-check and -ptr2arr-identity exclude each other" out.c -ptr2arr-check -ptr2arr-identity
p 1 "-ptr2arr-check and -ptr2arr-monitor exclude each other" out.c -ptr2arr-check -ptr2arr-monitor
p 1 "-ptr2arr-check and -ptr2arr-z-reading exclude each other" out.c -ptr2arr-check -ptr2arr-z-reading
p 1 "exclude each other" "$in" -ptr2arr -ptr2arr-identity -ptr2arr-monitor
p 1 "exclude each other" "$in" -ptr2arr -ptr2arr-identity -ptr2arr-z-reading
p 1 "exclude each other" "$in" -ptr2arr -ptr2arr-monitor -ptr2arr-z-reading
for o in "-ptr2arr-mode normal" "-ptr2arr-mode memory-safety" -ptr2arr-wrap-integers \
         "-ptr2arr-output e.c" "-ptr2arr-record e.json" "-ptr2arr-unsupported warn" \
         "-ptr2arr-region-size 10" "-ptr2arr-points-to steens" \
         "-ptr2arr-violation-markers split" "-ptr2arr-mode memory-cleanup" \
         "-ptr2arr-memtrack-check guess" -ptr2arr-memtrack-nonterminating; do
  # shellcheck disable=SC2086
  p 1 "${o%% *} is not used with -ptr2arr-check" out.c -ptr2arr-check $o
done
for a in -ptr2arr-identity -ptr2arr-monitor -ptr2arr-z-reading; do
  for o in "-ptr2arr-mode normal" "-ptr2arr-mode assume-safety" -ptr2arr-wrap-integers \
           "-ptr2arr-region-size 10" "-ptr2arr-violation-markers split" \
           "-ptr2arr-mode memory-cleanup" "-ptr2arr-memtrack-check fixpoint" \
           -ptr2arr-memtrack-nonterminating -ptr2arr-check-allow-pointers; do
    # shellcheck disable=SC2086
    p 1 "${o%% *} is not used with $a" "$in" -ptr2arr $a $o -ptr2arr-output e.c
  done
done
p 1 "-ptr2arr-points-to is not used with -ptr2arr-identity" "$in" -ptr2arr -ptr2arr-identity \
    -ptr2arr-points-to steens -ptr2arr-output e.c
p 1 "-ptr2arr-points-to is not used with -ptr2arr-z-reading" wout.c -ptr2arr -ptr2arr-z-reading \
    -ptr2arr-points-to steens -ptr2arr-output e.c
p 1 "-ptr2arr-output given twice" "$in" -ptr2arr -ptr2arr-output a.c -ptr2arr-output b.c
p 1 "-ptr2arr-record given twice" "$in" -ptr2arr -ptr2arr-record a.json -ptr2arr-record=b.json \
    -ptr2arr-output e.c
p 1 "-ptr2arr-unsupported given twice" "$in" -ptr2arr -ptr2arr-unsupported error \
    -ptr2arr-unsupported warn -ptr2arr-output e.c
p 1 "-ptr2arr-region-size given twice" "$in" -ptr2arr -ptr2arr-region-size 10 \
    -ptr2arr-region-size 20 -ptr2arr-output e.c
p 1 "-ptr2arr-points-to given twice" "$in" -ptr2arr -ptr2arr-points-to steens \
    -ptr2arr-points-to alias -ptr2arr-output e.c
p 1 "-ptr2arr-violation-markers given twice" "$in" -ptr2arr -ptr2arr-mode memory-safety \
    -ptr2arr-violation-markers split -ptr2arr-violation-markers reach-error -ptr2arr-output e.c
p 1 "-ptr2arr-data-model given twice" "$in" -ptr2arr -ptr2arr-data-model LP64 \
    -ptr2arr-data-model ILP32 -ptr2arr-output e.c
p 1 "-ptr2arr-wrap-integers given twice" "$in" -ptr2arr -ptr2arr-wrap-integers \
    -ptr2arr-no-wrap-integers -ptr2arr-output e.c
# a negation is the same option with the value false
p 1 "-ptr2arr given twice" "$in" -ptr2arr -ptr2arr-identity -ptr2arr-monitor -no-ptr2arr
p 1 "-ptr2arr-check given twice" out.c -ptr2arr-check -ptr2arr-output e.c -ptr2arr-no-check
p 1 "-ptr2arr-identity given twice" "$in" -ptr2arr -ptr2arr-identity -ptr2arr-no-identity
p 1 "-ptr2arr-no-identity is not used with -ptr2arr-monitor" "$in" -ptr2arr -ptr2arr-no-identity \
    -ptr2arr-monitor -ptr2arr-output e.c
# -then starts another run, whose options are checked on their own
p 1 "-ptr2arr-mode given twice" "$in" -then -ptr2arr -ptr2arr-mode memory-safety \
    -ptr2arr-mode assume-safety -ptr2arr-output e.c
# -commands-file FILE puts the options of FILE in its place
printf -- '-ptr2arr-mode memory-safety\n-ptr2arr-mode=assume-safety\n' > "$work/cmds2.txt"
printf -- '# a comment\n-ptr2arr-mode "memory-safety"\n' > "$work/cmds1.txt"
p 1 "-ptr2arr-mode given twice" "$in" -ptr2arr -commands-file cmds2.txt -ptr2arr-output e.c
p 1 "-ptr2arr-mode given twice" "$in" -ptr2arr -commands-file=cmds1.txt -ptr2arr-mode assume-safety \
    -ptr2arr-output e.c
p 1 "exactly one input file" "$in" "$in2" -ptr2arr -ptr2arr-output e.c
p 1 "exactly one input file" out.c out32.c -ptr2arr-check
q 1 "preprocesses with -m32, not -m64" -cpp-extra-args=-m64 "$in" -ptr2arr -ptr2arr-data-model ILP32 \
    -ptr2arr-output e.c

echo "== plugin: allowed"
p 0 "" "$in" -ptr2arr -ptr2arr-output b0.c
p 0 "" "$in" -ptr2arr -ptr2arr-mode memory-safety -ptr2arr-violation-markers split -ptr2arr-output b1.c
p 0 "" "$in" -ptr2arr -ptr2arr-mode memory-safety -ptr2arr-violation-markers=reach-error \
    -ptr2arr-output b2.c
p 0 "" "$in" -ptr2arr -ptr2arr-mode assume-safety -ptr2arr-output b3.c
p 0 "" "$in" -ptr2arr -ptr2arr-mode memory-cleanup -ptr2arr-violation-markers reach-error \
    -ptr2arr-output b15.c
p 0 "" "$in" -ptr2arr -ptr2arr-mode memory-safety -ptr2arr-memtrack-check fixpoint \
    -ptr2arr-output b16.c
p 0 "" "$in" -ptr2arr -ptr2arr-mode memory-safety -ptr2arr-memtrack-check=guess \
    -ptr2arr-memtrack-check guess -ptr2arr-output b17.c
p 0 "" "$in" -ptr2arr -ptr2arr-mode memory-cleanup -ptr2arr-memtrack-nonterminating \
    -ptr2arr-memtrack-check fixpoint -ptr2arr-output b18.c
p 0 "" "$in" -ptr2arr -ptr2arr-mode normal -ptr2arr-wrap-integers -ptr2arr-record b4.json \
    -ptr2arr-unsupported warn -ptr2arr-region-size 1000 -ptr2arr-points-to steens \
    -ptr2arr-data-model LP64 -ptr2arr-output b4.c
p 0 "" "$in" -ptr2arr -ptr2arr-mode memory-safety -ptr2arr-mode memory-safety -ptr2arr-output b5.c
p 0 "" "$in" -ptr2arr -ptr2arr-region-size 100 -ptr2arr-region-size=0100 -ptr2arr-output b6.c
p 0 "" "$in" -ptr2arr -commands-file cmds1.txt -ptr2arr-output b7.c
p 0 "" "$in" -ptr2arr -ptr2arr-mode memory-safety -ptr2arr-output b8.c \
    -then -ptr2arr-mode assume-safety -ptr2arr-output b9.c
p 0 "" out.c -ptr2arr-check
p 0 "" out.c -ptr2arr-check -ptr2arr-check-allow-pointers -ptr2arr-data-model LP64
p 0 "" "$in" -ptr2arr -ptr2arr-identity -ptr2arr-output b10.c -ptr2arr-record b10.json \
    -ptr2arr-unsupported warn -ptr2arr-data-model LP64
p 0 "" "$in" -ptr2arr -ptr2arr-monitor -ptr2arr-points-to steens -ptr2arr-output b11.c \
    -ptr2arr-record b11.json -ptr2arr-unsupported warn -ptr2arr-data-model LP64
p 0 "" wout.c -ptr2arr -ptr2arr-z-reading -ptr2arr-output b12.c -ptr2arr-record b12.json \
    -ptr2arr-unsupported warn -ptr2arr-data-model LP64
q 0 "" "$in" -ptr2arr -ptr2arr-data-model ILP32 -ptr2arr-output b13.c
q 0 "" "$in" -ptr2arr -ptr2arr-mode assume-safety -ptr2arr-data-model ILP32 -ptr2arr-output b14.c
q 0 "" out32.c -ptr2arr-check -ptr2arr-data-model ILP32

echo "== integer options"
x 0 "" --wrap-integers=all -o i1.c "$in"
x 0 "" --wrap-integers=unsigned --wrap-integers -o i2.c "$in"
x 0 "" --check-overflow -o i3.c "$in"
x 0 "" --check-overflow --wrap-integers -o i4.c "$in"
x 0 "" --check-overflow --data-model=ILP32 -o i5.c "$in"
x 1 "--wrap-integers given twice" --wrap-integers=all --wrap-integers -o e.c "$in"
x 1 "invalid --wrap-integers=signed" --wrap-integers=signed -o e.c "$in"
for m in --memory-safety --memory-cleanup --assume-safety; do
  x 1 "--check-overflow and $m exclude each other" $m --check-overflow -o e.c "$in"
done
x 1 "--check-overflow and --wrap-integers=all exclude each other" \
    --check-overflow --wrap-integers=all -o e.c "$in"
x 1 "--check-overflow is not used with --check" --check --check-overflow out.c
for a in --identity --monitor --z-reading; do
  x 1 "--check-overflow is not used with $a" $a --check-overflow -o e.c "$in"
  x 1 "--wrap-integers is not used with $a" $a --wrap-integers=all -o e.c "$in"
done
x 1 "--violation-markers is used only with --memory-safety" \
    --check-overflow --violation-markers=reach-error -o e.c "$in"
p 0 "" "$in" -ptr2arr -ptr2arr-wrap-integers -ptr2arr-wrap-integers-kind all -ptr2arr-output d1.c
p 0 "" "$in" -ptr2arr -ptr2arr-check-overflow -ptr2arr-wrap-integers -ptr2arr-output d2.c
p 1 "-ptr2arr-wrap-integers-kind is used only with -ptr2arr-wrap-integers" \
    "$in" -ptr2arr -ptr2arr-wrap-integers-kind all -ptr2arr-output e.c
p 1 "invalid -ptr2arr-wrap-integers-kind signed" \
    "$in" -ptr2arr -ptr2arr-wrap-integers -ptr2arr-wrap-integers-kind signed -ptr2arr-output e.c
p 1 "-ptr2arr-check-overflow is used only with -ptr2arr-mode normal" \
    "$in" -ptr2arr -ptr2arr-mode memory-safety -ptr2arr-check-overflow -ptr2arr-output e.c
p 1 "-ptr2arr-check-overflow and -ptr2arr-wrap-integers-kind all exclude each other" \
    "$in" -ptr2arr -ptr2arr-check-overflow -ptr2arr-wrap-integers \
    -ptr2arr-wrap-integers-kind all -ptr2arr-output e.c
p 1 "-ptr2arr-check-overflow is not used with -ptr2arr-identity" \
    "$in" -ptr2arr -ptr2arr-identity -ptr2arr-check-overflow -ptr2arr-output e.c

# --uninit: every value with the transformation, its modes and integer
# options; keep with every action; check excludes --check-overflow
for v in keep check nondet; do
  x 0 "" --uninit=$v -o u_$v.c "$in"
  for m in --memory-safety --memory-cleanup --assume-safety; do
    x 0 "" --uninit=$v $m -o u_$v$m.c "$in"
  done
  x 0 "" --uninit=$v --memory-safety --violation-markers=reach-error -o u_${v}_re.c "$in"
  x 0 "" --uninit=$v --wrap-integers -o u_${v}_w.c "$in"
  x 0 "" --uninit=$v --wrap-integers=all -o u_${v}_wa.c "$in"
  x 0 "" --uninit=$v --data-model=ILP32 -o u_${v}_32.c "$in"
done
x 0 "" --uninit=nondet --check-overflow -o u_nd_ovf.c "$in"
x 0 "" --uninit=keep --check-overflow -o u_k_ovf.c "$in"
x 1 "--uninit=check and --check-overflow exclude each other" \
    --uninit=check --check-overflow -o e.c "$in"
x 1 "invalid --uninit=zero" --uninit=zero -o e.c "$in"
x 1 "--uninit given twice with different values" --uninit=check --uninit=nondet -o e.c "$in"
x 0 "" --uninit=check --uninit=check -o u_twice.c "$in"
x 0 "" --identity --uninit=keep -o u_id.c "$in"
x 0 "" --monitor --uninit=keep -o u_mon.c "$in"
x 0 "" --check --uninit=keep u_keep.c
for v in check nondet; do
  for a in --identity --monitor --z-reading; do
    x 1 "--uninit=$v is not used with $a" $a --uninit=$v -o e.c "$in"
  done
  x 1 "--uninit=$v is not used with --check" --check --uninit=$v u_keep.c
done
p 0 "" "$in" -ptr2arr -ptr2arr-uninit check -ptr2arr-mode memory-safety -ptr2arr-output pu1.c
p 0 "" "$in" -ptr2arr -ptr2arr-uninit nondet -ptr2arr-check-overflow -ptr2arr-output pu2.c
p 0 "" "$in" -ptr2arr -ptr2arr-identity -ptr2arr-uninit keep -ptr2arr-output pu3.c
p 1 "invalid -ptr2arr-uninit zero" "$in" -ptr2arr -ptr2arr-uninit zero -ptr2arr-output e.c
p 1 "-ptr2arr-uninit check and -ptr2arr-check-overflow exclude each other" \
    "$in" -ptr2arr -ptr2arr-uninit check -ptr2arr-check-overflow -ptr2arr-output e.c
p 1 "-ptr2arr-uninit nondet is not used with -ptr2arr-identity" \
    "$in" -ptr2arr -ptr2arr-identity -ptr2arr-uninit nondet -ptr2arr-output e.c
p 1 "-ptr2arr-uninit check is not used with -ptr2arr-check" \
    pu3.c -ptr2arr-check -ptr2arr-check-allow-pointers -ptr2arr-uninit check
p 1 "-ptr2arr-uninit given twice with different values" \
    "$in" -ptr2arr -ptr2arr-uninit check -ptr2arr-uninit keep -ptr2arr-output e.c

echo "== --unbounded-regions"
x 0 "" --unbounded-regions -o ub1.c "$in"
x 0 "" --memory-safety --violation-markers=reach-error --memtrack-check=none \
    --unbounded-regions -o ub2.c "$in"
x 0 "" --assume-safety --unbounded-regions --unbounded-regions -o ub3.c "$in"
x 1 "--unbounded-regions is not used with --check" --check --unbounded-regions ub1.c
for a in --identity --monitor --z-reading; do
  x 1 "--unbounded-regions is not used with $a" $a --unbounded-regions -o e.c "$in"
done
p 0 "" "$in" -ptr2arr -ptr2arr-mode memory-safety -ptr2arr-unbounded-regions -ptr2arr-output pub1.c
x 0 "" --scalar-cells -o sc1.c "$in"
x 0 "" --memory-safety --scalar-cells --unbounded-regions -o sc2.c "$in"
x 1 "--scalar-cells is not used with --check" --check --scalar-cells sc1.c
for a in --identity --monitor --z-reading; do
  x 1 "--scalar-cells is not used with $a" $a --scalar-cells -o e.c "$in"
done
p 0 "" "$in" -ptr2arr -ptr2arr-scalar-cells -ptr2arr-output psc1.c
p 1 "-ptr2arr-unbounded-regions is not used with -ptr2arr-identity" \
    "$in" -ptr2arr -ptr2arr-identity -ptr2arr-unbounded-regions -ptr2arr-output e.c
echo "== #line lines"
x 0 "" --line-directives -o l1.c "$in"
x 0 "" --line-directives --memory-safety -o l2.c "$in"
x 0 "" --line-directives --check-overflow --data-model=ILP32 -o l3.c "$in"
x 0 "" --line-directives --identity -o l4.c "$in"
x 0 "" --line-directives --monitor -o l5.c "$in"
x 0 "" --line-directives --z-reading -o l6.c wout.c
x 0 "" --line-directives --line-directives -o l7.c "$in"
x 0 "" --check l1.c
x 0 "" --check --allow-pointers l4.c
x 1 "--line-directives is not used with --check" --check --line-directives out.c
p 0 "" "$in" -ptr2arr -ptr2arr-line-directives -ptr2arr-output m1.c
p 0 "" "$in" -ptr2arr -ptr2arr-identity -ptr2arr-line-directives -ptr2arr-output m2.c
p 0 "" "$in" -ptr2arr -ptr2arr-monitor -ptr2arr-line-directives -ptr2arr-output m3.c
p 0 "" wout.c -ptr2arr -ptr2arr-z-reading -ptr2arr-line-directives -ptr2arr-output m4.c
p 1 "-ptr2arr-line-directives is not used with -ptr2arr-check" \
    out.c -ptr2arr-check -ptr2arr-line-directives
p 1 "-ptr2arr-line-directives given twice" \
    "$in" -ptr2arr -ptr2arr-line-directives -ptr2arr-no-line-directives -ptr2arr-output e.c

echo "== function pointers: the forms that stay unsupported (status 2), with their kinds"
fp="$here/tests/cases"
x 0 "" -o e.c "$fp/c147_fnptr_via_void_ptr.c"
x 2 "function-pointer-external" -o e.c "$fp/c148_fnptr_refused_external.c"
x 2 "function-pointer-external" -o e.c "$fp/c186_qsort_unknown_element_refused.c"
x 0 "" -o e.c "$fp/c183_qsort_model.c"
x 0 "" -o e.c "$fp/c184_bsearch_model.c"
x 2 "implicit-declaration" -o e.c "$fp/c188_implicit_builtin_conflict.c"
x 0 "" -o e.c "$fp/c187_implicit_builtin_decl.c"
x 0 "" --identity -o e.c "$fp/c187_implicit_builtin_decl.c"
x 2 "float-constant" -o e.c "$fp/c190_nan_constant_refused.c"
x 0 "" -o e.c "$fp/c189_infinity_constants.c"
x 2 "int-pointer-cast" -o e.c "$fp/c193_main_return_pointer_read_refused.c"
x 0 "" -o e.c "$fp/c191_pointer_equality_via_integers.c"
x 0 "" -o e.c "$fp/c192_main_returns_pointer.c"
x 0 "" -o e.c "$fp/c194_nondet_pointer.c"
x 0 "" -o e.c "$fp/c195_setjmp_longjmp.c"
x 0 "" --data-model=ILP32 -o e.c "$fp/c195_setjmp_longjmp.c"
x 2 "setjmp-longjmp" --identity -o e.c "$fp/c195_setjmp_longjmp.c"
x 2 "function-pointer-variadic" -o e.c "$fp/c149_fnptr_variadic.c"
x 0 "" --unsupported=warn -o e.c "$fp/c139_fnptr_local.c"
x 0 "" --unsupported=warn -o e.c "$fp/c147_fnptr_via_void_ptr.c"
x 2 "function-pointer-value" -o e.c "$fp/c179_fnptr_value_ordered.c"
x 2 "function-pointer-value" -o e.c "$fp/c180_fnptr_value_arith.c"
x 2 "function-pointer-value" -o e.c "$fp/c181_fnptr_value_external.c"
x 2 "function-pointer-value" -o e.c "$fp/c182_fnptr_value_narrow.c"
x 0 "" -o e.c "$fp/c178_fnptr_casts.c"
x 2 "function-pointer" --identity -o e.c "$fp/c139_fnptr_local.c"
x 0 "" --monitor -o e.c "$fp/c139_fnptr_local.c"

echo "ok: $pass"
echo "FAIL: $fail"
echo DONE
[ "$fail" -eq 0 ]
