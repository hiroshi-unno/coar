# athena-witness: SV-COMP witnesses for athena

Writes the SV-COMP verification witness (YAML exchange format 2.1,
https://gitlab.com/sosy-lab/benchmarking/sv-witnesses) for a result of athena
on one input file. Locations in the witness are positions in the input file
itself, read from the `source_map` of the transformation record that
Ptr2ArrFC writes beside its output (`athena/Ptr2ArrFC`, `src/record.ml`).

## Status

| result | property | witness |
| --- | --- | --- |
| TRUE | `unreach-call`, `no-overflow` | an `invariant_set` of the loop invariants given by `--invariants`, none without it |
| TRUE | `termination` | an `invariant_set` with no invariant |
| TRUE | `valid-memsafety`, `valid-memcleanup` | none (exit 2): SV-COMP 2027 requires none |
| FALSE | `unreach-call` (of `reach_error`), `no-overflow`, `valid-deref`, `valid-free` | a `violation_sequence` of one `target` waypoint |
| FALSE | `valid-memtrack`, `valid-memcleanup` | none (exit 2): needs format 2.3 |
| FALSE | `termination` | none (exit 2): needs a cycle |

Paths to the violation and cycles are not produced yet; the types in
`src/witness.ml` already have room for them.

## Build

Needs the opam packages `yaml`, `yojson` and `cmdliner`. A build of the
repository leaves this directory out (`athena/dune`).

```sh
dune build --root athena/Witness     # -> athena/Witness/_build/default/bin/main.exe (installed name athena-witness)
```

## Run

```sh
athena-witness --input IN.c --record OUT.p2a.json --property PROP.prp --result true|false
               [--task TASK.yml | --data-model ILP32|LP64]
               [--violated valid-deref|valid-free|valid-memtrack|valid-memcleanup]
               [--invariants LINES]
               --producer-version V [--producer-name MuVal] [--format-version 2.1] -o WITNESS.yml
```

- `--input` names the input file as the verifier was given it: that string is
  written as the witness's `input_files` entry and every location's
  `file_name`. Its SHA-256 must be the record's `input.sha256`.
- The data model is the task's `options.data_model`, else `--data-model`;
  there is no default, and when both are given they must agree. It must match
  the record's `input.machdep` (`gcc_x86_32` is ILP32, `gcc_x86_64` LP64).
- `--violated` names the sub-property of a `valid-memsafety` property file
  that was found violated, and the witness's `specification` is that
  sub-property's formula. Without it, the sub-property of the first target in
  the source map (by input line and column) is taken and named on stderr.
- `--invariants` names the lines CoAR prints after its verdict on the direct
  LLVM route (`-p llvmsafe` with the LLVM frontend's `witness` setting), one
  per loop head of Ptr2ArrFC's output:
  `(invariant (loc LINE COLUMN) (function "F") (vars (X signed|unsigned WIDTH [global]) ...) EXPR)`
  or `(skipped [(loc LINE COLUMN)] (function "F") "REASON")`, EXPR an
  S-expression over the output's variables in linear integer arithmetic. Each
  top-level conjunct of EXPR is written as C over the input's names (the
  record's `names`, role `program`) with every variable and numeral a
  `long long`, or dropped, which only weakens the invariant: a conjunct with a
  name the input does not have, or with a subterm whose range, computed from
  the variables' types, may not fit a `long long`. Locations go back to the
  input through the source map's loop heads; an input loop that several output
  loops come from gets the disjunction of their invariants, and none unless
  every one of them has an invariant line. What was dropped is named on stderr.
- When the source map holds several targets for the property, the result
  does not say which one is reached; the first by input line and column is
  taken, and stderr says so.

Exit status: 0 the witness was written; 2 this result gets no witness (the
reason on stderr, nothing written); 1 an error (nothing written).

## Tests

```sh
tests/run_tests.py [--ptr2arr PTR2ARR.exe] [--validate validate.sh] [--keep DIR]
```

Each case runs the executable on an input under `tests/cases`, a property
file under `tests/properties` and a record, and checks the exit status, the
witness's fields and stderr; every witness written is then checked by
witnesslint (`script/svcomp/validation/validate.sh --validator none`). The
records are the hand-written ones under `tests/records`, or, with `--ptr2arr`,
made by running that Ptr2ArrFC on the inputs, with the same expectations.
