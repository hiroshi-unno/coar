# OOPSLA25R2 Artifact

## Introduction

This is the artifact of the following paper:

**Taro Sekiyama, Ugo Dal Lago, Hiroshi Unno. On Higher-Order Model Checking of Effectful Answer-Type-Polymorphic Programs. OOPSLA 2025.**

The artifact supports the following claims in the paper:

- The proof-of-concept HOMC tool for our language on top of a subset of OCaml 5.
- The experimental results described in the paper.

## Hardware Dependencies

We assume no specific hardware.

## Getting Started Guide

### Structure

The artifact consists of the source code and build scripts for our HOMC tool, as well as benchmarks and scripts for reproducing the experimental results reported in the paper.

### Building the HOMC Tool from Source Code

#### Software Requirements

- `libblas-dev`
- `liblapack-dev`
- `libmpfr-dev`
- `libgmp-dev`
- `libglpk-dev`
- `libffi-dev`
- `pkg-config`

#### Building Instructions

The following instructions assume that you are in the root directory of the GitHub repository.

1. Install [opam](https://opam.ocaml.org/) (>= 2.0). You can make sure it is up-to-date by running:

   ```
   opam update --all --repositories
   ```

2. Create a new [opam switch](https://ocaml.org/docs/opam-switch-introduction) with OCaml 5.3.0. For example, run:

   ```
   opam switch create oopsla2025-artifact 5.3.0
   ```

   Don't forget to activate the created switch to make sure the environment is up-to-date. E.g., run 
   ```
   eval $(opam env --switch=oopsla2025-artifact)
   ```
   if the switch is created by the above command.

3. Install [dune](https://dune.build/) (>= 3.19) and required packages:

   ```
   opam install dune
   opam install . --deps-only
   ```

4. Build the source code:

   ```
   dune build main.exe
   ```

5. Build the backend solver [HorSat2](https://github.com/hopv/horsat2): 

   ```
   wget https://github.com/hopv/horsat2/archive/refs/heads/master.zip
   unzip master.zip
   cd horsat2-master
   make horsat2
   cp ./horsat2 ../
   cd ..
   ```

## Step by Step Instructions

To reproduce the experimental results described in the paper, run:

```
./script/oopsla2025/run.sh
```

This command runs the tool on each benchmark found in the directory `./benchmarks/OCaml/oopsla25`, which includes all the benchmarks presented in the implementation section (Section 7) of the paper.

The following is the correspondence between the benchmarks in the paper and the files in `./benchmarks/OCaml/oopsla25`.

| Benchmark                                                       | File                   |
|-----------------------------------------------------------------|------------------------|
| $\mathbf{Open} \, (); V_\mathrm{R} \, (); \mathbf{Close} \, ()$ | `file_SAT.ml`          |
| $\mathbf{Open} \, (); V_\mathrm{R} \, (); \mathbf{Open} \, ()$  | `file_unsafe_UNSAT.ml` |
| $V \, \mathsf{true}$                                            | `state_SAT.ml`         |
| $V \, \mathsf{false}$                                           | `state_UNSAT.ml`       |


## Reusability Guide

To verify an original program against a specification, the user has to prepare a `.ml` file following a certain template. We illustrate the template using `./benchmarks/OCaml/oopsla25/file_SAT.ml`, which corresponds to the first program shown in the table in Section 7 of the paper.

```
(* 
  This declares the algebraic operations used in the programs as a generalized algebraic datatype (GADT).
  See https://ocaml.org/manual/5.2/gadts-tutorial.html for an introduction to GADTs in OCaml.
*)

type 'a eff =
  | Open : unit eff
  | EOF : bool eff
  | Read : unit eff
  | Close : unit eff
  | Raise : 'a eff
[@@boxed]

(*
  The following declarations provide the same interface as OCaml 5.0 programming with effect handlers.
  The user does not need to read them in detail, but may refer to https://ocaml.org/manual/5.3/effects.html for more information.
  The exception is `perform_atp`, which is used to invoke an answer-type polymorphic (ATP) algebraic operation. (Therefore, it must be handled by a tail-resumptive clause.)
  In contrast, `perform` is used to invoke an answer-type modifying (ATM) operation, which must be handled by a non-tail-resumptive clause.
*)

type ('a, 'b) continuation = K

type 'a effect_handler = {
  effc : 'b. 'b eff -> (('b, 'a) continuation -> 'a) option;
}

type ('a, 'b) handler = {
  retc : 'a -> 'b;
  exnc : exn -> 'b;
  effc : 'c. 'c eff -> (('c, 'b) continuation -> 'b) option;
}

external perform : 'a eff -> 'a = "unknown"
external perform_atp : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

(*
  The following is the program to be verified.
  It is written in the style of OCaml 5 programming with effect handlers, using the algebraic operations and functions declared above.
  Note that `perform_atp` is used to invoke ATP operations such as `Open`, `EOF`, `Read`, and `Close`, whereas `perform` is used to invoke the ATM operation `Raise`.
*)

let rec f () =
  match_with
    (fun () ->
      let b = perform_atp EOF in
      if b then perform Raise else (perform_atp Read; f ()))
    ()
    {
      retc = (fun _ -> ());
      exnc = raise;
      effc =
        (fun (type b) (e : b eff) ->
          match e with
          | Open -> Some (fun (k : (b, _) continuation) -> let r = perform_atp Open in continue k r)
          | EOF -> Some (fun k -> let r = perform_atp EOF in continue k r)
          | Read -> Some (fun k -> let r = perform_atp Read in continue k r)
          | Close -> Some (fun k -> let r = perform_atp Close in continue k r)
          | Raise -> Some (fun k -> ()));
    }

let main = perform_atp Open; f (); perform_atp Close

(*
  Finally, the file defines a property to be verified as an alternating tree automaton (ATA).
  The property is specified by the following description, enclosed in double quotes.
  It follows the grammar supported by our backend solver `HorSat2`. The section between `%BEGINR` and `%ENDR` declares tree constructors along with their arities, while the section between `%BEGINATA` and `%ENDATA` defines the transition rules of the ATA. See https://github.com/hopv/horsat2 for more information.

  The declarations without the mark (!) can be considered boilerplate; they are necessary to handle the higher-order recursion scheme (HORS) produced by the CPS transformation implemented in our tool.
  The user needs to add the declarations of the tree constructors corresponding to their own algebraic operations, and the corresponding transition rules (marked with (!) in the following).

  Please remove the mark (!) and the comment before feeding the file into our tool.
*)

[@@@check_toplevel "
%BEGINR
opOpen -> 1.       (!)
opEOF -> 2.        (!)
opRead -> 1.       (!)
opClose -> 1.      (!)
opRaise -> 1.      (!)
fail -> 0.
unit -> 0.
tuple2 -> 2.
tuple3 -> 3.
tuple4 -> 4.       (* The user may want to add `tuplen -> n` if the program uses n-tuples. *)
tt -> 0.
ff -> 0.
not -> 1.
and -> 2.
or -> 2.
imply -> 2.
iff -> 2.
xor -> 2.
if -> 3.
%ENDR

%BEGINATA
q0 opOpen -> (1,q1).                                  (!)
q0 if -> (1,qT) /\\ (2,q0) \\/ (1,qF) /\\ (3,q0).
q0 unit -> true.
q0 tuple2 -> true.
q0 tuple3 -> true.
q0 tuple4 -> true.
q0 tt -> true.
q0 ff -> true.
q0 not -> true.
q0 and -> true.
q0 or -> true.
q1 opEOF -> (1,q1) /\\ (2,q2).                        (!)
q1 opClose -> (1,q0).                                 (!)
q1 if -> (1,qT) /\\ (2,q1) \\/ (1,qF) /\\ (3,q1).
q1 unit -> true.
q1 tuple2 -> true.
q1 tuple3 -> true.
q1 tuple4 -> true.
q1 tt -> true.
q1 ff -> true.
q1 not -> true.
q1 and -> true.
q1 or -> true.
q2 opRead -> (1,q1).                                  (!)
q2 opEOF -> (1,q1) /\\ (2,q2).                        (!)
q2 opClose -> (1,q0).                                 (!)
q2 if -> (1,qT) /\\ (2,q2) \\/ (1,qF) /\\ (3,q2).
q2 unit -> true.
q2 tuple2 -> true.
q2 tuple3 -> true.
q2 tuple4 -> true.
q2 tt -> true.
q2 ff -> true.
q2 not -> true.
q2 and -> true.
q2 or -> true.
qV unit -> true.
qV tuple2 -> (1,qV) /\\ (2,qV).
qV tuple3 -> (1,qV) /\\ (2,qV) /\\ (3,qV).
qV tuple4 -> (1,qV) /\\ (2,qV) /\\ (3,qV) /\\ (4,qV).
qV tt -> true.
qV ff -> true.
qV not -> (1,qV).
qV and -> (1,qV) /\\ (2,qV).
qV or -> (1,qV) /\\ (2,qV).
qT tt -> true.
qT ff -> false.
qT not -> (1,qF).
qT and -> (1,qT) /\\ (2,qT).
qT or -> (1,qT) \\/ (2,qT).
qT imply -> (1,qF) \\/ (2,qT).
qT iff -> (1,qT) /\\ (2,qT) \\/ (1,qF) /\\ (2,qF).
qT xor -> (1,qT) /\\ (2,qF) \\/ (1,qF) /\\ (2,qT).
qT if -> (1,qT) /\\ (2,qT) \\/ (1,qF) /\\ (3,qT).
qF tt -> false.
qF ff -> true.
qF not -> (1,qT).
qF and -> (1,qF) \\/ (2,qF).
qF or -> (1,qF) /\\ (2,qF).
qF imply -> (1,qT) /\\ (2,qF).
qF iff -> (1,qT) /\\ (2,qF) \\/ (1,qF) /\\ (2,qT).
qF xor -> (1,qT) /\\ (2,qT) \\/ (1,qF) /\\ (2,qF).
qF if -> (1,qT) /\\ (2,qF) \\/ (1,qF) /\\ (3,qF).
%ENDATA
"]
