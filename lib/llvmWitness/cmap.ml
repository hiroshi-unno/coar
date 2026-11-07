(* Where the loop-head predicates of the direct LLVM translation stand in the
   C program the IR was compiled from (clang -g), and which C variable each of
   their parameters holds there.  The translation builds it; the solution of
   the predicates is turned into invariants of that C program through it
   (Cinvariant).

   A parameter is listed only when the debug information says, on every path
   to the loop head, that it is the value of that C variable there; any other
   parameter (a temporary, a memory component C cannot name) is absent, and a
   conjunct that mentions it is dropped, which only weakens the invariant. *)

(* An integer C type: its width in bits and whether it is signed. *)
type ctype = { signed : bool; width : int }

type var = {
  name : string;  (** the C variable's name *)
  ctype : ctype;
  global : bool;  (** a global variable, rather than a local or a parameter of [func] *)
}

type point = {
  pred : string;  (** the predicate's name in the muCLP problem *)
  func : string;  (** the C function holding the loop *)
  loc : (int * int) option;
      (** line and column, from 1, of the first character of the loop
          statement in the C file, from the loop's debug metadata; [None]
          when the IR carries none (a cut point that is not a loop, such as
          the entry of a recursive function) *)
  params : (string * var) list;  (** a parameter's name -> the C variable it holds *)
}

(* How the translation holds a C integer value: [Int] as an integer congruent
   to its bit pattern modulo 2^N and lying in [-2^(N-1), 2^N), so that a bit
   pattern has two holders; [Bv] as a bit-vector of the type's width. *)
type mode = Int | Bv

type t = { mode : mode; points : point list }
