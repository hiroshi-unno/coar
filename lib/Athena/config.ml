(* Configuration of Athena, the route from a C program to a verdict that
   rewrites the program on Frama-C (Ptr2ArrFC), compiles it to LLVM IR with
   clang 19, translates the IR -- to a labelled transition system (llvm2lts)
   or directly to muCLP (the LLVM frontend) -- and solves the result with
   MuVal, all inside this executable except clang.  It is a verification
   method of its own, not another reader of [-p cltl]/[-p cctl]'s input: the
   C frontend reads a program over unbounded integers straight to muCLP,
   while Athena reads it under C's fixed-width integers (or the reading
   [integers] names), so one file can get two correct, different answers. *)
open Core
open Common.Util

(* which translation of the LLVM IR *)
type route =
  | Llvm2lts
      (** to an LTS in the T2 format, read by CoAR's LTS frontend as
          [-p ltsterm]/[-p ltssafe] read it *)
  | Direct  (** to muCLP, by the LLVM frontend of [-p llvmterm]/[-p llvmsafe] *)
[@@deriving yojson]

(* How the program's integers are read.  Each is one of the competition
   scripts' categories; the rewriting and the translation each take their
   part of it. *)
type integers =
  | Mathematical
      (** as mathematical integers bounded by their type's range, without
          wrap-around (the category C) *)
  | Modulo
      (** as mathematical integers, each wrap-around made explicit by the
          rewriting (C_Mod) *)
  | Bit_vector  (** as bit-vectors of their width (C_BV) *)
  | Auto
      (** chosen per program by the rewriting: bit-vectors where a bitwise
          operation needs them, else mathematical integers with a reduction
          placed wherever its value analysis cannot show that a value stays
          in its type's range (C_Auto) *)
  | Unbounded
      (** as mathematical integers that are not bounded by their type's range
          at all, termCOMP's reading of C: no over- or underflow, a
          nondeterministic value any integer, and the bit operations with a
          constant operand read in infinite two's complement *)
  | Wrap_unsigned
      (** as C reads them, the reading SV-COMP's verdicts follow: unsigned
          arithmetic and the narrowing and sign-changing conversions wrap, a
          signed overflow (undefined) stops the execution, a
          nondeterministic value is one of its type's, and the bit operations
          with a constant operand are read (llvm2lts's [int-wrap-unsigned];
          the direct route's [llvmfront/wrap_unsigned.json]); the older
          spelling of [Wrapping] with [signed_overflow] [Undefined] *)
  | Wrapping
      (** as bounded integers with wrap-around, each value held as its
          unsigned representative and every arithmetic result reduced
          modulo 2^N, so that unsigned arithmetic and the narrowing and
          sign-changing conversions wrap; a nondeterministic value is one of
          its type's, and the bit operations with a constant operand are
          read.  What a signed overflow does is [signed_overflow]'s
          (llvm2lts's [int-wrap-unsigned] and [int-wrap-all]; the direct
          route's [Wrap_unsigned] and [Wrap_all]) *)
  | Wrap_all
      (** the older spelling of [Wrapping] with [signed_overflow] [Wraps] *)
[@@deriving yojson]

(* What an operation whose signed result leaves its type's range yields
   (C leaves it undefined) *)
type signed_overflow =
  | Wraps
      (** the two's-complement value, as gcc and clang define it under
          -fwrapv: an answer is about the program built so *)
  | Undefined
      (** undefined behaviour, read as [undefined_behaviour] says: by
          default the execution stops, SV-COMP's reading (a program that
          traps there has the same terminating executions and the same
          reachable errors, so trapping needs no value of its own) *)
  | Arbitrary_value
      (** any value of the type, each to be covered: a YES holds for every
          implementation in which an overflowing operation yields some value
          of its type or ends the program; a NO may rest on such a choice.
          The direct route only *)
[@@deriving yojson]

(* What an execution that reaches undefined behaviour means *)
type undefined_behaviour =
  | Path_stops  (** it is not considered: no violation, and it ends *)
  | Is_violation
      (** from there on anything may happen: a violation under a safety
          question, an execution that does not end under termination (the
          direct route only) *)
[@@deriving yojson]

(* What a question in an Int reading does when the translation refuses a
   bit operation only bit-vectors translate (an and/or/xor of two variables,
   a shift by a variable amount) *)
type bv_fallback =
  | No_fallback  (** it is declined *)
  | Bit_vector_fallback
      (** the program is rewritten and translated again with [Bit_vector]
          integers, from the rewriting on (whose regions differ), and the
          bit-vector problem is solved: a reading with the same verdicts,
          the values being the IR's two's-complement ones *)
[@@deriving yojson]

(* How long the rewriting's region arrays are *)
type regions =
  | Bounded  (** each of the rewriting's fixed length *)
  | Unbounded_regions
      (** of no length, as the translations read an array, so that no
          allocation can exhaust one (the rewriting's [--unbounded-regions]);
          not under [Bit_vector] integers, where an index wraps *)
[@@deriving yojson]

(* Whether a loop's reads of an array cell no transition of the loop writes
   are read once before the loop (llvm2lts's [--hoist]), so that proving
   termination needs no invariant about the array: the llvm2lts route only *)
type hoist = Not_hoisted | Hoisted [@@deriving yojson]

(* Which self calls llvm2lts's tail-call elimination turns into loops: the
   llvm2lts route only, and before inlining, so a recursion it leaves is
   declined *)
type tail_recursion =
  | Returned_as_is
      (** a call whose result is returned unchanged ([return f(x);]) *)
  | Accumulated
      (** also a call whose result is added to or multiplied by a value
          computed before the call and then returned ([return n + f(x);]),
          through an accumulator that computes the sum or product in the
          opposite order: the same answers when the integers are unbounded,
          so only with [Unbounded] (llvm2lts's
          [--tailcallelim-accumulator]) *)
[@@deriving yojson]

(* Whether the control-flow graph clang wrote is simplified before mem2reg
   (llvm2lts's [--simplifycfg], LLVM's simplifycfg without speculating a
   block): the llvm2lts route only.  Its use here is that the rewriting's
   single return point leaves an empty block between a [void] function's
   self call and its return, through which tail-call elimination does not
   look, so [f(x); return;] stays recursion and is declined *)
type control_flow =
  | As_compiled  (** as clang wrote it *)
  | Simplified
      (** empty blocks merged, branches folded; admitted only with
          [Unbounded] integers, the reading it was checked under *)
[@@deriving yojson]

(* What a termination question assumes of memory safety *)
type memory =
  | Unchecked  (** nothing: the rewriting's plain reading of each access *)
  | Assumed_safe
      (** an execution ends at its first memory-safety violation (the
          rewriting's [--assume-safety]): the verdict is about the executions
          that violate nothing *)
[@@deriving yojson]

(* How a memory-safety question checks valid-memtrack *)
type memtrack =
  | Not_checked  (** not at all: valid-deref and valid-free only *)
  | Halting  (** in the executions that end (the rewriting's default) *)
  | Nonterminating_too
      (** also where an execution never ends, as a G property requires *)
[@@deriving yojson]

(* Which preprocessor the rewriting's Frama-C runs on a [.c] input (a [.i]
   one is not preprocessed) *)
type preprocessor =
  | Clang
      (** the [clang] below, so that clang is the only compiler the route
          runs *)
  | Gcc
      (** gcc, Frama-C's default, as the competition scripts' standalone
          rewriting runs it *)
[@@deriving yojson]

(* The solver of the problem the translation states.  One constructor, so
   that a solver configuration file of [config/solver/], which names its
   backend, is the nested file as it stands. *)
module Solver = struct
  type t = MuVal of MuVal.Config.t [@@deriving yojson]

  let instantiate_ext_files = function
    | MuVal cfg ->
        Or_error.map (MuVal.Config.instantiate_ext_files cfg) ~f:(fun cfg ->
            MuVal cfg)

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Athena solver"
    let instantiate = instantiate_ext_files
  end)
end

type t = {
  route : route; [@default Llvm2lts]
  integers : integers; [@default Mathematical]
  signed_overflow : signed_overflow option; [@default None]
      (** when absent, [Wraps] for [Wrap_all] and [Undefined] otherwise;
          refused where it means nothing or is not built ([reading]) *)
  undefined_behaviour : undefined_behaviour; [@default Path_stops]
  solver : Solver.t ext_file;
      [@default
        ExtFile.Filename
          "./config/solver/muval_yesno.json"]
  llvmfront : string option; [@default None]
      (** the direct route: the LLVM frontend's configuration file; when
          absent, the one for the integers' reading,
          [./config/llvmfront/modulo.json] for [Modulo] and
          [./config/llvmfront/llvmfront.json] otherwise *)
  witness : bool; [@default false]
      (** the direct route: also map each loop head to where its loop stands
          in the C program and which C variable each predicate parameter
          holds, and after a YES print, one line per loop head, the invariant
          the solution gives it (for a correctness witness), whatever the
          LLVM frontend's configuration says *)
  clang : string; [@default "clang-19"]
      (** clang 19, a path or a name looked up in PATH *)
  preprocessor : preprocessor; [@default Clang]
  framac_share : string option; [@default None]
      (** Frama-C's share directory (machine descriptions, headers), for a
          Frama-C that is no longer where it was installed, such as one
          carried in an archive; when absent, where it was installed *)
  regions : regions; [@default Bounded]
  hoist : hoist; [@default Not_hoisted]
  tail_recursion : tail_recursion; [@default Returned_as_is]
  control_flow : control_flow; [@default As_compiled]
  memory : memory; [@default Unchecked]
      (** [-p cterm]; the termination side of [-p ctermmemsafe] always
          assumes it *)
  memtrack : memtrack; [@default Halting]
      (** [-p cmemsafe] and the safety side of [-p ctermmemsafe] *)
  bv_fallback : bv_fallback; [@default No_fallback]
  clang_flags : string list; [@default []]
      (** further options for clang's compilation of the rewritten program,
          such as [-fbracket-depth=4096] for a program nesting blocks deeper
          than clang's default limit *)
  safety_wait_s : int option; [@default None]
      (** [-p ctermmemsafe]: seconds after this run starts past which a
          termination answer no longer waits for the safety side and is the
          answer; when absent it waits for that side to end *)
  eva_timeout_s : int; [@default 60]
      (** [Auto]: past this many seconds the rewriting's value analysis is
          given up, and the program is rewritten again without it (every
          reduction kept, the reading still chosen) *)
  work_dir : string option; [@default None]
      (** where the intermediate files are written and left; when absent, a
          directory of this process's own, removed once the problem to solve
          has been read *)
}
[@@deriving yojson]

(* [reading cfg]: the representation and the reading of signed overflow
   [cfg] states, the older spellings [Wrap_unsigned] and [Wrap_all] read as
   [Wrapping] with [Undefined] and with [Wraps].  Contract: the
   representation returned is never [Wrap_unsigned] nor [Wrap_all]; the
   signed overflow is [None] exactly for [Unbounded], which has no range to
   leave.  Refused, with the reason:
   - any [signed_overflow] with [Unbounded];
   - a [signed_overflow] that contradicts an older spelling;
   - [Wraps] with [Auto] (the rewriting's choice of reading excludes its
     wrap-around of signed arithmetic, and neither of its choices,
     bit-vectors or reductions placed where a value may leave its range,
     is one representation to switch to).
   [Wraps] with [Mathematical] reads the integers as [Wrapping]: the
   mathematical reading has no wrap-around, so wrapping needs the reduction
   the wrapping representation makes ([wraps_mathematical] says when this
   happens, for the caller's note).
   - [Arbitrary_value] and [Is_violation] on the llvm2lts route, which
     implements neither. *)
let reading cfg =
  let open Or_error in
  let stated = cfg.signed_overflow in
  let name so = match so with Wraps -> "Wraps" | Undefined -> "Undefined" | Arbitrary_value -> "Arbitrary_value" in
  (match (cfg.integers, stated) with
  | Unbounded, None -> return (Unbounded, None)
  | Unbounded, Some so ->
      error_string
        (sprintf "Athena: signed_overflow %s with integers Unbounded: unbounded integers have no range to overflow" (name so))
  | Wrap_unsigned, (None | Some Undefined) -> return (Wrapping, Some Undefined)
  | Wrap_all, (None | Some Wraps) -> return (Wrapping, Some Wraps)
  | ((Wrap_unsigned | Wrap_all) as old), Some so ->
      error_string
        (sprintf "Athena: signed_overflow %s contradicts integers %s, which states %s; write integers Wrapping"
           (name so)
           (match old with Wrap_all -> "Wrap_all" | _ -> "Wrap_unsigned")
           (match old with Wrap_all -> "Wraps" | _ -> "Undefined"))
  | Mathematical, Some Wraps -> return (Wrapping, Some Wraps)
  | Auto, Some Wraps ->
      error_string
        "Athena: signed_overflow Wraps with integers Auto: the rewriting's choice of reading excludes its \
         wrap-around of signed arithmetic; use integers Modulo, Wrapping or Bit_vector"
  | ((Mathematical | Modulo | Bit_vector | Auto | Wrapping) as ints), so ->
      return (ints, Some (Option.value so ~default:Undefined)))
  >>= fun ((_, so) as result) ->
  match (cfg.route, so, cfg.undefined_behaviour) with
  | Llvm2lts, Some Arbitrary_value, _ ->
      error_string
        "Athena: signed_overflow Arbitrary_value is implemented on the direct route only (route Direct)"
  | Llvm2lts, _, Is_violation ->
      error_string "Athena: undefined_behaviour Is_violation is implemented on the direct route only (route Direct)"
  | _ -> return result

(* Whether [reading cfg] switches the representation from [Mathematical]
   to [Wrapping] because signed overflow wraps. *)
let wraps_mathematical cfg =
  match (cfg.integers, cfg.signed_overflow) with
  | Mathematical, Some Wraps -> true
  | _ -> false

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  (if cfg.eva_timeout_s > 0 then return ()
   else
     error_string
       (sprintf "eva_timeout_s must be positive (got %d)" cfg.eva_timeout_s))
  >>= fun () ->
  reading cfg >>= fun _ ->
  (match (cfg.tail_recursion, cfg.route, cfg.integers) with
  | Returned_as_is, _, _ | Accumulated, Llvm2lts, Unbounded -> return ()
  | Accumulated, _, _ ->
      error_string
        "tail_recursion Accumulated is read on the Llvm2lts route with \
         Unbounded integers only")
  >>= fun () ->
  (match (cfg.control_flow, cfg.route, cfg.integers) with
  | As_compiled, _, _ | Simplified, Llvm2lts, Unbounded -> return ()
  | Simplified, _, _ ->
      error_string
        "control_flow Simplified is read on the Llvm2lts route with \
         Unbounded integers only")
  >>= fun () ->
  Solver.load_ext_file cfg.solver >>= fun solver -> Ok { cfg with solver }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "Athena"
  let instantiate = instantiate_ext_files
end)
