(* The readings and encodings of the direct translation that are a choice.
   Every field has a default (the SV-COMP reading where the choice is a
   reading), so an empty JSON object is the default configuration. *)

type ub_reading =
  | Stop_path  (** an execution that reaches UB is not considered *)
  | Literal_c
      (** from the UB on anything may happen: a violation under safety, an
          execution that does not end under termination *)
[@@deriving yojson]

type int_reading =
  | Mathematical  (** the [C] route and TermComp; no wrap-around *)
  | Modulo  (** the [C_Mod] route *)
  | Unbounded
      (** integers without a range, as CoAR's C frontend reads them (an
          alternative for TermComp, whose expected answers take a C int as
          an unbounded integer): a value read as signed is its holder, with
          no conversion into the signed range; a [__VERIFIER_nondet_T] of a
          type wider than 16 bits gets no bound, only [>= 0] when unsigned;
          a reading as unsigned still converts, since the IR spells an
          unsigned constant such as [UINT_MAX] by its signed pattern ([-1]);
          no wrap-around, and [trunc] is the identity *)
  | Wrap_unsigned
      (** C's arithmetic made explicit, as llvm2lts's int-wrap-unsigned: the
          result of every [add], [sub], [mul] and [shl] is reduced into
          [[0, 2^N)]; [nsw] and [nuw] are promises whose breach is UB, as in
          BV mode; [trunc] and the overflow builtins reduce as in the
          modulo reading *)
  | Wrap_all
      (** as [Wrap_unsigned] with [nsw] not read, so that signed arithmetic
          wraps too, as llvm2lts's int-wrap-all (gcc's -fwrapv) *)
[@@deriving yojson]

(* What an operation whose signed result leaves its type's range yields,
   where the integer reading reads [nsw] (the mathematical, modulo and
   unsigned-wrapping readings, and BV mode outside [Wrap_all]): [nsw] on
   [add], [sub], [mul] and [shl], [sdiv]/[srem] of the minimum by -1,
   [llvm.abs] of the minimum with its poison flag, and a left shift clang's
   [shift-base] check rejects. *)
type signed_overflow =
  | Undefined
      (** undefined behaviour, read as [ub_reading] says (the execution
          stops by default; a program that traps there has the same
          terminating executions and the same reachable errors) *)
  | Arbitrary_value
      (** a value of the type, any of them, each to be covered (a demonic
          choice): a YES then holds for every implementation in which such an
          operation yields some value of its type or ends the program; a NO
          may rest on such a choice *)
[@@deriving yojson]

type choice_encoding =
  | Split  (** [(c => Q[a/v]) /\ (not c => Q[b/v])] *)
  | Ite  (** [Q[ite(c, a, b)/v]] *)
[@@deriving yojson]

type copy_encoding =
  | Lambda  (** an array [lambda] term *)
  | Loop  (** a loop with a predicate of its own *)
[@@deriving yojson]

type data_model =
  | Auto  (** the module's own, read from its triple and DataLayout *)
  | ILP32
  | LP64  (** the task's; the module must have been compiled for it *)
[@@deriving yojson]

(* The optional LLVM passes run before the translation; the defaults are the
   ones the translation is written for. *)
type passes = {
  simplifycfg : bool; [@default false]
  licm : bool; [@default false]
  tail_call_elimination : bool; [@default true]
  inline : bool; [@default false]
  promote : bool; [@default false]
      (** after the allow-list check: a cell of a region array or a whole
          global that is the only one of its global a loop reads and writes
          is held in a register across the loop (see Hoist.promote) *)
  hoist : bool; [@default false]
      (** after the allow-list check: a read of a region array or a whole
          global that no instruction of a loop can write is moved before
          the loop (see Hoist) *)
}
[@@deriving yojson]

type t = {
  ub_reading : ub_reading; [@default Stop_path]
  int_reading : int_reading; [@default Mathematical]
  signed_overflow : signed_overflow; [@default Undefined]
      (** not with [Unbounded] (no range to leave) nor [Wrap_all] (signed
          arithmetic wraps) *)
  conditional_value : choice_encoding; [@default Split]
      (** [select], [zext]/[sext] of [i1], [llvm.abs] *)
  signedness_conversion : choice_encoding; [@default Split]
      (** [to_S]/[to_U]; split by default after measuring formula size: the
          conditional term printed smaller but made MuVal's optimizer fail
          on a conditional term with a formula condition *)
  variable_length_copy : copy_encoding; [@default Lambda]
  bounds_conditions : bool; [@default true]
      (** on accesses to arrays other than Ptr2Arr's [memoryK] *)
  inline_acyclic_joins : bool; [@default false]
      (** give a join that lies on no cycle no predicate, building what
          follows it at each edge into it (as the T2 route's contraction of
          parallel edges into a choice ends up doing) *)
  drop_implied_guards : bool; [@default false]
      (** drop from a predicate's body every conjunct of an implication's
          premise that the enclosing premises imply on single-variable
          bounds (an overflow guard such as [n + 11 < 2^31] under the branch
          [n <= 100]); meaning-preserving *)
  every_point : bool; [@default false]
      (** emit every program point's predicate, without contraction, for
          checking *)
  data_model : data_model; [@default Auto]
  passes : passes;
      [@default { simplifycfg = false; licm = false; tail_call_elimination = true; inline = false; promote = false; hoist = false }]
  dump_ll : string option; [@default None]
      (** where to print the module after the passes, also when a step
          refuses it, for inspection *)
  witness : bool; [@default false]
      (** also record, for each loop head, where the loop stands in the C
          program and which C variable each predicate parameter holds, and
          print the invariants a solution gives the C program after the
          verdict *)
}
[@@deriving yojson]

let default : t =
  match of_yojson (`Assoc []) with
  | Ok config -> config
  | Error message -> failwith ("LLVMFront.Config.default: " ^ message)

(* The combinations refused before anything is read: a reading of signed
   overflow other than [Undefined] where no signed operation can overflow
   ([Unbounded]) or where signed overflow is defined to wrap ([Wrap_all]). *)
let validate config =
  match (config.signed_overflow, config.int_reading) with
  | Arbitrary_value, Unbounded ->
      Error "signed_overflow Arbitrary_value: the Unbounded reading has no range for a signed result to leave"
  | Arbitrary_value, Wrap_all ->
      Error "signed_overflow Arbitrary_value: the Wrap_all reading defines signed overflow to wrap"
  | (Undefined | Arbitrary_value), _ -> Ok config

(* [load ?overrides path]: the configuration of the JSON file [path], each
   member of [overrides] (a field name and its value in the file's own
   spelling) replacing the file's member of that name or added to it, then
   validated.  Contract: the result is what the file with those members
   written into it would read as; an error names the file. *)
let load ?(overrides = []) path =
  match Yojson.Safe.from_file path with
  | exception Yojson.Json_error message -> Error (path ^ ": " ^ message)
  | exception Sys_error message -> Error message
  | json -> (
      let json =
        match (json, overrides) with
        | _, [] -> json
        | `Assoc members, _ ->
            `Assoc
              (List.filter (fun (name, _) -> not (List.mem_assoc name overrides)) members
              @ overrides)
        | other, _ -> other
      in
      match Result.bind (of_yojson json) validate with
      | Ok config -> Ok config
      | Error message -> Error (path ^ ": " ^ message))

(* The configuration whose JSON object is [members] alone, every other
   field at its default, validated: [load ~overrides] without a file. *)
let of_members members = Result.bind (of_yojson (`Assoc members)) validate
