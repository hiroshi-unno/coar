(* Configuration of RCaml: the predicate constraint solver for assertion
   problems ([solver]), the CHC optimisation solver for type-optimization
   problems ([chc_optimizer]), the refinement-type constraint generator's own settings
   ([cgen_config]), whether predicate variables are eliminated before solving
   ([enable_pvar_elim]), a per-problem timeout in seconds, and the fixpoint
   logic solver ([fixpoint_solver]) for an assertion problem that carries least
   or greatest fixpoint predicates (the temporal effects of recursive
   functions): with none, such a problem is printed and answered [unknown]; and
   whether a counterexample is printed after an [unsat] line
   ([report_counterexample]); [mucyc_solver] names a MuCyc configuration that
   replaces [solver] for assertion problems; [check_main_asserts] makes the
   [assert]s of [main] the property of a file that states none; whether an
   operation that escapes a top-level item is a failure or the program is
   refused ([toplevel_effects]); which operations are answer-type
   polymorphic ([atp_operations]); whether the problems with one shared
   instance per abstracted predicate of a predicate-polymorphic definition
   are tried first ([merge_instantiation_copies], within
   [merged_attempt_timeout]); and the effect-constraint solver's settings
   ([mbcsol]). *)

open Core
open Common.Util

type t = {
  solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat.json"]
      (** the predicate constraint solver: by default PCSat at its own default
          (templates with quantified-array atoms and cells, adaptive restarts),
          so an RCaml run and a PCSat run on the same constraints use one
          solver; a configuration that names another file keeps it *)
  chc_optimizer : CHCOptSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/optpcsat_nc_pcsat_improver.json"]
      (** the CHC optimisation solver: by default OptPCSat with no side
          condition whose improving and checking solvers are both PCSat at its
          default, the same solver as [solver]'s default *)
  cgen_config : Ast.Rtype.config; [@default Common.Util.config_default Ast.Rtype.config_of_yojson "{}"]
  verbose : bool; [@default true]
  enable_pvar_elim : bool; [@default true]
  timeout : int option; [@default None]
  mucyc_solver : string option; [@default None]
      (** a MuCyc solver configuration file (["MuCyc", {...}], as under
          [config/solver/]) that solves assertion problems in place of
          [solver]; MuCyc reaches the predicate constraint solvers itself, so
          this is a path rather than a [solver] value *)
  report_counterexample : bool; [@default false]
      (** print, after an [unsat] verdict line, the counterexample the
          constraint solver gave (PPDP 2009's, from the [Unwind] solver),
          once it has passed the evaluation check; nothing else changes *)
  fixpoint_solver : MuVal.Config.t ext_file option; [@default None]
  check_main_asserts : bool; [@default false]
      (** a file with no [[@@@assert]] that binds [main] is checked as if it
          asserted [typeof(main) <:] main's simple type: every [assert] that
          [main] can reach must hold (the input form of Horn-entailment
          benchmarks, whose property is an [assert] in [main]) *)
  toplevel_effects : ToplevelHandler.toplevel_effects;
      [@default ToplevelHandler.Fail_on_escape]
      (** what a top-level item that performs an operation or raises means:
          [Fail_on_escape] (OCaml's semantics: an operation or exception
          that escapes every handler is a failure, so the item is read under
          a handler whose every clause fails), or [Refuse] (the program is
          refused, as before 2026-11-02) *)
  atp_operations : MBcgen.Config.atp_operations; [@default Annotated]
      (** which effect operations the effect inference reads as
          answer-type polymorphic: with [Annotated], an operation every
          [perform] of which is written [perform_atp], whose every handler
          clause must then resume its continuation in tail position; a file
          with no [perform_atp] is read as with [Off] *)
  merge_instantiation_copies : bool; [@default true]
      (** first solve the problems generated with every use of a
          predicate-polymorphic definition sharing one instance of each of
          its abstracted predicates (one per predicate and argument sorts)
          instead of a fresh copy per use; an assertion that problem answers
          [sat] is answered [sat] (a solution of the shared system gives
          one of the copying system), and every other assertion is answered
          by the ordinary copying generation, as without this option.
          On by default: the copying generation doubles its constraints with
          each nesting of a polymorphic call and exhausts memory on a
          three-deep nesting that the shared system answers in about a
          second, and on 684 OCaml inputs the shared attempt changed no
          verdict, gained two and lost none.  The attempt runs in a forked
          copy raced against the copying run, the first to answer every
          assertion winning: run first instead, it delayed the copying run by
          up to [merged_attempt_timeout] on every input whose shared system
          it did not answer, and on relational inputs, where one predicate
          shared by several calls of a function must hold of all of their
          contexts at once, that shared system is often far harder than the
          copies (seconds or never, against under a second), so answers the
          copying run gives in most of a caller's time limit were lost.  Its
          cost is a second core for at most [merged_attempt_timeout] *)
  merged_attempt_timeout : int; [@default 20]
      (** the wall-clock budget, in seconds, of the shared attempt as a whole
          (its constraint generation and the solving of all its problems);
          when it runs out, the attempt gives up and the copying run, which
          has been running beside it, answers alone.  A time budget, because
          nothing in the problem predicts how long the constraint solver
          takes to find a solution or to give up; it bounds the second core
          the attempt takes, not the copying run's time *)
  mbcsol : MBcsol.Config.t;
      [@default Common.Util.config_default MBcsol.Config.of_yojson "{}"]
      (** the effect-constraint solver's settings; its [verbose] is replaced
          by this configuration's *)
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  PCSPSolver.Config.load_ext_file cfg.solver >>= fun solver ->
  CHCOptSolver.Config.load_ext_file cfg.chc_optimizer >>= fun chc_optimizer ->
  (match cfg.fixpoint_solver with
  | None -> Ok None
  | Some f -> MuVal.Config.load_ext_file f >>| Option.some)
  >>= fun fixpoint_solver -> Ok { cfg with solver; chc_optimizer; fixpoint_solver }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "RCaml"
  let instantiate = instantiate_ext_files
end)
