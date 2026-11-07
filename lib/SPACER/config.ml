(* Configuration of the Spacer backend (Z3's fixedpoint engine run in-process
   through the Z3 library).  Besides the preprocessing applied first and Z3's
   own options (native model-based projection, global guidance, Z3's internal
   validation), it says whether a returned solution must be usable
   ([solution_needed], which turns off the Z3 transformations that make it
   unsound), whether a counterexample is wanted, and whether a solution is
   re-checked against the clauses ([check_validity]); [conservative_check]
   rejects a solution whose check is undecided, and [solve_again_if_invalid]
   queries again instead of failing when the check rejects one.

   [xform_options], when not empty, says exactly which of Z3's fixedpoint
   rule-set transformations [slice], [inline_linear], [inline_eager] and
   [subsumption_checker] run: the named ones on, the others off.  They rewrite the rules before
   Spacer runs and keep whether the query is derivable, but what Z3 reads back
   through them (a solution, a derivation) may be wrong, so they are accepted
   only together with [verdict_only], which reads nothing back: Z3's [unsat]
   is returned as [Sat] with an EMPTY map, which is no solution, and Z3's
   [sat] as [Unsat None].  A caller of a verdict-only solver may use the
   verdict and nothing else. *)
open Core
open Common.Util
open Preprocessing

type t = {
  preprocessor : Preprocessor.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/preprocessor/disable.json"]
  timeout_ms : int option; [@default None]
      (** a budget in milliseconds for each query, given to Z3; [None] leaves
          it to the caller's [~timeout] (in seconds) *)
  use_z3_native_mbp : bool; [@default true]
  enable_global_guidance : bool; [@default true]
  gg_concretize : bool; [@default true]
      (** Read only while [enable_global_guidance] is on: [false] sets Z3's
          [spacer.gg.concretize] to false, [true] leaves Z3's default, which
          is true, so the default asks Z3 exactly what it asked before the
          field existed.  Global guidance (Z3's Spacer, [spacer.global]) has
          three steps, concretize, conjecture and subsume; this switches off
          the first alone and keeps the other two.  The reason it exists: Z3
          5.1.0's Spacer, when a blocking check of a proof obligation comes
          back undecided (a cancelled or resource-limited check), treats the
          obligation as not blocked with no model set, and the concretizing
          step then evaluates a literal in that null model, which kills the
          process with a segmentation fault.  With concretize off that call
          is never made.  What it costs Spacer's search is not measured, so
          the default keeps Z3's behaviour. *)
  enable_z3_validation : bool; [@default false]
  check_validity : bool; [@default false]
  conservative_check : bool; [@default true]
  solve_again_if_invalid : bool; [@default true]
  solution_needed : bool; [@default false]
  cex_needed : bool; [@default false]
  xform_options : string list; [@default []]
  verdict_only : bool; [@default false]
  flat_and_or : bool; [@default false]
      (** Hand each rule's constraint to Z3 with every nest of conjunctions
          (disjunctions) as one n-ary [and] ([or]) over its operands, left to
          right, instead of the binary nest the formulas are built as.  The
          rules mean the same; only their shape differs.  Z3's fixedpoint
          engine takes a rule as given and does not flatten its constraint, so
          a binary nest is what its search works on, and the rule text Z3
          prints flattens it, which hides the difference.  Measured on a
          strategy check of a game, 427 rules over 191 relations: asked as
          built it was undecided at 70 s in 3 of 3 runs, and decided in 5.8,
          10.5 and 44.9 s with the n-ary form, as the same rules printed and
          read back by Z3 were (5-10 s).  Off, as before the field existed. *)
  cone_of_influence : bool; [@default false]
      (** Hand Z3 only the clauses on which a goal's derivability depends
          ([Ast.ChcCone]: the goal clauses whose body unknowns are derivable
          and the clauses defining a needed unknown from derivable ones), read
          off the clausal form before it is converted.  A derivation Z3 finds
          is one of the whole set clause by clause, and a solution of the cone
          is extended to every unknown (a derivable one outside the cone
          [true], an underivable one [false]), so both answers are the whole
          set's.  Off, as before the field existed. *)
  share_answer_decoding : bool; [@default true]
      (** Decode Z3's answer (a solution, or the derivation of a
          counterexample) with each distinct subexpression decoded once per
          bound-variable environment ([Z3interface.with_shared_decoding]),
          instead of once per occurrence.  A derivation names a step once
          however many later steps use it, so as a tree it can be much larger
          than as Z3 holds it: on one strategy check's counterexample 3,211
          distinct nodes stood for 2.5 million tree nodes, and the decoding
          took about 115 s after a 9 s query.  The value is the same up to the
          names of bound variables (a repeated quantified subexpression keeps
          one set of bound names) and is physically shared where Z3 shares;
          fewer fresh names are drawn.  On by default. *)
  blast_term_ite_inflation : int option; [@default None]
      (** [Some n] sets Z3's [spacer.blast_term_ite_inflation] to [n]; [None]
          keeps Z3's default (3). Spacer hoists the term-level [ite]s of every
          rule body into Boolean case splits before it builds the transition
          relation, as long as the body grows at most [n]-fold; [0] disables
          the hoisting. The answer is unaffected (the rewrite is an
          equivalence); only the cost of Spacer's queries changes. On a
          bit-vector body with many nested [ite]s the hoisted body can make
          every query of the search much dearer at the same search, and the
          first reachability query may then not return within the budget. *)
  query_as_relation : bool; [@default false]
      (** [false] poses the goal clauses (those without a positive literal)
          to Z3 as a formula, [Fixedpoint.query (exists V. body)]. Z3 then
          makes a fresh query predicate whose arguments are ALL the
          variables of the body (rule_manager::mk_query in Z3's
          muz/base/dl_rule.cpp), and Spacer tracks obligations and learns
          lemmas over them. [true] declares one fresh nullary relation [q]
          instead, adds every goal clause as the rule [body => q] and asks
          [Fixedpoint.query_r [q]]: the same satisfiability question, with
          no arguments to the query predicate. [q] is not part of the
          answer. On a goal over wide bit-vectors the obligations over the
          query predicate's arguments can make a reachability check of that
          predicate far dearer; on other queries the nullary form is the
          slower one, so neither dominates. *)
  verbose : bool; [@default false]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

(* The transformations [xform_options] may name. *)
let known_xforms = [ "slice"; "inline_linear"; "inline_eager"; "subsumption_checker" ]

(* A transformation turned on where something is read back would hand the
   caller a solution or a derivation of the transformed rules, which need not
   be one of the original rules; refused when the configuration is read. *)
let check_xforms cfg =
  match
    List.find cfg.xform_options ~f:(fun x ->
        not (List.mem known_xforms x ~equal:String.equal))
  with
  | Some x ->
      Or_error.errorf "SPACER: unknown xform_options entry %S (known: %s)" x
        (String.concat ~sep:", " known_xforms)
  | None ->
      if
        (not (List.is_empty cfg.xform_options))
        && not (cfg.verdict_only && (not cfg.solution_needed) && not cfg.cex_needed)
      then
        Or_error.error_string
          "SPACER: xform_options requires verdict_only, with solution_needed \
           and cex_needed false: the transformed rules give no trustworthy \
           solution or counterexample"
      else Ok ()

let instantiate_ext_files cfg =
  let open Or_error in
  check_xforms cfg >>= fun () ->
  Preprocessor.Config.load_ext_file cfg.preprocessor >>= fun preprocessor ->
  Ok { cfg with preprocessor }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "SPACER"
  let instantiate = instantiate_ext_files
end)
