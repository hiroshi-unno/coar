open Core
open Common.Util

(* definitions for software model checking [PLDI'24] *)

type cex_typ = QE | Model | MBP of int
(* 0 : use latest, 1 : use saved, 2 : use saved loop invariant *)
[@@deriving yojson]

type com_typ =
  | Or
  | Return of bool (* cex accumulation *)
  | Yield of
      bool (* query weakening *) * bool (* share trace among coroutines *)
[@@deriving yojson]

type strategy = Solve | Refine of cex_typ * com_typ [@@deriving yojson]
type cshare = Level | Global of bool (* use saved *) [@@deriving yojson]

type induct =
  | Normal of bool (* use disjuncts *)
  | Light of bool (* use disjuncts *)
[@@deriving yojson]

(* definitions for QSMT solving *)

type backtrack_strategy =
  | Original
  | Chronological
  | NonChronological
  | NonChronologicalRec
[@@deriving yojson]

type t = {
  verbose : bool; [@default false]
  simplify : bool; [@default true]
  reduce : bool; [@default true]
  slice_forward : bool; [@default true]
  slice_backward : bool; [@default true]
  gen_lemmas_with_ai : bool; [@default false]
  gen_determ_conjs : bool; [@default false]
  pcsp_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/spacer_sol.json"]
  timeout_check_valid : int; [@default 0]
  timeout_prove_each_conj : int; [@default 3]
  (* options for software model checking [PLDI'24] *)
  refinement_strategy : strategy; [@default Common.Util.config_default strategy_of_yojson {|["Refine", ["MBP", 0], ["Return", false]]|}]
  top_down_search : bool; [@default false]
      (* true: top-down proof search a la PPDP'09
         false: bottom-up proof search a la Spacer *)
  monotone_trace : bool; [@default false]
  induction : induct option; [@default None]
  query_reuse : bool; [@default false]
  counterexample_sharing : cshare option; [@default None]
  backup_for_interp : bool; [@default true]
  (* which end of the interpolant lattice the backup takes.  Both are valid:
     eliminating what only the antecedent mentions gives the strongest,
     eliminating what only the consequent mentions gives the weakest *)
  strongest_backup_for_interp : bool; [@default false]
  backup_for_mbp : bool; [@default true]
  (* the largest result [Formula.elim_ite] may produce before the rewriting
     follows the model instead; [None] always rewrites every branch *)
  ite_size_limit : int option; [@default None]
  (* Do not rewrite a conditional into the paths through it at all.
     A conditional is not a connective of the projection's language: A[ite (c, t, e)]
     stands for (c /\ A[t]) \/ (~c /\ A[e]), and rewriting an atom into those paths takes
     the product of the branches of each argument at every level, which on a word-level
     circuit is an atom with a thousand conditionals in it.  With this set, a conditional
     is instead replaced by the branch the model takes, with its condition conjoined as a
     literal -- a subterm for one of its own subterms, so the formula never grows and no
     bound is needed to keep it from growing.
     A conditional that mentions none of the variables being eliminated is carried
     through whole: what it denotes does not bear on the elimination, and asserting its
     condition would constrain the other variables for no gain.  One that mentions a
     variable being eliminated is settled, which does weaken the projection -- the models
     taking the other branch are left to other calls -- and that is the same bargain the
     projection's other rules make.  The test is applied to the whole conditional, its
     branches included, not to its condition alone.
     When set, [ite_size_limit] is not read. *)
  resolve_ite_in_projection : bool; [@default false]
  (* Do not inline the let-bound definitions either.  Inlining a definition into each of
     its uses is exponential in the sharing -- 1,837 nodes of one input became
     17,917,748 -- and a conditional left in place is copied along with it.  With this
     set, every compound subterm is given a fresh name instead and the naming stated as
     an equation, which is an equivalence and is linear in the shared form; the fresh
     variables are existential, so they are removed by the projection's own rule for
     several variables.  This is the definitional encoding of G. S. Tsejtin, "On the
     complexity of derivation in propositional calculus" (1968), taken at the level of
     terms rather than of propositions -- the same move an SMT preprocessor calls
     flattening.
     Each conditional is then settled against the model once, rather than once per use of
     it, the definitions nothing refers to any more are dropped, and a name whose
     definition mentions none of the variables being removed is left alone and
     substituted back once at the end.
     When set, neither [ite_size_limit] nor [resolve_ite_in_projection] is read.

     It is OFF although it is the better setting on a circuit, because a default is paid
     by every input and the gain is confined to one kind of them.  On the 330 word-level
     bit-vector problems it takes 32 answers to 42 and memory exhaustion from 66 to 3,
     and re-running every problem the two settings disagreed on -- three times each, at
     two and a half times the budget -- leaves 12 that only this answers against 2 that
     only the inlining does, nine of the twelve being inputs the inlining exhausts memory
     on every time.  But on 3,912 CHC-COMP25 problems outside bit-vectors it is slower
     across the board rather than only in a tail: the median of the ratio is 1.16 on the
     array category, 1.13 on the algebraic-datatype one and 1.05 on their combination,
     with a tail reaching 7, and at a 20 s budget that costs 27 answers.  Re-running the
     55 that differed, three times each at 90 s, leaves 11 against 6, which is no longer
     a difference -- so what it costs there is time rather than answers -- but a tax of
     five to sixteen per cent on every non-circuit input is not worth paying by default
     for a gain no non-circuit input sees.
     Turn it on for bit-vector work; `config/solver/mucyc_or_mbp1_bv.json` is that
     configuration.
     The two problems it does not answer and the inlining does are not a defect to fix:
     they need a literal about the branch the model did not take, and an encoding that
     separates the conditionals into different atoms cannot produce one in linear size.
     No answer differs between the two settings anywhere it has been measured -- 4,242
     problems, both settings, no wrong verdict and no disagreement -- and the
     projection's four conditions were checked under `check_validity` on both corpora.
     What would make it a default is deciding it per input rather than per run: the
     gain follows the bit-vector sorts, and nothing here looks at them. *)
  name_subterms_in_projection : bool; [@default false]
  (* Whether the projection says anything about the branch the model did not take.
     Settling a conditional against the model keeps its condition and the branch taken;
     the published rule signs every atom of the formula, and the naming makes the other
     branch one of them, so it survives as a comparison of the two branches.  That
     comparison is a strengthening of an input that already implies the original, so it
     is optional: unset, the projection covers more models and says less about each.
     What it costs is that the other branch is referred to and so cannot be dropped,
     which puts its whole cone back into the result.
     Read only when [name_subterms_in_projection] is set.
     It is off because it was measured: over the 79 problems at the boundary of the
     bit-vector corpus it gained no answer and cost four, and the reason is the kind of
     literal rather than the number.  What the exhaustive rewriting keeps is the original
     predicate evaluated at the other branch -- a comparison, which bounds an interval --
     while this keeps a comparison of the two branches, which under a model that makes
     them differ is a disequality, the weakest literal there is; on one input 5,242 of
     5,766 of them were disequalities. *)
  compare_branches_in_projection : bool; [@default false]
  enable_pvar_elim : bool; [@default false]
  check_validity : bool; [@default false]
  (* options for relational verification [CAV'17] *)
  ask_pred_app_to_unfold : bool; [@default false]
  valid_with_smt_threshold : int option; [@default None]
  induct_threshold : int option; [@default None]
  enable_apply_threshold : bool; [@default false]
  normalize_lemma : bool; [@default false]
  check_lemma_lhs : bool; [@default false]
  fold_lemmas : bool; [@default false]
  (* options for QSMT solving *)
  (* what a refutation at the innermost level contributes to the frame two levels out.
     [false] negates the model-based projection of the unsat core, which is a conjunction
     of atoms and, where the core carries a divisibility constraint, describes one
     congruence class at a time.  [true] replaces the refuted player's variables by witness
     terms and instantiates the whole matrix with them, which implies the same refutation
     and keeps the disjunctions of the matrix.  It applies only to the innermost level,
     where every remaining variable belongs to that player and the instance therefore stays
     quantifier-free *)
  subst_lemma : bool; [@default false]
  (* handle the outermost existential block by abstraction refinement instead of as one
     more level of the frame search: a candidate is proposed from the instances collected
     so far and checked by a fresh game with it fixed, so the check never carries the
     lemmas learned for other candidates.  Needs a variable at the outermost level and a
     third level below it; otherwise the frame search runs as usual *)
  forward : bool; [@default false]
  update_only_atoms_j_and_before : bool; [@default false]
  update_all_frames_j_and_after : bool; [@default false]
  reuse_prev_frame : bool; [@default false]
  backtrack_strategy : backtrack_strategy; [@default Original]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  Or_error.(
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver >>= fun pcsp_solver ->
    Ok { cfg with pcsp_solver })

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "MuCyc"
  let instantiate = instantiate_ext_files
end)
