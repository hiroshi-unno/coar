(* The quantitative solver's own configuration: the fields read only by
   [QflSolver] (validity checking for Quantitative Fixpoint Logic, the
   supermartingale and distribution-bound syntheses), nested in MuVal's record
   as its [qfl] member.  The muCLP solver reads none of them; the fields both
   solvers read (tracing, the answer's format, the two constraint solvers) stay
   in MuVal's record. *)

type sm_kind =
  | SSM (* Streett supermartingale (SSM) *)
  | GSSM (* generalized Streett supermartingale (GSSM) *)
  | LexGSSM (* lexicographic GSSM (LexGSSM) *)
  | PMSM (* progress-measure supermartingale (PMSM) *)
  | LexPMSM (* lexicographic PMSM (LexPMSM) *)
[@@deriving yojson]

(* The quantitative solver's Pareto cache: the invariants found for earlier
   postconditions are kept, and once [threshold] queries have been checked, the invariant for
   a new postcondition is first sought from them -- with weight templates of
   [num_conds] conditions of degree [cond_degree], and a reward fixed at zero
   with [zero_reward] -- by the dual PCSP solver within [timeout] milliseconds
   (unbounded with [None]); if that does not settle it, the problem without the
   cache is solved as a backup. *)
type pareto_cache =
  | No_cache
  | Cache_after of {
      threshold : int; [@default 2]
      timeout : int option; [@default None]
      num_conds : int; [@default 4]
      cond_degree : int; [@default 1]
      zero_reward : bool; [@default false]
    }
[@@deriving yojson]

(** a quantitative template's shape: [num_conds] conditions of degree
    [cond_degree] over terms of degree [term_degree], the input's own
    if-then-else structure kept with [use_orig_ite] *)
type quant_template = {
  num_conds : int; [@default 1]
  use_orig_ite : bool; [@default false]
  cond_degree : int; [@default 1]
  term_degree : int; [@default 1]
  annot_branches_follow_ite : bool; [@default false]
      (** with [use_orig_ite], the branch an annotation's condition selects
          also follows the input's if-then-else structure; off, it is one
          affine template *)
  cond_branches_follow_ite : bool; [@default true]
      (** with [use_orig_ite], the branch each of the [num_conds] template
          conditions selects follows the input's if-then-else structure; off,
          it is one affine template *)
}
[@@deriving yojson]

(** the under-approximation template's degrees *)
type underapprox = {
  cond_degree : int option; [@default Some 1]
  term_degree : int option; [@default None]
}
[@@deriving yojson]

(** the omega-regular objectives' invariant shape and supermartingale kind *)
type omega_regular = {
  inv_shape : int list; [@default [ 1 ]]
  supermartingale : sm_kind; [@default LexPMSM]
}
[@@deriving yojson]

(** the templates of the pre-fixpoint, the ranking supermartingale and the
    post-fixpoint, with the post-fixpoint's non-constancy constraint *)
type templates = {
  prefp : quant_template; [@default Common.Util.config_default quant_template_of_yojson "{}"]
  rank : quant_template; [@default Common.Util.config_default quant_template_of_yojson "{}"]
  postfp : quant_template; [@default Common.Util.config_default quant_template_of_yojson "{}"]
  postfp_force_non_const : bool; [@default false]
  guard_complement_template : bool; [@default false]
      (** in the lower-bound check, a guarded predicate's template takes an
          affine template (of the pre-fixpoint template's term degree) where
          its guard is negative; off, the value there is zero *)
  underapprox : underapprox; [@default Common.Util.config_default underapprox_of_yojson "{}"]
  omega_regular : omega_regular;
      [@default Common.Util.config_default omega_regular_of_yojson "{}"]
}
[@@deriving yojson]

(** the distribution-bound synthesis *)
type dist_bound = {
  use_l1_norm : bool; [@default false]
  use_optimathsat : bool; [@default false]
  initialize_standard_basis : bool; [@default false]
  use_strict_bound : bool; [@default false]
  relax : float option; [@default Some 0.1]
}
[@@deriving yojson]

type t = {
  output_time : bool; [@default false]
      (** append the solving time to the answer line *)
  output_witness : bool; [@default false]
      (** append the witness, when there is one, to the answer line *)
  templates : templates; [@default Common.Util.config_default templates_of_yojson "{}"]
  enable_geometric_pla : bool; [@default false]
  pareto_cache : pareto_cache; [@default No_cache]
  dist_bound : dist_bound; [@default Common.Util.config_default dist_bound_of_yojson "{}"]
  integer_states : bool; [@default false]
      (** a problem over integer-sorted states is still relaxed to the reals,
          but its fixpoint obligations are stated at the integer states only
          (an [is_int] hypothesis per relaxed argument) instead of at every
          real state; no effect on a problem without an integer sort *)
  lb_max_on_invariant : bool; [@default false]
      (** in the lower-bound check (without the geometric PLA), the
          certificate is [max(0, L)] for an unconstrained-sign template [L],
          whose post-fixpoint obligation is required only where [L > 0], plus
          the body's non-negativity at zero unknowns; and every obligation is
          restricted to an SMT-checked invariant of the states the query
          reaches, when one is found *)
}
[@@deriving yojson]
