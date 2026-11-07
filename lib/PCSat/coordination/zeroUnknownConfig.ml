open Core

(** The configuration of the zero-unknown verdict's ladder: the stages that
    decide a problem with no unknown left after preprocessing (or the clauses
    without an unknown, asked first) by validity questions, exact rewrites,
    instantiations that only strengthen a question, and pins that only read a
    countermodel.  The ladder decides validity; it does not coordinate the
    CEGIS phases, so its configuration is a record of its own, one member of
    the coordinator's configuration ([zero_unknown]), grouped by stage.

    Every field has a default, and a configuration states only what differs
    (inside a nested object too).  An optional mechanism with parameters is a
    variant whose "on" constructor carries the parameters only it reads, so a
    configuration cannot state a parameter the code ignores; a plain [option]
    is an optional bound ([None]: none).  Durations are milliseconds and end in
    [_ms]; Z3 resource counts end in [rlimit]. *)

(** Whether, and in which order, the early rewritten pass asks a piece
    through the words of its quantifier-free matched-instance forms: every
    form of [SeqInstantiation.matched_forms] (every positive existential, a
    premise universal among them, replaced by its instances at the piece's
    own ground terms), and of the same matching in two rounds (the second
    against the ground terms the first round's instances write), that
    converts an integer to a word, asked by
    [Z3interface.check_valid_by_words]; then the piece as it is. *)
type word_instances =
  | No_word_instances
      (** the piece is asked as it is, with no words question before it *)
  | One_round_first
      (** each piece's one-round form is asked through its words, and the
          two-round form only when the one-round one is past the size bound
          ([SeqInstantiation.word_forms ~two_rounds_first:false]) *)
  | Two_rounds_first
      (** the two-round form is asked through its words, and the one-round
          form only when the two-round one is past the size bound.  The
          one-round form implies the two-round one (the second pass only adds
          instances beside those of the first), so it is valid only if the
          two-round form is: skipping it costs only a proof the solver would
          find through the smaller form's words and not the larger one's.
          Why: on a bit-set input the one-round words question of a piece ran
          out of its 10 s where the two-round one was proved in 0.6 s, and of
          another piece both ran out and the piece as it is was proved in
          2.7 s, so each such piece paid 10 s for a question the one after it
          subsumes *)
[@@deriving yojson]

(** a per-question cap and a whole-stage budget, in milliseconds *)
type budget_pair = {
  per_question_ms : int; [@default 1000]
      (** each question gets at most this many milliseconds *)
  whole_ms : int; [@default 10000]
      (** no question is asked once this many milliseconds have elapsed
          since the stage began *)
}
[@@deriving yojson]

(** The quick sweep: every residual clause asked first, at a short budget. *)
type quick_sweep = {
  per_question_ms : int; [@default 500]  (** the budget of each question *)
  whole_ms : int; [@default 5000]
      (** the sweep stops asking once this many milliseconds are spent *)
  finish_clause : bool; [@default true]
      (** with [budgets.quick_sweep], let the sweep's whole budget
          stop it only between clauses, or inside a clause once one of its
          pieces was left undecided: a clause started before the budget ran
          out is asked to its end while every piece so far was shown valid,
          so that it can still be recorded as valid
          ([NoUnknownLadder.quick_sweep]).  Without it the budget cuts a
          clause at any piece and the pieces already shown valid are lost.
          Only adds questions the sweep would ask of the same pieces, so it
          changes when an answer is reached, never which.  What it buys: a
          tuple variable split into its fields gave a residual clause 60
          pieces (36 unsplit), six of them about 1 s each, and the 5 s sweep
          stopped a few pieces short; the later stages took 40 s more to prove
          the clause, and the file went from 32-59 s to 78-104 s; with this
          on it answered in 30-31 s.  On by default *)
  plain_retry : bool; [@default false]
      (** a piece the sweep leaves undecided (neither proved nor refuted)
          whose question the integer-binder split
          ([rewrites.split_int_binders_at_ite]) would change is asked once
          more, under the same budget and in a fresh solver context, with
          that split off: the question as given, through the same validity
          call
          ([Z3interface.without_split_int_binders]).  Exact: the split is an
          equivalence in every model that adds no free variable, so both
          questions are the same validity question and either answer is one
          about the piece.  Only an undecided answer is retried, and only the
          plain form's decided answer replaces it.  Why: the split helps a
          solver match a read at [x - c] with a ground read, but on a piece
          over a concatenation's range tests Z3 5.1.0 left the split form
          undecided past 20 s under three seeds while the plain form was
          unsatisfiable in 0.08 s.  Off by default *)
}
[@@deriving yojson]

(** The budgets of the ladder's questions. *)
type budgets = {
  query_ms : int; [@default 10000]
      (** when preprocessing leaves no predicate variable, the wall-clock
          budget in milliseconds of each validity question the zero-unknown
          verdict asks (the conjunction, each clause and piece, the rewritten
          forms, the sequence-instantiated clauses, and the sequence-axiom
          fallback's share).  An undecided question is carried out as
          [timeout] or [unknown], never as a verdict; being wall-clock, the
          same question can be decided on an idle machine and run out on a
          loaded one *)
  refutation_ms : int; [@default 5000]
      (** the wall-clock budget in milliseconds of each last-resort
          refutation query of the same verdict (pinned array-literal bounds,
          pinned sequence lengths), asked only where the answer would
          otherwise be [timeout] or [unknown] *)
  query_rlimit : int option; [@default None]
      (** a Z3 resource limit ([rlimit]: a count of the solver's own steps,
          the same whatever the host's load) per query of the zero-unknown
          verdict, beside the wall-clock budgets above, which stay as the
          bound on a query Z3 does not interrupt.  A query that exhausts it is
          treated as one that ran out of time.  [None] sets none *)
  stage_rlimits : (string * int) list; [@default []]
      (** a Z3 resource limit per question for the named stages of the
          zero-unknown verdict's ladder (the stage names its trace prints:
          [quick], [early-seqinst], [conj], ...), in place of
          [budgets.query_rlimit] for the questions asked in that stage;
          a stage not named keeps that field's value.  Beside the stage's
          wall-clock budget, which stays as the bound on a check Z3 does not
          interrupt.  Why per stage: a resource count separates the checks
          a stage decides from the ones it cuts only where the stage's
          wall budget is short.  In the 500 ms quick sweep every decided
          check (Z3 5.1.0, Rust-derived inputs) took at most about 12,000
          units and every cut one at least about 69,000; in the 1 s and
          10 s stages the two ranges overlap, because units per second
          differ a hundredfold between questions, so no single count can
          stand in for those budgets.  A count, unlike a wall-clock budget,
          does not move with the host's load.  [[]] sets none *)
  reads_strict_deadline : bool; [@default false]
      (** inside a solve bounded by a strict deadline
          ([PCSatCommon.SolveDeadline.within ~strict_budget:true]: every
          probe of PCSat's, the nested finite-sort solve when its budget is
          strict, the unknown-free clauses' in-process check), the zero-unknown verdict stops once the deadline has passed:
          no further validity question is asked (a question that would have
          been asked is reported as having run out of time) and no further
          stage of its ladder is entered, nor the cvc5 retry or the lemma
          route tried on a sequence piece (and a try started before it is
          given at most the time left), the verdict being [unknown].  Only
          undecided answers replace questions, so only an answer of the
          bounded solve can be lost, never a wrong one given; outside such a
          solve nothing changes.  [false]: the ladder runs to its end
          whatever the deadline.  Why: the deadline is read only between
          CEGIS phases, and a problem with no unknown left never enters one,
          so a probe given 60 s spent 118-125 s in its ladder and with it the
          whole run of a 120 s budget, three runs of three *)
  report_exhaustion : bool; [@default false]
      (** when the zero-unknown verdict is left undecided and at least one
          of its validity questions ran out of its budget, answer [unknown]
          rather than [timeout] and say on stderr which budget ran out and
          how many questions it cut ("budget exhausted: ...").  Without it
          such a run answers [timeout], the word the run-wide time limit also
          prints, and the budget's part is visible only in the verbose
          trace *)
  quick_sweep : quick_sweep option;
      [@default
        Some
          {
            per_question_ms = 500;
            whole_ms = 5000;
            finish_clause = true;
            plain_retry = false;
          }]
      (** when preprocessing leaves no predicate variable, first ask every
          residual clause -- split into its [ClausePieces] when
          [pieces.split_clause_heads] is on -- with a short budget
          per question, [per_question_ms] each and [whole_ms] in all, before
          the conjunction and the long per-clause questions: a piece shown
          invalid refutes the problem at once, and a clause all of whose
          pieces are shown valid is recorded as valid and not asked again.
          The questions are the ones asked later anyway, so this changes only
          their order and budget.  What it buys: a Thrust problem whose last
          residual clause has a piece refuted in 0.03 s spent 57 s first on
          the conjunction, a rewritten conjunction and a piece of an earlier
          clause, each at the 10 s budget, and on proving two other clauses
          valid.  The sweep stops asking once its whole budget is spent.
          [None] skips it. *)
  two_pass_ms : int option; [@default None]
      (** [Some ms]: the early rewritten pieces
          ([early_stage.exact_forms_first]) and every form of a piece
          the sequence instantiation asks are first asked with a budget of
          [ms] milliseconds each; only for a piece none of whose forms is
          proved so are the forms that ran out of that budget (not those
          answered invalid or refused for their shape) asked again with
          [budgets.query_ms].  The early rewritten pieces get their
          full-budget question from the later rewritten pass of the ladder,
          which asks them anyway when nothing earlier decides.  Only [`Valid]
          is read from the sequence-instantiated forms and a refutation only
          from an exact rewrite, so this changes when an answer is reached,
          never which: a form that needs more than [ms] is still asked with
          the full budget.  What it buys: a form asked later that is proved
          at once is no longer queued behind an earlier form that spends the
          whole budget -- one Thrust input spent 41 of 46 s in four such
          questions while every decided question of eight profiled inputs
          returned within 2.3 s.  [None]: every question has the full budget
          and the forms are asked once, in order *)
  conjunction_ms_after_early : int option; [@default None]
      (** [Some ms]: once the early rewritten pieces and the early sequence
          instantiation ([early_stage.exact_forms_first]) have run and
          left the problem undecided, the whole-conjunction questions (the
          conjunction, the conjunction with its single-constructor binders
          opened, and the conjunction of the rewritten clauses not yet shown
          valid) are asked with at most [ms] milliseconds each instead of
          [budgets.query_ms], and [ms <= 0] does not ask them
          ([NoUnknownLadder.conj_timeout], [NoUnknownLadder.ask_conj]).  The
          per-clause and per-piece questions keep their budget.  Only
          [`Valid] and [`Invalid] are read from these questions, so a
          shorter budget can only lose an answer one of them would have
          given between [ms] and the full budget, to the later stages, and
          changes which questions are asked after it.  Read from the same
          traces: the conjunction and its opened form each spent their full
          10 s (11.9-13.4 s of wall time) on two inputs and decided nothing
          on any of the 13.  [None], the default, keeps the full budget *)
  arith_solver : int option; [@default None]
      (** Z3's [smt.arith.solver] for every pooled question the zero-unknown
          verdict asks ([Z3interface.with_arith_solver]): [Some 2] asks them
          with the simplex-based [theory_arith] instead of the default
          [lp]-based [theory_lra], on instances of their own.  The questions
          are the same, so only their time, and whether one outside the
          decidable fragment is decided, can change.  [None], the default,
          leaves the parameter unset. *)
}
[@@deriving yojson]

(** The pieces-first stage: each residual clause asked piece by piece. *)
type pieces_first = {
  z3_ms : int; [@default 1000]
      (** each piece's budget in a fresh Z3 context (the default is the
          preprocessor's pieces-first budget; no configuration relies on it) *)
  cvc5_ms : int option; [@default None]
      (** when Z3 leaves a piece undecided, cvc5's budget for it; [None]: no
          cvc5 question *)
}
[@@deriving yojson]

(** Where a grouped question's lead forms (the push-witness and
    matched-instance forms of each piece) are asked under open grouping. *)
type open_lead =
  | Before_grouping
      (** let [pieces.grouping.mode (Consecutive lead_first)] act under
          [pieces.grouping.mode (Open)] too: each piece's lead forms
          are asked before it is listed for open grouping, a piece they
          prove joins no group, and a member asked alone after its group's
          question fails starts after the lead forms already asked
          ([SeqInstantiation.lead_forms_under_open_grouping]).  Off, the
          open path asks no lead stage before grouping.  Needs
          [pieces.grouping.mode (Consecutive lead_first)]; ignored while
          [pieces.grouping.mode (Open After unasked_groups)] is set, which
          decides the open path's lead forms alone.  Sound: only a proof of
          a form is read, and no question is asked twice.  Why off: on one
          Rust-derived counter clause it proved six pieces whose grouped
          question ran to the cap, while on a Rust-derived map clause its
          lead proofs displaced cheaper grouped questions and the file, at
          the edge of its budget, lost answers *)
  | After of {
      unasked_groups : bool; [@default true]
          (** with [pieces.grouping.mode (Open)], ask a piece's lead
              forms (push-witness and matched-instance forms) as a stage of
              their own, before its other forms, only for the pieces no grouped
              question is asked about -- members of a group whose question is
              past [pieces.grouping.max_nodes], a group of one,
              a piece with no first form -- and list every piece for grouping
              as with [pieces.grouping.mode (Consecutive lead_first)] off, which
              then does not act on the open path (nor does
              [pieces.grouping.mode (Open Before_grouping)]; this switch
              acts whether or not that one is set)
              ([SeqInstantiation.lead_forms_for_unasked_groups]).  The pieces
              affected are asked the same forms in the same order; only the
              lemma route's one attempt after a form's timeout
              ([lemmas (Lemmas after_form_timeout)]) moves
              after the lead forms.  Sound: only a proof of a form, which
              implies its piece, is read.  Why: on a Rust-derived counter
              clause a skipped five-piece question and a piece alone each left
              a piece whose matched-instance form timed out to the lemma route,
              which ran 60 s without a proof where the piece's next
              matched-instance form proved it, while asking every piece's lead
              forms before grouping displaced cheap grouped proofs on another
              clause *)
      over_nodes : int option; [@default None]
          (** with [pieces.grouping.mode (Open)], a group of two or more
              pieces whose grouped question has more than this many nodes is
              not asked; its members are asked their lead forms (push-witness
              and matched-instance forms) as a stage of their own, before their
              other forms.  Every other group is asked as with the switch off,
              and no lead stage is asked before grouping on the open path
              ([pieces.grouping.mode (Open Before_grouping)] is not read
              while this is set) ([SeqInstantiation.lead_forms_open_min_nodes]).
              Sound: only a proof of a form, which implies its piece, is read,
              and no question is asked twice.  Why: the lead stage before
              grouping proved six pieces of a Rust-derived counter clause whose
              grouped question of about 428,000 nodes proved nothing in about
              90 s, while on a Rust-derived bit-set clause it replaced two
              small grouped questions proving 128 pieces by 129 serial
              questions; the size of the grouped question tells the two
              apart *)
    }
      (** no lead stage before grouping; the lead forms are asked as a stage
          of their own only for the pieces below *)
[@@deriving yojson]

(** Which pieces a grouped question gathers. *)
type grouping_mode =
  | Consecutive of {
      lead_first : bool; [@default true]
          (** with [pieces.grouping] (consecutive grouping;
              open grouping only with
              [pieces.grouping.mode (Open Before_grouping)]), ask each
              piece's forms that come before its deep forms (the
              push-witness and matched-instance forms) before building the deep
              first form the grouping compares, and leave a piece they prove out
              of every group ([SeqInstantiation.lead_forms_before_grouping]); a
              piece they do not prove is grouped as before and asked its
              remaining forms, so no question is asked twice.  Sound: only a
              proof of a form, which is a strengthening of its piece, is read.
              Why: on a Rust-derived loop clause the deep first forms, about a
              second each at idle, were built for twelve pieces of which the
              matched-instance forms then proved eleven at 0.1-0.2 s each *)
    }  (** only consecutive pieces of a clause *)
  | Open of { lead : open_lead; [@default After { unasked_groups = true; over_nodes = None }] }
      (** with [pieces.grouping], let a piece join any
          open group whose common part admits it, not only the group of
          the pieces just before it ([SeqInstantiation.group_open_pieces]),
          and ask the groups once every piece has its first form.  Sound as
          the grouping is: a group's question implies each member's first
          form.  Why: a loop-body clause's pieces fall into a few families
          with different premise instances, interleaved, so grouping only
          consecutive pieces asked 18 questions where 3 would do *)
[@@deriving yojson]

type piece_grouping = {
  mode : grouping_mode;
      [@default Open { lead = After { unasked_groups = true; over_nodes = None } }]
  max_nodes : int option; [@default Some 380000]
      (** with [pieces.grouping], a grouped question
          larger than this many formula nodes, as it would be asked, is not
          asked, and its group's pieces are asked their own forms at once,
          as after a grouped question that is not proved
          ([SeqInstantiation.group_question_max_nodes]); [None] asks every
          one.  Only a proof is read from a grouped question, so this
          changes which questions are asked and never which answer is
          read.  Why: one grouped question of 570,000 nodes was held by Z3
          for 44 s under a 10 s budget and left the run no time for the
          per-piece forms that prove its pieces, while the grouped
          questions proved on the same inputs were under 90,000 nodes.
          On by default. *)
  share_simplify : bool; [@default true]
      (** with [pieces.grouping], group the pieces'
          first forms before their last simplification and simplify each
          grouped question once ([SeqInstantiation.share_piece_simplify]),
          so that the disjuncts the pieces share are simplified once per
          group instead of once per piece.  The question is equivalent in
          every model to the one asked without it, but not the same
          formula; a piece whose group is not proved is asked its own
          forms as without it.  Inert without the grouping switch.  On by
          default, measured together with it *)
  replay_names : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, build
          the first forms of a clause's pieces for grouping with the fresh
          names replayed from one scope per clause
          ([SeqInstantiation.replay_piece_names]), so the instances of the
          premise the pieces share are named alike in every piece.  Sound:
          each first form is the strengthening of its piece it always is,
          only named differently, and the grouped question still implies
          each member's form, whatever names two members share.  Why: each
          piece's first form drew hundreds of fresh names of its own, which
          the grouping renamed back into one before seeing the common part *)
}
[@@deriving yojson]

(** What the sequence instantiation shares between the pieces of a clause. *)
type piece_sharing = {
  premise_instances : bool; [@default false]
      (** in the sequence instantiation of the zero-unknown verdict, ask a
          clause of several pieces first as the pieces of ONE instantiation
          of the whole clause, which is then quantifier-free, so the split
          is exact, before instantiating every piece on its own; the premise
          disjuncts the pieces share are instantiated once instead of once
          per piece.  Sound as the other forms are: the whole clause's
          instantiation strengthens it, and only a proof of validity is
          read.  When it does not prove the clause the pieces are asked as
          without it, so it costs time and never an answer.  Off by
          default: on the one input measured the shared forms were larger
          and the first undecided *)
  replayed_int_instances : bool; [@default true]
      (** inside the replay of fresh names under which a clause's pieces
          have their first deep forms built for grouping, let the integer
          step reuse the instances of an existential met again with the
          same candidates, budget left and replay position
          ([SeqInstantiation.share_replayed_int_instances]).  Each form is
          the formula built without it, name for name, so the questions
          asked are the same; only the building time changes.  Why: the 64
          pieces of a Rust-derived clause share their premise, and its
          integer instances were built once per piece, 11 s of a 120 s
          budget.  On by default, being exact *)
  deep_shapes : bool; [@default true]
      (** build the first deep form of the pieces of one clause that differ
          only in small quantifier-free literals no step of the deep form
          reads (no sequence, array or opaque-sort subterm, no binder) once
          per premise part and replay position, with a placeholder for the
          literals, and give each piece that form with its own literals put
          back where the simplification of the whole piece puts them
          ([SeqInstantiation.share_deep_shapes]).  Each form is the formula
          built without it, with the same fresh names drawn, so the
          questions asked are the same; a piece whose literals the
          simplification could merge with the premise part is built as
          without it.  Why: a Rust-derived loop-body
          clause has 64 pieces in families of eight sharing their premise
          part, and their first deep forms, 139,000-307,000 nodes each,
          took 75 s of a run at load 14.  Off by default: to be measured *)
}
[@@deriving yojson]

(** How a clause is split into pieces and how pieces are asked. *)
type pieces = {
  split_clause_heads : bool; [@default true]
      (** when preprocessing leaves no predicate variable and a residual
          clause is asked alone, first ask each of its [ClausePieces] -- a
          clause [body => c1 /\ ... /\ cn] is valid exactly when every
          [body => ci] is -- and ask the whole clause only when a piece is
          undecided ([ClausePieces.ask_by_pieces]); when off, each clause is asked
          whole, as before.  On by default: on the 112-file control it moved
          no verdict *)
  uncapped_conjunctions : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, split a
          conjunction into its sides' pieces however many they are together
          ([SeqInstantiation.uncapped_conjunction_pieces]), instead of
          keeping it whole once they pass the bound that limits a
          disjunction's distribution, and split a disjunction past that
          bound along one side as [candidates.pointwise_concat]
          does, so that no clause gets fewer pieces than without it.  Exact:
          a conjunction is valid exactly when each of its pieces is, so only
          which questions are asked changes.  Why: one more conjunct in a
          loop-body clause's conclusion took its 42 + 32 goal pieces past the
          bound, and the whole conclusion became one question whose
          instantiated form was millions of nodes and left undecided, where
          each piece is proved in a fraction of a second.  On by default *)
  bound : int option; [@default Some 4]
      (** with [Some m], a residual clause asked by its [ClausePieces] in
          the zero-unknown verdict is split into at most [m] pieces rather
          than the default bound's, and a piece left undecided is split once
          more, down to the default bound ([ClausePieces.ask_by_pieces]);
          [None], or a bound not below the default, keeps the default split.
          Each split is exact, so the bound changes which questions are
          asked and their number, never what an answer means.  The quick
          sweep keeps the default split *)
  pieces_first : pieces_first option; [@default None]
      (** when preprocessing leaves no predicate variable, before the quick
          sweep: [Some (z3_ms, cvc5_ms)] asks every residual clause by its
          [ClausePieces] ([ClausePieces.prove_pieces]), each piece in a fresh
          context under [z3_ms] (skipped for a shape the solver may not
          return on) and, when that leaves it undecided and [cvc5_ms] is
          set, by cvc5 under that budget ([Cvc5Proof.valid_within]), with no
          budget for the whole stage.  A clause whose pieces are all shown
          valid is recorded as valid; a piece refuted refutes the problem;
          any other clause is left whole to the stages after it.  Only
          proofs and refutations of pieces are read, and a clause is the
          conjunction of its pieces in every model, so the stage changes
          when an answer is reached, never which.  [None] skips it.  Why:
          the residual clauses of a Rust-derived loop are each a case split
          of a negated postcondition over several hundred shared premise
          disjuncts; the ladder left them undecided whole for 200 s, while
          cvc5 proves most of their cases in 0.1-0.4 s each. *)
  remember_proved : bool; [@default true]
      (** a schedule for the zero-unknown verdict's clause-by-clause
          stages that keeps what one stage proved for the next ones and
          lets no clause or piece end a stage for the others:
          - a rewritten clause asked by its pieces (the early and the late
            rewritten passes) is asked EVERY piece, not only those up to the
            first undecided one; a piece refuted still refutes at once, and
            when a piece stays undecided the whole clause is asked last, as
            without the switch;
          - the pieces left undecided are remembered, and the later
            rewritten pass and the sequence instantiation ask the
            conjunction of those pieces in place of the rewritten clause
            (the clause is the conjunction of its pieces in every model, so
            the clause is valid once the remembered pieces are) -- only
            when some piece was shown valid: with every piece undecided
            that conjunction is the clause again, in a form the sequence
            instantiation splits worse, and the clause is kept;
          - the sequence instantiation asks every clause not yet shown
            valid, smallest first by formula size (ties in the clauses'
            order), records each it proves, and does not stop at the first
            it cannot prove.
          Only a proof is read from the new questions and a refutation is
          taken only where it was before (a piece of a rewritten clause
          refuted, which refutes the rewritten clause), so the switch
          changes which answer is reached within the time and never which
          answer is right.  What it buys: a 32-piece clause whose second
          rewritten piece the sequence-axiom fallback decided in one run
          and not in another went whole, in the second, to the sequence
          instantiation, where every piece took about 27 s; the other
          pieces had each been decided in 0.1 s in the rewritten form.
          On by default *)
  grouping : piece_grouping option;
      [@default
        Some
          {
            mode = Open { lead = After { unasked_groups = true; over_nodes = None } };
            max_nodes = Some 380000;
            share_simplify = true;
            replay_names = true;
          }]
      (** in the sequence instantiation of the zero-unknown verdict, ask the
          first forms of consecutive pieces of one clause as ONE question
          before asking each piece's forms: the forms, renamed so that the
          premise disjuncts they repeat coincide, with their common
          disjuncts factored out ([SeqInstantiation.PieceGroups]).  The
          question is equivalent to the conjunction of the renamed forms,
          each of which is valid exactly when its form is, so only a proof
          of validity is read and it proves every piece of the group; when
          the question is not proved, each piece is asked its forms as
          without the switch, the first being the same one, so it costs
          time and never an answer.  On by default: over 198 sequence and
          array inputs at 120 s, together with the switch below, it gained
          an input no run answered without it (6 of 6 against 0 of 6) and
          lost none *)
  share : piece_sharing; [@default { premise_instances = false; replayed_int_instances = true; deep_shapes = true }]
}
[@@deriving yojson]

(** The one-point rewrite of a question. *)
type onepoint = {
  split : bool; [@default true]
      (** when preprocessing leaves no predicate variable and the
          unrewritten validity questions are undecided, also ask them after
          the one-point rule, the single-constructor split and the
          sequence-length split ([Evaluator.elim_onepoint_and_split_binders],
          all exact), in a fresh solver context; when off, the questions
          asked are exactly the unrewritten ones *)
  array_reads : bool; [@default true]
      (** inside the rewrite [rewrites.onepoint.split] switches on,
          also eliminate a literal fixing a read of a bound array:
          [exists s. L(s) /\ select s k = t] becomes
          [exists s. L(store s k t)], and a range of reads fixed pointwise:
          [exists s. L(s) /\ forall i. R(i) \/ s[i + c] = u(i)] becomes
          [exists s. L(lam j. ite (not R(j - c)) u(j - c) s[j])] (both
          dually under a universal), exact under array extensionality.  A
          disjunct [exists s. not P(s) /\ x = s[0]] -- the array encoding of
          a sequence witness whose first element an equation fixes -- needs
          a witness array the question does not contain, and Z3 answers
          "incomplete quantifiers" until the store is spelled out; a
          trait law's prepend witness is stated by both shapes at once.
          When off, bound arrays are left as they are *)
}
[@@deriving yojson]

(** Surjective pairing inside the one-point rewrite. *)
type surjective_pairing =
  | No_surjective_pairing  (** an equation [u = C(a1..an)] is left as it is *)
  | Flat_pairing
      (** inside the rewrite [rewrites.onepoint.split] switches on,
          also split an equation [u = C(a1..an)] of a datatype or tuple with
          a single constructor [C] into [sel_1 u = a1 /\ .. /\ sel_n u = an]
          (a disequation into the disjunction of the fields'), when some
          [ai] is a variable of the enclosing quantifier block not occurring
          in [u]; the one-point rule then eliminates it as [sel_i u].  Exact
          by surjective pairing and injectivity; a bound pair of integers a
          projection fixes, [exists v1 v2. t.0 = tuple(v1, v2) /\ ...],
          otherwise stays bound because the projection is no constructor
          application.  On by default: exact, and over 203 sequence and array inputs
          it answered, together with the chain and prepend witness forms, 171.6
          expected against 169.2 without. *)
  | Nested_pairing
      (** with [rewrites.surjective_pairing], also split such an
          equation when an [ai] mentions a variable of the enclosing block
          not occurring in [u] without being one ([u = TM (mut c d)], two
          single-constructor types, becomes [sel (sel u) = c /\ ..] in two
          steps and [c] is removed).  Exact; only when the split fires
          changes *)
[@@deriving yojson]

(** The contextual [ite] rule inside the one-point rewrite. *)
type contextual_ite =
  | No_contextual_ite  (** an [ite] is left as it is *)
  | In_place
      (** inside the rewrite [rewrites.onepoint.split] switches on,
          also replace an [ite] by the branch its context selects: where a
          sibling conjunct, the negation of a sibling disjunct or an
          enclosing [ite] guard entails the guard (or its negation), decided
          syntactically over integer linear literals.  Exact in every model,
          so it can neither lose nor invent an answer; what it buys is a
          bound array the array-read one-point rule left only in the else
          branch of the lambda it wrote, [k < 0 \/ k >= n \/ ite (0 <= k < n)
          u s[k]], which then no longer occurs and is dropped with its
          binder *)
  | As_extra_form
      (** with [rewrites.contextual_ite], apply the contextual
          [ite] rule not in place, to every rewritten clause and every form
          the verdict asks, but only to forms asked in addition, after the
          forms asked without it have failed: each rewritten clause not
          decided piece by piece is asked once more, piece by piece, in its
          contextual-ite form ([Evaluator.elim_onepoint_and_split_binders_contextual]),
          and in the sequence instantiation each piece gets its
          [SeqInstantiation.contextual_ite_form] as its last form, after
          the grouped question of its group and every other form of its own.
          Every other question is then the one asked with
          [rewrites.contextual_ite] off, so the contract is: with
          the field on, every clause and every piece proved, and every
          clause refuted, without the rewrite is proved (resp. refuted) by
          the same question, before any added question is asked.  The added
          questions are exact (the rewrite holds in every model) or
          strengthenings (the instantiation), so a proof read from one is
          sound, and a refutation is read only from the exact clause form.
          Why: applied in place, the rewrite changed the forms the grouped
          piece questions are built from, and on a Rust-derived call-site
          input those questions proved 8 pieces where without it they
          proved 21, turning an input answered 6 of 6 into 1 of 6.  Inert
          without [rewrites.contextual_ite].  On by default. *)
[@@deriving yojson]

(** Where a prefix of a concatenation is split. *)
type seq_prefix_split =
  | No_prefix_split  (** prefixes of concatenations are left as they are *)
  | Everywhere
      (** in the sequence instantiation of the zero-unknown verdict, where
          every read of a concatenation is split by index, also split every
          prefix of a concatenation: [extract (a ++ b) 0 k] becomes
          [if k <= len a then extract a 0 k else a ++ extract b 0 (k - len
          a)], and likewise in the clauses asked before any rewriting.  An
          equivalence in every model (SMT-LIB's extraction is empty for
          [k <= 0] and the whole sequence past its end), so the question
          stays the same one. *)
  | Focus_only
      (** with [rewrites.split_seq_prefix], split
          prefixes of concatenations only inside the chain-focused and
          associativity-matched forms (their instantiated variant), not in
          the clauses asked before rewriting nor in the deep forms.  Those
          forms hold a few kilobytes and one witness, so the split's
          [ite]s stay few, where applied to a deep form it was measured to
          triple its size; the split is exact wherever it applies, so this
          only chooses which questions carry it *)
[@@deriving yojson]

(** The decided form of a piece. *)
type decided_forms = {
  rlimit : int; [@default 200000]
      (** the resource limit of each entailment question *)
}
[@@deriving yojson]

(** The exact rewrites a question is asked through. *)
type rewrites = {
  onepoint : onepoint; [@default { split = true; array_reads = true }]
  surjective_pairing : surjective_pairing; [@default Nested_pairing]
  lift_spine_blocks : bool; [@default true]
      (** inside the rewrite [rewrites.onepoint.split] switches on,
          merge a block of the same quantifier that is a conjunct of an
          existential's body (a disjunct of a universal's) into the
          enclosing block, when none of its variables is bound there or
          free in the other parts: [exists xs. A /\ exists ys. B] is
          [exists xs ys. A /\ B].  Exact; what it buys is that an outer
          witness defined only through an inner binder ([w = t ++ s]) is
          removed by the one-point rule *)
  contextual_ite : contextual_ite; [@default As_extra_form]
  split_constructor_equations : bool; [@default true]
      (** inside the rewrite [rewrites.onepoint.split] switches on,
          also split an equation between two applications of one datatype
          constructor into the equations of their fields (a disequation into
          the disjunction of the fields' disequations), exact by the
          injectivity of constructors; so a bound tuple the single-constructor
          split opened and an equation fixes to a literal is eliminated by
          the one-point rule, and a bound sequence whose length it fixed is
          written out as units *)
  split_int_binders_at_ite : bool; [@default true]
      (** every validity question the zero-unknown verdict asks through
          [Z3interface.check_valid], [check_valid_seq_as_array] or the
          sequence-axiom fallback (the lemma route's included) is first
          rewritten with each integer binder whose body holds an [ite] on
          [x < c] (alone, or inside a compound condition such as the range
          tests a read of a concatenation is split with) split at [c] and
          its upper part shifted to start at zero
          ([Z3interface.with_split_int_binders], [IntBinderSplit.rewrite]).
          Exact: each split is an equivalence in every model, so every
          answer means what it meant.  Why: a proof that needs a universal
          at [x := k + c] from a read at [x - c] was found only by
          model-based instantiation, whose success depended on the spelling
          of a generated sort name or of bound variables and on the seed.
          On by default *)
  unwrap_embedded_formulas : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, first
          write every equation of two embedded formulas as the formula it
          states ([<p> = <true>] as [p]; [SeqInstantiation.unwrap_embedded_formulas]),
          so that a quantified fact a clause named by a Boolean variable is
          met by the matched-instance search in its first round.  An exact
          rewrite *)
  decided_forms : decided_forms option; [@default Some { rlimit = 200000 }]
      (** in the early rewritten pass of the zero-unknown verdict, when no
          words question of a piece's matched-instance forms proves it, ask
          one more question before the piece itself: the piece under the
          contextual [ite] rule, its two-round matched-instance form, with
          the integer atoms its own integer facts decide replaced by their
          values ([PCSatCommon.EntailedAtoms.decide], each entailment asked
          of the integer facts alone under
          [rewrites.decided_forms.rlimit], the answers kept for the
          ladder), natively in a context of its own.  The form implies the
          piece, so only a proof is read.  Adds a question per such piece.
          On by default: on a Rust-derived bit-set input whose clauses mix
          linear integer facts with words read through [int_to_bv], the
          solver does not close an integer case split those facts decide,
          and the decided form is refuted in about a second where the piece
          itself does not return *)
  implied_factor_equalities : bool; [@default false]
      (** each native question of the zero-unknown verdict (the quick sweep's
          and the fresh-context ones) is asked with the equations between
          the factors of its products that its linear facts imply stated as
          disjuncts [t != u] ([Z3interface.implied_factor_equalities], each
          equation shown by an [unsat] under the question's budget): an
          equivalence in every model, so every answer is one about the
          question.  Why: Z3's nonlinear arithmetic does not compare two
          products [n * t] and [w * i] once the linear part forces [n = w];
          on a bit-set obligation the question ran past 30 s under two of
          three seeds, and in the verdict two fresh 10 s questions of its
          pieces ran 30-88 s, while with [n = w] stated it was answered in
          under 0.12 s under every seed.  Off by default *)
  cancel_forced_sequence_binders : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, first
          eliminate a sequence binder [x] of an existential whose body has a
          conjunct [p ++ x = q] (or [x ++ p = q]) when the piece has a
          disjunct [p ++ u != q] (respectively [u ++ p != q]) over variables
          not bound there: the existential is replaced by its instance at
          [u].  Exact, by cancellation of a common prefix or suffix: where
          the disjunct is false [x] is forced to be [u], where it is true
          the piece holds.  So the binder is never offered candidates.  On
          by default *)
  rejoin_single_cons_fields : bool; [@default true]
      (** before the zero-unknown verdict asks a clause, fold back every group
          of clause variables that occurs only as one single-constructor
          application [c(y1 .. yn)] into one variable of the datatype
          ([Evaluator.rejoin_single_cons_fields]).  Exact: the rewritten clause
          is valid iff the clause is.  Why: the preprocessor's
          single-constructor split is made while a selector reads the
          variable; when predicate elimination later removes every such read,
          the residual keeps the fields only as [c(y1 .. yn)], and on a
          Rust-derived input decided at this verdict the countermodel the
          unsplit residual gave was not found on that form.  On by default.
          Off: the clause is asked as preprocessing left it.  On with
          nothing folded is not the same run as off: the attempt draws fresh
          names (the clauses' round trip through the old representation), so
          every later name differs *)
  guarded_length_only_sequences : bool; [@default true]
      (** before the zero-unknown verdict asks a clause, replace every
          integer-sequence variable the clause observes only through its
          length and through element guards (a premise "every element is in
          [lo, hi)") by a non-negative integer, when the constant sequence of
          one element makes every guard hold whatever the theory gives a read
          outside the sequence (each such check a small quantifier-free
          question asked under a resource limit)
          ([Evaluator.eliminate_guarded_length_only_sequences]).  Exact: the
          rewritten clause is valid iff the clause is.  Why: refuting an
          overflow check [len s + 1 < 2^64] needs a sequence of length
          [2^64 - 1], which neither Z3 nor cvc5 builds, and every question of
          the verdict ran out of its budget; the integer question is decided
          at once *)
  subst_projection_definitions : bool; [@default false]
      (** before the zero-unknown verdict asks a clause, replace a
          sequence-valued projection of a clause variable, [sel x], by the
          constructor term [t] a disjunct [sel x != t] of the clause defines
          it as, in the clause's other disjuncts
          ([Evaluator.subst_seq_projection_definitions]).  The disjunct is
          kept, so the clause is equivalent to its rewritten form in every
          model.  Off by default *)
  skolemize_positive_universals : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, first
          replace every universal of a piece reached through conjunctions,
          disjunctions and other such universals alone -- a conclusion's
          universal, or a premise's existential after negation normal form
          -- by fresh free variables, so that terms built from its variables
          become candidate witnesses for a sequence existential beneath it
          and candidate instances of a premise law.  Validity is unchanged
          by that step, so the instantiation's contract is too: only a
          proof of validity is read.  Off by default *)
  split_seq_prefix : seq_prefix_split; [@default Focus_only]
  seq_as_array : bool; [@default true]
      (** when preprocessing leaves no predicate variable, ask each validity
          question whose sequence terms use no [seq.extract] and whose reads are
          range-guarded as arrays plus a length first
          ([Z3interface.check_valid_seq_as_array]), and untranslated when that
          is undecided, when a countermodel cannot be read back as sequences,
          or when the question is outside the fragment.
          Contract: the translation is equisatisfiable with the question, so
          a proof of validity, and a countermodel read back, mean what they
          would mean untranslated; a question outside the fragment is asked
          exactly as when off.  Not exact: a translated question can be
          decided where the untranslated one was not (and the reverse, after
          which the untranslated question is still asked), so it changes
          which runs answer.
          Why on: Z3's sequence theory does not build a countermodel whose
          sequence must be very long (a length near 2^62 or 2^64 for a loop
          over a full integer range), and as an array plus a length such a
          countermodel is found at once; on the Thrust iterator inputs it
          acted on, it decided step-form iterator specifications the
          sequence route left undecided and cost no answer on any of them.
          [false]: the questions are asked as they are *)
}
[@@deriving yojson]

(** The sequence instantiation of a clause: what it instantiates and how
    large it may grow. *)
type seq_instantiation = {
  premises : bool; [@default true]
      (** when preprocessing leaves no predicate variable and every validity
          question asked before ends undecided, also ask each clause not yet
          shown valid after instantiating its sequence binders, and then its
          integer binders, where that only strengthens the question
          ([NoUnknownSeqInst]); it can only
          turn [unknown]/[timeout] into [sat], never into [unsat].  On by
          default: it is asked only after every other question ended
          undecided, and on the Thrust corpus it answers the same two
          iterator-extension queries as the sequence-axiom fallback.  When
          off, nothing is asked beyond the existing questions *)
  element_binders : bool; [@default false]
      (** in the sequence instantiation of the zero-unknown verdict, also
          instantiate an existential over an element of a sort variable or
          an uninterpreted sort, at the indices of the reads of the same
          array outside it, and an existential over an array of any sort, at
          the arrays of its sort the clause mentions and a fresh array,
          instead of replacing it by [false].  A trait
          law over a quantified sort -- the transitivity of [produces] --
          reaches a clause as such an existential, whose witnesses are the
          states the clause already reads.  Sound for the same reason as the
          other instances: each implies the existential. *)
  index_map_binders : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict,
          instantiate an existential over an index map, an array
          [Int -> Int], as [element_binders] does, also when
          [element_binders] is off
          ([SeqInstantiation.instantiate_index_map_binders]); every other
          element and array binder is then still replaced by [false].
          What it is for: the index map of a filter's [produces], whose
          witnesses the [candidates.index_map] rules give, without the
          growth of every deep form that instantiating the element binders
          of quantified sorts brings.  Sound as the other instances are:
          each implies the existential.  On by default: on the Rust-derived
          corpus it answers a filter's [produces] that nothing else did, and
          outside it no verdict changed.  Off, nothing changes *)
  max_nodes : int option; [@default None]
      (** in the sequence instantiation of the zero-unknown verdict, the node
          budget of each piece's plain and deep instantiations
          ([SeqInstantiation.piece_max_nodes]); [None] bounds nothing but the
          per-quantifier limits.  A bounded instantiation is still a
          strengthening of the piece, so the bound only loses proofs.  Why: on
          two Rust-derived inputs the verdict went silent for 60-100 s while
          the first deep form of one piece was being built, no question
          asked, until the run was killed *)
  max_int_input_nodes : int option; [@default None]
      (** in the sequence instantiation of the zero-unknown verdict, a
          piece's deep form is not built when the formula its integer step
          would instantiate is past this many nodes
          ([SeqInstantiation.piece_max_int_input_nodes]); [None] builds every
          one.  Not building a form only loses a proof.  Why: that step did
          not return in 45-70 s on forms of 80,000 and 270,000 nodes, the
          silent stretch that ended two Rust-derived inputs' runs, while the
          deep forms proved on them were under 20,000 nodes *)
  witness_forms : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, also
          ask each piece, after every other form, in a form shaped for the
          solver's e-matching ([SeqInstantiation.witness_form]): an
          existential's variable that occurs only inside array lambdas
          instantiated at a fresh free variable, and an integer one read
          through [n - c] in a constructor argument or array index renamed
          so it reads as a variable.  A strengthening, so only a proof of
          validity is read from it and it can only turn an undecided piece
          into a proved one.  With [rewrites.onepoint.array_reads],
          a law witness stated pointwise (an array prepending one element
          to another) becomes a lambda the solver instantiates the law
          with *)
  single_index_map_witness_forms : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, also
          ask each piece, before its deep forms, with a positive existential
          over one index map (an array [Int -> Int]) replaced by its body at
          one free index map of the piece at a time, and its integer binders
          instantiated with every quantifier kept beside its instances
          ([SeqInstantiation.single_index_map_witness_forms_of]): a goal
          [exists f. enumerates f ..] whose witness is the index map a
          filter's [produces] opens.  A strengthening, so only a proof is
          read from it.  On by default: it builds a form only for a
          positive existential over [Array Int Int] in a zero-unknown piece,
          which on the measured corpora occurs in one Rust-derived input,
          where it decides the piece; elsewhere it builds nothing *)
  lazy_plain_form : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, build
          a piece's plain instantiation only when that form is asked
          ([SeqInstantiation.lazy_plain_form]), not when the piece's forms
          are listed (every piece of a clause, before grouping).  The same
          forms in the same order; only when each is built changes (and
          with it the order of fresh-name draws).  On by default: the
          eager listing built every piece's plain instantiation (1-3 s a
          piece under load) although that form comes late and is rarely
          asked, which spent most of a 120 s budget before any question *)
  drop_array_hypotheses : bool; [@default false]
      (** in the sequence instantiation of the zero-unknown verdict, also
          ask each piece, after every other form (the witness form
          included), with the disjuncts of its negation normal form that
          are existentials binding an array or sequence around a universal
          quantifier removed ([SeqInstantiation.drop_array_hypotheses_form]):
          the negated form of a premise quantified over arrays, which the
          solver's instantiation cannot decide even where the piece does
          not depend on it.  Removing a disjunct strengthens the question,
          so only a proof of validity is read from it and it can only turn
          an undecided piece into a proved one *)
  ground_funapps_linear : bool; [@default true]
      (** with [matched_instances.forms], the ground
          function applications a matched-instance form matches against are
          collected in one pass that computes each node's variables outside
          the formula's free ones from its children's
          ([SeqInstantiation.ground_funapps_one_pass]), instead of one
          [Term.tvs_of] per application, which is quadratic in the nesting
          depth.  The same list either way, so the forms and the questions
          are the same; only the time to build them changes.  On by
          default *)
}
[@@deriving yojson]

(** The offset positions offered an integer existential. *)
type offset_int =
  | No_offset_int  (** no offset position is offered *)
  | All_lengths
      (** in the sequence instantiation of the zero-unknown verdict, also
          offer an integer existential used as a read index or an
          extraction bound the positions [t - len u] and [t + len u], [t] an
          index or extraction bound the clause reads and [u] a sequence
          whose length it mentions, after every other candidate and at most
          eight of them: the position a lemma over prefixes of [u ++ w]
          needs to reach a read of the concatenation at [t].  Sound as the
          other instances are: each implies the existential. *)
  | Chain_only
      (** with [candidates.offset_int], offer the positions
          [t - len u] and [t + len u] only for a [u] that is an operand of
          the middle argument of a chained pair of ground applications
          [h(s, u1, m)], [h(m, u2, e)] of the piece -- the operands a
          transitivity witness [u1 ++ u2] is built from, and the only [u]
          whose offset a prefix lemma over that witness needs.  Fewer
          instances of the same kind, so sound as they are; with the
          unrestricted rule the extra instances were measured to cost more
          time than they save *)
[@@deriving yojson]

type index_map = {
  shift : bool; [@default true]
      (** with [seq_instantiation.element_binders] or
          [seq_instantiation.index_map_binders], also offer
          an existential over an array [Int -> Int] the shifts [lambda k. k
          + len u] by the lengths the clause mentions outside every binder,
          and the identity ([SeqInstantiation.index_map_shift_candidates]):
          the index map of a visited suffix [v] of [u ++ v], which a
          filter's [produces] needs after it has produced one item.  Sound
          as every instance is.  On by default, with [index_map_binders]:
          together they answer a filter's [produces] that nothing else did,
          and on a corpus no verdict was lost *)
  join : bool; [@default false]
      (** with [seq_instantiation.element_binders], also offer
          an existential over an array [Int -> Int] the joins [lambda k.
          ite (k < c) g[k] (h[k - c] + d)] of two free index maps at the
          prefix lengths of two concatenations its body mentions
          ([SeqInstantiation.index_map_join_candidates]): the index map of
          [ab ++ bc] over [s1 ++ s2] that a filter's [produces_trans]
          needs, which the input writes as a [lambda] that is beta-reduced
          before instantiation.  Sound as every instance is.  Off by
          default: built for one input, not measured on a corpus *)
}
[@@deriving yojson]

(** The witness candidates the sequence instantiation offers an existential. *)
type candidates = {
  offset_int : offset_int; [@default Chain_only]
  array_read_int : bool; [@default false]
      (** in the sequence instantiation of the zero-unknown verdict, also
          offer an integer existential read as an array index, [a[x + d]],
          the indices [u - d] of the reads [a[u]] of the same array outside
          every binder ([SeqInstantiation.array_read_int_candidates]): the
          witness of a goal [exists j. f[j] = i] over an index map joined
          from two, which is a premise's witness [k] or [k + n] and is read
          by no sequence.  Sound as every instance is: each implies the
          existential.  Off by default: built for one input, not measured
          on a corpus *)
  bool_binder : bool; [@default false]
      (** an existential of the zero-unknown verdict's integer
          instantiation that also binds a [Bool] is instantiated with the
          [Bool] at both values rather than replaced by [false]
          ([SeqInstantiation.bool_binder_candidates]): a law over a
          closure's postcondition, which quantifies over its result.  Sound
          as every instance is.  Off by default: built for one input, not
          measured on a corpus *)
  through_constructors : bool; [@default false]
      (** with [seq_instantiation.element_binders], an element
          binder that is a constructor's argument at an array index,
          [r[c(.., x, ..)]], is also offered the argument at that place of
          the same constructor at that index of a read of [r] outside the
          quantifier
          ([SeqInstantiation.element_candidates_through_constructors]): a
          law over a closure's states [mut c d].  Sound as every instance
          is.  Off by default: built for one input, not measured on a
          corpus *)
  literal_range_int : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, also
          offer an integer existential the integers in [-8, 8] satisfying
          every top-level conjunct of its body that mentions it alone, when
          there are at most four
          ([SeqInstantiation.literal_range_int_candidates]): a position of a
          sequence of literal length, such as the one item a filter's step
          visits.  Sound as every instance is.  On by default, with
          [index_map.shift]: together they answer a filter's [produces] that
          nothing else did, and on a corpus no verdict was lost *)
  index_map : index_map; [@default { shift = true; join = false }]
  recfun_predecessor_int : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, also
          offer an integer existential used in a read index [t - 1] for each
          integer argument [t] of an application of a recursive function
          outside every binder of the clause
          ([SeqInstantiation.recfun_predecessor_int_candidates]): the bit a
          counting function's step reads at counter [m] is [m - 1], inside
          its body, where no read of the clause names it.  Sound as every
          instance is; the terms come after every other rule's, so none of
          those is displaced.  Does nothing on a clause that applies no
          recursive function of the environment: an input without
          [define-fun-rec] (the datatype size functions in the environment
          are applied only by templates, never by a clause the ladder asks).
          On by default: it answers a step clause that needs the premise at
          the predecessor, and on a corpus no verdict was lost *)
  seq_array_view : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, also
          instantiate a positive existential over an array of sort
          [Int -> E] at the array views [lambda k. seq.nth s k] of the
          clause's ground sequences [s] of sort [Seq E]: a loop history a
          clause states once as a premise sequence and once as a goal array
          of the same states is witnessed by the sequence read as an array.
          Sound for validity only, as every instance of a positive
          existential is.  On by default *)
  pointwise_array : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, also
          instantiate a positive existential over an array of sort
          [Int -> E] at its pointwise definitions: for an equation
          [select x j = u] in its body, [j] an integer variable and [u]
          mentioning only [j] and the formula's free variables, the array
          [lambda j'. u[j'/j]].  A history stated in the array-and-length
          encoding of sequences, [forall k. 0 <= k < n => ta[k] = k + c], is
          witnessed by that function.  Sound for validity only, as every
          instance of a positive existential is.  On by default *)
  pointwise_seq_literal : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, also
          instantiate a sequence binder (a positive existential or a
          premise's universal) at its pointwise literals
          [unit u(0) ++ ... ++ unit u(k-1)]: [u] read off an equation or
          disequation [seq.nth x j = u(j)] of its body, [k] a length at
          which a test of the body over [seq.len x] alone changes its value
          ([SeqInstantiation.pointwise_seq_literal_candidates]).  A premise
          "no three items of the form [i + c] are produced" is refuted only
          at [[c, c+1, c+2]].  Sound as every instance is.  On by default *)
  prepend_unit : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, also
          offer a positive sequence existential whose body builds
          [x ++ p1 ++ ... ++ pk] the terms [unit e ++ u], where [u] is what
          a clause term [u ++ q1 ++ ... ++ qk] leaves for [x] and [unit e] a
          singleton of the clause: a law at a state one step later, after
          the step produced the item [e].  Sound as the other instances are:
          each implies the existential, so only a proof of validity is
          read.  Off by default *)
  pointwise_concat : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, also
          offer a positive sequence existential read pointwise and mentioning
          a clause sequence [w1 ++ ... ++ wm] the terms [u1 ++ ... ++ um],
          each [u_i] read beside [w_i] at one index in an atom of the clause
          (the premise [forall k. R(u_i[k], w_i[k])]); an element bound by a
          premise's universal is a candidate only with
          [rewrites.skolemize_positive_universals].  Sound as the
          other instances are: each implies the existential.  Also splits a
          piece whose distribution over its disjunctions would exceed the
          piece bound along one side of the disjunction, the other kept
          whole, which is exact.  Off by default *)
  singleton_extension : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, also
          offer a positive sequence existential whose element sort has a
          single value (a datatype of one constructor whose fields each
          have one value, such as the state of a closure capturing
          nothing) the terms [s ++ unit c], [s] a sequence of that sort in
          the clause and [c] the value: such a sequence is determined by
          its length, and a step extending a history by one item needs one
          longer than any the clause writes.  Sound as the other instances
          are: each implies the existential.  Where it offers no term (no
          such sort, or no sequence of it in the clause) the candidates and
          hence the questions are those without it *)
  chain_concat : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, also
          offer a positive sequence existential whose body applies a
          relation [h] (an array read as a chain of [select]s) with the
          binder at position [j] the concatenation [x0 ++ x1] of two
          applications [h(s, x0, m)] and [h(m, x1, e)] of the piece whose
          middle arguments agree -- the witness a transitivity law
          [h(a, u, b) /\ h(b, v, c) => h(a, u ++ v, c)] gives, which the
          clause never writes.  First among the candidates, those whose
          endpoints are the goal's own ahead, at most four.  Sound as the
          other instances are: each implies the existential.  On by
          default *)
  chain_free_only : bool; [@default true]
      (** with [candidates.chain_concat], read the chained
          applications only where their arguments mention no variable the
          clause binds, after rebinding such a variable by constructor
          injectivity against an equation over free terms
          ([SeqInstantiation.chain_apps_free_only]), so that the premise
          [forall i. r = Some i => h(b, [i], c)] beside [r = Some x] gives
          the witness [t ++ [x]] rather than [t ++ [i]] with [i] free.  Any
          term is a sound instance, so this changes which forms are built,
          never what a proof means.  When off, the candidates are exactly
          those built without it. *)
      (* not a field of [chain_concat]: the matched-instance forms read the
         chained applications through the same switch whatever
         [chain_concat] says *)
  nested_focus_forms : bool; [@default true]
      (** the chain-focused and associativity-matched forms of the
          zero-unknown verdict instantiate their integer binders in two
          nested rounds with equated candidates, as the deep forms do
          ([SeqInstantiation.nested_focus_forms]), so that an existential
          exposed by the first round's instances is instantiated rather
          than dropped.  Sound as every instance is.  On by default, with
          [index_map.shift]: together they answer a filter's [produces] that
          nothing else did, and on a corpus no verdict was lost *)
}
[@@deriving yojson]

(** The matched-instance forms.  [forms] is a switch beside the others
    rather than a variant over them: the solution checker's matched forms
    read [aligned_hyps] and [hyp_budget] whatever [forms] says. *)
type matched_instances = {
  forms : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, ask
          each piece FIRST with every positive existential replaced by its
          instances at the substitutions one round of first-order matching
          of its body's subterms against the piece's ground terms finds
          (at most eight each), [false] where none is found
          ([SeqInstantiation.matched_instance_form]).  Sound for validity
          only: each instance implies its existential, so the form implies
          the piece.  On by default *)
  hyp_budget : int option; [@default None]
      (** with [matched_instances.forms], the number of
          instances one pass of the earlier-pieces form may make
          ([SeqInstantiation.earlier_pieces_form]; 64 when [None], as for
          the other matched forms).  Only which instances are offered
          changes, so soundness is as above.  [None] by default *)
  element : bool; [@default true]
      (** with [matched_instances.forms], a sequence binder
          of a positive existential is also offered the one-element
          sequence [seq.unit t] for each element equation [seq.nth x i = t]
          of its body, and [u ++ seq.unit t] for each sequence [u] of its
          sort free in the piece
          ([SeqInstantiation.element_equation_candidates_for]), these only
          where the matches leave room; and [a ++ b] where the body states
          the binder pointwise as [a] below [len a] and [b] above
          ([SeqInstantiation.pointwise_definition_candidates_for]): the
          witness of an existential introduction built from the element the
          goal fixes, or a lemma's concatenation, which the piece never
          writes.  Only which instances are offered changes, so soundness
          is as above.  On by default *)
  chain_join : bool; [@default true]
      (** with [matched_instances.forms], a piece is also
          asked its chain-join forms ([SeqInstantiation.chain_join_forms_of],
          after its matched forms): a positive existential whose sequence
          binder its body reads instantiated at the join
          [u ++ extract w 1 (len w - 1)] (or [extract u 0 i ++ w]) of two
          sequences free in the piece whose elements [u[i]] and [w[0]] the
          piece equates to a common term
          ([SeqInstantiation.chain_join_candidates_for]) -- the witness of
          a chain of states over a concatenation whose halves share their
          middle state -- its reads split, its universals skolemized, the
          rest matched.  Each form is a strengthening, so only a proof is
          read.  On by default *)
  last_index : bool; [@default true]
      (** with [matched_instances.forms], an integer binder
          of a positive existential is also offered [len s - 1] for each
          [seq.len s] of its body free in the piece
          ([SeqInstantiation.last_index_candidates_for]): the instance at
          the last index of a premise stated for every index.  Only which
          instances are offered changes.  On by default *)
  assoc_open : bool; [@default true]
      (** with [matched_instances.forms], the matching that
          chooses a matched form's instances matches a concatenation
          pattern modulo associativity (a sequence binder standing for a
          run of the ground term's operands:
          [SeqInstantiation.assoc_concat_matching]), and an existential no
          complete substitution matches is instantiated at the maximal
          substitutions that fix every array and sequence binder, the
          scalar binders they leave out kept existential
          ([SeqInstantiation.open_scalar_matches]).  Every such instance
          implies its existential, so each form still only strengthens its
          piece and only a proof is read.  What it buys: a premise
          [forall s e r. P(h ++ s) /\ Q(s ++ [e], r) => P(h ++ s ++ [e])]
          whose ground facts write [h ++ [x] ++ y] is instantiated at
          [s = [x] ++ y], with the end state [r] that no ground term names
          left to the solver.  On by default *)
  collections_only : bool; [@default true]
      (** with [matched_instances.forms], each piece is also
          asked, after its other matched-instance forms, with only the
          existentials binding an array or a sequence instantiated by
          matching and every other existential left as it is
          ([SeqInstantiation.matched_instance_form]'s [collections_only]):
          a premise universal over indices then stays for the solver to
          instantiate at the index the goal's instance leaves.  A
          strengthening of the piece, so only a proof is read.  On by
          default *)
  aligned_hyps : bool; [@default true]
      (** with [matched_instances.forms], the earlier-pieces
          form first aligns each earlier piece with the piece, mapping its
          own variables onto the piece's by matching disjunct against
          disjunct and dropping the disjuncts so matched
          ([SeqInstantiation.aligned_hypotheses]), and then keeps every
          existential over no array or sequence and every universal for the
          solver to pair, the goal's index with a hypothesis's among them.
          Sound because the pieces before are proved first.  Off by
          default *)
  max_form_size : int option; [@default Some 20000]
      (** with [matched_instances.forms], a matched-instance
          form whose instances are estimated (instances times body size, in
          formula nodes, summed over the existentials it instantiates, before
          any is built) past this many nodes is not built and is skipped as
          an undecided form is ([SeqInstantiation.max_matched_form_size]);
          [None] builds every form.  Skipping a form only loses a proof.
          20,000 nodes by default: over the Thrust inputs with the largest
          matched forms, every form of at most 160,000 characters was
          estimated at 12,300 nodes or fewer, while the two pieces that
          built three-million-character forms (13-31 s each) were
          estimated at 30,500 and 110,300 *)
  bound_before_ranking : bool; [@default true]
      (** with [matched_instances.forms] and
          [matched_instances.max_form_size], an existential's share
          of a matched-instance form's size estimate is tested against the
          bound before its substitutions are ranked
          ([SeqInstantiation.matched_bound_before_ranking]) rather than
          after: the ranking is a permutation, so the same forms are built
          and the same are skipped; only the time to skip one changes.  On
          by default *)
  goal_directed : bool; [@default true]
      (** with [matched_instances.forms], a matched-instance
          form chooses its instances goal-directed
          ([SeqInstantiation.goal_directed_instances]): the per-pass
          instance budget dealt in rounds over the existentials at the top
          of the piece, every one with a substitution receiving one before
          any receives a second, and each one's substitutions searched from
          the goal's matching literals and ranked by literal and term
          agreement, instead of first come first served in traversal order
          and in the search's order.  Sound either way: each form implies
          its piece.  On by default: on the Rust-derived inputs where a
          planned pass occurs it answered the same files as first come
          first served, slightly faster (117 s against 123 s summed over
          four files, three runs each).  [false]: first come first
          served *)
}
[@@deriving yojson]

type chain_join = {
  forms_first : bool; [@default true]
      (** with [matched_instances.chain_join],
          a piece's chain-join forms are asked before its other matched
          forms instead of after them
          ([SeqInstantiation.chain_join_forms_first]): a chain-join form
          exists only where the piece has the shape of a transitivity law
          (an existential chain whose witness is the join of two chains the
          piece states), whose witness the other matched forms, which offer
          only terms the piece writes, cannot name.  Only the order of
          proof-only questions changes.  Why: on a Rust-derived iterator's
          transitivity piece the forms before the chain-join form and the
          lemma route between them cost 60-120 s, the chain-join form 5 s.
          On by default: together with the resource count of the
          sequence-axiom fallback below and the unknown-free condensation it
          made that input answer, and it lost no answer on the inputs it
          acts on *)
  direct_reads : bool; [@default true]
      (** with [matched_instances.chain_join],
          two chains are also joined where the piece writes their shared
          element as one equation [u[i] = w[0]] between the two reads,
          with no common term ([SeqInstantiation.chain_join_direct_reads]).
          That is the shape the pairs take once the middle state, a field
          of a tuple, is a variable the one-point rule replaced by one of
          the reads (as after the preprocessor's
          [clauses.split_single_cons]).  Only which instances are
          offered changes, so only a proof is read.  On by default *)
  focused : bool; [@default true]
      (** with [matched_instances.chain_join],
          the chain-join forms instantiate every existential left after the
          goal's instance at its two best substitutions, those whose
          instances write a term mentioning a constant the goal's
          skolemization introduced first (the per-index premise at the
          goal's fresh index, the transitivity law at the state it reads),
          then those writing the most terms of the piece, and keep no
          existential beside its instances.  A strengthening, so only a proof is read.
          On by default *)
  max_focus_size : int option; [@default None]
      (** with [matched_instances.forms], a chain-join form
          whose focused formula (the piece with the joined existential
          instantiated and the transitivity-law instances over every chained
          pair, before simplification) is past this many nodes is not built
          and is skipped as an undecided form is
          ([SeqInstantiation.max_chain_join_focus_size]); [None] builds every
          one.  Skipping a form only loses a proof.  Why: on Rust-derived
          pieces the focused formula and the simplification and matching
          run on it, before any instance estimate is reached, held the
          verdict for more than 200 s with no question asked *)
}
[@@deriving yojson]

type chain_focus = {
  form : bool; [@default true]
      (** in the sequence instantiation of the zero-unknown verdict, after
          every other form of a piece has failed, also ask it with a
          positive sequence existential [exists x. ... h(s, x, e) ...]
          instantiated at [x0 ++ x1] ALONE, for a pair of ground
          applications [h(s, x0, m)] and [h(m, x1, e)] of the piece, a
          sequence existential two of whose applications of [h] match that
          pair (a negated transitivity law) instantiated at the matched
          tuple alone, and every other sequence existential replaced by
          [false]; once with the integer binders left bound and once with
          them instantiated.  Sound for validity only: each instance
          implies its existential and [false] implies anything, so the form
          implies the piece.  Off by default *)
  push_witnesses : bool; [@default true]
      (** in the chain-focused forms ([chains.focus.form]
          and the pushed forms below), the chain-focused
          existential's OTHER sequence binders are instantiated too, each
          binder [y] the body reads at the focused binder's length ([t =
          seq.nth y (seq.len x)]) at [a ++ unit t], [a] the premise
          sequence whose length a premise ties to the chain's prefix (a
          loop's history restated after a step: the previous history
          pushed once, [SeqInstantiation.push_witnesses]); and each such
          focused form, with the premise laws over opaque values kept
          quantified and its integer binders instantiated, is asked FIRST
          among the piece's forms (at most two).  Sound for validity only:
          every instance implies its existential and keeping a disjunct is
          exact, so each form implies the piece.  Off by default *)
}
[@@deriving yojson]

(** The forms built for a chain of states (a transitivity law's witness). *)
type chains = {
  join : chain_join;
      [@default { forms_first = true; direct_reads = true; focused = true; max_focus_size = None }]
  focus : chain_focus; [@default { form = true; push_witnesses = true }]
  assoc_match : bool; [@default true]
      (** as [chains.focus.form], for a positive sequence
          existential whose body applies [h] with [v ++ t] in the middle
          ([v] bound by it) and a pair [h(a, u, b)], [h(b, w, c)] of ground
          applications whose start and end match the application's: [u ++
          w] is matched against [v ++ t] modulo associativity (so [v] is [u
          ++ w'] with [w = w' ++ t], the end bound to [c]), the existential
          is instantiated at that match alone and a transitivity law at the
          pair.  Sound for validity only, for the same reason.  Off by
          default *)
}
[@@deriving yojson]

(** A form that reads a concatenation at a skolem position, asked by the
    three cases of the position first. *)
type case_split_index =
  | No_index_cases  (** every form is asked whole *)
  | Index_cases of {
      budget_ms : int option; [@default None]
          (** with [case_split_index], ask each index
              case question at this budget in ms (capped at
              [budgets.query_ms]) instead of the form's own, so that a
              case the solver decides only slowly counts as undecided and the
              piece's forms are then asked whole
              ([SeqInstantiation.index_case_ask]).  Only when a proof is found
              changes: the cases are still all proved for a proof by cases,
              and a form not so proved is asked whole at its own budget.  Why:
              on a loop-step clause whose whole form is proved in about 11 s,
              each of its three cases was proved in 10.6-14.3 s, tripling its
              cost, while on the input the cases are for each case decides in
              0.1-0.2 s.  [None] (the default) asks the cases at the form's
              budget *)
      max_size_ratio : float option; [@default Some 0.5]
          (** with [case_split_index], ask a candidate
              split by cases only when each of its three case questions has an
              AST size at most this ratio times the form's, skipping it with no
              question otherwise ([SeqInstantiation.index_case_max_size_ratio]);
              a form none of whose candidates passes is asked whole, as
              without the cases.  Only removes case questions, so a proof by
              cases is still three proved cases.  Why: where a case decides
              the guards of most of the form's reads its question is a few
              percent of the form's size and decided fast; where it does not,
              each case question keeps most of the form's size and is about as
              slow as the whole form, tripling the piece's cost.  [None] asks
              every candidate; the default is 0.5 *)
    }
      (** in the sequence instantiation of the zero-unknown verdict, ask
          each of the first two forms of a piece that reads [seq.nth (u ++
          w) i] at [i = t] or [t + c] ([t] a free integer, the skolem of a
          position of an extended history) first by the three cases of [t]
          against [len u] ([SeqInstantiation.index_cases_outcome]: the form
          with [t >= len u], [t != len u], [t <= len u] added as a
          disjunct), and whole only when some case is not proved; once a
          case question of a piece is left undecided (it ran out of its
          budget), the piece's forms are asked only whole.  Sound: the
          cases cover every model, so the three proved prove the form, and
          the form implies the piece.  On by default, together with the size
          ratio below *)
[@@deriving yojson]

(** The axiomatised sequence question asked before a native one. *)
type axioms_first = {
  ms : int; [@default 1000]
      (** before each validity question of the zero-unknown verdict that
          mentions a sequence, first ask it with the sequences axiomatised
          (the sequence-axiom encoding), under this budget in milliseconds,
          and read only a proof; the native question follows otherwise.  The
          native sequence theory was measured spending 98% of a Thrust run in
          such questions, while the axiomatised form decides the pointwise
          shape at once.  On by default at 1000 ms: over 205 Thrust and
          quantified-invariant inputs it lost no answer and cut the time of
          the answered ones by about 5%. *)
  fresh : bool; [@default false]
      (** apply [axioms.first] also to the questions
          asked in a fresh context, which otherwise ask the native sequence
          theory first and reach the axiomatised form only through the
          sequence-axiom fallback, after the native question has spent its
          budget.  Contract: when on (and [axioms.first]
          is [Some]), every validity question the ladder asks in a fresh
          context -- the rewritten clauses early and late, the
          sequence-instantiated forms in both passes of the two-pass budget,
          and the point pin's proofs, which all go through one asker -- that
          mentions a sequence is first asked with the sequences axiomatised
          under that budget; when off, those questions are asked exactly as
          before.  The satisfiability questions of the pins, which read a
          model, are not affected: the axiomatised form yields no model.
          Only a proof is read from the axiomatised question, so it can
          only answer [Valid], and that proof is the one the fallback would
          read from the same encoding afterwards; any other outcome hands
          the question to the native theory as before, so a refutation of
          an exact rewrite is still reached, at most one axioms budget
          later.  The switch therefore changes timing only -- which answer
          is reached within the time, never which answer is right.  What it buys: pieces whose native question runs out its
          10 s and whose axiomatised form is proved in under a second, each
          asked 10 s sooner; what it costs: up to the axioms-first budget per
          question the encoding does not prove. *)
}
[@@deriving yojson]

(** Which fallbacks get the resource count. *)
type fallback_scope =
  | All_fallbacks
      (** every fallback a ladder question asks, the pooled ones inside
          [check_valid] included *)
  | Refused_only
      (** with [axioms.ladder_fallback], the pair applies
          only to the fallback of a fresh ladder question the solver was
          not asked at all -- [may_not_return] refused it and no forked
          copy asked it ([external.fork_refused_ms] off) --
          for which the fallback is the question's only attempt
          ([LadderSeqAxiomRlimit.for_fallback]); the fallback after a
          question the solver was asked and left undecided, and every
          fallback asked inside the pooled questions' [check_valid], keep
          the process-wide wall-clock budget, as without the pair.  The
          fallback turns nothing but an undecided answer into [`Valid], so
          only which undecided questions are proved, and what each costs,
          changes.  Why: over four Rust-derived inputs every fallback proof
          of a fresh question the solver had been asked was cheap (at most
          0.2 s), and on one loop step the 17 fallbacks after questions the
          solver had run to their budget proved nothing and cost 51 s under
          a 3 s kill, where the process-wide 500 ms would have cost 8.5 s *)
[@@deriving yojson]

(** The sequence-axiom fallback of a ladder question bound by a Z3 resource
    count. *)
type ladder_fallback = {
  rlimit : int; [@default 500_000]
      (** the fallback's Z3 resource count (scaled by [units_per_node] when
          that is set) *)
  kill_ms : int; [@default 3000]
      (** the fallback's wall-clock budget, in place of the process-wide
          one; a forked fallback is killed at three times it *)
  scope : fallback_scope; [@default Refused_only]
  units_per_node : int option; [@default Some 96]
      (** with [axioms.ladder_fallback] = [Some (units,
          kill_ms)], [Some k] makes the fallback's count of a fresh ladder
          question of [n] nodes [k * n] rather than [units], and gives a
          question the count only where [k * n] reaches [units]; a smaller
          question keeps the process-wide wall-clock budget, as without the
          pair ([LadderSeqAxiomRlimit.for_fallback]).  So a large question
          is given a count in proportion to its size and the budget
          [kill_ms], and a small one stops when it stopped before.  [None]: the fixed
          count [units] for every question.  The fallback turns nothing but
          an undecided answer into [`Valid], so only which undecided
          questions are proved, and what each costs, changes.  Why: over
          four Rust-derived inputs (125 fallback questions of the ladder,
          each asked with a 3 s or 1 s kill) the questions the fallback
          proved needed at most 135 units per node of the question except
          five of under 1,600 nodes (at most 0.71 s each), while those it
          did not prove ran at 170-40,000 units per node until stopped, the
          large ones at 5-50; so a count of 64 units per node is above
          every proof of a large question -- seven 22,900-node pieces of
          one loop step needed 650,000-1,120,000 units, 0.33-0.54 s against
          the 500 ms that load decided -- while a fixed count of 1,500,000
          units let small unproved questions run 1-3 s instead of 0.5 s,
          8-17 s more a run on three other inputs.  96 rather than 64: the
          deciding fallback of another Rust-derived loop needs about
          1,280,000 units at 15,953 nodes, so 81 units per node is its
          threshold; under 64 that question was proved or not depending on
          the process's history and load, and under 96 it was proved in
          every run, with no answer lost and no time added on the
          sequence-bearing inputs the count reaches *)
}
[@@deriving yojson]

(** The sequence axioms: the axiomatised question first, and the fallback
    after a native one. *)
type axioms = {
  first : axioms_first option; [@default Some { ms = 1000; fresh = false }]
  ladder_fallback : ladder_fallback option;
      [@default Some { rlimit = 500_000; kill_ms = 3000; scope = Refused_only; units_per_node = Some 96 }]
      (** [Some (units, kill_ms)]: every question of the zero-unknown
          ladder asks its sequence-axiom fallback under a Z3 resource count
          of [units] ([Z3interface.with_seq_axiom_rlimit]), its wall-clock
          budget raised (or lowered) from the process-wide
          [seq_axiom_fallback] to [kill_ms] (the question's own budget
          still caps it).  Both are Z3 parameters, which Z3 does not
          always read; the check is killed only when it is asked in a
          forked copy ([axioms.fork_fallbacks],
          [z3.seq_axiom_fork]), at three times [kill_ms].  An exhausted count is an undecided fallback, which leaves
          the question's answer as it was: only a proof comes out of the
          fallback.  [None]: the process-wide wall-clock budget alone.  Why:
          on a Rust-derived loop step the fallback's proofs of seven
          near-identical pieces took 0.37-0.74 s against its 500 ms budget,
          so the host's load decided how many of the seven were proved
          (seven in one run, three in the next), and each piece lost cost
          another 12-20 s of larger forms *)
  fork_fallbacks : bool; [@default true]
      (** ask every sequence-axiom fallback check a zero-unknown ladder
          question makes in a forked copy of the process, killed after
          three times the check's budget (at least 1 s), as the
          process-wide [z3.seq_axiom_fork] does for every fallback of the
          run ([Z3interface.with_seq_axiom_fork_runner]).  The copy asks the
          same check with the same budget and resource count and only a
          proof is read back, so only a proof lost to the kill can change.
          Why: asked in process, the fallback's budget and count are Z3's
          own parameters, and on a Rust-derived loop step Z3 read neither in
          one check of a 61,176-node question given 500 ms, which ran 52 s
          and cost the run its answer; a killed copy is the only bound
          that holds.  Where no copy can be made (other domains running)
          the check is asked in process, unbounded as before *)
  invalid_skips_fallback : bool; [@default false]
      (** a zero-unknown ladder question asked in a forked copy
          ([external.fork_seqinst],
          [external.fork_refused_ms]) and answered invalid
          there is not handed to the sequence-axiom fallback, as an
          in-process question answered invalid is not: the copy's
          countermodel is not sent back, so without the field its answer
          reaches the fallback as an undecided one.  The fallback can only
          turn an undecided answer into a proof, and a question with a
          countermodel has none to give, so only the time changes.  Why: on
          a Rust-derived input under a resource-counted fallback, each such
          question spent another 1-2 s in a fallback that proved none of
          them, about 20 s of one clause's 21 s *)
  first_after_fallback_proof : bool; [@default false]
      (** with [axioms.first] = [Some _] and [axioms.first.fresh] off: once
          a fresh-context question of this verdict has run its native
          question to its budget ([`Timeout]) and the sequence-axiom fallback
          then proved it, every later fresh-context question of the same
          verdict that mentions a sequence is asked as [axioms.first.fresh]
          asks it -- the axiomatised form first under [axioms.first.ms], the
          native question only when that does not prove it.  Before that
          event the questions are asked exactly as with the field off.
          Contract: only a proof is read from the axiomatised question, and
          any other outcome hands the question to the native theory and its
          fallback as before, so the field changes when an answer is
          reached, never which answer is right ([AxiomsFirst.ask]).  What
          it buys: on a Rust-derived problem the sequence instantiation's
          index-case questions of one clause (12 forms of about 14,000
          nodes) each ran the native theory to its 10 s budget -- undecided
          at 60 s replayed alone -- and were then proved by the axiomatised
          form in about 0.3 s; the event is the evidence that the native
          theory is the bottleneck on this problem's shapes.  What it costs:
          up to [axioms.first.ms] per later question the axiomatised form
          does not prove *)
}
[@@deriving yojson]

(** How an instantiated form is asked. *)
type fork_seqinst =
  | In_process  (** in this process *)
  | Killed_at_least of {
      floor_ms : int; [@default 10000]
          (** the copy is killed after the larger of this and the question's
              own budget (the default is the ladder's question budget) *)
    }
      (** in the sequence instantiation of the zero-unknown verdict, ask each
          instantiated form in a forked copy of the process, killed after
          the larger of this many milliseconds and the question's own budget
          ([PCSatCommon.ForkedQuery]); [None] asks in-process.  Only a
          [`Valid] is read from such a question (a countermodel of an
          instantiated form says nothing about the clause), so a copy that is
          killed, or that cannot be forked, only loses a proof.  Why: one such
          question, quantifier-free and of about 13,000 nodes, was asked under
          a 10 s budget and had not returned 83 s later, when the run was
          killed: Z3's own budget does not hold on it *)
  | Killed_after_budget of {
      margin_ms : int; [@default 0]
          (** the copy is killed at the question's own budget plus this *)
      read_as_in_process : bool; [@default false]
          (** the copy's answer is read as the same call's answer asked in
              process would be: an invalid answer comes back as invalid
              (with an empty countermodel: no reader of the sequence
              instantiation reads a countermodel, only whether the answer
              was a proof, a refutation or neither), a timeout or a killed
              copy as a timeout, any other undecided answer with its
              reason; and a question for which no copy can be made (the
              memory budget, a pipe, another domain running) is asked in
              process, as without the field, rather than dropped as a
              timeout.  So the questions asked and the reading of every
              answer that arrives within the kill are those of
              [In_process]; what changes is that a call that ignores its
              own budget is stopped by the kill and read as a timeout,
              where in process it runs, and holds its memory, until it
              returns.  [false]: an invalid answer comes back undecided
              (see [axioms.invalid_skips_fallback]) and a question with no
              copy is read as a timeout, as before.  Why: in the sequence
              instantiation one in-process check of a 4,000-node piece
              form over sequences ran 40 s and more under a 10 s budget,
              every stack sample inside the sequence theory's propagation
              adding [nth] and [at] axioms (a loop that does not poll the
              cancellation Z3's timer sets), its resident set growing from
              0.6 to 2.5 GB, and the run, with a forked copy of the solver
              doing the same, was killed by its 6 GB memory cap *)
      quantified_only : bool; [@default false]
          (** with [read_as_in_process], only a form with a quantifier is
              asked in a copy; a quantifier-free form is asked in process,
              as without the field.  [false]: every form is forked.  Why:
              a forked question loses what an in-process one leaves behind
              (pooled solver contexts, declarations, conversion memos) and
              pays a fork and a collection over the inherited heap, so on
              one input whose answer comes from a race between the main
              process and a forked probe, forking every form (all of them
              quantifier-free there) slowed the main process enough to
              change which copy answered, while the calls killed on the
              inputs the fork gains were quantified.  What it gives up: a
              quantifier-free call that ignores its budget (one has been
              seen, see [Killed_at_least]) is not bounded *)
    }
      (** with [external.fork_seqinst], [Some m] kills a
          forked form at its own budget plus [m] milliseconds
          ([ForkedQuery.ladder_kill_ms]) instead of at the larger of that
          field's value and the budget, so that a short budget -- the first
          pass of [budgets.two_pass_ms] -- bounds a forked
          question as Z3's timeout bounds one asked in process, and [m]
          covers what the copy does besides the solver call (the fork, the
          conversion of the form, the copy's exit).  [None]: the larger of
          the two, as before.  Only the time an undecided question costs
          changes: a proof read from the copy is the solver's proof.  Why:
          with the field's value at 15,000 ms and a first-pass budget of
          5,000 ms, three undecided forms of one Rust-derived loop step each
          held the run 15.6 s, 48 s of the 54 s spent before the form that
          proved the clause in 1.8 s *)
[@@deriving yojson]

(** The cvc5 retry of a piece no form proved. *)
type cvc5_retry = {
  ms : int; [@default 20000]
      (** in the sequence instantiation of the zero-unknown verdict (and
          wherever its forms are asked: the validator's read-back ladder and
          the Houdini pre-pass's sequence route), a piece none of its forms
          proved is asked once more, after its last form: its largest form
          built ([SeqInstantiation.best_built_form]) is given to cvc5 as a
          separate process with this many milliseconds of its own budget and
          killed by the wall clock one second later
          ([PCSatCommon.Cvc5Proof.valid_within]).  Only cvc5's [unsat] of the
          negation is read, as a proof of the form and so of the piece; its
          [sat] is never a refutation (its models are not checked here), and
          anything else leaves the piece undecided as before.  [None] asks
          nothing.  Why: a form of a Rust-derived produces-transitivity piece
          that Z3 left undecided at 30 s was proved by cvc5 in 3.5-15 s.
          On by default *)
  rlimit : int option; [@default None]
      (** with the cvc5 retry above, also give cvc5 a budget of this many of
          its own resource units ([--rlimit-per]); cvc5 answers [unknown]
          when they are spent, which leaves the piece undecided as any other
          non-proof does.  Unlike the budget in milliseconds, the count does
          not depend on the machine's load, so the same question gets the
          same chance on an idle and on a busy machine; the milliseconds stay
          as cvc5's time limit and the wall-clock kill.  [None] passes no
          resource limit *)
  on_undecided_form : bool; [@default false]
      (** with [external.cvc5_retry], a form of a piece
          that Z3 leaves undecided (a budget cut or a refusal, never a
          countermodel) is given to the same cvc5 retry at once, under the
          same budgets ([external.cvc5_retry],
          [external.cvc5_retry.rlimit]), before the piece's later
          forms and before the lemma route, rather than only the piece's
          largest form once after every form
          ([SeqInstantiation.cvc5_on_undecided_form]).  Only cvc5's [unsat]
          is read, as a proof of the form and so of the piece; a form so
          asked is not asked again at the end.  Why: a Rust-derived
          produces-transitivity piece's chain-join form, undecided by Z3 at
          10 s, was proved by cvc5 in 2.8 s, but only after 86 s spent on
          the forms and the lemma route after it *)
}
[@@deriving yojson]

(** How a question is spelt for cvc5: read by every cvc5 question of the
    process (the ladder's, validation's, elimination's and the solution
    checker's), not only by the ladder's retry. *)
type cvc5_spelling = {
  rename_reserved_symbols : bool; [@default true]
      (** every question asked of cvc5 ([PCSatCommon.Cvc5Proof]: the
          ladder's, validation's and elimination's retries) renames a
          symbol the input declares in a datatype that cvc5 also
          predefines ([tuple], the nullary constructor of a Rust-derived
          unit type) to a fresh name; without it cvc5 refuses every such
          text as ambiguous and no retry is asked.  A uniform renaming, so
          the same question; it lets those retries run to their budgets,
          which without it fail at parse at once *)
  unindex_recursive_functions : bool; [@default true]
      (** every question asked of cvc5 ([PCSatCommon.Cvc5Proof]'s retries
          and the solution checker's cvc5 route) first has Z3's indexed
          spelling of a recursive function's application, [((_ f 0) x)],
          rewritten to [(f x)] for an [f] the text defines recursively;
          no cvc5 reads the indexed form, so without it every question
          that mentions a recursive function fails at parse.  The same
          question; a text where the plain name could mean something else
          is not asked.  The retries also ask a text that defines a
          recursive function with [--enum-inst] (the checker passes it
          already), without which cvc5 did not unfold the definition under
          a universal within its budget *)
}
[@@deriving yojson]

(** The shape proof of each clause before the ladder. *)
type shape_proof = {
  ms : int; [@default 10000]
      (** before the zero-unknown verdict's ladder, each clause is asked by
          [PCSatCommon.ShapeProof.valid_within] with this budget per form
          (the one-point rule with the constructor-tester, case-merge and
          pairing rewrites, sequence reads and defined functions
          abstracted, then the premises restricted to those tied to the
          goal), and a clause proved is marked valid for every later stage.
          Only proofs are read and every form implies its clause.  Why: the
          layout obligations left after elimination in
          [univariant_sat.smt2] are instances of their premises that no
          stage of the ladder instantiates (the premises' variables are
          defined by cases or through constructors, with no ground term to
          match); the shape forms are proved in under a second each.
          [None] (the default): not asked *)
  literal_closures : int; [@default 0]
      (** with [external.shape_proof] set, a clause the shape
          forms leave unproved is asked at most this many further forms,
          one per top-level literal taken as the conclusion with the
          premises two steps away through rare variables
          ([Evaluator.literal_closures]), each with
          [external.shape_proof.literal_closure_ms] milliseconds, a
          proof of any one proving the clause.  Only proofs are read and
          every form implies its clause.  Why: the two loop-body clauses of
          [univariant_sat] are valid and conclude one comparison among about
          570 literals, with no conjunction marking a goal; their premise
          restriction from the right literal is proved in 0.3 s, the clause
          whole is undecided at 1,500 s.  [0] (the default): none asked *)
  literal_closure_ms : int; [@default 90000]
      (** the budget of each form asked under
          [external.shape_proof.literal_closures] (read only with
          that field positive).  Measured: the valid closures of the two
          loop bodies of [univariant_sat] are proved by Z3 in 7-25 s
          depending on the random seed (asked from a file), and in a solver
          run in 7 s and 35 s; the one of a smaller clause takes 15-26 s.
          90 s is about three times the slowest proof seen; an invalid
          closure is refuted in under 3 s *)
}
[@@deriving yojson]

(** How the ladder's two pooled whole-conjunction questions ([conj], and
    [conj-opened], the same conjunction with its single-constructor binders
    opened) are asked when [Z3interface.may_not_return] refuses their shape
    (a quantifier binding a sequence or a regular expression). *)
type conj_seq_binder =
  | Asked_in_process
      (** asked in this process like any other, under the question's own
          budget, which Z3 may not honour on this shape *)
  | Asked_fresh
      (** asked in this process in a Z3 context made for the question and
          told only the defined functions it reaches, under the question's
          own budget, instead of in the pooled context.  The same formula, so
          its [`Valid] and its countermodel mean what the pooled answers
          mean; only the context differs, and with it what Z3 decides (a
          pooled context that has been in a scope before falls back to a
          weaker tactic).  Not bounded: Z3 may still not honour the budget *)
  | Refused
      (** not asked: read as undecided ([`Unknown]), as the ladder reads
          every answer of these questions but [`Valid] and [`Invalid _].
          Sound because an undecided answer only sends the ladder on to its
          next stage (the conjuncts one at a time); what it can cost is a
          verdict the question would have decided *)
  | Killed_copy of {
      margin_ms : int; [@default 2000]
          (** the copy is killed this many milliseconds after the question's
              own budget (at least 0), which covers the fork and what the copy
              does besides the solver call *)
      fresh : bool; [@default false]
          (** the copy asks in a fresh context, as [Asked_fresh] does,
              instead of in its copy of the pooled context *)
    }
      (** asked in a forked copy of the process exactly as in this process
          (the same pooled solver state, or a fresh context with [fresh], the
          same budget), and given up when
          the copy has not answered within the question's budget plus
          [margin_ms]: a copy that decides becomes the run and continues
          from that answer ([PCSatCommon.ParallelRace.decide_in_copy]), so a
          [`Valid] or an [`Invalid] model is the in-process answer, and a
          copy killed, or answering anything else, is read as undecided.
          Where no copy can be made (other domains, the memory budget, a
          nested solve under a deadline) the question is asked in process,
          as with [Asked_in_process] *)
[@@deriving yojson]

(** Questions asked in a forked copy, by another solver or in a weakened
    form. *)
type external_ = {
  fork_seqinst : fork_seqinst; [@default In_process]
  conj_seq_binder : conj_seq_binder;
      [@default Killed_copy { margin_ms = 2000; fresh = false }]
      (** how the ladder's [conj] and [conj-opened] questions are asked when
          their shape is one [may_not_return] refuses (see
          [conj_seq_binder]); every other such question, and every question
          of another shape, is asked in process as before.  Why: on a
          Rust-derived loop step these two questions bind a sequence and,
          asked in process under a 10 s budget, returned after 20-36 s in 4
          of 24 asks, every stack sample past the budget inside Z3's
          sequence theory with its timer already fired (Z3 5.1.0), while
          the other 20 answered [unknown] (incomplete quantifiers) within
          2 s; none decided.  The default asks them in a killed copy:
          the same question and the same reading of its answer, bounded by
          the budget plus the margin; on the Thrust set it changed no verdict
          and cut the worst overrun of the two stages from 44 s to 24 s *)
  fork_refused_ms : int option; [@default None]
      (** a fresh-context question of the zero-unknown verdict that
          [may_not_return] refuses (a quantifier binding a sequence) is asked
          all the same, in a forked copy killed after the smaller of this many
          milliseconds and the question's budget, and only a [`Valid] is read
          from it; [None] refuses it as before.  The smaller, because every
          refused question then costs its kill: at the 10 s budget the
          rewritten stage of one input spent 90 s on nine refused pieces,
          none proved, where refusing them took 0.6 s each.  The sequence-axiom fallback
          still follows an undecided answer.  Sound for the reason the fork of
          [external.fork_seqinst] is: the copy's proof is
          the solver's proof, and anything else is undecided.  Why: on a
          Rust-derived input a refused piece of the rewritten stage is proved
          by Z3 in 2.5 s when asked, while the forms that replace it time out
          at 12 s *)
  weaken_refused_ms : int option; [@default None]
      (** a fresh-context validity question of the zero-unknown verdict that
          [may_not_return] refuses is first handed, with this many
          milliseconds (capped by the question's own budget), to its weakened
          form: the negation's top-level conjuncts [may_not_return] refuses
          (those binding a sequence under a quantifier) are dropped and the
          rest is asked in-process ([WeakenedQuery.rest_unsat]).  Only an
          [unsat] of the rest is read, as [`Valid]; anything else leaves the
          question as it is without this field (refused, or forked under
          [external.fork_refused_ms], then the sequence-axiom
          fallback).  [None] asks nothing.  Why: on five sequence inputs
          that otherwise go unanswered the ladder refused 182 questions and the weakened form
          proved 97 of them valid, none invalid *)
  cvc5_retry : cvc5_retry option;
      [@default Some { ms = 20000; rlimit = None; on_undecided_form = false }]
  cvc5_spelling : cvc5_spelling;
      [@default { rename_reserved_symbols = true; unindex_recursive_functions = true }]
  proof_shortcuts : bool; [@default true]
      (** two exact shortcuts in front of solver calls whose answer is
          already known.  (1) A form of the sequence instantiation (in every
          route that asks its forms) that is literally [true] is proved
          without being asked ([SeqInstantiation.true_forms_proved]), and so
          is a literally [true] formula handed to the cvc5 retry.  (2) The
          cvc5 retry answers a text it has already had [unsat] or [sat] to,
          in this process, from that answer ([PCSatCommon.Cvc5Proof.
          shortcuts]; a forked copy keeps what was recorded before its
          fork).  Both give the answers asking would give: [true] is valid
          in every model, and cvc5 is deterministic on one text, so only
          budget cuts, which say nothing about a form, are skipped.  Why:
          on six Rust-derived inputs ten of 27 cvc5 retries were of a form
          that was [true], left unproved by an asker whose budget was cut,
          and one 46,467-unit text was sent four times in one run.  On by
          default *)
  shape_proof : shape_proof option; [@default None]
}
[@@deriving yojson]

(** The point pin's settings. *)
type point_pin = {
  binder_free_relaxation : bool; [@default true]
      (** in the point pin, guess a point first from a quantifier-free
          relaxation of the piece's negation built by taking its binders
          apart from the outside in ([ScalarPin.binder_free_relaxation]):
          an existential's variables made free, a universal over an integer
          replaced by its instances at the integer literals of the formula
          and their negations, any other universal by one instance at a
          fresh variable.  Every model of the negation extends to a model
          of it, so its models cover the countermodels; a point is still
          reported only once the pinned negation is proved.  On by
          default *)
  binder_free_chain_bound : bool; [@default false]
      (** with [pins.scalars (Point_pin binder_free_relaxation)], count
          the relaxation's integer instances along a chain of nested
          universals rather than per block ([ScalarPin.binder_free_chain_bound]):
          a universal whose instances would bring the product past the
          bound is instantiated once at fresh variables.  Changes only
          which point is guessed; a point is reported only once proved *)
  drop_valid_premises : bool; [@default true]
      (** in the point pin of the zero-unknown verdict, accept a point
          also when the quantified conjuncts of its pinned negation that
          are not proved valid have a model: the conjuncts proved valid
          hold in every model, so dropping them leaves the negation's
          models unchanged, and a model of the rest is a countermodel.
          Only a model is read from the added question.  On by default *)
  default_compound_values : bool; [@default false]
      (** in the point pin, give a variable the guessed model leaves
          unassigned a closed default value also when its sort is a tuple or
          a datatype (the constructor of fewest arguments applied to
          defaults, recursively), where without it the point is dropped;
          the point is still proved by the validity of the pinned negation,
          so a default costs time and never an answer *)
}
[@@deriving yojson]

(** The point pin. *)
type scalar_pin =
  | No_point_pin  (** no point is searched *)
  | Point_pin of point_pin
      (** when preprocessing leaves no predicate variable and every question
          above, the sequence-length pin included, leaves the answer
          [unknown]/[timeout], also look for a point of a clause's free
          variables at which the clause is PROVED false in every model
          ([NoUnknownScalarPin]): a point guessed from a quantifier-free
          relaxation of the clause's negation, then the negation at that
          point proved valid by the sequence instantiation.  It can only turn
          [unknown]/[timeout] into [unsat].  Built for a clause whose
          sequences are all bound and whose countermodel is an integer
          point *)
[@@deriving yojson]

(** The sequence-length pin's settings. *)
type length_pin = {
  from_model : bool; [@default true]
      (** with [pins.seq_lengths], first, clause by
          clause, take each free sequence's length from a model of the
          quantifier-free relaxation of the clause's negation (its quantified
          parts replaced by [true]), at most 32, and ask the clause's
          negation strengthened by those length equations, before the fixed
          lengths 0, 1, 2.  Up to two more questions per clause; a
          refutation is still only a model of a strengthening of the
          negation, so it can only turn [unknown]/[timeout] into [unsat].
          The relaxation's model is read for lengths and for nothing else *)
  asked_shapes_only : bool; [@default false]
      (** the sequence-length pin (early and late) does not ask a pinned
          negation that [Z3interface.may_not_return] refuses -- one that
          still binds a sequence under a quantifier, which pinning the free
          sequences' lengths leaves in place -- and treats it as undecided,
          as the validity questions of the same ladder treat that shape.
          The relaxations it reads lengths from are quantifier-free and are
          asked as before.  Not exact: a refused question could have had a
          model the solver finds, so a refutation can be lost, never
          gained; an answer is never wrong by it.  Why: on a satisfiable
          Rust-derived closure input every pinned negation kept the
          closure's contract and the relation laws, universals over
          sequences, and all of them ran to the one-second cap without an
          answer (7-10 s of the early pins' 10 s), a pinned negation of a
          valid clause having no model to find.  Off by default: over the
          inputs where it refused a question it answered the same files no
          faster (37 s against 38 s), and it lost the refutation of a
          generic collect loop's failing side, whose pinned negation binds a
          sequence under a quantifier and which the solver answers [sat] at
          once.  [false]: every pinned negation is asked *)
  late_skips_proved : bool; [@default true]
      (** the LATE sequence-length pin leaves out the clauses a question
          before it has proved valid ([SeqPin.refute ?already_valid]), as
          the late point and relation pins always have.  Exact: the negation
          of a valid clause has no model, so leaving it out of the
          disjunction of negations leaves every question's models as they
          were and only drops questions that could not refute.  Why: with
          the early pins asked before the exact forms, the late pin is the
          only one asked after them, and it carried every clause the exact
          forms had proved -- a model of a proved clause's relaxation, then
          its pinned negation, each under the late per-question budget --
          before it reached the one open clause it refutes in a second;
          on a Rust-derived map-extension input it spent its last 17 s on
          the proved clauses and the run ended unanswered *)
  fixed_lengths_per_clause : bool; [@default true]
      (** the sequence-length pin (early and late) asks its fixed lengths
          0, 1 and 2 of each open clause on its own rather than of the
          conjunction of the open clauses ([SeqPin.refute
          ~fixed_per_clause]).  The same models in total, other questions:
          a clause whose pinned negation the solver does not decide within
          the per-question cap no longer hides the one beside it that it
          would refute.  Why: on a Rust-derived map-extension input, the
          early pin's two open clauses -- one with no countermodel at small
          lengths, one whose negation with its sequences' lengths pinned to
          1 has a model Z3 finds in 0.2 s -- were asked together at each
          length and timed out at the 1 s cap each time, and the length
          guess for the refutable clause had read all-zero lengths, at which
          its question does not return either.  On by default.  [false]:
          each fixed length is asked of the open clauses' conjunction *)
  fork_unreturning : bool; [@default true]
      (** the sequence-length pin (early and late) asks a pinned or
          fixed-length negation of a shape on which Z3 may ignore its own
          timeout ([Z3interface.may_ignore_timeout]: a quantifier binding a
          sequence, or any quantifier in a question that reads a sequence) in
          a forked copy killed after the question's budget, and asks it again
          in process only when the copy answered [sat], for the model.  The
          same answers as asking in process whenever that call honours its
          budget; it bounds the call that does not.  Why: Z3 5.1.0 ignored
          its one-second [timeout] on such a negation of a Rust-derived
          iterator loop and grew past the memory cap, while the same
          formula with its uninterpreted sorts named differently was
          answered within the budget, so whether the run survived depended
          on the input's numbering.  A WORKAROUND for Z3 5.1.0 ignoring its
          timeout in a context that has been in a scope; fixed upstream in
          Z3 5.3.3, but opam-repository's newest Z3 is 5.1.0: the field
          stays until opam provides a fixed Z3, and is removed, with
          [preprocessor.elimination.questions.fork.seq_unreturning], when
          the reproducer row for
          [benchmarks/SMT/simple/z3_seq_pin_scoped_timeout_unsat.smt2] in
          [script/rerun_external_reproducers.sh] reports GONE for the Z3
          that opam installs.  [false]: every such negation is asked in
          process *)
}
[@@deriving yojson]

(** The sequence-length pin. *)
type seq_length_pin =
  | No_length_pin  (** no sequence length is pinned *)
  | Length_pin of length_pin
      (** when preprocessing leaves no predicate variable and the validity
          questions end undecided or out of budget, also look for a
          refutation with every free sequence variable fixed to a literal of
          length 0, then 1, then 2 ([NoUnknownSeqPin]); it can only turn
          [unknown]/[timeout] into [unsat], never into [sat]: a model violating
          the clause with a sequence fixed to a literal violates the clause.
          On by default: with [split_seq_reads] in the preprocessor it
          refutes a nested-sequence Thrust query that no other setting
          decides.  When off, nothing is asked beyond the existing
          questions *)
[@@deriving yojson]

(** The pins: refutations read only from a model of a strengthened negation. *)
type pins = {
  scalars : scalar_pin;
      [@default Common.Util.config_default scalar_pin_of_yojson {|["Point_pin", {}]|}]
  relations : bool; [@default true]
      (** when preprocessing leaves no predicate variable and every question
          above, the point pin included, leaves the answer
          [unknown]/[timeout], also look for a countermodel of a clause whose
          free variables include Boolean-valued arrays (universally
          quantified relations) with those arrays fixed to the finite
          relations the clause's own facts and laws generate
          ([NoUnknownRelationPin]); the pinned negation is asked for
          satisfiability and only a model is read, so it can only turn
          [unknown]/[timeout] into [unsat].  It runs only after the point
          pin has found nothing, so no answer reached without it can be
          reached any later with it *)
  relation_attempts_per_piece : bool; [@default false]
      (** with [relations], the relation pin (early and late) asks at most its
          eight pinned negations per piece instead of eight over all clauses
          and pieces ([RelationPin.refute ~attempts_per_piece]; each question
          past the shared eight is the event [past-shared-cap]).  Why: the
          first pieces can spend all eight on sequence shapes that do not
          refute them, and a later piece that a pin refutes --
          the conclusion that a quantified relation is functional, whose
          negation names two outputs for one input as ground facts -- is then
          never asked.  Reads only models, as before; costs at most eight
          more satisfiability questions per further piece.  Off by
          default *)
  seq_lengths : seq_length_pin;
      [@default Common.Util.config_default seq_length_pin_of_yojson {|["Length_pin", {}]|}]
  pointwise_array_countermodels : bool; [@default false]
      (** in the zero-unknown verdict, when a clause's (or a piece's)
          validity question is left undecided, ask once more, under the
          same budget, the instance of it with each free array of sort
          [Int -> E] replaced by a pointwise definition read off the clause
          ([SeqInstantiation.pointwise_array_instance]), reading only a
          refutation.  Sound for refutation only: the clause holds for every
          value of its free variables, so a countermodel of an instance is
          one of the clause.  Off by default *)
}
[@@deriving yojson]

(** The early rewritten pass. *)
type early_rewritten = {
  max_pieces : int option; [@default Some 32]
      (** [Some n]: the early rewritten pass
          ([early_stage.exact_forms_first]) leaves a clause that splits
          into more than [n] pieces ([ClausePieces.of_clause], each piece
          counted by its own sub-pieces, the questions the pass would ask) to
          the early sequence instantiation after it, which
          splits it itself, groups pieces that share their premise and asks
          each group once; the pass asks it nothing.  Only which stage asks
          first changes: the pass reads proofs and refutations of exact
          rewrites, which the stages after it ask again when the sequence
          instantiation does not decide the clause.  Why: on a Rust-derived
          loop-body clause of 69 pieces in families of 4-8 that differ only
          in their goal, the pass asked every piece in a fresh context, 18-25
          s of a 120 s budget at a load of 4-8, 27 of the questions left
          undecided in families, while the sequence instantiation proves every
          piece and asks one question per family.  [Some 32] by default,
          measured together with [rewrites.decided_forms]: on a
          Rust-derived bit-set input whose loop clauses have more than 32
          pieces the pass's questions about them decided nothing, and
          leaving those clauses to the sequence instantiation cut the run
          from 80-110 s to about 33 s.  32 is the count that measurement
          chose, not a derived bound; [None] asks every clause *)
  within_refinement : bool; [@default false]
      (** the early rewritten pass ([early_stage.exact_forms_first])
          leaves to the early sequence instantiation, as
          [early_stage.rewritten.max_pieces] does past its bound,
          a clause whose refinement ([ClausePieces.refinement_size]: the
          sub-pieces of its pieces that split) exceeds the sub-pieces the
          pass may ask over one clause when it refines
          ([ClausePieces.refinement_budget]): see
          [ClausePieces.early_question ~within_refinement].  Not a count
          chosen by measurement but the pass's own refinement budget: a
          clause within it is asked exactly as without the switch, and one
          past it is one the pass cannot cut to its sub-pieces, so what it
          hands on is a mix of sub-pieces and whole coarse pieces.  Why: a
          Rust-derived loop-body clause of 128 such sub-pieces cost the pass
          20-30 s and the later stage its answer ([ClausePieces] has the
          account).  Off by default *)
  refute_skipped : bool; [@default false]
      (** with [early_stage.rewritten.max_pieces], a clause the
          early rewritten pass skips for its piece count is still asked once,
          whole, in its rewritten form, at the pass's budget
          ([ClausePieces.early_question]), and only a countermodel is read:
          an invalid clause is refuted there, a valid or undecided one costs
          that one question and is left to the sequence instantiation as
          without the switch.  Why: an invalid clause of more pieces than
          the bound, refuted by the pass in 1.6 s with four questions when
          the pass asked it, was otherwise asked again only by the late
          rewritten pass, which the time limit did not reach; off by
          default *)
  full_major_every : int option; [@default Some 8]
      (** [Some n]: during the early rewritten pass
          ([early_stage.exact_forms_first]'s piece-by-piece questions
          before the early sequence instantiation), the full major collection
          forced before a new Z3 context runs before every n-th one only, as
          [early_stage.pins (Early_pins full_major_every)] does for the pins.
          Same questions; only the collector's timing changes.  Why: on a
          Rust-derived loop-body clause the pass asks 69 pieces in the
          sequence-axiom form, each in a context of its own with model
          production off, and the collections before them were 5-11 s of the
          pass's 19-32 s on two cores, more under load; off by default *)
}
[@@deriving yojson]

(** The early relation pin's own budget. *)
type relation_budget = {
  per_question_ms : int; [@default 1000]
      (** each question's cap (CPU milliseconds under [cpu_clock]) *)
  whole_ms : int; [@default 10000]
      (** the pin's whole budget, started when the pin starts *)
  cpu_clock : bool; [@default false]
      (** with [early_stage.pins (Early_pins relation.budget)], charge that
          budget by the CPU time of the thread running the pin instead of
          by the wall clock ([NoUnknownLadder.cpu_budget]): the whole budget
          is CPU milliseconds, and each question's cap, which the solver
          takes in wall time, is the per-question CPU budget times the
          wall-over-CPU slowdown the pin has seen so far (at most
          [early_stage.pins (Early_pins relation.budget.max_scale)]), the whole stage
          being cut off at that many times the whole budget in wall time.
          On a loaded machine the pin's wall time is a multiple of its CPU
          time -- each question, and the full major collection forced
          before each fresh solver context, waits for a processor -- so a
          wall-clock budget ran out, or a shape guess hit its cap and ended
          the search at its length sum, before the shape that refutes was
          reached, on a Rust-derived input the pin refutes in about 10 s of
          CPU time.  The questions are the same and asked in the same
          order; only how far down the list the budget reaches changes, so
          this changes when a refutation is found, never an answer.  Off by
          default *)
  max_scale : float; [@default 6.]
      (** the bound on the slowdown factor of
          [early_stage.pins (Early_pins relation.budget.cpu_clock)] *)
}
[@@deriving yojson]

(** The early relation pin. *)
type early_relation_pin = {
  budget : relation_budget option; [@default None]
      (** [Some (per question, whole)] in milliseconds: with
          [early_stage.pins], the EARLY relation pin gets a budget
          of its own, which starts when that pin starts, instead of what the
          sequence-length and point pins before it have left of
          [early_stage.pins (Early_pins budget)].  Under the shared budget
          those two pins can spend all of it, and the relation pin then
          builds its shapes and asks none of them, or asks its shape guesses
          under a one-second cap that a loaded machine overruns, which ends
          the shape search for that length sum.  The late relation pin is
          unchanged.  The relation pin returns at once on a clause with no
          Boolean-valued array among its free variables, so the budget is
          spent only where a relation can be pinned.  A pin reads only a
          model of a strengthened negation, so this changes when a
          refutation is reached and which questions are asked before it,
          never an answer.  Built for a Rust-derived input refuted only by
          the late relation pin near the end of a 120 s run; off by
          default: to be measured *)
  precheck : bool; [@default false]
      (** with [early_stage.pins], the early relation pin asks,
          once per piece and before its per-sum shape guesses, whether the
          piece's relaxation with every sequence length in range has a model
          at all; when the answer is [unsat] no guess is asked, since each is
          that question with conjuncts added and would be [unsat] too.  Any
          other answer leaves the guesses as they were.  On a Rust-derived
          input one piece's relaxation is unsatisfiable and its nine
          guesses were a seventh of the pin's time.  Fewer questions with
          the same shapes found, so this never changes an answer; off by
          default *)
  full_major_every : int option; [@default None]
      (** [Some n]: during the early relation pin, the full major collection
          forced before a new Z3 context runs before every n-th one only
          ([Z3interface.with_new_context_full_major_every]), whatever
          [z3.collections] says elsewhere.  Each shape guess
          and pinned negation is asked in a fresh context, and on a
          Rust-derived input the collections before them were 35-65% of the
          pin's wall time, more under load, the questions themselves being
          small.  Same questions; only the collector's timing changes, and at
          most n dropped contexts wait for it at once *)
  length_shapes : bool; [@default true]
      (** with [early_stage.pins], the EARLY relation pin finds a
          piece's sequence-length shapes from the piece's length-only
          conjuncts ([RelationPin.length_vectors]): at each length sum, the
          vectors those conjuncts leave (at most six) are confirmed one at a
          time by asking whether the relaxation has a model with exactly
          those lengths, every sequence a literal over fresh elements, and
          a sum they leave empty asks nothing; a sum with more candidates is
          asked as before, by one guess per shape with only the sum fixed.
          A confirmation has no length left to choose and is a small
          question, where a per-sum guess at a sum with a model searched
          the lengths too: on a Rust-derived input refuted only by this pin
          (lengths tied by [len x9 = len x3 + len x5] and two equalities,
          so only sums divisible by three have a model), the guess at the
          refuting sum took 0.5-2.6 s of CPU near idle, overran the
          one-second cap under load and so ended that sum's search, and the
          six guesses at the sums with no model were asked anyway.  The
          shapes found are models of the relaxation, as before, and a pin
          reads only a model of a strengthened negation, so this changes
          which questions are asked and when a refutation is reached, never
          an answer.  The late relation pin is unchanged.  On by default *)
  first : bool; [@default false]
      (** with [early_stage.pins], ask the EARLY relation pin
          before the sequence-length and point pins, instead of after them,
          whenever a clause not yet shown valid has a Boolean-valued array
          among its free variables -- the one shape the relation pin acts
          on; otherwise the order is unchanged.  The three early pins share
          [early_stage.pins (Early_pins budget)]'s whole budget in order, and
          on a Rust-derived input refuted only by this pin the two before it
          spent 6-10 s of the 10 s under load (sequence-pinned questions
          timing out at the one-second cap, a point pin on a clause with no
          relation), so the relation pin asked two of its five pinned
          negations, and the late relation pin answered near the end of a
          120 s run or not at all.  The budget, its per-question cap and
          the questions each pin asks are as before; each pin reads only a
          model of a strengthened negation, so this changes which pin is
          asked first and when a refutation is reached, never an answer.
          The late pins are unchanged.  Off by default *)
  per_clause : bool; [@default true]
      (** with [early_stage.pins], the EARLY relation pin searches its open
          clauses one at a time, each under a budget of its own: the n-th of
          the k clauses not yet shown valid that have a Boolean-valued array
          among their free variables gets the rest of the pin's whole budget
          ([relation.budget]'s when set, else [early_stage.pins (Early_pins
          budget)]'s) divided by k - n + 1, from when it starts, with every
          question still under the pin's own per-question cap and deadline,
          and the cap of [RelationPin.max_attempts] pinned negations counted
          per clause rather than over all of them.  Without it the pin
          searches the clauses in order under one budget, so a clause whose
          shape guesses do not decide takes all of it, and a later clause
          the pin would refute is never started: on a Rust-derived
          unsatisfiable input, after the single-constructor split made the
          quick sweep's question about one valid clause slow, the pin spent
          its 7 s on that clause and never reached the clause it refutes in
          0.8 s otherwise.  Each search is the pin's on one clause, so a
          model it returns is a countermodel as before; this changes which
          questions are asked and when a refutation is reached, never an
          answer.  The late relation pin is unchanged.  On by default *)
  unsplit_after_exact_forms : bool; [@default false]
      (** when the preprocessor offers the input preprocessed again without
          the single-constructor split (its [clauses.split_single_cons
          (Split_single_cons outside_early_pins)]), search that problem's
          clauses as an early stage of its own run after every other early
          stage (the exact forms and the sequence instantiation included),
          instead of inside the early relation pin right after its search of
          the split clauses.  The search, its fresh budget and its isolation
          from the rest of the run are the same; only when it is asked
          changes.  Why: the second preprocessing and that search cost about
          25 s on a satisfiable Rust-derived input whose proof the sequence
          instantiation finds, and run first they pushed that proof past a
          120 s limit; run last they are never paid where an earlier stage
          decides.  A pin reads only a countermodel, so this changes when a
          refutation is reached and which questions are asked before it,
          never an answer.  Off by default *)
}
[@@deriving yojson]

(** The early pins' settings. *)
type early_pin_settings = {
  stop_at_deadline : bool; [@default true]
      (** with [early_stage.pins], stop the early pins once the
          whole budget of [early_stage.pins (Early_pins budget)] has elapsed,
          before building the next clause's, piece's or relaxation's
          question, and build a point or relation pin's relaxations one at
          a time rather than all at once.  Without it the deadline only
          stops questions from being asked, while the pins go on building
          the relaxations they would ask -- two sequence instantiations per
          piece, each measured at 17-25 s on a Rust-derived map-extension
          clause, where two such inputs spent 78 and 94 s in early pins of a
          10 s budget.  Only the early pins are cut short, and they read
          only a model of a pinned negation or a proof, so this changes
          when the ladder moves on, never an answer: the late pins still
          run in full.  On by default *)
  budget : budget_pair; [@default { per_question_ms = 1000; whole_ms = 10000 }]
      (** [(per question, whole)] in milliseconds for the early pins: each
          question gets at most the first, and none is asked once the
          second has elapsed since the early pins began *)
  full_major_every : int option; [@default Some 8]
      (** [Some n]: during the whole early-pin stage (sequence-length, point
          and relation pins; [early_stage.pins]) the full major
          collection forced before a new Z3 context runs before every n-th
          one only, as [early_stage.pins (Early_pins relation.full_major_every)]
          does for the relation pin alone (which, when set, still governs
          that pin).  Same questions; only the collector's timing changes.
          Why: the pins ask many small questions, each in a fresh context,
          under one shared wall-clock budget; on a Rust-derived input refuted
          only by the point pin, its 28 questions took 7.2 s, 3.6 s of it
          the collections, and at a higher load the stage ran out of its
          10 s before the refuting question, so the input went unanswered;
          on a satisfiable Rust-derived filter the relation pin's 9 s were 7 s
          of collections *)
  require_applicable : bool; [@default true]
      (** with [early_stage.pins], each EARLY pin asks only about
          the clauses and pieces its shape admits, decided before any of its
          questions: the sequence-length pin leaves out the clauses a
          question before it has proved valid and, with
          [pins.seq_lengths (Length_pin from_model)], those whose
          relaxation it found to have no model ([SeqPin.refute]); the point
          pin skips a piece with a free variable at a sort every value of
          which holds an element of an uninterpreted sort or a sort variable
          ([ScalarPin.opaque_sort]: no closed point exists for it) and, with
          one satisfiability question, a piece whose cheapest relaxation has
          no model; the relation pin skips a clause with no Boolean-valued
          array among its free variables before splitting it, and asks the
          same cheap question of each piece before building its relaxations.
          A skipped clause or piece is one the pin could not have refuted
          (the relaxation is implied by the negation; a point needs a closed
          value of every free variable, and the decoder renders an element of
          an uninterpreted sort as a variable), so this changes which
          questions are asked and when an answer is reached, never an
          answer.  The late pins are unchanged by this field (the late
          sequence-length pin's own skip of proved clauses is
          [pins.seq_lengths (Length_pin late_skips_proved)]).  Built for Rust-derived
          inputs whose clauses quantify over generic element types, where
          the point pin's guesses were dropped for want of a closed point
          and the length pin's questions carried the clauses already proved;
          on by default *)
  raced : bool; [@default false]
      (** with [early_stage.pins_after_exact_forms] (and
          [early_stage.pins]), start the early pins, before the
          exact forms, in a forked copy of the process
          ([PCSatCommon.ParallelRace]) that answers only with a refutation,
          while the process goes on with the exact forms and the rest of the
          ladder in the pins-after order unchanged (its own early pins
          included, after the exact forms).  A copy whose pins
          find a countermodel takes the run over and answers [unsat] from
          it, exactly as the sequential pins would have at that point; a
          copy that finds nothing leaves silently (in the copy each pin has
          the stage's whole budget to itself, a copy delaying nothing); the
          process kills the
          copy when its ladder has a verdict (or raises) and before that
          verdict leaves the ladder.  Sequential, in the pins-after order,
          when no copy can be forked or inside a solve bounded by a
          deadline.  Each side is sound alone (the pins read only a model of
          a strengthened negation; the exact forms read a proof or a
          refutation of an exact rewrite), so the race changes when an
          answer is reached, never which.  Why: the pins-after order spares
          a problem the exact forms prove the pins' questions, which on the
          satisfiable twin of a Thrust pair spend their whole budget, and
          makes the unsatisfiable twin, which the sequence-length pin
          refutes in one to six seconds, wait a minute or more for the exact
          forms to stay undecided; no shape test tells the two apart (the
          twins share their shape), and a second core does not have to.
          Off by default, a candidate for the next default-deciding batch:
          three runs each against the default on eight Rust-derived inputs
          gave a refutation at 14-17 s where the default took 77-92 s and at
          80-119 s where it took 191-241 s, and the six others answered
          alike *)
  point_pin_first : bool; [@default true]
      (** with [early_stage.pins_after_exact_forms] (and
          [early_stage.pins], [pins.scalars]),
          ask the point pin alone BEFORE the exact forms
          ([NoUnknownLadder.Point_pin]), under a budget of its own equal to
          [early_stage.pins (Early_pins budget)] and started when it starts,
          and the other early pins after the exact forms as before.  The
          later early pins leave the point pin out when the first one
          searched every open clause under full per-question caps
          ([NoUnknownLadder.point_pin_searched_all]); the late pins at the
          end of the ladder are unchanged.  The point pin reads only a
          point at which a clause's negation is proved valid (a
          countermodel), so this changes when a refutation is reached and
          which questions are asked before it, never an answer.
          Why the point pin and no other: its first questions are about
          quantifier-free relaxations and its proofs about the clause with
          every free variable fixed to a closed value, where the
          sequence-length pin's pinned negations keep their quantifiers and
          on an input with no countermodel run to their per-question cap
          (the cost the pins-after order saves).  Two Rust-derived
          refutations the pins-after order delayed are both found by the
          point pin: one in about a second after the quick sweep, but only
          after a minute of exact forms; the other after the
          sequence-length pin, which with every clause still open spent the
          pins' shared budget and left the point pin about two seconds.
          On by default: five runs each against the default on those two
          inputs gave the refutation within 12-17 s (default none in 30 s)
          and 64-101 s (default none in 120 s), and an input decided by the
          CEGIS loop answered alike *)
  cheap_first : bool; [@default false]
      (** with [early_stage.pins_after_exact_forms] (and
          [early_stage.pins]), ask BEFORE the exact forms the one
          pin question whose cost the problem's shape bounds
          ([SeqPin.cheap_first]; [NoUnknownLadder.Cheap_pins]): the negation
          of the clauses not yet shown valid with every free sequence pinned
          to the empty sequence, asked only when some such clause has a free
          sequence, does not simplify to [false] there, and the simplified
          question has at most [SeqPin.cheap_max_size] nodes.  It is asked
          once, under the early pins' per-question cap; a model is a
          refutation (the question is a strengthening of the negation),
          anything else is dropped and the ladder goes on exactly as without
          the switch, the full early pins still asked after the exact forms.
          So it changes when a refutation is reached and costs at most one
          question when the shape is wrong, never an answer.  Built for an
          input the pins-after order slowed from a refutation in the first
          seconds (by this very question) to one after a minute of the
          sequence instantiation.  Off by default: to be measured *)
  relation : early_relation_pin;
      [@default
        { budget = None; precheck = false; full_major_every = None; length_shapes = true; first = false;
          per_clause = true; unsplit_after_exact_forms = false }]
}
[@@deriving yojson]

(** The early pins. *)
type early_pins =
  | No_early_pins  (** the pins are asked only at the end of the ladder *)
  | Early_pins of early_pin_settings
      (** when preprocessing leaves no predicate variable, also ask the
          sequence-length, point and relation pins (the three fields above)
          once right after the quick sweep, before the rewritten forms and
          the sequence instantiation, on the clauses not yet shown valid,
          under [early_stage.pins (Early_pins budget)]; a refutation found
          there is returned as the late pins' is, and otherwise the ladder
          continues unchanged, the late pins included.  It changes only the
          time at which a pin's answer is reached, never the answer.  On
          by default; built for a Thrust input whose point pin refutes it
          only at the end of the ladder, near the run's budget *)
[@@deriving yojson]

(** The stages asked before the long questions. *)
type early_stage = {
  exact_forms_first : bool; [@default true]
      (** after the quick sweep, ask each clause not yet shown valid in its
          rewritten form ([rewrites.onepoint.split]) piece by piece,
          and then the sequence instantiation
          ([seq_instantiation.premises]), BEFORE the long
          questions on the unrewritten conjunction and clauses, instead of
          after them.  Only the order changes: each of these questions can
          refute only through an exact rewrite and prove only validity, so an
          answer is the same whichever order reaches it; what changes is the
          time spent first on questions that run out their budget.  On by default
          together with the next field: over 349 Thrust, quantified-invariant
          and CHC inputs at 120 s the pair answered 296.8 expected against
          294.6 without, with no verdict disagreement. *)
  pins_after_exact_forms : bool; [@default false]
      (** with [early_stage.pins] and
          [early_stage.exact_forms_first], ask the early pins AFTER the
          early rewritten pieces and the early sequence instantiation
          instead of before them ([NoUnknownLadder.early_order]); the early
          pins then also skip every clause those stages showed valid.  Each
          of the two stages is sound alone (the pins read only a
          refutation, the exact forms a refutation of an exact rewrite or a
          proof), so the order changes which questions are asked before an
          answer and when it is reached, never which answer is right: a
          problem the exact forms prove no longer pays the pins' questions,
          and a refutation by a pin is reached later by the time the exact
          forms spend.  Its budget, [early_stage.pins (Early_pins budget)],
          starts when the pins start.  Read from traces of 13 Rust-derived
          inputs with no predicate variable left: the early pins took
          8.7-13 s on every input and found nothing on any of them, and the
          three inputs that answer near the 120 s budget are proved by the
          exact forms after them.  Off by default: with the pins first, a
          satisfiable Rust-derived map input answered in three runs of three
          against none with this order, and no input answered with this
          order was lost *)
      (* a switch of its own, not a field of [Early_pins]: the stage order
         it chooses is read whatever the early pins are *)
  rewritten : early_rewritten;
      [@default { max_pieces = Some 32; within_refinement = false; refute_skipped = false; full_major_every = Some 8 }]
  pins : early_pins;
      [@default Common.Util.config_default early_pins_of_yojson {|["Early_pins", {}]|}]
}
[@@deriving yojson]

(** The lemma route's resource counts. *)
type lemma_rlimits = {
  native : int; [@default 300000]  (** per question as asked *)
  fallback : int; [@default 500000]
      (** per question of the sequence-axiom fallback asked after an
          undecided one *)
}
[@@deriving yojson]

(** Which lemma route. *)
type lemma_route =
  | Plain_route  (** the plain route *)
  | Extended_route of {
      goal_first_probe : int option; [@default None]
          (** [Some n], with [lemmas (Lemmas route Extended_route)]: a
              piece some of whose goal pieces have a witness goal that only the
              last-witness-disjunct rule finds is first given a short extended
              goal-first probe of at most [n] questions per goal piece, before
              the plain route ([PCSatCommon.LemmaApplication.goal_first_probe]).
              Only the order and the caps change; only proofs are read.  Why:
              on a loop step the plain route spent all 64 of its questions
              (35-60 s) where the extended route then proved the piece in 11. *)
    }
      (** with [lemmas], the extended route
          ([PCSatCommon.LemmaApplication.extended]): a conclusion that is a
          conjunction split into one piece per conjunct, each piece's
          negated goal tried first; the existential facts opened; a
          sequence binder offered the one-step extensions [g ++ [e]] of the
          facts' sequences, and the instances that build their terms tried
          first; a disjunct the facts leave undecided asked again by cases
          (an existential's disjunctive body distributed, an index split
          against a concatenation's prefix), each with selections of the
          facts, smallest first.  Only proofs are read, as without it.
          Why: a loop step whose witness extends the invariant's history by
          the one item [next] produced was undecided whole by z3 and cvc5,
          with the witness given too, while each case, asked beside the two
          or three facts about its terms, was decided in under a second. *)
[@@deriving yojson]

(** The lemma application of a piece nothing else proved. *)
type lemmas =
  | No_lemmas  (** nothing is asked *)
  | Lemmas of {
      ms : int; [@default 2000]
          (** the budget of each disjunct's question *)
      rlimits : lemma_rlimits option; [@default Some { native = 300000; fallback = 500000 }]
          (** with [lemmas], [Some (native,
              fallback)] bounds each of the route's questions by a Z3 resource
              count ([rlimit], the solver's own steps, the same whatever the
              host's load): [native] per question as asked, [fallback] per
              question of the sequence-axiom fallback asked after an undecided
              one; the route's milliseconds then stay as the kill of both (the
              fallback's wall-clock budget is raised to them from the
              process-wide one), so that what decides a question is its count
              and the wall clock only stops a check the count does not stop.
              An exhausted count is an undecided question, which the route reads
              as "not refuted", as it reads a timeout.  [None]: wall clock only.
              Why: on a Rust-derived filter's transitivity piece the route's
              questions split cleanly -- every refutation the route used took at
              most 37,347 units (under 0.1 s), every native question it did not
              decide ran to the 2000 ms budget (1.0-1.4 million units), and the
              fallback proved at 27,563 and 204,943 units where the questions it
              did not prove ran to its 500 ms budget (437,589-583,927 units) --
              so the undecided ones were 27 of the route's 36 s at load 8, and
              under load the fallback's 205k-unit proof came near its 500 ms *)
      before_cvc5 : bool; [@default true]
          (** ask a piece no form proved of the lemma application
              ([lemmas]) BEFORE the cvc5 retry
              ([external.cvc5_retry]) rather than after it;
              each reads only a proof, so the order changes the time a piece
              costs, never what is proved of it.  Why: on a Rust-derived
              filter's pieces the route proves, the cvc5 retry ran first and
              answered [unknown] after 6.6-7.4 s each (16.5 s of a run at load
              8), while the route's own refutations take well under a second *)
      after_form_timeout : bool; [@default true]
          (** ask a piece of the lemma application
              ([lemmas]) as soon as one of the
              piece's forms has run out of its budget, before its later forms
              (with [budgets.two_pass_ms], between the two passes
              when a form was deferred), instead of after every form.  A piece
              some form proves before any form runs out is asked exactly as
              without it; each step reads only a proof, so only the time a piece
              costs changes.  Why: on a Rust-derived filter's iterator law, which
              the route proves in a few seconds, three of the piece's thirteen
              forms ran to the 10 s budget, 34 s of the 37 s its forms cost *)
      route : lemma_route; [@default Plain_route]
      read_maps : bool; [@default false]
          (** with [lemmas], an index-map binder of a hypothesis is also
              offered, after the maps paired with the sequence it is read
              over, every free map of its sort the facts read, one candidate
              each ([PCSatCommon.LemmaApplication.offer_read_maps]).  It adds
              instances only, and an instance of a universal hypothesis
              follows from it, so only which questions are asked changes,
              never what a proof is.  Why: a lemma that reads its map over a
              container's keys while the facts read the witness map of a
              [produces_at] premise over the consumed sequence was never
              offered that witness, while a copy of the input with that one
              instance added answered.  Off: with it on, the route does try
              the lemma at that witness on those inputs, but each such
              instance leaves two or three disjuncts the facts do not refute,
              so it neither proves the piece nor adds a fact, and the inputs
              stay unanswered. *)
      map_lengths : bool; [@default false]
          (** with [lemmas], an integer binder of a hypothesis that also
              binds an index map is offered, after its matched terms, the
              lengths [seq.len v] the facts reading the instance's map state
              its domain by, at most four per map and [max_instances] more
              instances per hypothesis and round
              ([PCSatCommon.LemmaApplication.offer_map_lengths]).  It adds
              instances only, so only which questions are asked changes.
              Why: a lemma over a witness map and a count ([selects(keys, ..,
              f, n, ..)]) is needed at the length of the sequence the map is
              defined over, a term no ground atom pairs with the lemma's other
              arguments; on a Rust-derived filter's postcondition that one
              instance left the lemma's conclusion as a fact and the negated
              goal was then refuted, every question in under a second. *)
      law_retry : bool; [@default false]
          (** with [lemmas], a disjunct the facts leave undecided is asked
              again, at most twice, beside one instance of a hypothesis that
              binds exactly one sequence at a sequence the disjunct reads, its
              other binders left universal
              ([PCSatCommon.LemmaApplication.retry_with_laws]).  Such an
              instance follows from the hypothesis, so only proofs are read
              as without it.  Why: a count lemma's premise needed the law of a
              filter's predicate at the positions of the keys the disjunct
              reads under its own existential, which no ground term names; z3
              refuted the disjunct beside that instance in about a second. *)
      law_retry_rlimits : lemma_rlimits option;
          [@default Some { native = 2000000; fallback = 2000000 }]
          (** with [law_retry], the resource bounds of a question asked beside
              a law instance in place of [rlimits] (the milliseconds [ms]
              stay its kill); [None]: [rlimits].  Why: each such refutation
              measured took 1.0-1.7 million units, above the 300,000 a
              plain disjunct is given, while every other question the
              route proved with took under 0.1 million; at most two of
              these are asked per undecided disjunct *)
      keep_hypotheses : bool; [@default false]
          (** with [lemmas] and the plain route, a hypothesis one of whose
              instances left a fact is kept for the next round (its tried
              instances not asked again) instead of being dropped
              ([PCSatCommon.LemmaApplication.keep_after_fact]); the extended
              route keeps it already.  Only which questions are asked
              changes.  Why: on a Rust-derived collect's postcondition the
              lemma's first instance left a weak fact and its turn ended,
              so the instance whose premise the negated goal's fact discharges
              was never asked. *)
    }
      (** in the sequence instantiation of the zero-unknown verdict, a piece
          nothing else proved is given to [PCSatCommon.LemmaApplication]:
          its quantified hypotheses (a lemma the clause calls, the negated
          goal) are instantiated at matched terms, each disjunct of an
          instance is asked about alone, under this many milliseconds, and
          dropped when the facts refute it; a hypothesis left with one
          disjunct adds it as a fact, and one left with none proves the
          piece.  [None] asks nothing; the default is 2000.  Only proofs of
          validity are read.
          Why: a lemma applied at the premises' witnesses and a goal at the
          lemma's joined index map were each decided in about 0.1 s per
          disjunct, while every form asked whole, and the same instances
          asked as one question, were left undecided at 30 s by z3 and
          cvc5. *)
[@@deriving yojson]

(** The guarded-facts rule. *)
type guarded_facts =
  | No_guarded_facts  (** nothing is tried *)
  | Guarded_facts of {
      ms : int; [@default 3000]
          (** the forked copy is killed after this many milliseconds *)
      theory_facts_only : bool; [@default true]
          (** with [guarded_facts], a form whose derived
              facts are all reads of a relation (a Boolean [select] chain, a
              variable or a function application said to hold or fail) is not
              asked, and the piece is asked as without the rule.  Such a form
              is the question plus ground atoms of the relations its own
              hypotheses are guarded by.  Why: over five Rust-derived inputs no
              such form was decided where the question alone was not (each form
              and question replayed in z3 at 10 s): the decided ones were decided
              as fast without the facts, the others were undecided questions, and
              each undecided form held the forked copy for its whole budget --
              15-20 s of a loop-closure input that answers at 86-103 s of 120;
              the forms that proved what the question did not all derived a fact
              with arithmetic content.  [false] (the default): every form is
              asked. *)
    }
      (** in the quick sweep and the rewritten stages of the zero-unknown
          verdict, a piece (or a
          clause asked whole) whose negation holds a hypothesis
          [forall xs. not B(xs) \/ ...] with a guard [B] that a fact [B(ts)]
          matches is first given to [PCSatCommon.GuardedFacts]: the
          single-constructor variables it reads through selectors split into
          their fields, the hypothesis applied forward at [ts] (a disjunct the
          facts over its own variables refute dropped, the one left kept as a
          fact), and the strengthened question asked -- all in a forked copy
          killed after this many milliseconds, with the bit-vector rewrite of
          bounded integers off in the copy.  Only a proof is read; anything
          else falls through to the piece's own question.  Each question is
          tried once per process.  [None] (the default): nothing is tried.
          Why: on a Rust-derived bit-set postcondition (the word index and
          mask a call returned, read through a tuple, and the relation fixing
          the element's index) every form of the ladder was left undecided at
          10 s, while the tuple split with the contract's conclusion
          derived as a fact at the relation's point was decided in 0.1-0.3 s;
          with the contract's instance asserted as the implication it is, or
          with the tuples unsplit, Z3 left it undecided at 20-30 s *)
[@@deriving yojson]

(** The ladder's configuration, by stage. *)
type t = {
  budgets : budgets;
      [@default Common.Util.config_default budgets_of_yojson "{}"]
  pieces : pieces; [@default Common.Util.config_default pieces_of_yojson "{}"]
  rewrites : rewrites; [@default Common.Util.config_default rewrites_of_yojson "{}"]
  seq_instantiation : seq_instantiation;
      [@default Common.Util.config_default seq_instantiation_of_yojson "{}"]
  candidates : candidates;
      [@default Common.Util.config_default candidates_of_yojson "{}"]
  matched_instances : matched_instances;
      [@default Common.Util.config_default matched_instances_of_yojson "{}"]
  chains : chains; [@default Common.Util.config_default chains_of_yojson "{}"]
  case_split_index : case_split_index;
      [@default Common.Util.config_default case_split_index_of_yojson {|["Index_cases", {}]|}]
  axioms : axioms; [@default Common.Util.config_default axioms_of_yojson "{}"]
  words : word_instances; [@default Two_rounds_first]
      (** in the early rewritten pass ([early_stage.exact_forms_first]),
          whether each piece (and each whole clause asked) is asked first
          through the words of its matched-instance forms, and in which
          order (see [word_instances]).  Each form implies its piece and the
          words question is weaker than its form, so only a proof is read and
          only the order of the questions changes.  What it buys: a bit
          set's word and bit obligations, whose proof needs a premise at the
          goal's index and a premise at that index's word ([i div 64]) and
          then only bit-vector reasoning, are proved in a fraction of a
          second, where the piece as it is, and its matched forms asked as
          they are, run out their budget (Z3 does not combine [i div 64],
          [i mod 64] and bits read through [int_to_bv]); what it costs: the
          words questions of a piece they do not prove, each answered (a
          model of the weaker question, which says nothing) in about a
          second.  Best with [rewrites.contextual_ite], which removes
          the negative-index branches of a truncated division before the
          forms are matched *)
  external_ : external_; [@key "external"]
      [@default Common.Util.config_default external__of_yojson "{}"]
  pins : pins; [@default Common.Util.config_default pins_of_yojson "{}"]
  early_stage : early_stage;
      [@default Common.Util.config_default early_stage_of_yojson "{}"]
  lemmas : lemmas; [@default Common.Util.config_default lemmas_of_yojson {|["Lemmas", {}]|}]
  guarded_facts : guarded_facts;
      [@default Common.Util.config_default guarded_facts_of_yojson {|["Guarded_facts", {}]|}]
  congruence_match : bool; [@default false]
      (** before the shape proof and every other question of the ladder,
          each clause is tried by [PCSatCommon.CongruenceMatch.valid]: its
          conclusion matched, up to the equalities among its premises and
          the names of bound variables, against its premises, with no
          solver; a clause so matched is marked valid for every later stage.
          Only proofs are read, so it is skipped where only a refutation is
          read.  Why: an obligation whose goal restates a premise over
          variables the premises equate with the premise's own is asked of
          the solver with the definitions it applies unfolded, and the
          quantified question is not decided within its budget.  [false]
          (the default): not tried *)
}
[@@deriving yojson]

(** The value each of the ladder's flat switches takes under a configuration.
    The ladder's code, and the process-wide refs [LadderSwitches] sets from
    the configuration ([SeqInstantiation], [Ast.Evaluator], the pins), read
    booleans and options; a variant above folds several of them into one
    choice, and these functions unfold it.  Contract: under every choice each
    function returns the value the code reads, and where the choice makes a
    switch inert (a parameter of a mechanism that is off, or of another
    constructor) it returns that switch's default, which no reader looks at:
    the readers of such a switch are reached only under the constructor that
    carries it. *)
module Switch = struct
  let quick_sweep z =
    Option.map z.budgets.quick_sweep ~f:(fun q -> (q.per_question_ms, q.whole_ms))

  let quick_sweep_finish_clause z =
    match z.budgets.quick_sweep with Some q -> q.finish_clause | None -> true

  let quick_sweep_plain_retry z =
    match z.budgets.quick_sweep with Some q -> q.plain_retry | None -> false

  let pieces_first z =
    Option.map z.pieces.pieces_first ~f:(fun p -> (p.z3_ms, p.cvc5_ms))

  let group_piece_forms z = Option.is_some z.pieces.grouping

  let group_open_pieces z =
    match z.pieces.grouping with Some { mode = Open _; _ } -> true | _ -> false

  (* under open grouping the lead stage before grouping is asked only when
     the next three are as [Before_grouping] sets them *)
  let lead_forms_before_grouping z =
    match z.pieces.grouping with
    | Some { mode = Consecutive { lead_first }; _ } -> lead_first
    | _ -> true

  let lead_forms_under_open_grouping z =
    match z.pieces.grouping with
    | Some { mode = Open { lead = Before_grouping }; _ } -> true
    | _ -> false

  let lead_forms_for_unasked_groups z =
    match z.pieces.grouping with
    | Some { mode = Open { lead = After { unasked_groups; _ } }; _ } -> unasked_groups
    | Some { mode = Open { lead = Before_grouping }; _ } -> false
    | _ -> true

  let lead_forms_under_open_grouping_min_nodes z =
    match z.pieces.grouping with
    | Some { mode = Open { lead = After { over_nodes; _ } }; _ } -> over_nodes
    | _ -> None

  let group_question_max_nodes z =
    Option.value_map z.pieces.grouping ~default:(Some 380000) ~f:(fun g -> g.max_nodes)

  let share_piece_simplify z =
    Option.value_map z.pieces.grouping ~default:true ~f:(fun g -> g.share_simplify)

  let replay_piece_fresh_names z =
    Option.value_map z.pieces.grouping ~default:true ~f:(fun g -> g.replay_names)

  let surjective_pairing z =
    match z.rewrites.surjective_pairing with
    | No_surjective_pairing -> false
    | Flat_pairing | Nested_pairing -> true

  let surjective_pairing_nested z =
    match z.rewrites.surjective_pairing with
    | Flat_pairing -> false
    | No_surjective_pairing | Nested_pairing -> true

  let contextual_ite z =
    match z.rewrites.contextual_ite with
    | No_contextual_ite -> false
    | In_place | As_extra_form -> true

  let contextual_ite_as_extra_form z =
    match z.rewrites.contextual_ite with
    | In_place -> false
    | No_contextual_ite | As_extra_form -> true

  let split_seq_prefix_over_concat z =
    match z.rewrites.split_seq_prefix with
    | No_prefix_split -> false
    | Everywhere | Focus_only -> true

  let split_seq_prefix_focus_only z =
    match z.rewrites.split_seq_prefix with
    | Everywhere -> false
    | No_prefix_split | Focus_only -> true

  let decided_forms z = Option.is_some z.rewrites.decided_forms

  let decided_forms_rlimit z =
    Option.value_map z.rewrites.decided_forms ~default:200000 ~f:(fun d -> d.rlimit)

  let offset_int_candidates z =
    match z.candidates.offset_int with
    | No_offset_int -> false
    | All_lengths | Chain_only -> true

  let offset_int_candidates_chain_only z =
    match z.candidates.offset_int with
    | All_lengths -> false
    | No_offset_int | Chain_only -> true

  let case_split_index_forms z =
    match z.case_split_index with No_index_cases -> false | Index_cases _ -> true

  let case_split_index_budget z =
    match z.case_split_index with
    | Index_cases { budget_ms; _ } -> budget_ms
    | No_index_cases -> None

  let case_split_index_max_size_ratio z =
    match z.case_split_index with
    | Index_cases { max_size_ratio; _ } -> max_size_ratio
    | No_index_cases -> Some 0.5

  let seq_axioms_first z = Option.map z.axioms.first ~f:(fun f -> f.ms)

  let seq_axioms_first_fresh z =
    Option.value_map z.axioms.first ~default:false ~f:(fun f -> f.fresh)

  let seq_axioms_first_after_fallback_proof z =
    z.axioms.first_after_fallback_proof

  let ladder_seq_axiom_rlimit z =
    Option.map z.axioms.ladder_fallback ~f:(fun f -> (f.rlimit, f.kill_ms))

  let ladder_seq_axiom_rlimit_refused_only z =
    match z.axioms.ladder_fallback with
    | Some { scope = All_fallbacks; _ } -> false
    | Some { scope = Refused_only; _ } | None -> true

  let ladder_seq_axiom_units_per_node z =
    Option.value_map z.axioms.ladder_fallback ~default:(Some 96) ~f:(fun f ->
        f.units_per_node)

  (* under [Killed_after_budget] the floor is not read (the kill is the
     budget plus the margin), so any [Some] serves *)
  let fork_seqinst_questions z =
    match z.external_.fork_seqinst with
    | In_process -> None
    | Killed_at_least { floor_ms } -> Some floor_ms
    | Killed_after_budget _ -> Some 0

  let fork_seqinst_kill_margin z =
    match z.external_.fork_seqinst with
    | Killed_after_budget { margin_ms; _ } -> Some margin_ms
    | In_process | Killed_at_least _ -> None

  let fork_seqinst_read_as_in_process z =
    match z.external_.fork_seqinst with
    | Killed_after_budget { read_as_in_process; _ } -> read_as_in_process
    | In_process | Killed_at_least _ -> false

  let fork_seqinst_quantified_only z =
    match z.external_.fork_seqinst with
    | Killed_after_budget { quantified_only; _ } -> quantified_only
    | In_process | Killed_at_least _ -> false

  let ladder_cvc5_retry_ms z = Option.map z.external_.cvc5_retry ~f:(fun r -> r.ms)
  let ladder_cvc5_rlimit z = Option.bind z.external_.cvc5_retry ~f:(fun r -> r.rlimit)

  let ladder_cvc5_on_undecided_form z =
    Option.value_map z.external_.cvc5_retry ~default:false ~f:(fun r ->
        r.on_undecided_form)

  let shape_proof_ms z = Option.map z.external_.shape_proof ~f:(fun s -> s.ms)

  let shape_proof_literal_closures z =
    Option.value_map z.external_.shape_proof ~default:0 ~f:(fun s ->
        s.literal_closures)

  let shape_proof_literal_closure_ms z =
    Option.value_map z.external_.shape_proof ~default:90000 ~f:(fun s ->
        s.literal_closure_ms)

  let pin_scalars z =
    match z.pins.scalars with Point_pin _ -> true | No_point_pin -> false

  (* the point pin's settings, its defaults when the pin is off *)
  let point_pin z =
    match z.pins.scalars with
    | Point_pin p -> p
    | No_point_pin -> Common.Util.config_default point_pin_of_yojson "{}"

  let pin_scalars_binder_free_relaxation z = (point_pin z).binder_free_relaxation
  let pin_scalars_binder_free_chain_bound z = (point_pin z).binder_free_chain_bound
  let drop_valid_premises_before_pin z = (point_pin z).drop_valid_premises
  let pin_scalars_default_compound_values z = (point_pin z).default_compound_values

  let pin_seq_lengths z =
    match z.pins.seq_lengths with Length_pin _ -> true | No_length_pin -> false

  (* the sequence-length pin's settings, its defaults when the pin is off *)
  let length_pin z =
    match z.pins.seq_lengths with
    | Length_pin p -> p
    | No_length_pin -> Common.Util.config_default length_pin_of_yojson "{}"

  let pin_seq_lengths_from_model z = (length_pin z).from_model
  let pin_seq_lengths_asked_shapes_only z = (length_pin z).asked_shapes_only
  let late_seq_pin_skips_proved_clauses z = (length_pin z).late_skips_proved
  let seq_pin_fixed_lengths_per_clause z = (length_pin z).fixed_lengths_per_clause
  let pin_seq_lengths_fork_unreturning z = (length_pin z).fork_unreturning

  let early_pins z =
    match z.early_stage.pins with Early_pins _ -> true | No_early_pins -> false

  (* the early pins' settings, their defaults when the early pins are off *)
  let early_pin_settings z =
    match z.early_stage.pins with
    | Early_pins p -> p
    | No_early_pins -> Common.Util.config_default early_pin_settings_of_yojson "{}"

  let early_pins_stop_at_deadline z = (early_pin_settings z).stop_at_deadline

  let early_pins_budget z =
    let b = (early_pin_settings z).budget in
    (b.per_question_ms, b.whole_ms)

  let early_pins_full_major_every z = (early_pin_settings z).full_major_every
  let early_pins_require_applicable z = (early_pin_settings z).require_applicable
  let early_pins_raced z = (early_pin_settings z).raced
  let early_point_pin_first z = (early_pin_settings z).point_pin_first
  let early_cheap_pins_first z = (early_pin_settings z).cheap_first

  let early_relation_pin_budget z =
    Option.map (early_pin_settings z).relation.budget ~f:(fun b ->
        (b.per_question_ms, b.whole_ms))

  let early_relation_pin_cpu_clock z =
    Option.value_map (early_pin_settings z).relation.budget ~default:false
      ~f:(fun b -> b.cpu_clock)

  let early_relation_pin_max_scale z =
    Option.value_map (early_pin_settings z).relation.budget ~default:6.
      ~f:(fun b -> b.max_scale)

  let early_relation_pin_precheck z = (early_pin_settings z).relation.precheck

  let early_relation_pin_full_major_every z =
    (early_pin_settings z).relation.full_major_every

  let early_relation_pin_length_shapes z =
    (early_pin_settings z).relation.length_shapes

  let early_relation_pin_first z = (early_pin_settings z).relation.first
  let early_relation_pin_per_clause z = (early_pin_settings z).relation.per_clause

  let early_unsplit_after_exact_forms z =
    (early_pin_settings z).relation.unsplit_after_exact_forms

  let lemma_application_ms z =
    match z.lemmas with Lemmas { ms; _ } -> Some ms | No_lemmas -> None

  let lemma_application_rlimits z =
    match z.lemmas with
    | Lemmas { rlimits; _ } ->
        Option.map rlimits ~f:(fun r -> (r.native, r.fallback))
    | No_lemmas -> Some (300000, 500000)

  let lemma_application_before_cvc5 z =
    match z.lemmas with Lemmas { before_cvc5; _ } -> before_cvc5 | No_lemmas -> true

  let lemma_application_after_form_timeout z =
    match z.lemmas with
    | Lemmas { after_form_timeout; _ } -> after_form_timeout
    | No_lemmas -> true

  let lemma_application_extended z =
    match z.lemmas with
    | Lemmas { route = Extended_route _; _ } -> true
    | Lemmas { route = Plain_route; _ } | No_lemmas -> false

  let lemma_read_maps z =
    match z.lemmas with Lemmas { read_maps; _ } -> read_maps | No_lemmas -> false

  let lemma_map_lengths z =
    match z.lemmas with
    | Lemmas { map_lengths; _ } -> map_lengths
    | No_lemmas -> false

  let lemma_law_retry z =
    match z.lemmas with Lemmas { law_retry; _ } -> law_retry | No_lemmas -> false

  (** the rlimits of a law question: [law_retry_rlimits], or [rlimits] *)
  let lemma_law_retry_rlimits z =
    match z.lemmas with
    | Lemmas { law_retry_rlimits = Some r; _ } -> Some (r.native, r.fallback)
    | Lemmas { law_retry_rlimits = None; _ } | No_lemmas -> None

  let lemma_keep_hypotheses z =
    match z.lemmas with
    | Lemmas { keep_hypotheses; _ } -> keep_hypotheses
    | No_lemmas -> false

  let lemma_goal_first_probe z =
    match z.lemmas with
    | Lemmas { route = Extended_route { goal_first_probe }; _ } -> goal_first_probe
    | Lemmas { route = Plain_route; _ } | No_lemmas -> None

  let guarded_facts_ms z =
    match z.guarded_facts with
    | Guarded_facts { ms; _ } -> Some ms
    | No_guarded_facts -> None

  let guarded_facts_theory_facts_only z =
    match z.guarded_facts with
    | Guarded_facts { theory_facts_only; _ } -> theory_facts_only
    | No_guarded_facts -> true
end
