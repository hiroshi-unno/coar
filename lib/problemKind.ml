open Core

(* The problem classes CoAR solves, as selected by [-p].  This module is the
   single source for the [-p] parser, the help string and the
   backend x problem compatibility check ([Solver.supports]): the four used
   to be written out separately in [main.ml] and [lib/solver.ml] and had
   drifted. *)
type t =
  | PSAT  (** Boolean SAT Solving *)
  | PDQSAT  (** Boolean QSAT/DQSAT Solving *)
  | PHOSAT  (** Boolean HOSAT Solving *)
  | PSMT  (** SMT Solving *)
  | PHOMC  (** Higher-Order Model Checking *)
  | PSyGuS  (** SyGyS Inv/CLIA *)
  | PPCSP
      (** pfwnCSP Satifiability Checking (CHC, QCHC, DQCHC, pCSP, pfwCSP,
          pfwnCSP) *)
  | PCHCMax  (** CHC Maximization *)
  | PMuCLP  (** muCLP Validity Checking *)
  | PMuCLPInter  (** Interactive Conditional muCLP Validity Checking *)
  | PQFL  (** QFL Validity Checking *)
  | PPGCL  (** pGCL Verification *)
  | PSGCL  (** SGCL Verification *)
  | PCLTL  (** LTL Verification of C Programs *)
  | PCCTL  (** CTL Verification of C Programs *)
  | PLTSSafe of (* BV mode *) bool
      (** Safety Verification of Labeled Transition Systems *)
  | PLTSNSafe of (* BV mode *) bool
      (** Non-Safety Verification of Labeled Transition Systems *)
  | PLTSTerm of (* BV mode *) bool
      (** Termination Verification of Labeled Transition Systems *)
  | PLTSNTerm of (* BV mode *) bool
      (** Non-Termination Verification of Labeled Transition Systems *)
  | PLTSMuCal of (* BV mode *) bool
      (** Modal mu-Calculus Model Checking of Labeled Transition Systems *)
  | PLTSRel of (* BV mode *) bool
      (** Relational Verification of Labeled Transition Systems *)
  | PLTSTermInter of (* BV mode *) bool
      (** Interactive Conditional (Non-)Termination Analysis of Labeled
          Transition Systems *)
  | PPLTSTerm
      (** Termination Verification of Pushdown Labeled Transition Systems *)
  | PPLTSNTerm
      (** Non-Termination Verification of Pushdown Labeled Transition Systems *)
  | POCaml  (** Refinement Type Inference of OCaml Programs *)
  | PBTOR2  (** Safety Verification of Word-Level Hardware Models in BTOR2 *)
[@@deriving show, eq]

(* Every problem with its display name (for the help string) and the names
   [-p] accepts for it, compared case-insensitively.  The whole family
   [chc], [qchc], [dqchc], [qechc], [dqechc], [qpcsp], [dqpcsp], [pcsp],
   [pfwcsp], [pfwncsp] is one problem class: a quantified or
   dependency-quantified system is a pfwCSP whose universal sorts and
   predicates the front end records, and the Horn restriction each name
   suggests is not checked at all.  The names exist so that an input can be
   run under the
   name of the class it belongs to; adding one changes nothing but the help
   string. *)
let table : (t * string * string list) list =
  [
    (PSAT, "SAT", [ "sat" ]);
    (PDQSAT, "QSAT/DQSAT", [ "qsat"; "dqsat" ]);
    (PHOSAT, "HOSAT", [ "hosat" ]);
    (PSMT, "SMT", [ "smt" ]);
    (PHOMC, "HOMC", [ "homc" ]);
    (PSyGuS, "SyGuS", [ "sygus" ]);
    ( PPCSP,
      "CHC/QCHC/DQCHC/QECHC/DQECHC/pCSP/QpCSP/DQpCSP/pfwCSP/pfwnCSP",
      [
        "chc";
        "qchc";
        "dqchc";
        "qechc";
        "dqechc";
        "pcsp";
        "qpcsp";
        "dqpcsp";
        "q-pcsp";
        "dq-pcsp";
        "pfwcsp";
        "pfwncsp";
      ] );
    (PCHCMax, "CHCMax", [ "chcmax" ]);
    (PMuCLP, "muCLP", [ "muclp" ]);
    (PMuCLPInter, "muCLPInter", [ "muclpinter"; "muclp-inter" ]);
    (PQFL, "QFL", [ "qfl" ]);
    (PPGCL, "pGCL", [ "pgcl" ]);
    (PSGCL, "SGCL", [ "sgcl" ]);
    (PCLTL, "CLTL", [ "cltl"; "c-ltl" ]);
    (PCCTL, "CCTL", [ "cctl"; "c-ctl" ]);
    (PLTSSafe false, "LTSsafe", [ "ltssafe"; "lts-safe" ]);
    (PLTSSafe true, "LTSsafeBV", [ "ltssafebv"; "lts-safe-bv" ]);
    (PLTSNSafe false, "LTSnsafe", [ "ltsnsafe"; "lts-nsafe" ]);
    (PLTSNSafe true, "LTSnsafeBV", [ "ltsnsafebv"; "lts-nsafe-bv" ]);
    (PLTSTerm false, "LTSterm", [ "ltsterm"; "lts-term" ]);
    (PLTSTerm true, "LTStermBV", [ "ltstermbv"; "lts-term-bv" ]);
    (PLTSNTerm false, "LTSnterm", [ "ltsnterm"; "lts-nterm" ]);
    (PLTSNTerm true, "LTSntermBV", [ "ltsntermbv"; "lts-nterm-bv" ]);
    (PLTSMuCal false, "LTSmucal", [ "ltsmucal"; "lts-mucal" ]);
    (PLTSMuCal true, "LTSmucalBV", [ "ltsmucalbv"; "lts-mucal-bv" ]);
    (PLTSRel false, "LTSrel", [ "ltsrel"; "lts-rel" ]);
    (PLTSRel true, "LTSrelBV", [ "ltsrelbv"; "lts-rel-bv" ]);
    (PLTSTermInter false, "LTStermInter", [ "ltsterminter"; "lts-term-inter" ]);
    ( PLTSTermInter true,
      "LTStermInterBV",
      [ "ltsterminterbv"; "lts-term-inter-bv" ] );
    (PPLTSTerm, "PLTSterm", [ "pltsterm"; "plts-term" ]);
    (PPLTSNTerm, "PLTSnterm", [ "pltsnterm"; "plts-nterm" ]);
    (POCaml, "ML", [ "ml" ]);
    (PBTOR2, "BTOR2", [ "btor2" ]);
  ]

let all = List.map table ~f:(fun (p, _, _) -> p)

let of_string s =
  let s = String.lowercase s in
  List.find_map table ~f:(fun (p, _, names) ->
      if List.mem names s ~equal:String.equal then Some p else None)

(* the canonical (first) name of a problem, e.g. for messages and scripts *)
let name_of p =
  match List.find table ~f:(fun (p', _, _) -> equal p p') with
  | Some (_, _, n :: _) -> n
  | _ -> show p

(* Problem classes that are declared -- they have a [-p] name, a constructor
   and backends that would accept them -- but no implementation: the reduction
   from an LTS to muCLP needs an input the T2 format does not carry.  The
   check in [main.ml]'s [load_solver_config] refuses them before any file is
   read, instead of the [failwith "not implemented"] deep in
   [MuCLP.Util.of_lts].  Implementing them is two separate projects. *)
let unimplemented = function
  | PLTSMuCal _ ->
      Some
        "modal mu-calculus model checking of an LTS needs the property as an \
         input, which the T2 format does not carry; the input format and the \
         product construction are not decided yet"
  | PLTSRel _ ->
      Some
        "relational verification of an LTS needs a relational specification \
         (which runs are related, which variables are low/high) as an input; \
         its format and the product construction are not decided yet"
  | _ -> None

(* the help text's list of problems, derived from [table]; the declared but
   unimplemented ones are marked *)
let help_string () =
  "["
  ^ String.concat ~sep:"/"
      (List.map table ~f:(fun (p, d, _) ->
           if Option.is_some (unimplemented p) then d ^ "(unimplemented)" else d))
  ^ "]"
