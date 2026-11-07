open Core
open Ast
open Ast.LogicOld

(* Craig interpolation over bit-vectors, asked of Bitwuzla through a file.

   MuCyc's own interpolation asks a CHC solver to synthesize a predicate that
   sits between the two formulas.  Bitwuzla, since its 2026 support for
   [get-interpolant], answers the question directly, and on bit-vector queries
   it is much the faster of the two.  There is no OCaml binding for that command
   -- the one on opam wraps an older C API -- so the exchange is SMT-LIB text
   over a temporary file, the way the other external solvers are driven. *)

type t =
  | Interpolant of Formula.t
  | NoInterpolant  (** the two formulas are jointly satisfiable *)
  | Unavailable of string
      (** the solver is absent, declined, or answered something unusable; the
          caller must fall back rather than read this as an answer *)

let binary = "./bitwuzla"
let available () = Sys_unix.is_file_exn binary

(* Name the shared subterms without binding them.

   The conversion to Z3 turns every [let] into an existential, and
   [get-interpolant] rejects a quantified assertion, so the naming is done here
   instead and the definition variables are left free.  That is sound for
   interpolation: [elim_let_equisat] pins each new variable to its definition
   inside the formula it came from, so a model of the original extends to one of
   the result and back, and the two sides are renamed apart, so no definition
   variable is shared -- an interpolant, which may only mention shared symbols,
   therefore cannot name one. *)
let name_shared_subterms phi =
  snd @@ Formula.elim_let_equisat @@ Normalizer.normalize_let ~rename:true phi

let declarations ctx exprs =
  List.concat_map exprs ~f:(fun e ->
      Z3.SMT.benchmark_to_smtstring ctx "interp" "QF_BV" "unknown" "" [] e
      |> String.split_lines
      |> List.filter ~f:(String.is_prefix ~prefix:"(declare-"))
  |> List.dedup_and_sort ~compare:String.compare

let query_of ~decls ~a ~b =
  String.concat ~sep:"\n"
    ([ "(set-option :produce-interpolants true)"; "(set-logic QF_BV)" ]
    @ decls
    @ [
        sprintf "(assert %s)" a;
        sprintf "(assert %s)" b;
        "(check-sat)";
        (* the argument has to repeat the assertion verbatim: Bitwuzla matches
           it against what was asserted, not against its meaning *)
        sprintf "(get-interpolant (%s))" a;
        "(exit)";
      ])

(* How Bitwuzla builds the interpolant (read in its source, commit c85e1a9,
   [src/interpolator.cpp] and [src/sat/interpolants/cadical_tracer.cpp]).
   Bit-vectors are bit-blasted and the interpolant is read off CaDiCaL's
   resolution proof; [pudlak] selects Pudlak's labelling instead of McMillan's
   (the default), [lift] (on by default) re-expresses the resulting AIG with
   theory-level operators where it can, and [simp] post-processes it (gate
   extraction, lowering of one-bit vectors).  [subst] tries first, before any
   proof is read, to eliminate the symbols local to one side by the
   preprocessor's substitutions while keeping the shared ones: when that
   leaves the first formula (or the negated second) over shared symbols only,
   that formula itself is the interpolant. *)
type options = { subst : bool; pudlak : bool; lift : bool; simp : bool }

let default_options =
  { subst = false; pudlak = false; lift = true; simp = true }

let flags_of opts =
  String.concat ~sep:" "
  @@ List.filter_opt
       [
         Some "--produce-interpolants";
         Option.some_if opts.subst "--interpolants-subst";
         Option.some_if opts.pudlak "--interpolants-algo pudlak";
         Option.some_if (not opts.lift) "--interpolants-lift=false";
         Option.some_if opts.simp "--interpolants-simp";
       ]

let run ~opts ~timeout file =
  let cmd =
    sprintf "%s %s %s %s" binary (flags_of opts)
      (match timeout with
      | None -> ""
      | Some secs -> sprintf "-t %d" (secs * 1000))
      (Filename.quote file)
  in
  let cin = Core_unix.open_process_in cmd in
  let lines =
    let rec loop acc =
      match In_channel.input_line cin with
      | None -> List.rev acc
      | Some l -> loop (l :: acc)
    in
    loop []
  in
  ignore (Core_unix.close_process_in cin : Core_unix.Exit_or_signal.t);
  lines

(* Read the interpolant back as a formula, with the repository's own SMT-LIB
   reader -- its bit-vector coverage is what parses the benchmarks.

   The symbols are handed over as an environment rather than as [declare-fun]
   lines: that reader is a constraint-problem front end, where a declared
   function is an unknown to be synthesized, so declaring them asks it to solve
   for the interpolant's own variables instead of reading them.  Passing only
   the caller's vocabulary also makes the reader reject an interpolant that
   names anything else. *)
let formula_of ~uni_senv text =
  Formula.and_of @@ fst
  @@ SMT.Smtlib2.from_string ~print:(fun _ -> ()) ~inline:false ~uni_senv
  @@ sprintf "(assert %s)" text

(* Read Bitwuzla's answer to [query_of] from the lines of its standard output.
   [args] is the shared vocabulary, [max_size] a bound in bytes on the
   interpolant's text.  The exit status is not consulted: after [sat] the
   [get-interpolant] command is an error, which may end the run with a failure
   status although the verdict was printed.
   Guarantees: [NoInterpolant] only when the first line is [sat];
   [Interpolant] only when the first line is [unsat] and the rest reads as one
   formula over [args] (a truncated or error text does not read); every other
   output -- empty, [unknown], an error report, an unreadable interpolant -- is
   [Unavailable], never an exception (a timeout excepted). *)
let answer_of_output ?max_size args lines =
  match lines with
  | [] -> Unavailable "no output"
  | "sat" :: _ -> NoInterpolant
  | "unsat" :: rest -> (
      let text = String.strip @@ String.concat ~sep:"\n" rest in
      if String.is_empty text then Unavailable "no interpolant printed"
      else if
        Option.value_map max_size ~default:false ~f:(fun m ->
            String.length text > m)
      then Unavailable (sprintf "interpolant of %d bytes" (String.length text))
      else
        match formula_of ~uni_senv:(Map.Poly.of_alist_exn args) text with
        | exception exn_ when not (Common.Timer.is_async exn_) ->
            Unavailable ("unreadable interpolant: " ^ Exn.to_string exn_)
        | phi ->
            (* the vocabulary is the caller's contract, not the solver's:
               an interpolant naming anything else cannot be used *)
            let allowed = Set.Poly.of_list @@ List.map args ~f:fst in
            if Set.is_subset (Formula.tvs_of phi) ~of_:allowed then
              Interpolant (Evaluator.simplify phi)
            else Unavailable "interpolant outside the given vocabulary")
  | l :: _ -> Unavailable (String.prefix l 80)

let interpolate ?(opts = default_options) ?timeout ?max_size args phi1 phi2 =
  if not (available ()) then Unavailable "no bitwuzla binary"
  else
    let file = Filename_unix.temp_file "coar_interp" ".smt2" in
    Exn.protect
      ~finally:(fun () ->
        (* only a failed unlink is ignored: a catch-all here would also
           swallow a timeout raised during the clean-up *)
        try Core_unix.unlink file with Core_unix.Unix_error _ -> ())
      ~f:(fun () ->
        match
          let cfg = [ ("model", "true") ] in
          let ctx = Z3.mk_context cfg in
          let dtenv = Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx (get_dtenv ()) in
          let fenv =
            Z3Smt.Z3interface.z3_fenv_of ~id:None ctx [] [] (get_fenv ()) dtenv
          in
          let to_z3 =
            Z3Smt.Z3interface.of_formula_with_z3fenv ~id:None ctx [] [] fenv
              dtenv
          in
          let ea = to_z3 @@ name_shared_subterms phi1 in
          let eb = to_z3 @@ name_shared_subterms (Formula.mk_neg phi2) in
          let decls = declarations ctx [ ea; eb ] in
          let a = Z3.Expr.to_string ea and b = Z3.Expr.to_string eb in
          Out_channel.write_all file ~data:(query_of ~decls ~a ~b);
          run ~opts ~timeout file
        with
        | exception exn_ when not (Common.Timer.is_async exn_) ->
            Unavailable (Exn.to_string exn_)
        | lines -> answer_of_output ?max_size args lines)
