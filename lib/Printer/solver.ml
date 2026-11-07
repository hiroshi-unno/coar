open Core
open Common.Util
open Preprocessing

module type SolverType = sig
  val print_sat : SAT.Problem.t -> unit
  val print_dqsat : DQSAT.Problem.t -> unit
  val print_hosat : HOSAT.Problem.t -> unit
  val print_homc : HOMC.Problem.t -> unit
  val print_smt : SMT.Problem.t -> unit

  (*val string_of_pcsp : PCSP.Problem.t -> string*)
  val print_pcsp : PCSP.Problem.t -> unit Or_error.t
  val print_muclp : MuCLP.Problem.t -> unit
  val print_lts : LTS.Problem.t -> unit
  val print_xmltype : Grammar.RegTreeExpReader.defs -> unit

  val print_hfl : string -> unit Or_error.t
  (** an HES or its OCaml representation, by file name, printed in the
      configured [hfl_format] *)

  val print_qfl : ?header:string -> QFL.Problem.t list -> unit Or_error.t
  (** QFL problems in the concrete syntax of [-p qfl] ([.qhes]), each readable
      back on its own; [header] is printed first as a comment *)
end

(* A muCLP equation of kind [MuOrNu] has no concrete syntax: printed as it is
   ([=mu_or_nu]), the file is refused by the reader of the format.  Its
   producer guarantees that the least and the greatest reading give the same
   solution, so either keyword states the same problem; [mu] is written when no
   equation is a greatest fixpoint, so that a problem of least fixpoints only
   (a termination problem from an LTS) reads back as one, and [nu] otherwise,
   the reading the reductions give it.  Every other equation is unchanged. *)
let with_concrete_fixpoints (muclp : MuCLP.Problem.t) =
  let open Ast.LogicOld in
  let kind =
    if
      List.exists muclp.preds ~f:(fun (p : MuCLP.Pred.t) ->
          Poly.(p.kind = Predicate.Nu))
    then Predicate.Nu
    else Predicate.Mu
  in
  {
    muclp with
    preds =
      List.map muclp.preds ~f:(fun (p : MuCLP.Pred.t) ->
          if Poly.(p.kind = Predicate.MuOrNu) then { p with kind } else p);
  }

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  let () =
    if config.simplify_inline_lets_once then
      Atomic.set Ast.Evaluator.simplify_inline_lets_once true

  let () =
    if config.simplify_skip_settled_bv_eval then
      Atomic.set Ast.Evaluator.simplify_skip_settled_bv_eval true

  let preprocessor =
    let open Or_error in
    ExtFile.unwrap config.preprocessor >>= fun cfg -> Ok (Preprocessor.make cfg)

  (*let string_of_pcsp pcsp =
    match config.smt_format with
    | SMT2 ->
        Smtlib2.of_pcsp ~id:None (*ToDo*)
          ~add_missing_forall:config.add_missing_forall pcsp
    | String -> PCSP.Problem.str_of pcsp*)

  let print_homc = HOMC.Problem.pr Format.std_formatter

  let print_sat cnf =
    match config.sat_format with
    | HOMC ->
        let module HOMCSat = HOMCSat.Solver.Make (struct
          let config = config.homc_sat
        end) in
        print_homc @@ HOMCSat.homc_of_hosat @@ HOSAT.Problem.of_sat cnf
    | String -> print_endline @@ SAT.Problem.str_of cnf

  let print_dqsat dqsat =
    match config.sat_format with
    | HOMC ->
        let module HOMCSat = HOMCSat.Solver.Make (struct
          let config = config.homc_sat
        end) in
        print_homc @@ HOMCSat.homc_of_hosat @@ HOSAT.Problem.of_dqsat dqsat
    | String -> print_endline @@ DQSAT.Problem.str_of dqsat

  let print_hosat hosat =
    match config.sat_format with
    | HOMC ->
        let module HOMCSat = HOMCSat.Solver.Make (struct
          let config = config.homc_sat
        end) in
        print_homc @@ HOMCSat.homc_of_hosat hosat
    | String -> print_endline @@ HOSAT.Problem.str_of hosat

  let print_pcsp pcsp =
    let open Or_error in
    preprocessor >>= fun (module Preprocessor) ->
    let defining_context =
      Poly.(config.smt_format = SMT2)
      && Smtlib2.has_supported_defining_context (Smtlib2.exported_fenv pcsp)
    in
    let pcsp =
      if defining_context
      then
        (* Assertion-only elimination can choose a predicate's interpretation
           without substituting it in known defining equations. Keep the full
           clauses as well as the definitions for this context-preserving
           export path; otherwise the exported file can be satisfiable where
           the input with its definitions is not. *)
        pcsp
      else
        snd
        @@ Preprocessor.preprocess
             ~purpose:Preprocessing.Preprocessor.Purpose.decide pcsp
    in
    return @@ print_endline
    @@ (match config.smt_format with
      | SMT2 ->
          Smtlib2.of_pcsp ~id:None (*ToDo*)
            ~add_missing_forall:config.add_missing_forall
      | String -> PCSP.Problem.str_of)
    @@ pcsp

  let print_muclp muclp =
    print_endline @@ MuCLP.Problem.str_of @@ with_concrete_fixpoints muclp

  (* [smt_format SMT2], the default, writes an SMT-LIB2 script; [String] the
     internal notation, which no SMT-LIB2 reader takes *)
  let print_smt phi =
    print_endline
    @@
    match config.smt_format with
    | SMT2 -> Smtlib2.of_smt ~id:None phi
    | String -> Ast.LogicOld.Formula.str_of phi

  let print_lts lts =
    match config.lts_format with
    | PCSP ->
        (* no reduction of an LTS to a pCSP exists in this tree; the MuCLP
           format is the one an LTS can be printed in *)
        Common.Refusal.refuse
          "lts_format PCSP: an LTS cannot be printed as a pCSP, since that \
           reduction has no implementation; use lts_format MuCLP"
    | MuCLP ->
        print_muclp @@ MuCLP.Util.of_lts ~print:(fun _ -> ()) lts

  (* The tree automaton of the start type, as a [%BEGINA] section: the trivial
     tree automaton syntax the [.hors] and EHMTT readers accept, so the output
     can be pasted into such a file as its input or output automaton.  The
     definitions must have passed [RegTreeExpReader.check]. *)
  let print_xmltype defs =
    Format.printf "%%BEGINA@\n%a%%ENDA@."
      (Automata.TTA.pr Format.pp_print_string)
      (Grammar.RegTreeExp.tta_of defs)

  (* An HES file is read in the union dialect, an OCaml file by the inverse
     translation; a construct the requested format cannot express is an
     error naming it. *)
  let print_hfl filename =
    let open HFL in
    let read () =
      match snd (Filename.split_extension filename) with
      | Some "ml" -> HflOfOCaml.from_file filename
      | _ -> HflReader.from_file ~dialect:HflSyntax.Coar filename
    in
    try
      let hes = read () in
      match config.hfl_format with
      | "ocaml" ->
          print_string (HflToOCaml.print hes);
          Ok ()
      | "muclp" ->
          print_string (HflToMuCLP.to_text hes);
          Ok ()
      | d -> (
          match HflSyntax.dialect_of_string d with
          | Some dialect ->
              print_string (HflPrinter.print ~dialect hes);
              Ok ()
          | None -> Or_error.errorf "unknown hfl_format %S" d)
    with
    | HflReader.Refused msg | HflOfOCaml.Refused msg
    | HflPrinter.Unprintable msg | HflToMuCLP.Not_order1 msg ->
        Or_error.error_string ("refused: " ^ msg)

  (* A problem whose functions are tuple-valued is read as one problem per
     component, and each is printed as a file of its own, after a comment
     line that says which. *)
  let print_qfl ?header qfls =
    Option.iter header ~f:(fun h ->
        (* a block comment cannot contain its own terminator *)
        if String.is_substring h ~substring:"*/" then
          String.split_lines h
          |> List.iter ~f:(fun l -> print_endline ("// " ^ l))
        else printf "/*\n%s\n*/\n" h);
    let many = List.length qfls > 1 in
    List.iteri qfls ~f:(fun i qfl ->
        if many then printf "// component %d of %d\n" (i + 1) (List.length qfls);
        print_string (QFL.Qhes.str_of qfl));
    Out_channel.flush stdout;
    Ok ()
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
