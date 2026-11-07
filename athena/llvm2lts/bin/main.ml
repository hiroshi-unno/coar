(* The standalone llvm2lts command.  Exit codes: 0 on success, then one per
   kind of failure (Outcome.exit_code); the failure's one-line reason goes to
   stderr. *)

open Llvm2lts

let usage = "usage: llvm2lts [options] INPUT.ll|INPUT.bc"

let () =
  let input = ref None in
  let data_model = ref None in
  let dump_ll = ref None in
  let mode = ref Lts.Bv in
  let property = ref Translate.Unreach_call in
  let unbounded_nondet = ref false in
  let hoist = ref false in
  let output = ref None in
  let passes = ref Passes.default in
  let switch name ~default what set =
    ( "--" ^ name,
      Arg.Symbol ([ "yes"; "no" ], fun v -> passes := set !passes (v = "yes")),
      Printf.sprintf " %s (default: %s)" what (if default then "yes" else "no")
    )
  in
  let spec =
    [
      switch "simplifycfg" ~default:false "run simplifycfg before mem2reg"
        (fun p b -> { p with simplifycfg = b });
      switch "licm" ~default:false "run licm after mem2reg" (fun p b ->
          { p with licm = b });
      switch "tailcallelim" ~default:true
        "turn `return f(x);` self recursion into loops" (fun p b ->
          { p with tail_call_elimination = b });
      switch "tailcallelim-accumulator" ~default:false
        "also turn `return n + f(x);` and `return n * f(x);` into loops \
         with an accumulator (only with --unbounded-nondet)" (fun p b ->
          { p with accumulator_recursion = b });
      switch "inline" ~default:true
        "check that no recursion is left and inline every call" (fun p b ->
          { p with inline = b });
      ( "--data-model",
        Arg.Symbol
          ( [ "ILP32"; "LP64" ],
            fun s ->
              data_model :=
                Some (if s = "ILP32" then Reader.ILP32 else Reader.LP64) ),
        " the task's data model; the input must have been compiled for it" );
      ( "--mode",
        Arg.Symbol
          ( [ "bv"; "int"; "int-bitwise"; "int-wrap-unsigned"; "int-wrap-all" ],
            fun m ->
              mode :=
                match m with
                | "int" -> Lts.Int Plain
                | "int-bitwise" -> Lts.Int Bitwise
                | "int-wrap-unsigned" -> Lts.Int Wrap_unsigned
                | "int-wrap-all" -> Lts.Int Wrap_all
                | _ -> Lts.Bv ),
        " integers as bit-vectors (bv, the default) or as mathematical \
         integers: without wrap-around or bit operations (int), with bit \
         operations in infinite two's complement (int-bitwise), wrapping \
         as unsigned with signed overflow assumed away (int-wrap-unsigned), \
         or wrapping as unsigned and as signed (int-wrap-all)" );
      ( "--property",
        Arg.Symbol
          ( [ "unreach-call"; "termination" ],
            fun p ->
              property :=
                if p = "termination" then Translate.Termination
                else Translate.Unreach_call ),
        " the property the output is for (default: unreach-call)" );
      ( "--hoist",
        Arg.Symbol ([ "yes"; "no" ], fun v -> hoist := v = "yes"),
        " read an array cell no transition of a loop writes once before the \
         loop, rather than in every iteration (default: no)" );
      ( "--unbounded-nondet",
        Arg.Set unbounded_nondet,
        " with --mode int or int-bitwise: a __VERIFIER_nondet_T returns any \
         integer, not one of T's range (integers read as mathematical \
         integers throughout, as termCOMP's C semantics reads them)" );
      ( "-o",
        Arg.String (fun path -> output := Some path),
        "FILE write the T2 output to FILE (default: standard output)" );
      ( "--dump-ll",
        Arg.String (fun path -> dump_ll := Some path),
        "FILE write the module as llvm2lts last held it to FILE" );
    ]
  in
  let set_input path =
    match !input with
    | None -> input := Some path
    | Some _ -> raise (Arg.Bad "more than one input file")
  in
  (try Arg.parse_argv Sys.argv (Arg.align spec) set_input usage with
  | Arg.Bad message | Arg.Help message ->
      let help = String.starts_with ~prefix:"usage:" message in
      (if help then print_string else prerr_string) message;
      exit (if help then 0 else Outcome.exit_code (Input_error "")));
  let path =
    match !input with
    | Some path -> path
    | None ->
        prerr_endline usage;
        exit (Outcome.exit_code (Input_error ""))
  in
  (match (!unbounded_nondet, !mode) with
  | true, (Lts.Bv | Lts.Int (Wrap_unsigned | Wrap_all)) ->
      (* a wrapping mode holds every value as a representative in [0, 2^N),
         and a bit-vector has its width: neither has an unbounded value *)
      prerr_endline "--unbounded-nondet is used only with --mode int or int-bitwise";
      exit (Outcome.exit_code (Input_error ""))
  | _ -> ());
  let options =
    {
      Pipeline.data_model = !data_model;
      passes = !passes;
      mode = !mode;
      property = !property;
      unbounded_nondet = !unbounded_nondet;
      hoist = !hoist;
      dump_ll = !dump_ll;
    }
  in
  match Pipeline.run options path with
  | Ok lts -> (
      let text = Lts.to_t2 lts in
      match !output with
      | None -> print_string text
      | Some path -> Out_channel.with_open_text path (fun oc -> output_string oc text))
  | Error failure ->
      prerr_endline (Outcome.to_string failure);
      exit (Outcome.exit_code failure)
