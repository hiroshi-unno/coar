(* The whole translation of one input file: read and check the module, run
   the passes, check what is left against the allow-list, and translate
   main. *)

type options = {
  data_model : Reader.data_model option;  (** None: read from the module *)
  passes : Passes.options;
  mode : Lts.mode;
  property : Translate.property;
  unbounded_nondet : bool;
      (** in int and int-bitwise: a __VERIFIER_nondet_T is any integer, not
          one of T's range *)
  hoist : bool;
      (** move loop-invariant array reads out of their loops (Hoist) *)
  dump_ll : string option;
      (** where to print the module after the passes, also when a step
          rejects it *)
}

let default ~mode ~property =
  {
    data_model = None;
    passes = Passes.default;
    mode;
    property;
    unbounded_nondet = false;
    hoist = false;
    dump_ll = None;
  }

(* Converting the accumulator form computes the sum or product in the
   opposite order.  That gives the same answers exactly when the add or mul
   is read as a total, associative and commutative operation without a
   guard: in Int and Int Bitwise mode, where nsw is not read.  It is admitted
   only with the integers unbounded (termCOMP's reading of C), where that is
   also the C program's own arithmetic; in BV and Wrap_unsigned mode nsw is
   a guard, and reordering moves the point where it stops a path. *)
let check_options options =
  if options.passes.Passes.accumulator_recursion then
    if not options.passes.tail_call_elimination then
      Some "the accumulator form needs tail-call elimination"
    else
      match options.mode with
      | Lts.Int (Plain | Bitwise) when options.unbounded_nondet -> None
      | _ ->
          Some
            "the accumulator form is admitted only with unbounded integers \
             (int or int-bitwise with unbounded nondeterministic values)"
  else None

let run options path =
  match check_options options with
  | Some reason -> Error (Outcome.Input_error reason)
  | None ->
  Reader.install_fatal_error_handler ();
  let ctx = Llvm.create_context () in
  let result =
    match Reader.read ?data_model:options.data_model ctx path with
    | exception Outcome.Stop failure -> Error failure
    | { llmodule; _ } ->
        let dump () =
          Option.iter (fun file -> Llvm.print_module file llmodule) options.dump_ll
        in
        let result =
          match
            Passes.run options.passes llmodule;
            Allowlist.check llmodule;
            let lts =
              Translate.translate ~mode:options.mode ~property:options.property
                ~unbounded_nondet:options.unbounded_nondet llmodule
            in
            if options.hoist then Hoist.run lts else lts
          with
          | lts -> Ok lts
          | exception Outcome.Stop failure -> Error failure
        in
        dump ();
        Llvm.dispose_module llmodule;
        result
  in
  Llvm.dispose_context ctx;
  result
