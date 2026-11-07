(* The direct translation of one LLVM IR file to a muCLP problem: read and
   check the module, run the passes the config selects (no inlining by
   default; under the arbitrary-value reading of signed overflow, first a
   left shift clang's shift-base check rejects made a choice of its type),
   check what is left against the allow-list, optionally hold
   loop cells in registers and move loop-invariant reads of global memory
   before their loop (Hoist), then translate (Translate), for unreach-call
   and termination.  A construct outside what is translated is answered
   UNKNOWN with its reason. *)

type property = Unreach_call | Termination

(* With the [witness] setting, a problem comes with the map from its loop
   heads to the C program (LLVMWitness.Cmap). *)
type answer = Problem of MuCLP.Problem.t * LLVMWitness.Cmap.t option | Unknown of string

let run ~bv_mode ~property ~(config : Config.t) path =
  Reader.install_fatal_error_handler ();
  let ctx = Llvm.create_context () in
  let result =
    let data_model = match config.data_model with Auto -> None | ILP32 -> Some Reader.ILP32 | LP64 -> Some Reader.LP64 in
    match Reader.read ?data_model ctx path with
    | exception Outcome.Stop failure -> Error failure
    | { llmodule; _ } ->
        let result =
          let mode = if bv_mode then Translate.Bv else Translate.Int in
          let property =
            match property with
            | Unreach_call -> Translate.Unreach_call
            | Termination -> Translate.Termination
          in
          let passes =
            {
              Passes.simplifycfg = config.passes.simplifycfg;
              licm = config.passes.licm;
              tail_call_elimination = config.passes.tail_call_elimination;
              inline = config.passes.inline;
            }
          in
          match
            (* under the arbitrary-value reading of signed overflow a left
               shift clang's check rejects yields an arbitrary value, which
               the IR states before any pass moves the check *)
            if config.signed_overflow = Arbitrary_value then Passes.havoc_rejected_shifts llmodule;
            Passes.run passes llmodule;
            Allowlist.check llmodule;
            if config.passes.promote then ignore (Hoist.promote llmodule);
            if config.passes.hoist then ignore (Hoist.run llmodule);
            Translate.translate ~mode ~property ~config llmodule
          with
          | problem, map -> Ok (Problem (problem, map))
          | exception Outcome.Stop (Unknown reason) -> Ok (Unknown reason)
          | exception Outcome.Stop failure -> Error failure
        in
        Option.iter (fun file -> Llvm.print_module file llmodule) config.dump_ll;
        Llvm.dispose_module llmodule;
        result
  in
  Llvm.dispose_context ctx;
  Result.map_error Outcome.to_string result
