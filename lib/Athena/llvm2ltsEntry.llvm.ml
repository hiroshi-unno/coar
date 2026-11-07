(* The LTS translation with llvm2lts linked in (see llvm2ltsEntry.mli). *)

let available = true

type mode = Bv | Int | Int_bitwise | Int_wrap_unsigned | Int_wrap_all
type property = Unreach_call | Termination
type data_model = LP64 | ILP32
type answer = T2 of string | Failed of string

(* llvm2lts's modules are named in full: this library has a [Pipeline] of
   its own, which an [open] would leave the build to confuse with
   llvm2lts's *)
let translate ?(unbounded_nondet = false) ?(hoist = false)
    ?(accumulator_recursion = false) ?(simplifycfg = false) ~data_model ~mode ~property path =
  let options =
    {
      (Llvm2lts.Pipeline.default
         ~mode:
           (match mode with
           | Bv -> Llvm2lts.Lts.Bv
           | Int -> Llvm2lts.Lts.Int Plain
           | Int_bitwise -> Llvm2lts.Lts.Int Bitwise
           | Int_wrap_unsigned -> Llvm2lts.Lts.Int Wrap_unsigned
           | Int_wrap_all -> Llvm2lts.Lts.Int Wrap_all)
         ~property:
           (match property with
           | Unreach_call -> Llvm2lts.Translate.Unreach_call
           | Termination -> Llvm2lts.Translate.Termination))
      with
      Llvm2lts.Pipeline.data_model =
        Some
          (match data_model with
          | LP64 -> Llvm2lts.Reader.LP64
          | ILP32 -> Llvm2lts.Reader.ILP32);
      unbounded_nondet;
      hoist;
      passes =
        {
          Llvm2lts.Passes.default with
          Llvm2lts.Passes.accumulator_recursion;
          simplifycfg;
        };
    }
  in
  (* The standalone llvm2lts stops with a status for any exception that
     escapes it, and the competition script reads that as MAYBE; in this
     process the same exception would end the whole run without an answer.
     A timeout or an interrupt still escapes. *)
  match Llvm2lts.Pipeline.run options path with
  | Ok lts -> Ok (T2 (Llvm2lts.Lts.to_t2 lts))
  | Error failure -> Ok (Failed (Llvm2lts.Outcome.to_string failure))
  | exception exn when not (Common.Timer.is_async exn) ->
      Ok (Failed ("INTERNAL_ERROR: " ^ Printexc.to_string exn))
