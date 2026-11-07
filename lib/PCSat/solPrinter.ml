open Core
open Common.Util
open PCSatCommon

module Config = struct
  (** how an answer is printed *)
  type format =
    | Verdict_and_iterations
        (** the verdict and the number of CEGIS iterations, [sat,12] *)
    | Verdict  (** the verdict alone *)
    | Sygus_solution
        (** a [sat] answer's solution in the SyGuS competition's format;
            another answer's verdict alone *)
  [@@deriving yojson]

  type t = {
    format : format; [@default Verdict_and_iterations]
    print_unsat_witness : bool; [@default false]
        (* after an [unsat] verdict, print the evidence the solver recorded *)
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "SolPrinter"

    (* a leaf: no nested config to load *)
    let instantiate = Or_error.return
  end)
end

module type SolPrinterType = sig
  val print : ?sygus_signature:SyGuS.Printer.signature -> State.output -> unit
  (** [sygus_signature]: the functions a SyGuS input requests, which the
      SyGuS format's answer defines exactly; absent for any other input *)

  val prints_solution : bool
  (** whether [print] shows a [sat] answer's solution, and not only the
      verdict (and the iteration count) *)
end

module Make (Config : Config.ConfigType) = struct
  let config = Config.config

  (* [str_of_solution] prints the verdict of a [sat] answer and not its
     substitution; only the SyGuS printer shows the solution *)
  let prints_solution =
    match config.format with
    | Sygus_solution -> true
    | Verdict_and_iterations | Verdict -> false

  let print ?sygus_signature (solution, info) =
    Out_channel.print_endline
      (match config.format with
      | Sygus_solution ->
          PCSP.Problem.str_of_sygus_solution ?signature:sygus_signature
            solution
      | Verdict_and_iterations ->
          sprintf "%s,%d"
            (PCSP.Problem.str_of_solution solution)
            info.State.num_cegis_iters
      | Verdict -> PCSP.Problem.str_of_solution solution);
    (* the verdict is out before the witness is printed: printing a
       countermodel's witness runs the search for its terms (see
       [UnsatWitness.Countermodel]), which may take the solver's query
       budget several times over and must not withhold a decided answer.
       A timer that fires during that search ends only the witness. *)
    Out_channel.flush stdout;
    (if config.print_unsat_witness then
       match (solution, info.State.unsat_witness) with
       | PCSP.Problem.Unsat _, Some w ->
           Out_channel.print_endline
             (try UnsatWitness.str_of w
              with Common.Timer.Timeout ->
                "(unsat-witness (interrupted-by-timeout))")
       | PCSP.Problem.Unsat _, None ->
           Out_channel.print_endline "(unsat-witness (none-recorded))"
       | _ -> ());
    Out_channel.flush stdout
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolPrinterType)
