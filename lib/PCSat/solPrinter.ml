open Core
open Common.Util
open PCSatCommon

module Config = struct
  type t = {
    output_iteration : bool; [@default true]
    sygus_comp : bool; [@default false]
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
  val print : State.output -> unit

  val prints_solution : bool
  (** whether [print] shows a [sat] answer's solution, and not only the
      verdict (and the iteration count) *)
end

module Make (Config : Config.ConfigType) = struct
  let config = Config.config

  (* [str_of_solution] prints the verdict of a [sat] answer and not its
     substitution; only the SyGuS printer shows the solution *)
  let prints_solution = config.sygus_comp

  let print (solution, info) =
    Out_channel.print_endline
    @@
    if config.sygus_comp then PCSP.Problem.str_of_sygus_solution solution
    else if config.output_iteration then
      sprintf "%s,%d"
        (PCSP.Problem.str_of_solution solution)
        info.State.num_cegis_iters
    else PCSP.Problem.str_of_solution solution;
    (if config.print_unsat_witness then
       match (solution, info.State.unsat_witness) with
       | PCSP.Problem.Unsat _, Some w ->
           Out_channel.print_endline (UnsatWitness.str_of w)
       | PCSP.Problem.Unsat _, None ->
           Out_channel.print_endline "(unsat-witness (none-recorded))"
       | _ -> ());
    Out_channel.flush stdout
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolPrinterType)
