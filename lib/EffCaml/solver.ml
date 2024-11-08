open Core
open Common
open Common.Ext
open Common.Util

module type SolverType = sig
  val solve_from_file : ?print_sol:bool -> string -> (unit, Error.t) Result.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let solver =
    let open Or_error in
    ExtFile.unwrap config.solver >>= fun cfg -> Ok (HOMCSolver.Solver.make cfg)

  let _ = Debug.set_module_name "EffCaml"

  module Cgen = Cgen.Make (Config)

  let solve_from_file ?(print_sol = true) filename =
    ignore print_sol;
    match snd (Filename.split_extension filename) with
    | Some "ml" ->
        let open Or_error.Monad_infix in
        solver >>= fun (module HOMCSolver : HOMCSolver.Solver.SolverType) ->
        Cgen.from_ml_file filename >>= fun problems ->
        List.iter problems ~f:(fun (desc, prb) ->
            Debug.print @@ lazy (sprintf "begin checking %s" desc);
            ignore (*ToDo*) @@ HOMCSolver.solve ~print_sol prb;
            Debug.print @@ lazy (sprintf "end checking %s" desc));
        Ok ()
    | _ -> Or_error.unimplemented "solve_from_file"
end
