open Core
open Common.Util

type t = {
  enable : bool;
  show_constraints : bool;
  show_num_constrs : bool;
  show_num_pvars : bool;
  show_dep_graph : bool;
  show_num_iters : bool;
  show_user_time : bool;
  show_kind : bool;
  show_sort : bool;
  show_relevance : bool;
  show_num_args : bool;
  show_pcsat_actions : bool;
  show_elapsed_time : bool;
  show_candidates : bool;
  show_examples : bool;
  show_unsat_core : bool;
  ask_smt_timeout : bool;
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg = Ok cfg

let load_ext_file = function
  | ExtFile.Instance x -> Ok (ExtFile.Instance x)
  | Filename filename -> (
      let open Or_error in
      try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
      match of_yojson raw_json with
      | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
      | Error msg ->
          error_string
          @@ sprintf "Invalid RL Configuration (%s): %s" filename msg)

let disabled : t =
  {
    enable = false;
    show_constraints = false;
    show_num_constrs = false;
    show_num_pvars = false;
    show_dep_graph = false;
    show_num_iters = false;
    show_user_time = false;
    show_kind = false;
    show_sort = false;
    show_relevance = false;
    show_num_args = false;
    show_pcsat_actions = false;
    show_elapsed_time = false;
    show_candidates = false;
    show_examples = false;
    show_unsat_core = false;
    ask_smt_timeout = false;
  }

(* For concurrency control in RL mode *)
let mutex = Caml_threads.Mutex.create ()
let lock () = Caml_threads.Mutex.lock mutex
let unlock () = Caml_threads.Mutex.unlock mutex
