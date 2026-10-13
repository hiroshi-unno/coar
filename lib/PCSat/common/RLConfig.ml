(* Configuration of PCSat's reinforcement-learning channel, off by default
   ([disabled]).  When [enable] is set, the solver prints machine-readable
   lines on stdout -- the problem's statistics, each loop event, candidates,
   examples, unsat cores, as the [show_*] fields select -- for an external
   agent that drives PCSat's choices, and may ask that agent for an SMT
   timeout.  [lock]/[unlock] serialise the writers when several solver
   domains share stdout. *)
open Core
open Common.Util

type t = {
  enable : bool; [@default false]
  show_constraints : bool; [@default false]
  show_num_constrs : bool; [@default false]
  show_num_pvars : bool; [@default false]
  show_dep_graph : bool; [@default false]
  show_num_iters : bool; [@default false]
  show_user_time : bool; [@default false]
  show_kind : bool; [@default false]
  show_sort : bool; [@default false]
  show_relevance : bool; [@default false]
  show_num_args : bool; [@default false]
  show_pcsat_actions : bool; [@default false]
  show_elapsed_time : bool; [@default false]
  show_candidates : bool; [@default false]
  show_examples : bool; [@default false]
  show_unsat_core : bool; [@default false]
  ask_smt_timeout : bool; [@default false]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg = Ok cfg

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "RL"
  let instantiate = instantiate_ext_files
end)

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
