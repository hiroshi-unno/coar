(* A counterexample to a BTOR2 safety question, written in the BTOR2 witness format that the
   reference simulator checks with [btorsim -c] (Niemetz, Preiner, Wolf and Biere, "Btor2,
   BtorMC and Boolector 3.0", CAV 2018, section 3).

   The trace is found by bounded unrolling of the transition system the constraint problem was
   built from, so it does not depend on which backend answered: at depth k the query is
   init(s@0) /\ step(s@0, i@0, s@1) /\ ... /\ step(s@k-1, i@k-1, s@k) /\ bad(s@k, i@k), asked
   for k = 0, 1, ... until it is satisfiable. The first satisfiable depth is the length of a
   shortest trace, and its model gives every value the witness needs.

   What the witness states, and why that is enough for the simulator to replay it:
   - a state or an input is named by its position among the model's states or inputs in file
     order, not by its node id;
   - frame #0 assigns the registered states without an [init] and the free states (a state
     without [next] is an input at every time); the simulator computes the initialised ones and
     rejects an assignment that disagrees with their [init];
   - frame #k for k > 0 assigns only the free states, since the simulator computes a registered
     state from its [next] and rejects a disagreeing assignment;
   - every frame @k assigns the inputs;
   - a state or input outside the cone of the properties and the constraints is not assigned,
     and the simulator gives it 0: nothing a property or a constraint reads depends on it. *)

open Core
open Ast
open Ast.LogicOld
open Problem

(** Where a witness is written: after the [sat] line on standard output, whose first line it
    then is, or into a file of its own, with [sat] alone on standard output. *)
type target = Stdout | File of string

(* ["stdout"] names standard output; anything else is a path, so a file called [stdout] is
   written as [./stdout]. *)
let target_of_string = function "stdout" -> Stdout | path -> File path

let var_at prefix id t = Ident.Tvar (sprintf "%s%d_%d" prefix id t)

(* the copy of a formula of the system at time [t]: [s<id>] at [t], [sn<id>] at [t + 1] and
   [i<id>] at [t] *)
let at (ts : ts) (sys : Chc.system) t phi =
  let ssort id = Chc.sort_of_btor (sort_of ts.model id) in
  let ren name prefix id t' =
    (Ident.Tvar (sprintf "%s%d" name id), Term.mk_var (var_at prefix id t') (ssort id))
  in
  let map =
    List.concat_map sys.cone_states ~f:(fun id -> [ ren "s" "s" id t; ren "sn" "s" id (t + 1) ])
    @ List.map sys.cone_inputs ~f:(fun id -> ren "i" "i" id t)
  in
  Formula.subst (Map.Poly.of_alist_exn map) phi

let check phis =
  Z3Smt.Z3interface.check_sat ~id:None (LogicOld.get_fenv ()) phis

let bits w n =
  let n = Z.(erem n (shift_left one w)) in
  String.init w ~f:(fun i -> if Z.testbit n (w - 1 - i) then '1' else '0')

(* the lines of the witness for a model of the unrolling to depth [k] reaching property
   [bad_pos] (its position among the model's properties) *)
let lines_of (ts : ts) (sys : Chc.system) ~k ~bad_pos model =
  let values =
    Map.Poly.of_alist_reduce ~f:(fun v _ -> v)
    @@ List.filter_map model ~f:(fun ((x, _), v) -> Option.map v ~f:(fun v -> (x, v)))
  in
  let in_cone ids id = List.mem ids id ~equal:Int.equal in
  let assign prefix pos id t =
    match sort_of ts.model id with
    | Array _ ->
        Error
          (sprintf "node %d is an array, whose value the witness writer does not print yet" id)
    | Bitvec w ->
        let n =
          match Map.Poly.find values (var_at prefix id t) with
          | Some (Term.FunApp (T_bv.BVNum (_, n), [], _)) -> Ok n
          | Some v -> Error (sprintf "unexpected value %s for node %d" (Term.str_of v) id)
          | None -> Ok Z.zero (* a value the query leaves free *)
        in
        Result.map n ~f:(fun n -> sprintf "%d %s %s@%d" pos (bits w n) (sprintf "%s%d" prefix id) t)
  in
  let frame t =
    let states =
      List.filter_mapi ts.states ~f:(fun pos id ->
          let free = not (is_registered ts id) in
          let uninit = Option.is_none (Hashtbl.find ts.init id) in
          if in_cone sys.cone_states id && (free || (t = 0 && uninit)) then
            Some (assign "s" pos id t)
          else None)
    in
    let inputs =
      List.filter_mapi ts.inputs ~f:(fun pos id ->
          if in_cone sys.cone_inputs id then Some (assign "i" pos id t) else None)
    in
    Result.map (Result.all states) ~f:(fun ss -> (sprintf "#%d" t :: ss))
    |> Result.bind ~f:(fun ss ->
           Result.map (Result.all inputs) ~f:(fun is -> ss @ (sprintf "@%d" t :: is)))
  in
  Result.map
    (Result.all (List.init (k + 1) ~f:frame))
    ~f:(fun frames -> ("sat" :: sprintf "b%d" bad_pos :: List.concat frames) @ [ "." ])

(** A witness for the properties [bads] (by default all of them), as the lines of a BTOR2
    witness file, found by unrolling up to [max_depth] steps. [Error] says why there is none:
    no trace of at most that length, a query the solver did not settle, or a value it cannot
    write. *)
let build ?(max_depth = 256) ?bads (ts : ts) =
  let bads = Option.value bads ~default:ts.bads in
  let _, _, sys = Chc.system_of ts bads in
  let rec search k prefix =
    if k > max_depth then Error (sprintf "no trace of at most %d steps" max_depth)
    else
      match check (at ts sys k sys.bad_any :: prefix) with
      | `Unsat -> search (k + 1) (at ts sys k sys.step_f :: prefix)
      | `Sat _ -> (
          (* the first property reached at this depth, in file order *)
          let reached =
            List.find_map sys.bad_now ~f:(fun (b, phi) ->
                match check (at ts sys k phi :: prefix) with
                | `Sat model -> Some (b, model)
                | _ -> None)
          in
          match reached with
          | None -> Error (sprintf "no single property settled at depth %d" k)
          | Some (b, model) ->
              let bad_pos =
                fst
                @@ Option.value_exn
                     (List.findi ts.bads ~f:(fun _ b' -> Int.equal b b'))
              in
              lines_of ts sys ~k ~bad_pos model)
      | `Timeout -> Error (sprintf "the solver timed out at depth %d" k)
      | `Unknown reason -> Error (sprintf "the solver answered unknown at depth %d: %s" k reason)
  in
  search 0 [ at ts sys 0 sys.init_f ]
