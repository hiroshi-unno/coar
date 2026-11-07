(* Programs given as a set of procedures with parameterised transition relations
   (one relation formula per edge), as read from integer transition systems
   written in SMT-LIB, with a termination or non-termination property.  [lts_of]
   turns one into a single labelled transition system: each relation becomes the
   commands that realise it, locations are qualified by their procedure, and a
   fresh initial location runs the initial relation. *)
open Common.Ext
open Ast
open Ast.LogicOld

type plts =
  Ident.tvar_set
  * (string * sort_env_list * string * Formula.t)
  * (string
    * sort_env_list
    * sort_env_list
    * (string * string * Formula.t) Core.Set.Poly.t)
    list

type mode = Term | NonTerm
type t = plts * mode

let init = "__init__"
let proc_loc proc loc = proc ^ "@" ^ loc

let lts_of ~print
    ((_locs, (init_proc, init_args, init_loc, init_rel), nexts) : plts) =
  (*print_endline @@ String.concat_map_set ~sep:", " ~f:Ident.name_of_tvar locs;*)
  let trans =
    let args =
      List.find_map_exn nexts ~f:(fun (proc, args, _, _) ->
          if String.(proc = init_proc) then Some args else None)
    in
    (* The initial relation's formals correspond to the transition relation's
       pre-state formals by position, not by name.  The relation is moved onto
       the pre-state formals by one simultaneous substitution and realised on
       them directly.  Realising it on its own formals and then copying them
       with a sequence of assignments read a permutation of shared names
       wrongly: with [init_main (pc y x)] and [next_main (pc x y ...)], [x := y]
       ran before [y := x], so every initial state had [x = y], and a loop that
       runs forever exactly when [x > y] was answered terminating. *)
    let init_rel =
      match List.zip init_args args with
      | Unequal_lengths ->
          failwith
            (Printf.sprintf "init_%s and next_%s have different numbers of variables"
               init_proc init_proc)
      | Ok pairs ->
          Formula.subst
            (Map.Poly.of_alist_exn
            @@ List.map pairs ~f:(fun ((x, _), (y, s)) -> (x, Term.mk_var y s)))
            init_rel
    in
    ( init,
      LTS.Problem.seq @@ LTS.Problem.commands_of_formula ~print args init_rel,
      proc_loc init_proc init_loc )
    :: List.concat_map nexts ~f:(fun (proc, args1, args2, trans) ->
           Set.to_list
           @@ Set.Poly.map trans ~f:(fun (src, dst, rel) ->
                  ( proc_loc proc src,
                    LTS.Problem.seq
                    @@ LTS.Problem.commands_of_formula ~print args2 rel
                    @ LTS.Problem.subst args1
                        (List.map args2 ~f:(Core.Tuple2.uncurry Term.mk_var)),
                    proc_loc proc dst )))
  in
  (Some init, [], None, None, trans, None)

let lts_mode_of = function
  | Term -> LTS.Problem.Term
  | NonTerm -> LTS.Problem.NonTerm
