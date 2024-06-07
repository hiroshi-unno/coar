open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

type plts =
  Ident.tvar Set.Poly.t
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
    ( init,
      LTS.Problem.seq
      @@ LTS.Problem.commands_of_formula ~print init_args init_rel
      @ LTS.Problem.subst args (List.map init_args ~f:(uncurry Term.mk_var)),
      proc_loc init_proc init_loc )
    :: List.concat_map nexts ~f:(fun (proc, args1, args2, trans) ->
           Set.to_list
           @@ Set.Poly.map trans ~f:(fun (src, dst, rel) ->
                  ( proc_loc proc src,
                    LTS.Problem.seq
                    @@ LTS.Problem.commands_of_formula ~print args2 rel
                    @ LTS.Problem.subst args1
                        (List.map args2 ~f:(uncurry Term.mk_var)),
                    proc_loc proc dst )))
  in
  (Some init, None, None, trans)

let lts_mode_of = function
  | Term -> LTS.Problem.Term
  | NonTerm -> LTS.Problem.NonTerm
