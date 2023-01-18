open Core
open Common
open Ast.Logic
open Ast.Ident

module type ConfigType = sig
  val dir_map : (tvar, CHCOpt.Problem.direction) Map.Poly.t
  val verbose : bool
  val point_wise : bool
end

module Make (Config : ConfigType) : NonOptChecker.NonOptCheckerType = struct
  module Debug = Debug.Make (val Debug.Config.(if Config.verbose then enable else disable))
  let _ = Debug.set_module_name "LexiImprover"

  let is_dup p = CHCOpt.Problem.is_dup @@ Map.Poly.find_exn Config.dir_map p
  let is_ddown p = CHCOpt.Problem.is_ddown @@ Map.Poly.find_exn Config.dir_map p
  let gen_maxc delta p theta =
    let dir = Map.Poly.find_exn Config.dir_map p in
    let sort = Map.Poly.find_exn delta p in
    let args, senv = CHCOpt.Problem.mk_fresh_args sort in
    Map.Poly.of_alist_exn senv,
    ExtTerm.beta_reduction
      (CHCOpt.Problem.genc ~is_pos:true dir delta theta (p, sort))
      args
  let improve (delta:sort_env_map) (priority:tvar list) theta =
    if Config.point_wise then
      let geqs, gts, env =
        List.unzip3 @@
        List.map priority ~f:(fun p ->
            let sort = Map.Poly.find_exn delta p in
            let args, senv = CHCOpt.Problem.mk_fresh_args sort in
            let dir = Map.Poly.find_exn Config.dir_map p in
            let geq =
              ExtTerm.mk_forall senv @@
              (ExtTerm.beta_reduction @@
               CHCOpt.Problem.genc ~is_pos:true dir delta theta (p, sort))
                args
            in
            let mp = mk_ne_tvar p in
            let gt =
              ExtTerm.mk_forall senv @@
              ExtTerm.imply_of
                (ExtTerm.beta_reduction(*ToDo*)
                   (ExtTerm.mk_lambda senv @@ ExtTerm.mk_var_app mp args)
                   args)
                (ExtTerm.beta_reduction
                   (CHCOpt.Problem.genc ~is_pos:false (CHCOpt.Problem.reverse_direction dir)
                      delta theta (p, sort))
                   args)
            in
            geq, gt, (mp, sort))
      in
      ExtTerm.and_of @@ (ExtTerm.or_of gts :: geqs),
      Map.Poly.of_alist_exn env
    else
      let rec inner theta = function
        | [] -> ExtTerm.mk_bool false, Map.Poly.empty
        | p :: priority ->
          let sort = Map.Poly.find_exn delta p in
          let dir = Map.Poly.find_exn Config.dir_map p in
          let args, senv = CHCOpt.Problem.mk_fresh_args sort in
          let pnext, nepvs = inner theta priority in
          let geq =
            ExtTerm.mk_forall senv @@
            ExtTerm.beta_reduction
              (CHCOpt.Problem.genc ~is_pos:true dir delta theta (p, sort))
              args
          in
          let mp = mk_ne_tvar p in
          let gt =
            ExtTerm.mk_forall senv @@
            ExtTerm.imply_of
              (ExtTerm.mk_var_app mp args)
              (ExtTerm.beta_reduction
                 (CHCOpt.Problem.genc ~is_pos:false (CHCOpt.Problem.reverse_direction dir)
                    delta theta (p, sort))
                 args)
          in
          let leq =
            ExtTerm.mk_forall senv @@
            ExtTerm.beta_reduction
              (CHCOpt.Problem.genc ~is_pos:true (CHCOpt.Problem.reverse_direction dir)
                 delta theta (p, sort))
              args
          in
          (*ToDo:
            ExtTerm.or_of [ExtTerm.and_of [geq; gt]; ExtTerm.and_of [leq; pnext]]],
          *)
          ExtTerm.and_of [geq; ExtTerm.or_of [gt; ExtTerm.and_of [leq; pnext]]],
          Map.Poly.add_exn nepvs ~key:mp ~data:sort
      in
      inner theta priority
end

let make verbose dir_map point_wise =
  (module Make (struct
       let dir_map = dir_map
       let verbose = verbose
       let point_wise = point_wise
     end) : NonOptChecker.NonOptCheckerType)
