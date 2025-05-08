open Core
open Common.Ext
open Common.Combinator

type t = DQSAT of SAT.Parser.quant list * SAT.Problem.clause list

let make quants clauses = DQSAT (quants, clauses)

let from_dqdimacs_file filename =
  let ic = In_channel.create ~binary:false filename in
  let res =
    uncurry2 make
    @@ SAT.Parser.parse ~no_quant:false [] [] [] (fun () ->
           In_channel.input_line_exn ic)
  in
  In_channel.close ic;
  res

let from_gzipped_dqdimacs_file filename =
  let ic = Gzip.open_in filename in
  let res =
    uncurry2 make
    @@ SAT.Parser.parse ~no_quant:false [] [] [] (fun () ->
           SAT.Problem.input_line_exn ic)
  in
  Gzip.close_in ic;
  res

let term_of ?(quant = true) =
  let open Ast.Logic in
  function
  | DQSAT (quants, clauses) ->
      let senvs, esenv_sub_s =
        List.partition_map quants ~f:(function
          | First ns ->
              First
                (List.map ns ~f:(fun n ->
                     (true, SAT.Problem.tvar_of n, BoolTerm.SBool)))
          | Second (ns, None) ->
              First
                (List.map ns ~f:(fun n ->
                     (false, SAT.Problem.tvar_of n, BoolTerm.SBool)))
          | Second (ns, Some dns) ->
              let dns_set = Set.Poly.of_list dns in
              let sorts =
                List.map (Set.to_list dns_set) ~f:(fun n ->
                    (SAT.Problem.tvar_of n, BoolTerm.SBool))
              in
              let fun_sort =
                Sort.mk_fun @@ List.map sorts ~f:snd @ [ BoolTerm.SBool ]
              in
              let sub =
                Map.Poly.of_alist_exn
                @@ List.map ns ~f:(fun n ->
                       ( SAT.Problem.tvar_of n,
                         Term.mk_var_app (SAT.Problem.tvar_of n)
                         @@ List.map sorts ~f:(fst >> Term.mk_var) ))
              in
              Second
                ( List.map ns ~f:(fun n -> (SAT.Problem.tvar_of n, fun_sort)),
                  sub ))
      in
      let esenvs, subs = List.unzip esenv_sub_s in
      let t =
        Term.subst (Map.force_merge_list subs)
        @@ SAT.Problem.term_of ~quant:false
        @@ SAT.Problem.Cnf clauses
      in
      let t =
        BoolTerm.mk_exists (List.concat esenvs)
        @@ List.fold_right (List.concat senvs) ~init:t ~f:(fun (uni, x, s) t ->
               BoolTerm.mk_bind (if uni then Forall else Exists) x s t)
      in
      if quant then
        let fvs = Term.fvs_of t in
        BoolTerm.exists
          (List.map (Set.to_list fvs) ~f:(fun x -> (x, BoolTerm.SBool)))
          t
      else t

let str_of _ = failwith "not implemented"

type solution = Sat | Unsat | Unknown

let str_of_solution = function
  | Sat -> "sat"
  | Unsat -> "unsat"
  | Unknown -> "unknown"
