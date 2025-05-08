open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* ToDo *)
module Debug = Debug.Make ((val Debug.Config.disable))

type query = Formula.t
type t = { preds : Pred.t list; query : query }
type solution = Valid | Invalid | Unknown | Timeout

let make preds query = { preds; query }
let flip_solution = function Valid -> Invalid | Invalid -> Valid | x -> x

let str_of_solution = function
  | Valid -> "valid"
  | Invalid -> "invalid"
  | Unknown -> "unknown"
  | Timeout -> "timeout"

let lts_str_of_solution = function
  | Valid -> "YES"
  | Invalid -> "NO"
  | Unknown | Timeout -> "MAYBE"

let str_of muclp =
  sprintf "%s\ns.t.\n%s"
    (Formula.str_of muclp.query)
    (Pred.str_of_list muclp.preds)

let has_only_mu muclp =
  List.for_all ~f:(fun pred -> Stdlib.( = ) pred.kind Predicate.Mu) muclp.preds

let has_only_nu muclp =
  List.for_all ~f:(fun pred -> Stdlib.( = ) pred.kind Predicate.Nu) muclp.preds

let has_only_exists muclp =
  let rec check fml =
    if Formula.is_atom fml then true
    else if Formula.is_and fml || Formula.is_or fml then
      let _, fml_left, fml_right, _ = Formula.let_binop fml in
      check fml_left && check fml_right
    else if Formula.is_forall fml then false
    else if Formula.is_exists fml then check @@ snd3 @@ Formula.let_exists fml
    else failwith "not implemented"
    (*Debug.print @@ lazy (sprintf "not implemented for: %s" @@ Formula.str_of fml)*)
  in
  List.for_all
    ~f:(Evaluator.simplify >> check)
    (muclp.query :: List.map muclp.preds ~f:(fun pred -> pred.body))

let has_only_forall muclp =
  let rec check fml =
    if Formula.is_atom fml then true
    else if Formula.is_and fml || Formula.is_or fml then
      let _, fml_left, fml_right, _ = Formula.let_binop fml in
      check fml_left && check fml_right
    else if Formula.is_forall fml then check @@ snd3 @@ Formula.let_forall fml
    else if Formula.is_exists fml then false
    else failwith "not implemented"
  in
  List.for_all ~f:check
    (muclp.query :: List.map muclp.preds ~f:(fun pred -> pred.body))

let has_no_quantifier muclp = has_only_exists muclp && has_only_forall muclp
let map_formula f muclp = make (Pred.map_list f muclp.preds) (f muclp.query)
let size_of muclp = List.length muclp.preds

let penv_of ?(init = Map.Poly.empty) muclp =
  Pred.pred_sort_env_map_of_list init muclp.preds

let get_depth_ht muclp =
  let res = Hashtbl.Poly.create ~size:(List.length muclp.preds) () in
  List.iteri muclp.preds ~f:(fun i pred ->
      Hashtbl.Poly.add_exn res ~key:pred.name ~data:i);
  res

let avoid_dup pvar pvars =
  if not @@ List.exists pvars ~f:(Ident.pvar_equal pvar) then pvar
  else
    let suffix = ref 2 in
    while
      List.exists pvars ~f:(fun pvar' ->
          Ident.pvar_equal pvar'
            (Ident.Pvar (Ident.name_of_pvar pvar ^ string_of_int !suffix)))
    do
      suffix := !suffix + 1
    done;
    Ident.Pvar (Ident.name_of_pvar pvar ^ string_of_int !suffix)

let aconv_tvar muclp =
  make
    (List.map muclp.preds ~f:(fun pred ->
         let map, args =
           List.unzip
           @@ List.map pred.args ~f:(fun (x, sort) ->
                  let x' = Ident.mk_fresh_tvar () in
                  ((x, Term.mk_var x' sort), (x', sort)))
         in
         {
           pred with
           args;
           body =
             Formula.(subst (Map.Poly.of_alist_exn map) @@ aconv_tvar pred.body);
         }))
    (Formula.aconv_tvar muclp.query)

let move_quantifiers_to_front = map_formula Formula.move_quantifiers_to_front
let rm_forall = map_formula (Formula.rm_quant ~forall:true >> snd)
let simplify = map_formula Evaluator.simplify
let complete_tsort = map_formula (Formula.complete_tsort Map.Poly.empty)

(* TODO : this should be applied to hes Parser *)
let complete_psort uninterp_pvs muclp =
  let map = penv_of ~init:uninterp_pvs muclp in
  map_formula (Formula.complete_psort map) muclp

let bind_fvs_with_forall muclp =
  make muclp.preds @@ Formula.bind_fvs_with_forall muclp.query

let detect_arity0_preds muclp =
  if List.exists ~f:(fun pred -> List.length pred.args = 0) muclp.preds then
    failwith "arity0 predicates is not supported."
  else make muclp.preds muclp.query

let detect_undefined_preds muclp =
  let check map formula =
    let fpv = LogicOld.Formula.pvs_of formula in
    if false then
      Debug.print
      @@ lazy
           (sprintf "fpvs: %s"
           @@ String.concat_map_set ~sep:"," fpv ~f:Ident.name_of_pvar);
    match Set.find ~f:(Map.Poly.mem map >> not) fpv with
    | Some (Ident.Pvar pid) -> failwith @@ "undefined predicates: " ^ pid
    | None -> ()
  in
  let rec mk_env map = function
    | [] -> map
    | pred :: xs ->
        mk_env (Map.Poly.add_exn map ~key:pred.Pred.name ~data:pred.name) xs
  in
  let map = mk_env Map.Poly.empty muclp.preds in
  check map muclp.query;
  List.iter muclp.preds ~f:(fun pred -> check map pred.body);
  muclp

let check_problem muclp =
  if false then
    muclp
    |> (if false then detect_arity0_preds else Fn.id)
    |> detect_undefined_preds
  else muclp
