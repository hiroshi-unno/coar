open Core
open Common.Combinator

type t = Cnf of clause list
and clause = string list * string list (* negatives * positives *)

let make clauses = Cnf clauses

let input_line_exn gz_in =
  let buffer = Buffer.create 128 in
  let rec read_line () =
    match Gzip.input_char gz_in with
    | '\n' -> Buffer.contents buffer
    | c ->
        Buffer.add_char buffer c;
        read_line ()
    | exception End_of_file ->
        if Buffer.length buffer = 0 then raise End_of_file
        else Buffer.contents buffer
  in
  read_line ()

let from_dimacs_file filename =
  let ic = In_channel.create ~binary:false filename in
  let res =
    make @@ snd
    @@ Parser.parse ~no_quant:true [] [] [] (fun () ->
           In_channel.input_line_exn ic)
  in
  In_channel.close ic;
  res

let from_gzipped_dimacs_file filename =
  let ic = Gzip.open_in filename in
  let res =
    make @@ snd
    @@ Parser.parse ~no_quant:true [] [] [] (fun () -> input_line_exn ic)
  in
  Gzip.close_in ic;
  res

let of_prop_formula = Ast.PropLogic.Formula.cnf_of >> make
let clauses_of (Cnf l) = l
let tvar_of n = Ast.Ident.Tvar ("x" ^ n)

let term_of_clause (nl, pl) =
  let open Ast.Logic in
  BoolTerm.or_of
  @@ List.map nl ~f:(fun s -> BoolTerm.neg_of @@ Term.mk_var (tvar_of s))
  @ List.map pl ~f:(fun s -> Term.mk_var (tvar_of s))

let term_of ?(quant = true) =
  let open Ast.Logic in
  function
  | Cnf clauses ->
      let t = BoolTerm.and_of @@ List.map clauses ~f:term_of_clause in
      if quant then
        let fvs = Term.fvs_of t in
        BoolTerm.exists
          (List.map (Set.to_list fvs) ~f:(fun x -> (x, BoolTerm.SBool)))
          t
      else t

type soft = (t * int) list

type solution = Sat of assign | Unsat | Unknown
and assign = (string * bool) list

let assign_of_sol = function Sat a -> a | _ -> []
let sol_of_assign l = Sat l

type incsol =
  | IncSat of assign * (?print_sol:bool -> t -> incsol)
  | IncUnsat
  | IncUnknown

let str_of_clause (neg, pos) =
  let negstr =
    List.fold_left neg ~init:"/\\ (" ~f:(fun res str -> res ^ "-" ^ str ^ "\\/")
  in
  let posstr =
    List.fold_left pos ~init:"" ~f:(fun res str -> res ^ str ^ "\\/")
  in
  negstr ^ posstr ^ "\b\b) \n"

let str_of =
  clauses_of
  >> List.fold_left ~init:"" ~f:(fun res (neg, pos) ->
         res ^ str_of_clause (neg, pos))

let str_of_assign assign =
  let rec aux acc = function
    | [] -> acc
    | (v, true) :: tl -> aux (acc ^ " " ^ v) tl
    | (v, false) :: tl -> aux (acc ^ " -" ^ v) tl
  in
  aux "" assign

let str_of_solution ?(verbose = false) = function
  | Sat assign -> if verbose then "sat\n" ^ str_of_assign assign else "sat"
  | Unsat -> "unsat"
  | Unknown -> "unknown"

let str_of_incsol ?(verbose = false) = function
  | IncSat (assign, _) ->
      if verbose then "sat\n" ^ str_of_assign assign else "sat"
  | IncUnsat -> "unsat"
  | IncUnknown -> "unknown"

let minimize_core_cnf cnf solution =
  let clauses = clauses_of cnf in
  let vars =
    List.dedup_and_sort ~compare:Stdlib.compare @@ List.map solution ~f:fst
  in
  let pos_edge_of v =
    List.filter clauses ~f:(fun (_, pos) -> List.mem pos v ~equal:Stdlib.( = ))
  in
  let neg_edge_of v =
    List.filter clauses ~f:(fun (neg, _) -> List.mem neg v ~equal:Stdlib.( = ))
  in
  let edges = List.map vars ~f:(fun v -> (v, (neg_edge_of v, pos_edge_of v))) in
  let assignments =
    let assess_of edges (var, value) =
      let neg, pos = List.Assoc.find_exn edges var ~equal:Stdlib.( = ) in
      List.length @@ if value then pos else neg
    in
    List.sort solution ~compare:(fun a b ->
        Stdlib.compare (assess_of edges b) (assess_of edges a))
  in
  let rec greedy_search remain used not_used =
    match remain with
    | [] -> used
    | remain -> (
        match not_used with
        | [] -> used
        | (var, value) :: not_used ->
            let is_solved (neg, pos) =
              List.mem (if value then pos else neg) var ~equal:Stdlib.( = )
            in
            let remain = List.filter ~f:(Fn.non is_solved) remain in
            greedy_search remain ((var, value) :: used) not_used)
  in
  greedy_search clauses [] assignments

let minimize_core clauses solution =
  let clauses = Ast.PropLogic.Formula.(clauses |> nnf_of |> cnf_of) in
  minimize_core_cnf (make clauses) solution
