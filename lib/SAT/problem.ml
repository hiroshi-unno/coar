open Core

type t = Cnf of clause list
and clause = string list * string list
(* negatives * positives *)

type soft = (t * int) list

type solution = Sat of assign | Unsat
and assign = (string * bool) list

type incsol = IncSat of assign * (?print_sol:bool -> t -> incsol) | IncUnsat

let of_list = function clauses -> Cnf clauses
let to_list = function Cnf l -> l
let assign_of = function Sat a -> a | _ -> []
let solution_of l = Sat l

let str_of_clause (neg, pos) =
  let negstr =
    List.fold_left neg ~init:"/\\ (" ~f:(fun res str -> res ^ "-" ^ str ^ "\\/")
  in
  let posstr =
    List.fold_left pos ~init:"" ~f:(fun res str -> res ^ str ^ "\\/")
  in
  negstr ^ posstr ^ "\b\b) \n"

let str_of t =
  to_list t
  |> List.fold_left ~init:"" ~f:(fun res (neg, pos) ->
         res ^ str_of_clause (neg, pos))

let assess_of edges (var, value) =
  let neg, pos = List.Assoc.find_exn edges var ~equal:Stdlib.( = ) in
  List.length @@ if value then pos else neg

let minimize_core_cnf cnf solution =
  let clauses = to_list cnf in
  let vars =
    List.map ~f:fst solution |> List.dedup_and_sort ~compare:Stdlib.compare
  in
  let pos_edge_of v =
    List.filter ~f:(fun (_, pos) -> List.mem pos v ~equal:Stdlib.( = )) clauses
  in
  let neg_edge_of v =
    List.filter ~f:(fun (neg, _) -> List.mem neg v ~equal:Stdlib.( = )) clauses
  in
  let edges = List.map ~f:(fun v -> (v, (neg_edge_of v, pos_edge_of v))) vars in
  let assignments =
    List.sort
      ~compare:(fun a b ->
        Stdlib.compare (assess_of edges b) (assess_of edges a))
      solution
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
  minimize_core_cnf (of_list clauses) solution

let str_of_assign assign =
  let rec aux acc = function
    | [] -> acc
    | (v, true) :: tl -> aux (acc ^ " " ^ v) tl
    | (v, false) :: tl -> aux (acc ^ " -" ^ v) tl
  in
  aux "" assign

let str_of_solution_verbose = function
  | Sat assign -> "sat\n" ^ str_of_assign assign
  | Unsat -> "unsat"

let str_of_solution = function Sat _ -> "sat" | Unsat -> "unsat"

let str_of_incsol_verbose = function
  | IncSat (assign, _) -> "sat\n" ^ str_of_assign assign
  | IncUnsat -> "unsat"

let str_of_incsol = function IncSat _ -> "sat" | IncUnsat -> "unsat"
let of_prop_formula phi = of_list @@ Ast.PropLogic.Formula.cnf_of phi
