open Core
open Common.Ext
open Ast

type logic_type = Any | Lia | BV | Reals | Arrays | RE

let logic_type_of_str = function
  | "LIA" | "SAT" -> Lia
  | "BV" -> BV
  | "Reals" -> Reals
  | "Arrays" -> Arrays
  | "RE" -> RE
  | _ -> Any

type symbol = string
type sort = symbol * Logic.Sort.t

module type TermType = sig
  val logic_of : unit -> logic_type
  val str_of : Logic.term -> string
  val str_of_sym : Logic.sym -> string
  val str_of_sort : Logic.Sort.t -> string
end

module CFG (Term : TermType) : sig
  type identifier = Identifier of Logic.term

  type bfTerm =
    | Id of identifier
    | Lit of Logic.term
    | Fun of identifier * bfTerm list

  type gTerm =
    | Constant of Logic.Sort.t
    | Variable of Logic.Sort.t
    | BfTerm of bfTerm

  type rule = gTerm list
  type t = symbol * (symbol, Logic.Sort.t * rule) Map.Poly.t

  (* constructor *)
  val mk_cfg : symbol -> (symbol, Logic.Sort.t * rule) Map.Poly.t -> t
  val mk_gTerm_constant : Logic.Sort.t -> gTerm
  val mk_gTerm_variable : Logic.Sort.t -> gTerm
  val mk_gTerm_bfTerm : bfTerm -> gTerm
  val mk_identifier : Logic.term -> identifier
  val mk_bfTerm_identifier : identifier -> bfTerm
  val mk_bfTerm_identifier_of_term : Logic.term -> bfTerm
  val mk_bfTerm_literal : Logic.term -> bfTerm
  val mk_bfTerm_fun : identifier -> bfTerm list -> bfTerm
  val mk_symbol : string -> symbol
  val starting_symbol : t -> symbol
  val sort_of_symbol : t -> symbol -> Logic.Sort.t
  val rule_of_symbol : t -> symbol -> rule
  val str_of_rule : rule -> string
  val str_of : t -> string
end = struct
  type identifier = Identifier of Logic.term

  type bfTerm =
    | Id of identifier
    | Lit of Logic.term
    | Fun of identifier * bfTerm list

  type gTerm =
    | Constant of Logic.Sort.t
    | Variable of Logic.Sort.t
    | BfTerm of bfTerm

  type rule = gTerm list
  type t = symbol * (symbol, Logic.Sort.t * rule) Map.Poly.t

  let mk_cfg start symbols = (start, symbols)
  let mk_gTerm_constant sort = Constant sort
  let mk_gTerm_variable sort = Variable sort
  let mk_gTerm_bfTerm bfTerm = BfTerm bfTerm
  let mk_identifier term = Identifier term
  let mk_bfTerm_identifier id = Id id
  let mk_bfTerm_identifier_of_term term = Id (Identifier term)
  let mk_bfTerm_literal term = Lit term
  let mk_bfTerm_fun id bfterms = Fun (id, bfterms)
  let mk_symbol symbol = symbol
  let starting_symbol = function sym, _ -> sym

  let sort_of_symbol cfg symbol =
    match cfg with
    | _, map -> (
        match Map.Poly.find map symbol with
        | Some (sort, _) -> sort
        | None -> failwith @@ sprintf "%s is not defined in the grammar" symbol)

  let rule_of_symbol cfg symbol =
    match cfg with
    | _, map -> (
        match Map.Poly.find map symbol with
        | Some (_, rule) -> rule
        | None -> failwith @@ sprintf "%s is not defined in the grammar" symbol)

  let rec str_of_bfTerm = function
    | Id (Identifier term) | Lit term -> Term.str_of term
    | Fun (Identifier sym, bfTerms) ->
        String.paren
        @@ sprintf "%s %s" (Term.str_of sym)
             (String.concat_map_list ~sep:" " ~f:str_of_bfTerm bfTerms)

  let str_of_gTerm = function
    | Constant sort -> sprintf "Constant %s" (Term.str_of_sort sort)
    | Variable sort -> sprintf "Variable %s" (Term.str_of_sort sort)
    | BfTerm bfTerm -> sprintf "%s" (str_of_bfTerm bfTerm)

  let str_of_rule rule =
    String.concat_map_list ~sep:"\n   " ~f:str_of_gTerm rule |> sprintf "   %s"

  let str_of = function
    | sym, map ->
        Map.Poly.to_alist map
        |> String.concat_map_list ~sep:"\n" ~f:(fun (sym, (sort, rule)) ->
               sprintf "%s : %s\n%s" sym (Term.str_of_sort sort)
                 (str_of_rule rule))
        |> sprintf "starting symbol : %s\n%s" sym
end

module Make (Term : TermType) : sig
  type t =
    (Ident.tvar, Logic.Sort.t * CFG(Term).t option) Map.Poly.t
    * Logic.sort_env_map
    * Logic.term list

  (* constructor *)
  val mk_problem :
    (Ident.tvar, Logic.Sort.t * CFG(Term).t option) Map.Poly.t ->
    Logic.sort_env_map ->
    Logic.term list ->
    t

  val add_synth_fun : t -> Ident.tvar -> Logic.Sort.t -> CFG(Term).t option -> t
  val add_declared_var : t -> Ident.tvar -> Logic.Sort.t -> t
  val add_constraint : t -> Logic.term -> t
  val logic_of : unit -> logic_type

  val find_synth_fun_of :
    t -> Ident.tvar -> (Logic.Sort.t * CFG(Term).t option) option

  val str_of : t -> string
end = struct
  module CFG = CFG (Term)

  type t =
    (Ident.tvar, Logic.Sort.t * CFG.t option) Map.Poly.t
    * Logic.sort_env_map
    * Logic.term list

  let mk_problem synth_funs declared_vars constraints =
    (synth_funs, declared_vars, constraints)

  let add_synth_fun (synth_funs, declared_vars, constraints) sym sort cfg =
    ( Map.Poly.add_exn synth_funs ~key:sym ~data:(sort, cfg),
      declared_vars,
      constraints )

  let add_declared_var (synth_funs, declared_vars, constraints) sym sort =
    (synth_funs, Map.Poly.add_exn declared_vars ~key:sym ~data:sort, constraints)

  let add_constraint (synth_funs, declared_vars, constraints) constr =
    (synth_funs, declared_vars, constr :: constraints)

  let logic_of = Term.logic_of

  let find_synth_fun_of (synth_funs, _declared_vars, _constraints) symbol =
    Map.Poly.find synth_funs symbol

  let str_of_synth_funs map =
    Map.Poly.to_alist map
    |> List.fold ~init:"" ~f:(fun acc (sym, (sort, cfg)) ->
           sprintf "%s\n%s, (%s) %s" acc (Ident.name_of_tvar sym)
             (Term.str_of_sort sort)
             (match cfg with Some cfg -> CFG.str_of cfg | None -> ""))

  let str_of_declared_vars map =
    Map.Poly.to_alist map
    |> List.fold ~init:"" ~f:(fun acc (sym, sort) ->
           sprintf "%s\n%s, (%s)" acc (Ident.name_of_tvar sym)
             (Term.str_of_sort sort))

  let str_of_constraints constraints =
    List.fold ~init:"" constraints ~f:(fun acc constr ->
        sprintf "%s\nconstraint : %s" acc (Term.str_of constr))

  let str_of = function
    | synth_funs, declared_vars, constraints ->
        sprintf
          "***** synth_funs *****\n\
           %s\n\n\
           ***** declared_vars *****\n\
           %s\n\n\
           ***** constraints *****\n\
           %s\n\n\
          \ ***************\n"
          (str_of_synth_funs synth_funs)
          (str_of_declared_vars declared_vars)
          (str_of_constraints constraints)
end

module ExtTerm : TermType = struct
  let logic_of () = Lia
  let str_of = Logic.ExtTerm.str_of
  let str_of_sym = Logic.ExtTerm.str_of_sym
  let str_of_sort = Logic.ExtTerm.str_of_sort
end
