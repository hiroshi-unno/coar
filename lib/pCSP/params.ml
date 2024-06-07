open Core
open Ast
open Ast.Logic
open Kind

type random_info = {
  name : Ident.tvar;
  random_ex_bound : int;
  random_ex_size : int;
}

type t = {
  (* unknowns *)
  senv : sort_env_map;
  kind_map : Kind.map;
  (* defined *)
  id : int option;
  fenv : LogicOld.FunEnv.t;
  dtenv : LogicOld.DTEnv.t;
  sol_space : SolSpace.t;
  messenger : Common.Messenger.t option;
  args_record : (Ident.pvar, bool array * Logic.Sort.t list) Map.Poly.t;
  sol_for_eliminated : Logic.term_subst_map;
  stable_clauses : ClauseSet.t;
  partial_sol_targets : (Ident.tvar, random_info Set.Poly.t) Map.Poly.t;
  dep_graph : (Ident.tvar, Ident.tvar Set.Poly.t) Map.Poly.t;
}

let id = Atomic.make 0
let new_id () = Option.some @@ (Atomic.fetch_and_add id 1 + 1)
let is_kind t is_kind tvar : bool = is_kind @@ Map.Poly.find_exn t.kind_map tvar

let mk_random_info name random_ex_bound random_ex_size =
  { name; random_ex_bound; random_ex_size }

let empty =
  {
    senv = Map.Poly.empty;
    id = None;
    messenger = None;
    sol_space = Map.Poly.empty;
    kind_map = Map.Poly.empty;
    fenv = Map.Poly.empty;
    dtenv = Map.Poly.empty;
    args_record = Map.Poly.empty;
    sol_for_eliminated = Map.Poly.empty;
    stable_clauses = Set.Poly.empty;
    partial_sol_targets = Map.Poly.empty;
    dep_graph = Map.Poly.empty;
  }

let make ?(kind_map = Map.Poly.empty) ?(fenv = Map.Poly.empty)
    ?(dtenv = Map.Poly.empty) ?(id = None) ?(messenger = None)
    ?(sol_space = Map.Poly.empty) ?(args_record = Map.Poly.empty)
    ?(sol_for_eliminated = Map.Poly.empty) ?(stable_clauses = Set.Poly.empty)
    ?(partial_sol_targets = Map.Poly.empty) ?(dep_graph = Map.Poly.empty) senv =
  let kind_map =
    Map.Poly.fold senv ~init:kind_map ~f:(fun ~key ~data:_ acc ->
        if Map.Poly.mem acc key then acc
        else Map.Poly.add_exn acc ~key ~data:Ord)
  in
  {
    senv;
    kind_map;
    id;
    messenger;
    sol_space;
    fenv;
    dtenv;
    args_record;
    sol_for_eliminated;
    stable_clauses;
    partial_sol_targets;
    dep_graph;
  }
