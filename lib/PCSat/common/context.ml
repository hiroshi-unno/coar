(* The state a PCSat solve can carry over to the next one on the same
   context: the example graph, the truth tables, the problem and its sort
   environment, as one [version], with a stack for incremental [push]/[pop].

   [significant_version_of t pcsp] starts a solve of [pcsp] from the current
   version when there is one, keeping the examples of the clauses [pcsp]
   still has and the truth tables of the predicates whose sort is unchanged
   ([remove_unused]); otherwise it starts empty.  [isolated] runs a solve of
   a different problem without reading or overwriting the current version. *)
open Core
open Ast
open Ident
open Common.Ext

type version = {
  graph : ClauseGraph.t;
  truth_table : TruthTable.t;
  problem : PCSP.Problem.t;
  senv : Logic.sort_env_map;
}

type t = { version_stack : version Stack.t; mutable version : version option }

module type ContextType = sig
  val context : t
end

let create_version pcsp =
  {
    graph = ClauseGraph.create ();
    truth_table = TruthTable.create ();
    problem = pcsp;
    senv = PCSP.Problem.senv_of pcsp;
  }

let create () = { version_stack = Stack.create (); version = None }

let reset t =
  Stack.clear t.version_stack;
  t.version <- None

let version_of version (vs : VersionSpace.t) : version =
  {
    graph = vs.examples;
    truth_table = vs.truth_table;
    problem = version.problem;
    senv = version.senv;
  }

let set_version t v = t.version <- Some v
let clear_version t = t.version <- None

(* Run [f] as a solve that neither reads nor leaves behind this context's
   current version: the version is cleared before [f] and put back on every
   exit, raising included.  A solve started on a context whose version is set
   reuses that version's example graph and truth tables (what an incremental
   caller wants), so a solve of a DIFFERENT problem run in between -- a nested
   solve of an instance, from inside the preprocessing of the problem the next
   solve is about -- would otherwise hand its examples to that next solve,
   which then starts from data about a problem it was never asked. *)
let isolated t f =
  let saved = t.version in
  t.version <- None;
  match f () with
  | v ->
      t.version <- saved;
      v
  | exception e ->
      t.version <- saved;
      raise e

let push t =
  match t.version with
  | Some version -> Stack.push t.version_stack version
  | None -> ()

let remove_unused old_version new_version =
  (*We assume new_version has a pcsp problem *)
  let old_senv = old_version.senv in
  let new_senv = new_version.senv in
  Map.Poly.iteri old_senv ~f:(fun ~key:(Tvar v) ~data ->
      let tvar = Tvar v in
      let pvar = Pvar v in
      if
        (not (Map.Poly.mem new_senv tvar))
        || Stdlib.( <> ) (Map.Poly.find_exn new_senv tvar) data
      then Hashtbl.Poly.remove old_version.truth_table pvar
      else if Hashtbl.Poly.mem old_version.truth_table pvar then
        Hashtbl.Poly.set ~key:pvar
          ~data:(Hashtbl.Poly.find_exn old_version.truth_table pvar)
          new_version.truth_table);
  let new_clauses =
    PCSP.Problem.clauses_of new_version.problem
    |> Set.Poly.map ~f:ClauseGraph.mk_clause
  in
  let old_clauses =
    PCSP.Problem.clauses_of old_version.problem
    |> Set.Poly.map ~f:ClauseGraph.mk_clause
  in
  let rm_vertexs =
    Set.filter old_clauses ~f:(fun v ->
        not @@ Set.exists new_clauses ~f:(fun v1 -> ClauseGraph.V.equal v v1))
    |> fun vss -> Set.add vss ClauseGraph.Dummy
  in
  (* print_endline @@ sprintf "rm_vertexs(clauses):%d" (Set.length rm_vertexs); *)
  (* print_endline @@ sprintf "%s" (String.concat_map_set ~sep:"\n" ~f:(ClauseGraph.str_of_vertex old_senv) rm_vertexs); *)
  Set.iter rm_vertexs ~f:(fun v ->
      ClauseGraph.remove_succ old_version.senv old_version.graph v);
  let new_graph = ClauseGraph.clone old_version.graph in
  { new_version with graph = new_graph; senv = new_senv }

let pop t =
  (* assert (1 < Stack.length t.version_stack); *)
  let open Option.Monad_infix in
  t.version >>= fun version ->
  Stack.pop t.version_stack >>= fun old_version ->
  let new_version = remove_unused version old_version in
  t.version <- Some new_version;
  t.version

let significant_version_of t pcsp =
  match t.version with
  | None -> create_version pcsp
  | Some version -> remove_unused version (create_version pcsp)

let set_version_space version vs =
  vs
  |> VersionSpace.set_examples version.graph
  |> VersionSpace.set_truth_table version.truth_table

let show_graph ?(pre = "") ~id = function
  | Some t -> ClauseGraph.output_graph ~pre ~id t.graph t.senv
  | _ -> ()
