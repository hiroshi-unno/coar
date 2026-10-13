open Core
open Ast
open Ast.Logic
open Kind
open Common.Ext

type random_info = {
  name : Ident.tvar;
  random_ex_bound : int;
  random_ex_size : int;
}

type preds_argnames_map = (Ident.pvar, Ident.tvar list) Map.Poly.t

(* Why the preprocessor gave an eliminated predicate the definition it did.
   The definitions are of two logical kinds and the term alone does not say
   which: [Forced], [LbValid] and [UbUnsat] are *implied* by the original
   clauses, so a checker can re-derive them with one query; the rest only
   preserve satisfiability -- every model of the original problem can be
   *changed* to satisfy them -- which is a forall-exists statement no single
   query expresses, and what a checker can verify instead is the rule's own
   side condition. *)
type elim_reason =
  | Forced  (** [P := lb] because [lb <=> ub] is valid *)
  | LbValid  (** [P := true] because the lower bound is valid *)
  | UbUnsat  (** [P := false] because the upper bound is unsatisfiable *)
  | OneSidedNoLB  (** [P := false]: no positive occurrence, so [P] may shrink *)
  | OneSidedNoUB  (** [P := true]: no negative occurrence, so [P] may grow *)
  | TrivKind  (** [P := true]: an NWF/Parity family member on no cycle *)
  | FnOneSided
      (** an [FN] predicate that every clause used only as a premise, replaced
          by an existential over its result: no definition is recorded, because
          the witness is *chosen* per argument tuple and need not be expressible
      *)
  | Unused  (** the residue after the other steps: no constraint mentions it *)
[@@deriving yojson]

let str_of_elim_reason = function
  | Forced -> "lb <=> ub valid"
  | LbValid -> "lower bound valid"
  | UbUnsat -> "upper bound unsatisfiable"
  | OneSidedNoLB -> "no positive occurrence"
  | OneSidedNoUB -> "no negative occurrence"
  | TrivKind -> "family member on no cycle"
  | FnOneSided -> "one-sided functional predicate, replaced by an existential"
  | Unused -> "unconstrained residue"

type t = {
  (* unknowns *)
  senv : sort_env_map; (* Identifier -> sort *)
  arg_original_names : preds_argnames_map;
  kind_map : Kind.map;
  (* defined *)
  id : int option;
  fenv : LogicOld.FunEnv.t;
  dtenv : LogicOld.DTEnv.t;
  sol_space : SolSpace.t;
  messenger : Common.Messenger.t option;
  args_record : (Ident.pvar, bool array * Logic.Sort.t list) Map.Poly.t;
  sol_for_eliminated : Logic.term_subst_map;
  elimination_reasons : (Ident.tvar, elim_reason * int) Map.Poly.t;
  (* why each entry of [sol_for_eliminated] was given its definition, and
         in which order the steps committed: a checker needs the reason to know
         which of the two conditions above to apply, and the order because
         the steps compose -- a one-sided elimination removes every clause
         mentioning its predicate, so the condition of a later one is visible
         only once those clauses are gone.  A missing entry means the step did
         not record one. *)
  (* definitions of the predicates removed by resolution; unlike
     [sol_for_eliminated] they mention other predicates and are only used to
     complete the final answer *)
  sol_for_resolved : (Ident.tvar, Logic.term Lazy.t) Map.Poly.t;
  erasure_trail : (Ident.pvar, ([ `RAF | `FAR ] * int list) list) Map.Poly.t;
      (* the dimension reducer's committed erasures per predicate, in order:
         the phase (RAF: the predicate is only queried at fresh values there,
         so the reduced predicate is [exists x. P]; FAR: only defined at fresh
         values, [forall x. P]) and the erased positions by original index.
         Lets a checker define the reduced predicate from the original one. *)
  stable_clauses : ClauseSet.t;
  partial_sol_targets : (Ident.tvar, random_info Set.Poly.t) Map.Poly.t;
  dep_graph : (Ident.tvar, Ident.tvar_set) Map.Poly.t;
  candidate_atoms : (Ident.tvar, candidate_atoms) Map.Poly.t;
      (* atoms the input declared as candidates for an unknown (hints for the
         hypothesis space, never constraints); see [candidate_atoms_at] *)
}

(* The candidate atoms declared for one unknown: a parameter list and atoms
   over it.  The atoms may also mention symbols the whole problem shares --
   universally quantified functions and constants -- but no other variable.
   They are hints: nothing asserts them, so they cannot change which
   interpretations satisfy the problem, and every use of one (a qualifier, a
   first candidate) is validated against the clauses like anything else the
   synthesizer proposes.

   The parameter list is the unknown's signature when the entry was made.  A
   preprocessing step that drops argument positions of an unknown and keeps its
   name records them in [args_record] and leaves this entry alone;
   [candidate_atoms_at] applies the record.  A step that replaces an unknown by
   a new one over some of its arguments moves the entry
   ([move_candidate_atoms]).  An unknown eliminated outright keeps its entry,
   which then names nothing in [senv] and is never read.  Any other change of
   signature is caught by comparing sorts at the use site, and the atoms are
   then not used rather than read at the wrong positions. *)
and candidate_atoms = LogicOld.sort_env_list * LogicOld.Formula.t list

let id = Atomic.make 0
let new_id () = Option.some (Atomic.fetch_and_add id 1 + 1)
let is_kind t is_kind tvar : bool = is_kind @@ Map.Poly.find_exn t.kind_map tvar

(* The unknowns are two maps keyed alike, with [senv ⊆ dom(kind_map)] maintained
   by hand: [make] establishes it and every [{ params with senv = ... }] can
   break it.  The converse is *not* an invariant -- [Kind.kind_map_of_nwf]
   registers every NWF/Parity tag pair up front, most of which never enter
   [senv] -- so this checks the one direction that holds.  Drift in it fails
   in two different ways depending on the reader: [kindpvs_of_aux] filters
   silently, [is_kind] above raises from [find_exn].  This measurement is what
   to have before the two maps are merged into one. *)
let unknowns_without_kind t =
  Set.diff (Map.key_set t.senv) (Map.key_set t.kind_map)
let tvars_of senv : Ident.tvar list = Map.Poly.keys senv

let str_of_arg_original_names ~pvar_sep ~tvar_sep ~pvar_tvar_delim
    arg_original_names =
  arg_original_names |> Map.Poly.to_alist
  |> List.map ~f:(fun (key, data) ->
      Ident.str_of_pvar key ^ pvar_tvar_delim
      ^ Ident.str_of_tvar_list ~sep:tvar_sep data)
  |> String.concat ~sep:pvar_sep

let mk_random_info name random_ex_bound random_ex_size =
  { name; random_ex_bound; random_ex_size }

let empty =
  {
    senv = Map.Poly.empty;
    arg_original_names = Map.Poly.empty;
    id = None;
    messenger = None;
    sol_space = Map.Poly.empty;
    kind_map = Map.Poly.empty;
    fenv = Map.Poly.empty;
    dtenv = Map.Poly.empty;
    args_record = Map.Poly.empty;
    sol_for_eliminated = Map.Poly.empty;
    elimination_reasons = Map.Poly.empty;
    sol_for_resolved = Map.Poly.empty;
    erasure_trail = Map.Poly.empty;
    stable_clauses = Set.Poly.empty;
    partial_sol_targets = Map.Poly.empty;
    dep_graph = Map.Poly.empty;
    candidate_atoms = Map.Poly.empty;
  }

let make ?(arg_original_names = Map.Poly.empty) ?(kind_map = Map.Poly.empty)
    ?(fenv = Map.Poly.empty) ?(dtenv = Map.Poly.empty) ?(id = None)
    ?(messenger = None) ?(sol_space = Map.Poly.empty)
    ?(args_record = Map.Poly.empty) ?(sol_for_eliminated = Map.Poly.empty)
    ?(elimination_reasons = Map.Poly.empty) ?(sol_for_resolved = Map.Poly.empty)
    ?(erasure_trail = Map.Poly.empty) ?(stable_clauses = Set.Poly.empty)
    ?(partial_sol_targets = Map.Poly.empty) ?(dep_graph = Map.Poly.empty)
    ?(candidate_atoms = Map.Poly.empty) senv =
  let kind_map =
    Map.Poly.fold senv ~init:kind_map ~f:(fun ~key ~data:_ acc ->
        if Map.Poly.mem acc key then acc
        else Map.Poly.add_exn acc ~key ~data:Ord)
  in
  {
    senv;
    arg_original_names;
    kind_map;
    id;
    messenger;
    sol_space;
    fenv;
    dtenv;
    args_record;
    sol_for_eliminated;
    elimination_reasons;
    sol_for_resolved;
    erasure_trail;
    stable_clauses;
    partial_sol_targets;
    dep_graph;
    candidate_atoms;
  }

(* Drop the positions [keep] rejects from a candidate-atom entry: the parameter
   list loses them and so does every atom that mentions one, since an atom about
   an argument the unknown no longer has cannot be read at any position of the
   new signature.  An atom mentioning only kept parameters is unchanged. *)
let restrict_candidate_atoms ((xs, atoms) : candidate_atoms) ~(keep : int -> bool)
    : candidate_atoms =
  let kept, dropped = List.partition_tf (List.mapi xs ~f:(fun i x -> (i, x)))
      ~f:(fun (i, _) -> keep i) in
  let dropped = Set.Poly.of_list @@ List.map dropped ~f:(fun (_, (x, _)) -> x) in
  ( List.map kept ~f:snd,
    List.filter atoms ~f:(fun phi ->
        Set.are_disjoint dropped (LogicOld.Formula.tvs_of phi)) )

(* The candidate atoms of [p] read against its current argument sorts
   [sorts]: [args_record] (positions a reducer erased, by position in the
   signature the entry was made for) applied first, then the sorts compared.
   [None] when there is no entry, and also when the sorts disagree -- a
   signature change nothing recorded, after which reading the atoms
   positionally would put them at the wrong arguments. *)
let candidate_atoms_at t (p : Ident.tvar) (sorts : LogicOld.Sort.t list) :
    candidate_atoms option =
  match Map.Poly.find t.candidate_atoms p with
  | None -> None
  | Some ((xs, _) as entry) ->
      let ((xs', _) as entry) =
        match Map.Poly.find t.args_record (Ident.tvar_to_pvar p) with
        | Some (arr, _) when Array.length arr = List.length xs ->
            restrict_candidate_atoms entry ~keep:(Array.get arr)
        | _ -> entry
      in
      if
        List.length xs' = List.length sorts
        && List.for_all2_exn xs' sorts ~f:(fun (_, s1) s2 ->
               Stdlib.(s1 = s2))
      then Some entry
      else None

(* [q] replaces [p] over the positions of [p]'s current signature that [keep]
   accepts, in order: [q]'s entry is [p]'s, restricted.  [p]'s current sorts
   are needed to read its entry ([candidate_atoms_at]). *)
let move_candidate_atoms t ~(from : Ident.tvar) ~(sorts : LogicOld.Sort.t list)
    ~(to_ : Ident.tvar) ~(keep : int -> bool) =
  match candidate_atoms_at t from sorts with
  | None -> t
  | Some entry ->
      {
        t with
        candidate_atoms =
          Map.Poly.set t.candidate_atoms ~key:to_
            ~data:(restrict_candidate_atoms entry ~keep);
      }
