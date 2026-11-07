open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* Seeded ground unfolding: choosing which ground instances of a problem's own
   clauses a solver holds as examples.

   The procedure.  The input is a clause set (the problem the constraint solver
   holds, after its own preprocessing), a list of SEEDS -- a variable name with
   a finite list of values -- and a list of CHOICE values.  Starting from the
   clauses with no body atom, each clause is instantiated at finitely many
   valuations of its variables: a variable fixed by an equation [x = t] of the
   clause's premise whose right-hand side is ground under the values already
   chosen takes [t]'s value (the one-point rule); a variable named after a seed
   (the same name, or failing that the same stem: the name up to its first
   ['^'] with trailing ["_<digits>"] groups removed) takes the seed's values; any
   other integer variable takes the choice values, a Boolean one both truth
   values.  A seed may also be an ATOM PATTERN, a predicate with a value or
   nothing per argument: a clause whose head applies that predicate (or the
   uninterpreted copy [U_<name>_] a reduction names) is instantiated once more
   with each head variable that the premise's equations leave open bound to
   the given value -- a proposal, never checked against anything, which finds
   the seeded instance
   where the clauses renamed the seeded variables, which a solver's
   normalisation does ([x0], [x1], ...) while keeping argument positions.  An
   instance is kept when its premise evaluates true (it is LIVE: an
   instance with a false premise is the true clause and says nothing).  The
   ground head atoms of the kept instances are REACHED; a clause with body atoms
   is instantiated, the same way, at every matching of its body atoms against
   reached atoms (semi-naive: each round matches at least one atom reached in
   the previous round).  It stops at closure, or when [atom_budget] atoms are
   reached or [atom_budget] instances kept, and returns what it has.

   Why it is sound, and the whole of what it claims.  Every instance returned
   is the clause it came from at one valuation of that clause's variables, so
   any interpretation satisfying the clause satisfies the instance: a set of
   such instances is a consequence of the clause set, whatever values were
   chosen and however the seeds were matched.  This module never concludes
   anything from the instances -- it neither evaluates the unknowns nor reports
   a refutation; a solver that holds them as examples and finds no labeling of
   them has refuted its own clauses, by its own rules.  The seeds, the stems and
   the one-point rule only choose WHICH instances; none of them carries any of
   the argument.

   What it declines.  A clause with a variable that is neither an integer nor a
   Boolean, or with an atom that does not apply an unknown, is skipped (its
   instances would need values this enumeration does not produce).  A valuation
   at which the premise or an atom's argument cannot be evaluated (an integer
   division by zero, a term the theory leaves open) is skipped: its instance
   would read an interpretation-dependent term, and evaluating it to one value
   would decide it for one model only.  A matching whose free variables have
   more than [max_combos] value combinations is skipped.  When no seed names a
   variable of any clause and no atom pattern applies to any head, nothing is
   enumerated at all: the seeds were meant for another problem, and choice
   values alone are not what was asked for. *)

type seeds = {
  seeds : (string * Value.t list) list;
      (** a variable name and the values it takes *)
  atoms : (string * Value.t option list) list;
      (** a predicate's name with a value, or nothing, per argument: an instance
          of a clause whose head applies that predicate (or its uninterpreted
          copy [U_<name>_]) with the given values is enumerated too, for where
          the clauses renamed the seeded variables *)
  choice_values : Value.t list;
      (** the values of every other integer variable no equation fixes *)
}

type matched = { by_name : bool; by_stem : bool; by_atom : bool }

let str_of_matched m =
  match
    List.filter_map
      [ (m.by_name, "name"); (m.by_stem, "stem"); (m.by_atom, "atom") ]
      ~f:(fun (b, s) -> if b then Some s else None)
  with
  | [] -> "none"
  | l -> String.concat ~sep:"+" l

let unmatched m = not (m.by_name || m.by_stem || m.by_atom)

type stats = {
  instances : int;  (** instances returned *)
  atoms : int;  (** distinct ground atoms reached *)
  rounds : int;
  matched : matched;
      (** how the seeds were used: a variable found by a seed's exact name, by
          its stem, a clause head matched by an atom pattern; none of them *)
  skipped_clauses : int;  (** clauses declined on their shape *)
  truncated : string option;
      (** [Some why] when a budget stopped the enumeration before closure *)
  exhausted : bool;
      (** the atom or instance budget stopped it (not merely a matching over too
          many combinations, which skips that matching alone) *)
  fact_vars : string list;
      (** when no seed matched: the integer variables of the clauses with no
          body atom (at most eight), to say what the seeds missed *)
}

(* [stem name]: [name] up to its first ['^'], with trailing ["_<digits>"]
   groups (and a trailing ['_']) removed: ["n^0_77"] and ["n_3"] both give
   ["n"].  A heuristic name equivalence, used only to choose values. *)
let stem name =
  let s =
    match String.index name '^' with
    | Some i -> String.prefix name i
    | None -> name
  in
  let rec strip s =
    match String.rsplit2 s ~on:'_' with
    | Some (pre, post)
      when (not (String.is_empty pre)) && String.for_all post ~f:Char.is_digit
      ->
        strip pre
    | _ -> s
  in
  strip s

type prepared = {
  index : int;  (** the clause's position in the input, naming it in keys *)
  clause : Clause.t;
  vars : (Ident.tvar * Sort.t) list;
  heads : (Ident.pvar * Term.t list) list;
  bodies : (Ident.pvar * Term.t list) list;
  pure : Formula.t;  (** the clause is [pure \/ heads \/ not bodies] *)
  premise : Formula.t list;  (** the conjuncts of [not pure], in NNF *)
  formula : Formula.t;  (** the whole clause, for building the instance *)
}

let pvar_app = function
  | Atom.App (Predicate.Var (p, _), ts, _) -> Some (p, ts)
  | _ -> None

let prepare exi_senv index (cl : Clause.t) =
  try
    let uni_senv, pos, neg, pure = Clause.to_old_clause exi_senv cl in
    let vars =
      Map.Poly.to_alist uni_senv
      |> List.map ~f:(fun (x, s) -> (x, Logic.ExtTerm.to_old_sort s))
    in
    let atoms set = List.map (Set.to_list set) ~f:pvar_app in
    let heads = atoms pos and bodies = atoms neg in
    if
      List.for_all vars ~f:(fun (_, s) ->
          Term.is_int_sort s || Term.is_bool_sort s)
      && List.for_all heads ~f:Option.is_some
      && List.for_all bodies ~f:Option.is_some
    then
      Some
        {
          index;
          clause = cl;
          vars;
          heads = List.filter_opt heads;
          bodies = List.filter_opt bodies;
          pure;
          premise =
            Formula.conjuncts_list_of @@ Formula.nnf_of
            @@ Evaluator.simplify_neg pure;
          formula = Clause.to_old_formula exi_senv cl;
        }
    else None
  with exn when not (Common.Timer.is_async exn) -> None

(* an equation of a premise conjunct: [t1 = t2], or the negation of [t1 <> t2] *)
let equation_of = function
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _)
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _),
        _ ) ->
      Some (t1, t2)
  | _ -> None

let key_of p vs =
  Ident.name_of_pvar p ^ "("
  ^ String.concat ~sep:"," (List.map vs ~f:Value.str_of)
  ^ ")"

exception Budget of string

(* [run ?kept_args ~exi_senv ~atom_budget ~max_combos seeds clauses]: the
   live instances
   chosen by the procedure above, each with the substitution that makes it and
   the clause it is an instance of, and the statistics.  Pure apart from the
   evaluator's own caches: the result depends only on the arguments.
   [kept_args q], when given, says which of [q]'s original arguments the
   clauses still carry (a solver's removal of unused arguments), so that an
   atom pattern stated at the original arity can be projected onto [q].

   Guarantees: every returned [(ex, sub, cl)] has [ex] an example clause of
   [ExClauseSet.of_subst exi_senv (formula of cl) sub] with [sub] ground on
   every variable of [cl] (so [ex] is a consequence of [cl]); at most
   [atom_budget] instances. *)
let run ?(kept_args = fun _ -> None) ~exi_senv ~atom_budget ~max_combos
    (seeds : seeds) clauses =
  let prepared = List.filter_mapi (Set.to_list clauses) ~f:(prepare exi_senv) in
  let skipped_clauses = Set.length clauses - List.length prepared in
  (* the values a variable takes when no equation fixes it *)
  let exact_names = Map.Poly.of_alist_reduce seeds.seeds ~f:( @ ) in
  let stem_names =
    Map.Poly.of_alist_reduce
      (List.map seeds.seeds ~f:(fun (n, vs) -> (stem n, vs)))
      ~f:( @ )
  in
  let dedup = List.dedup_and_sort ~compare:Stdlib.compare in
  let used_exact = ref false and used_stem = ref false in
  let values_of (x, sort) =
    if Term.is_bool_sort sort then [ Value.Bool true; Value.Bool false ]
    else
      let n = Ident.name_of_tvar x in
      match Map.Poly.find exact_names n with
      | Some vs ->
          used_exact := true;
          dedup vs
      | None -> (
          match Map.Poly.find stem_names (stem n) with
          | Some vs ->
              used_stem := true;
              dedup vs
          | None -> dedup seeds.choice_values)
  in
  let patterns : (string, Value.t option list list) Hashtbl.t =
    Hashtbl.create (module String)
  in
  List.iter seeds.atoms ~f:(fun (q, vs) ->
      Hashtbl.add_multi patterns ~key:q ~data:vs;
      Hashtbl.add_multi patterns
        ~key:(Ident.name_of_pvar (Ident.uninterp_pvar (Ident.Pvar q)))
        ~data:vs);
  (* the atom patterns that apply to a head of [p]: (head index, pattern) *)
  let head_patterns (p : prepared) =
    List.concat_mapi p.heads ~f:(fun i (q, ts) ->
        Hashtbl.find_multi patterns (Ident.name_of_pvar q)
        |> List.filter_map ~f:(fun pat ->
            if List.length pat = List.length ts then Some (i, pat)
            else
              (* the solver removed some of the predicate's arguments: keep
                 the pattern's values at the positions it kept *)
              match kept_args q with
              | Some kept
                when Array.length kept = List.length pat
                     && Array.count kept ~f:Fn.id = List.length ts ->
                  Some (i, List.filteri pat ~f:(fun j _ -> kept.(j)))
              | _ -> None))
  in
  let used_atom = ref false in
  let matched_somewhere =
    List.exists prepared ~f:(fun p ->
        List.exists p.vars ~f:(fun (x, s) ->
            Term.is_int_sort s
            &&
            let n = Ident.name_of_tvar x in
            Map.Poly.mem exact_names n || Map.Poly.mem stem_names (stem n))
        || not (List.is_empty (head_patterns p)))
  in
  let held : (string, unit) Hashtbl.t = Hashtbl.create (module String) in
  (* reached atoms per unknown, split into the rounds before ([old]) and the
     last round ([delta]) *)
  let old : (string, Value.t list list) Hashtbl.t =
    Hashtbl.create (module String)
  in
  let delta : (string, Value.t list list) Hashtbl.t =
    Hashtbl.create (module String)
  in
  let next : (string, Value.t list list) Hashtbl.t =
    Hashtbl.create (module String)
  in
  let seen_instances : (string, unit) Hashtbl.t =
    Hashtbl.create (module String)
  in
  let results = ref [] and n_instances = ref 0 in
  let truncated = ref None and exhausted = ref false in
  let eval_term env t = Evaluator.eval_term ~env t in
  let reach p vs =
    let k = key_of p vs in
    if not (Hashtbl.mem held k) then (
      if Hashtbl.length held >= atom_budget then
        raise (Budget (sprintf "atom budget %d" atom_budget));
      Hashtbl.set held ~key:k ~data:();
      Hashtbl.add_multi next ~key:(Ident.name_of_pvar p) ~data:vs)
  in
  (* the one-point rule over the premise's equations, to a fixed point *)
  let one_point (p : prepared) env =
    let rec go env =
      let fixed =
        List.find_map p.vars ~f:(fun (x, _) ->
            if Map.Poly.mem env x then None
            else
              List.find_map p.premise ~f:(fun phi ->
                  match equation_of phi with
                  | Some (t1, t2) -> (
                      let side a b =
                        match a with
                        | Term.Var (y, _, _)
                          when Ident.tvar_equal x y
                               && Set.for_all (Term.tvs_of b)
                                    ~f:(Map.Poly.mem env) -> (
                            try Some (x, eval_term env b)
                            with exn when not (Common.Timer.is_async exn) ->
                              None)
                        | _ -> None
                      in
                      match side t1 t2 with
                      | Some r -> Some r
                      | None -> side t2 t1)
                  | _ -> None))
      in
      match fixed with
      | Some (x, v) -> go (Map.Poly.set env ~key:x ~data:v)
      | None -> env
    in
    go env
  in
  (* every instance of [p] extending the body matching [env] *)
  let instantiate_core ~from_pattern (p : prepared) env =
    let env = one_point p env in
    (* the variables a premise equation may fix once the others are chosen
       are enumerated only if it does not: the rest are chosen first *)
    let definable =
      List.filter_map p.premise ~f:(fun phi ->
          match equation_of phi with
          | Some (t1, t2) ->
              Some
                (List.filter_map
                   [ (t1, t2); (t2, t1) ]
                   ~f:(function
                     | Term.Var (x, _, _), t
                       when not (Set.mem (Term.tvs_of t) x) ->
                         Some x
                     | _ -> None))
          | _ -> None)
      |> List.concat |> Set.Poly.of_list
    in
    let free = List.filter p.vars ~f:(fun (x, _) -> not (Map.Poly.mem env x)) in
    let chosen, defined =
      List.partition_tf free ~f:(fun (x, _) -> not (Set.mem definable x))
    in
    let count vars =
      List.fold vars ~init:1 ~f:(fun acc xs ->
          if acc > max_combos then acc else acc * List.length (values_of xs))
    in
    let combos = count chosen in
    let leaves = ref 0 in
    let over () =
      if Option.is_none !truncated then
        truncated :=
          Some (sprintf "a matching over %d value combinations" max_combos)
    in
    if combos > max_combos then over ()
    else
      (* choose the [chosen] variables, then let the one-point rule fix the
         [defined] ones; one that it leaves open is enumerated too, within the
         same bound on the number of valuations *)
      let rec enum env = function
        | (x, s) :: rest ->
            List.iter
              (values_of (x, s))
              ~f:(fun v -> enum (Map.Poly.set env ~key:x ~data:v) rest)
        | [] -> (
            let env = one_point p env in
            match
              List.find defined ~f:(fun (x, _) -> not (Map.Poly.mem env x))
            with
            | Some xs ->
                List.iter (values_of xs) ~f:(fun v ->
                    enum (Map.Poly.set env ~key:(fst xs) ~data:v) [])
            | None ->
                Int.incr leaves;
                if !leaves > max_combos then over () else emit env)
      and emit env =
        match
          try
            if Evaluator.eval ~env p.pure then None
            else
              let ground (q, ts) = (q, List.map ts ~f:(eval_term env)) in
              Some (List.map p.bodies ~f:ground, List.map p.heads ~f:ground)
          with exn when not (Common.Timer.is_async exn) -> None
        with
        | None -> ()
        | Some (bodies, heads) ->
            if
              List.for_all bodies ~f:(fun (q, vs) ->
                  Hashtbl.mem held (key_of q vs))
            then (
              if from_pattern then used_atom := true;
              let sub =
                Map.Poly.of_alist_exn
                @@ List.map p.vars ~f:(fun (x, _) ->
                    (x, Term.of_value (get_dtenv ()) (Map.Poly.find_exn env x)))
              in
              let ikey =
                String.concat ~sep:";"
                  (List.map
                     (bodies @ [ (Ident.Pvar "=>", []) ] @ heads)
                     ~f:(fun (q, vs) -> key_of q vs))
                ^ "|"
                ^ String.concat ~sep:","
                    (List.map p.vars ~f:(fun (x, _) ->
                         Value.str_of (Map.Poly.find_exn env x)))
                ^ "|" ^ Int.to_string p.index
              in
              if not (Hashtbl.mem seen_instances ikey) then (
                Hashtbl.set seen_instances ~key:ikey ~data:();
                let exs =
                  try ExClauseSet.of_subst exi_senv p.formula sub
                  with exn when not (Common.Timer.is_async exn) ->
                    Set.Poly.empty
                in
                if not (Set.is_empty exs) then (
                  if !n_instances >= atom_budget then
                    raise (Budget (sprintf "instance budget %d" atom_budget));
                  Set.iter exs ~f:(fun ex ->
                      Int.incr n_instances;
                      results := (ex, sub, p.clause) :: !results);
                  List.iter heads ~f:(fun (q, vs) -> reach q vs))))
      in
      enum env chosen
  in
  (* [p]'s instances extending [env]: as they are, and once more per atom
     pattern applying to a head of [p], with that head's variables bound to
     the pattern's values (a conflicting binding drops that pattern) *)
  let instantiate (p : prepared) env =
    instantiate_core ~from_pattern:false p env;
    List.iter (head_patterns p) ~f:(fun (i, pat) ->
        let _, ts = List.nth_exn p.heads i in
        (* the premise's equations first: a pattern value proposes a value
           only for a head variable they leave open *)
        let env = one_point p env in
        let env' =
          List.fold2_exn ts pat ~init:env ~f:(fun env t v ->
              match (t, v) with
              | Term.Var (x, _, _), Some v when not (Map.Poly.mem env x) ->
                  Map.Poly.set env ~key:x ~data:v
              | _ -> env)
        in
        if not (phys_equal env env') then
          instantiate_core ~from_pattern:true p env')
  in
  (* matchings of [atoms] (an unknown's application) against the value tuples
     [tuples], extending [env]; arguments that are not variables are checked
     once the valuation is complete *)
  let match_atom env ts vs =
    List.fold2_exn ts vs ~init:(Some env) ~f:(fun acc t v ->
        match (acc, t) with
        | None, _ -> None
        | Some env, Term.Var (x, _, _) -> (
            match Map.Poly.find env x with
            | None -> Some (Map.Poly.set env ~key:x ~data:v)
            | Some v' ->
                if Stdlib.( = ) (Value.str_of v') (Value.str_of v) then acc
                else None)
        | Some _, _ -> acc)
  in
  let tuples tbl q = Hashtbl.find_multi tbl (Ident.name_of_pvar q) in
  let rounds = ref 0 in
  (try
     if matched_somewhere then (
       List.iter prepared ~f:(fun p ->
           if List.is_empty p.bodies then instantiate p Map.Poly.empty);
       let rec loop () =
         Hashtbl.clear delta;
         Hashtbl.iteri next ~f:(fun ~key ~data -> Hashtbl.set delta ~key ~data);
         Hashtbl.clear next;
         if not (Hashtbl.is_empty delta) then (
           Int.incr rounds;
           List.iter prepared ~f:(fun p ->
               List.iteri p.bodies ~f:(fun i _ ->
                   (* body [i] from [delta], those before it from [old], those
                      after it from [old] and [delta] *)
                   let rec go j env = function
                     | [] -> instantiate p env
                     | (q, ts) :: rest ->
                         let srcs =
                           if j < i then tuples old q
                           else if j = i then tuples delta q
                           else tuples old q @ tuples delta q
                         in
                         List.iter srcs ~f:(fun vs ->
                             if List.length vs = List.length ts then
                               match match_atom env ts vs with
                               | Some env -> go (j + 1) env rest
                               | None -> ())
                   in
                   go 0 Map.Poly.empty p.bodies));
           Hashtbl.iteri delta ~f:(fun ~key ~data ->
               List.iter data ~f:(fun vs -> Hashtbl.add_multi old ~key ~data:vs));
           loop ())
       in
       loop ())
   with Budget why ->
     truncated := Some why;
     exhausted := true);
  let matched =
    { by_name = !used_exact; by_stem = !used_stem; by_atom = !used_atom }
  in
  ( List.rev !results,
    {
      instances = !n_instances;
      atoms = Hashtbl.length held;
      rounds = !rounds;
      matched;
      skipped_clauses;
      truncated = !truncated;
      exhausted = !exhausted;
      fact_vars =
        (if matched_somewhere then []
         else
           let facts, others =
             List.partition_tf prepared ~f:(fun p -> List.is_empty p.bodies)
           in
           let names ps =
             List.concat_map ps ~f:(fun p ->
                 List.filter_map p.vars ~f:(fun (x, s) ->
                     if Term.is_int_sort s then Some (Ident.name_of_tvar x)
                     else None))
             |> List.dedup_and_sort ~compare:String.compare
             |> Fn.flip List.take 8
           in
           (sprintf "facts:%d" (List.length facts) :: names facts)
           @ (sprintf "others:%d" (List.length others) :: names others));
    } )

let str_of_stats s =
  sprintf "instances=%d atoms=%d rounds=%d matched=%s skipped-clauses=%d%s%s"
    s.instances s.atoms s.rounds (str_of_matched s.matched) s.skipped_clauses
    (match s.truncated with None -> "" | Some why -> " truncated=" ^ why)
    (if List.is_empty s.fact_vars then ""
     else " fact-vars=" ^ String.concat ~sep:"," s.fact_vars)

(* The refutation cone: which of the instances a labeling refutation can use.

   A refutation of a finite set [E] of ground example clauses, in the sense a
   labeler decides, is the absence of a truth assignment to their atoms that
   satisfies every member and whose positive atoms of each well-founded unknown
   form an acyclic graph (an edge from the first half of an atom's arguments to
   the second; for a parity family, between the left and right nodes the
   family names, every cycle accepting).  An atom is PURE in [E] when it occurs
   with one polarity only and that polarity can be given to it whatever the
   other atoms are: false for an ordinary, well-founded or parity unknown (a
   subgraph of an acyclic graph is acyclic, and removing an edge closes no
   cycle), true for an ordinary unknown, and true for a well-founded or parity
   one when its edge lies on no cycle of the graph of ALL its family's atoms in
   [E], positive or not (then no assignment's positive graph can close a cycle
   through it).  Every instance containing a pure atom is satisfied by giving
   that atom its polarity, and the atom occurs nowhere else; so removing those
   instances, and repeating on what remains, leaves a set that is refuted
   exactly when [E] is (an assignment of the rest extends to the removed atoms,
   in the reverse order of removal).  The kept instances are the cone: for a
   termination lasso, its cycle together with the stem that forces the cycle's
   atoms true; a chain that reaches no cycle and no goal peels away whole.

   Keeping only the instances on a cycle would be wrong: without the stem the
   cycle's atoms are not forced, and the labeler sets them false.

   The equivalence is relative to [E] alone.  Examples held elsewhere may use
   an atom that is pure in [E]; a refutation that needs both can then be lost.
   Soundness is never at stake: every kept instance is still an instance of
   the clauses, and dropping examples only removes refutations.

   [role_of p ts] classifies a ground application: [Free] for an ordinary
   unknown, [Edge (family, source, target)] for a well-founded or parity one,
   [Fixed] for any other kind, whose atoms are never removed (a functional
   unknown's atoms can conflict without a cycle).  A parametric atom or a
   constraint atom counts as [Fixed] too.  Guarantees: the result is a sublist
   of [results] in the same order, and the second component is the number of
   instances removed. *)
type role = Free | Edge of string * string * string | Fixed

let refutation_cone ~role_of results =
  let results = Array.of_list results in
  let n = Array.length results in
  (* per atom: its role, alive occurrence counts and the instances it occurs in *)
  let ids : (string, int) Hashtbl.t = Hashtbl.create (module String) in
  let roles = ref [||] and npos = ref [||] and nneg = ref [||] in
  let occ : int list array ref = ref [||] in
  let n_atoms = ref 0 in
  let grow () =
    let cap = Array.length !roles in
    if !n_atoms >= cap then (
      let cap' = max 16 (2 * cap) in
      let ext a d = Array.append a (Array.create ~len:(cap' - cap) d) in
      roles := ext !roles Fixed;
      npos := ext !npos 0;
      nneg := ext !nneg 0;
      occ := ext !occ [])
  in
  let atom_id = function
    | ExAtom.PApp ((p, _), ts) ->
        let key =
          Ident.name_of_pvar p ^ "("
          ^ String.concat ~sep:"," (List.map ts ~f:Term.str_of)
          ^ ")"
        in
        ( key,
          fun () ->
            try role_of p ts
            with exn when not (Common.Timer.is_async exn) -> Fixed )
    | a -> ("#" ^ ExAtom.str_of a, fun () -> Fixed)
  in
  let lits =
    Array.mapi results ~f:(fun i (ex, _, _) ->
        let lit pol a =
          let key, role = atom_id a in
          let id =
            match Hashtbl.find ids key with
            | Some id -> id
            | None ->
                grow ();
                let id = !n_atoms in
                Int.incr n_atoms;
                Hashtbl.set ids ~key ~data:id;
                !roles.(id) <- role ();
                id
          in
          if pol then !npos.(id) <- !npos.(id) + 1
          else !nneg.(id) <- !nneg.(id) + 1;
          !occ.(id) <- i :: !occ.(id);
          (id, pol)
        in
        List.map (Set.to_list ex.ExClause.positive) ~f:(lit true)
        @ List.map (Set.to_list ex.ExClause.negative) ~f:(lit false))
  in
  let alive = Array.create ~len:n true in
  let removed = ref 0 in
  (* the edges of the alive atoms of each family that lie on a cycle of that
     family's graph: an edge (u, v) is on a cycle iff u = v or u and v are in
     one strongly connected component (Kosaraju, iterative) *)
  let on_cycle () =
    let res = Array.create ~len:!n_atoms false in
    let node_ids : (string, int) Hashtbl.t = Hashtbl.create (module String) in
    let node k =
      match Hashtbl.find node_ids k with
      | Some i -> i
      | None ->
          let i = Hashtbl.length node_ids in
          Hashtbl.set node_ids ~key:k ~data:i;
          i
    in
    let edges = ref [] in
    for a = 0 to !n_atoms - 1 do
      match !roles.(a) with
      | Edge (fam, u, v) when !npos.(a) + !nneg.(a) > 0 ->
          let u = node (fam ^ "\000" ^ u) and v = node (fam ^ "\000" ^ v) in
          if u = v then res.(a) <- true else edges := (a, u, v) :: !edges
      | _ -> ()
    done;
    let nn = Hashtbl.length node_ids in
    let succ = Array.create ~len:nn [] and pred = Array.create ~len:nn [] in
    List.iter !edges ~f:(fun (_, u, v) ->
        succ.(u) <- v :: succ.(u);
        pred.(v) <- u :: pred.(v));
    let visited = Array.create ~len:nn false in
    let order = ref [] in
    for s = 0 to nn - 1 do
      if not visited.(s) then (
        visited.(s) <- true;
        let stack = Stack.create () in
        Stack.push stack (s, succ.(s));
        while not (Stack.is_empty stack) do
          match Stack.pop_exn stack with
          | u, [] -> order := u :: !order
          | u, v :: rest ->
              Stack.push stack (u, rest);
              if not visited.(v) then (
                visited.(v) <- true;
                Stack.push stack (v, succ.(v)))
        done)
    done;
    let comp = Array.create ~len:nn (-1) in
    List.iteri !order ~f:(fun c s ->
        if comp.(s) < 0 then (
          comp.(s) <- c;
          let stack = Stack.create () in
          Stack.push stack s;
          while not (Stack.is_empty stack) do
            let u = Stack.pop_exn stack in
            List.iter pred.(u) ~f:(fun v ->
                if comp.(v) < 0 then (
                  comp.(v) <- c;
                  Stack.push stack v))
          done));
    List.iter !edges ~f:(fun (a, u, v) ->
        if comp.(u) = comp.(v) then res.(a) <- true);
    res
  in
  let rec outer () =
    let cyc = on_cycle () in
    let pure a =
      let p = !npos.(a) and q = !nneg.(a) in
      match !roles.(a) with
      | Fixed -> false
      | Free -> (p = 0 && q > 0) || (q = 0 && p > 0)
      | Edge _ -> (p = 0 && q > 0) || (q = 0 && p > 0 && not cyc.(a))
    in
    let work = Queue.create () in
    for a = 0 to !n_atoms - 1 do
      if pure a then Queue.enqueue work a
    done;
    let before = !removed in
    while not (Queue.is_empty work) do
      let a = Queue.dequeue_exn work in
      if pure a then
        List.iter !occ.(a) ~f:(fun i ->
            if alive.(i) then (
              alive.(i) <- false;
              Int.incr removed;
              List.iter lits.(i) ~f:(fun (b, pol) ->
                  if pol then !npos.(b) <- !npos.(b) - 1
                  else !nneg.(b) <- !nneg.(b) - 1;
                  if b <> a && pure b then Queue.enqueue work b)))
    done;
    (* a removal can break a cycle and make more edges pure *)
    if !removed > before then outer ()
  in
  outer ();
  ( List.filteri (Array.to_list results) ~f:(fun i _ -> alive.(i)),
    !removed )
