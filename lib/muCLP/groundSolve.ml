(* Deciding a ground muCLP query on its finite reachable part.

   THE CLASS.  The query is a Boolean combination of predicate applications
   whose arguments are closed terms, and no predicate reachable from the query
   (through the call graph, syntactically) has a quantifier in its body.  Then
   every ground atom [P(v1, ..., vk)] reachable from the query by instantiating
   bodies has, as its equation, its predicate's body with the parameters
   replaced by the values: a closed formula whose theory atoms evaluate to
   constants, leaving a positive Boolean combination of further ground atoms.
   The atoms reachable this way, each with its predicate's fixpoint sign and
   its predicate's position in the equation list, form a Boolean equation
   system.  When the set is finite, the query's truth value under the muCLP's
   fixpoint semantics is that of the system's solution, which is the winner of
   a finite parity game.

   THE GAME.  A play moves from an atom to its body, from a conjunction to a
   conjunct the refuter picks, from a disjunction to a disjunct the prover
   picks.  An infinite play visits atoms infinitely often (bodies are finite
   trees), and the prover wins it when the earliest equation among the
   predicates it visits infinitely often is a greatest fixpoint: the first
   equation of a muCLP is the outermost, as MuVal's reduction reads it, which
   gives priority by equation order.  [fix] is not a third sign: the
   transition-system front ends mark a location that is no cut point [fix],
   claiming that its two fixpoints coincide; [decide] solves the game with
   [fix] read as greatest and again as least and answers only when the two
   agree, so its answer holds whichever the claim is.

   THE SOLVER.  The system is split into strongly connected components of its
   dependency graph and solved callee components first, each by Zielonka's
   recursive algorithm (W. Zielonka, "Infinite games on finitely coloured
   graphs with applications to automata on infinite trees", Theoretical
   Computer Science 200, 1998) after its decided successors are substituted
   and its priorities are compressed.  A component whose atoms all carry one
   sign is decided by one attractor computation, linear in its size; a
   component with [d] alternating signs costs at most [O(n^d)] for [n] game
   nodes (Zielonka's bound), and [d] is at most the number of predicates.

   WHAT [decide] GUARANTEES.  [Decided b] only when the class holds, the
   reachable set has at most [atom_budget] atoms, every theory atom and every
   argument evaluated without exception to a Boolean, integer, real or
   bit-vector value, and both readings of [fix] agree; then [b] is the query's
   truth value.  Anything else is [Declined] or [Over_budget] and says nothing
   about the query: the caller hands the problem on unchanged.  An evaluation
   the theory leaves open (an integer division by zero, a read the theory does
   not fix) raises inside the evaluator and declines, so no answer rests on an
   interpretation-dependent value.  The budget counts atoms, so the work
   before an answer or a refusal is bounded by the budget times the largest
   body, whatever the clock. *)
open Core
open Ast
open Ast.LogicOld

(** {1 Positive Boolean formulas} *)

(** a positive Boolean formula over atoms of type ['a]; the smart
    constructors keep it free of constants below the root and of nested
    conjunctions in conjunctions (and disjunctions in disjunctions) *)
type 'a bf = T | F | A of 'a | And of 'a bf list | Or of 'a bf list

let mk_and bs =
  let rec go acc = function
    | [] -> Some acc
    | T :: rest -> go acc rest
    | F :: _ -> None
    | And cs :: rest -> go (List.rev_append cs acc) rest
    | b :: rest -> go (b :: acc) rest
  in
  match go [] bs with
  | None -> F
  | Some [] -> T
  | Some [ b ] -> b
  | Some cs -> And (List.rev cs)

let mk_or bs =
  let rec go acc = function
    | [] -> Some acc
    | F :: rest -> go acc rest
    | T :: _ -> None
    | Or cs :: rest -> go (List.rev_append cs acc) rest
    | b :: rest -> go (b :: acc) rest
  in
  match go [] bs with
  | None -> T
  | Some [] -> F
  | Some [ b ] -> b
  | Some cs -> Or (List.rev cs)

let rec bind_bf ~f = function
  | T -> T
  | F -> F
  | A a -> f a
  | And bs -> mk_and (List.map bs ~f:(bind_bf ~f))
  | Or bs -> mk_or (List.map bs ~f:(bind_bf ~f))

let rec iter_atoms ~f = function
  | T | F -> ()
  | A a -> f a
  | And bs | Or bs -> List.iter bs ~f:(iter_atoms ~f)

let rec eval_bf ~f = function
  | T -> true
  | F -> false
  | A a -> f a
  | And bs -> List.for_all bs ~f:(eval_bf ~f)
  | Or bs -> List.exists bs ~f:(eval_bf ~f)

(** {1 Boolean equation systems} *)

module Bes = struct
  (** One equation [X_i =sign body].  [rank] orders the blocks: rank 0 is the
      outermost fixpoint and the most significant priority.  Equations of one
      rank must carry one sign (they are the ground instances of one
      predicate).  [body] mentions equation indices. *)
  type eqn = { rank : int; nu : bool; body : int bf }

  (* Attractor and Zielonka over one game.  [owner.(v)] is 0 for the prover
     (a disjunction, or a node with one successor) and 1 for the refuter (a
     conjunction); [prio] is max-parity: the largest priority seen infinitely
     often decides, even for the prover.  Every node has a successor, and
     [pred] lists each edge once per occurrence in [succ], so the counters of
     the attractor stay consistent with duplicate successors. *)
  type game = {
    owner : int array;
    prio : int array;
    succ : int array array;
    pred : int list array;
  }

  let solve_game (g : game) (nodes : int list) : bool array =
    let n = Array.length g.owner in
    let win0 = Array.create ~len:n false in
    let stamp = ref 0 in
    let fresh () =
      incr stamp;
      !stamp
    in
    let mem = Array.create ~len:n 0 in
    let amark = Array.create ~len:n 0 in
    let cmark = Array.create ~len:n 0 in
    let cnt = Array.create ~len:n 0 in
    let mark s id = List.iter s ~f:(fun v -> mem.(v) <- id) in
    (* the [p]-attractor of [target] inside the subgame [in_sub]: the nodes
       from which [p] forces a visit to [target]; returns the nodes and a
       membership test valid until the next attractor call *)
    let attractor p in_sub target =
      let aid = fresh () in
      let q = Queue.create () in
      let res = ref [] in
      let add v =
        amark.(v) <- aid;
        res := v :: !res;
        Queue.enqueue q v
      in
      List.iter target ~f:(fun v -> if amark.(v) <> aid then add v);
      while not (Queue.is_empty q) do
        let v = Queue.dequeue_exn q in
        List.iter g.pred.(v) ~f:(fun u ->
            if in_sub u && amark.(u) <> aid then
              if g.owner.(u) = p then add u
              else (
                if cmark.(u) <> aid then (
                  cmark.(u) <- aid;
                  cnt.(u) <-
                    Array.count g.succ.(u) ~f:(fun w -> in_sub w));
                cnt.(u) <- cnt.(u) - 1;
                if cnt.(u) = 0 then add u))
      done;
      (!res, fun v -> amark.(v) = aid)
    in
    (* Zielonka's recursion; returns (prover's region, refuter's region) *)
    let rec zielonka s =
      match s with
      | [] -> ([], [])
      | _ -> (
          let sid = fresh () in
          mark s sid;
          let in_s v = mem.(v) = sid in
          let d =
            List.fold s ~init:Int.min_value ~f:(fun m v -> Int.max m g.prio.(v))
          in
          let p = d land 1 in
          let u = List.filter s ~f:(fun v -> g.prio.(v) = d) in
          let _, in_a = attractor p in_s u in
          let rest = List.filter s ~f:(fun v -> not (in_a v)) in
          let w0', w1' = zielonka rest in
          mark s sid;
          let w_opp = if p = 0 then w1' else w0' in
          match w_opp with
          | [] -> if p = 0 then (s, []) else ([], s)
          | _ ->
              let b, in_b = attractor (1 - p) in_s w_opp in
              let rest2 = List.filter s ~f:(fun v -> not (in_b v)) in
              let w0'', w1'' = zielonka rest2 in
              if p = 0 then (w0'', b @ w1'') else (b @ w0'', w1''))
    in
    let w0, _ = zielonka nodes in
    List.iter w0 ~f:(fun v -> win0.(v) <- true);
    win0

  (* Tarjan's strongly connected components of the dependency graph, callee
     components first (a component is emitted after every component it
     reaches) *)
  let sccs (eqns : eqn array) : int list list =
    let n = Array.length eqns in
    let deps =
      Array.map eqns ~f:(fun e ->
          let l = ref [] in
          iter_atoms e.body ~f:(fun j -> l := j :: !l);
          !l)
    in
    let index = Array.create ~len:n (-1) in
    let low = Array.create ~len:n 0 in
    let on_stack = Array.create ~len:n false in
    let stack = Stack.create () in
    let counter = ref 0 in
    let out = ref [] in
    let rec visit v =
      index.(v) <- !counter;
      low.(v) <- !counter;
      incr counter;
      Stack.push stack v;
      on_stack.(v) <- true;
      List.iter deps.(v) ~f:(fun w ->
          if index.(w) < 0 then (
            visit w;
            low.(v) <- Int.min low.(v) low.(w))
          else if on_stack.(w) then low.(v) <- Int.min low.(v) index.(w));
      if low.(v) = index.(v) then (
        let rec pop acc =
          let w = Stack.pop_exn stack in
          on_stack.(w) <- false;
          if w = v then w :: acc else pop (w :: acc)
        in
        out := pop [] :: !out)
    in
    for v = 0 to n - 1 do
      if index.(v) < 0 then visit v
    done;
    List.rev !out

  (** [solve eqns]: the solution of the system, block 0 outermost.  Requires
      every [body] to mention indices of [eqns] only.  Guarantees the value of
      every equation in the nested-fixpoint solution (the one [solve_naive]
      computes by iteration). *)
  let solve (eqns : eqn array) : bool array =
    let n = Array.length eqns in
    let value = Array.create ~len:n 0 (* 0 undecided, 1 false, 2 true *) in
    let max_rank =
      Array.fold eqns ~init:0 ~f:(fun m e -> Int.max m e.rank)
    in
    let prio_of e = (2 * (max_rank + 1 - e.rank)) + if e.nu then 0 else 1 in
    List.iter (sccs eqns) ~f:(fun comp ->
        (* local numbering: the component's atoms, then the internal nodes
           of their bodies, then the two sinks *)
        let local = Hashtbl.create (module Int) in
        List.iteri comp ~f:(fun i v -> Hashtbl.set local ~key:v ~data:i);
        let k = List.length comp in
        let subst j =
          match value.(j) with
          | 1 -> F
          | 2 -> T
          | _ -> A (Hashtbl.find_exn local j)
        in
        let bodies =
          List.map comp ~f:(fun v -> bind_bf ~f:subst eqns.(v).body)
        in
        let owner = Stdlib.Dynarray.create () in
        let prio = Stdlib.Dynarray.create () in
        let succ = Stdlib.Dynarray.create () in
        List.iter comp ~f:(fun v ->
            Stdlib.Dynarray.add_last owner 0;
            Stdlib.Dynarray.add_last prio (prio_of eqns.(v));
            Stdlib.Dynarray.add_last succ [||]);
        let min_atom_prio =
          List.fold comp ~init:Int.max_value ~f:(fun m v ->
              Int.min m (prio_of eqns.(v)))
        in
        let t_node = k and f_node = k + 1 in
        Stdlib.Dynarray.add_last owner 0;
        Stdlib.Dynarray.add_last prio 0;
        Stdlib.Dynarray.add_last succ [| t_node |];
        Stdlib.Dynarray.add_last owner 0;
        Stdlib.Dynarray.add_last prio 1;
        Stdlib.Dynarray.add_last succ [| f_node |];
        let rec node_of = function
          | T -> t_node
          | F -> f_node
          | A i -> i
          | (And bs | Or bs) as b ->
              let id = Stdlib.Dynarray.length owner in
              Stdlib.Dynarray.add_last owner
                (match b with And _ -> 1 | _ -> 0);
              (* any priority not above the component's atoms: every
                 infinite play inside the component visits atoms
                 infinitely often, so it never decides *)
              Stdlib.Dynarray.add_last prio min_atom_prio;
              Stdlib.Dynarray.add_last succ [||];
              let ss = Array.of_list_map bs ~f:node_of in
              Stdlib.Dynarray.set succ id ss;
              id
        in
        List.iteri bodies ~f:(fun i b ->
            Stdlib.Dynarray.set succ i [| node_of b |]);
        let owner = Stdlib.Dynarray.to_array owner in
        let prio = Stdlib.Dynarray.to_array prio in
        let succ = Stdlib.Dynarray.to_array succ in
        let m = Array.length owner in
        let pred = Array.create ~len:m [] in
        Array.iteri succ ~f:(fun u ss ->
            Array.iter ss ~f:(fun w -> pred.(w) <- u :: pred.(w)));
        (* the sinks first: the prover's attractor of [true] and then, in
           its complement (a trap for the prover), the refuter's attractor
           of [false] are won by their players; the rest has no sink *)
        let all = List.init m ~f:Fn.id in
        let g0 = { owner; prio; succ; pred } in
        let in_all _ = true in
        let win0 = Array.create ~len:m false in
        let removed = Array.create ~len:m false in
        let attr p in_sub target =
          (* plain attractor for the sink removal; linear *)
          let inattr = Array.create ~len:m false in
          let c = Array.map succ ~f:(fun ss -> Array.count ss ~f:in_sub) in
          let q = Queue.create () in
          List.iter target ~f:(fun v ->
              if not inattr.(v) then (
                inattr.(v) <- true;
                Queue.enqueue q v));
          while not (Queue.is_empty q) do
            let v = Queue.dequeue_exn q in
            List.iter pred.(v) ~f:(fun u ->
                if in_sub u && not inattr.(u) then
                  if owner.(u) = p then (
                    inattr.(u) <- true;
                    Queue.enqueue q u)
                  else (
                    c.(u) <- c.(u) - 1;
                    if c.(u) = 0 then (
                      inattr.(u) <- true;
                      Queue.enqueue q u)))
          done;
          inattr
        in
        let a = attr 0 in_all [ t_node ] in
        Array.iteri a ~f:(fun v b ->
            if b then (
              win0.(v) <- true;
              removed.(v) <- true));
        let b = attr 1 (fun v -> not removed.(v)) [ f_node ] in
        Array.iteri b ~f:(fun v x -> if x then removed.(v) <- true);
        let rest = List.filter all ~f:(fun v -> not removed.(v)) in
        (* priority compression on what is left: sort the priorities present
           and number them so that equal parity stays adjacent and merged *)
        let present =
          List.dedup_and_sort ~compare:Int.compare
            (List.map rest ~f:(fun v -> prio.(v)))
        in
        let cmap = Hashtbl.create (module Int) in
        (match present with
        | [] -> ()
        | p0 :: _ ->
            ignore
              (List.fold present ~init:(p0 land 1, p0 land 1) ~f:(fun (c, par) p ->
                   let c = if p land 1 = par then c else c + 1 in
                   Hashtbl.set cmap ~key:p ~data:c;
                   (c, p land 1))));
        let prio' =
          Array.mapi prio ~f:(fun v p ->
              if removed.(v) then 0 else Hashtbl.find_exn cmap p)
        in
        let w = solve_game { g0 with prio = prio' } rest in
        List.iter rest ~f:(fun v -> if w.(v) then win0.(v) <- true);
        List.iteri comp ~f:(fun i v -> value.(v) <- (if win0.(i) then 2 else 1)));
    Array.map value ~f:(fun x -> x = 2)

  (** [solve_naive eqns]: the nested-fixpoint solution by Kleene iteration of
      every block inside every iteration of the blocks around it, from false
      for a least and from true for a greatest fixpoint.  Exponential in the
      number of blocks; the reference [solve] is tested against. *)
  let solve_naive (eqns : eqn array) : bool array =
    let n = Array.length eqns in
    let v = Array.create ~len:n false in
    let ranks =
      List.dedup_and_sort ~compare:Int.compare
        (Array.to_list (Array.map eqns ~f:(fun e -> e.rank)))
    in
    let members r =
      List.filter (List.init n ~f:Fn.id) ~f:(fun i -> eqns.(i).rank = r)
    in
    let rec block = function
      | [] -> ()
      | r :: inner ->
          let ms = members r in
          List.iter ms ~f:(fun i -> v.(i) <- eqns.(i).nu);
          let rec iterate () =
            block inner;
            let nv =
              List.map ms ~f:(fun i -> eval_bf ~f:(fun j -> v.(j)) eqns.(i).body)
            in
            let changed =
              List.fold2_exn ms nv ~init:false ~f:(fun ch i b ->
                  if Bool.equal v.(i) b then ch
                  else (
                    v.(i) <- b;
                    true))
            in
            if changed then iterate ()
          in
          iterate ()
    in
    block ranks;
    v
end

(** {1 Ground muCLP queries} *)

type outcome =
  | Decided of bool  (** the query's truth value *)
  | Declined of string  (** outside the class or not evaluable; the reason *)
  | Over_budget of int  (** the reachable atoms exceed the budget given *)

type stats = {
  atoms : int;  (** ground atoms reached (when declined, up to the refusal) *)
  sccs : int;  (** strongly connected components with a cycle *)
  largest_scc : int;
}

let empty_stats = { atoms = 0; sccs = 0; largest_scc = 0 }

exception Decline of string
exception Budget

(* a value as a key component; the constructor is spelled so that equal keys
   are equal values of one sort *)
let key_of_value = function
  | Value.Bool b -> if b then "#t" else "#f"
  | Value.Int z -> Z.to_string z
  | Value.Real q -> "r" ^ Q.to_string q
  | Value.BV (Some s, z) -> sprintf "bv%d:%s" s (Z.to_string z)
  | _ ->
      raise
        (Decline
           "an argument evaluates to a value that is not a Boolean, an \
            integer, a real or a sized bit-vector")

(* the predicates reachable from the query through the call graph *)
let reachable_preds (muclp : Problem.t) =
  let defs = Hashtbl.create (module String) in
  List.iter muclp.preds ~f:(fun p ->
      Hashtbl.set defs ~key:(Ident.name_of_pvar p.Pred.name) ~data:p);
  let seen = Hash_set.create (module String) in
  let rec go phi =
    Set.iter (Formula.pvs_of phi) ~f:(fun pv ->
        let s = Ident.name_of_pvar pv in
        if not (Hash_set.mem seen s) then (
          Hash_set.add seen s;
          match Hashtbl.find defs s with Some p -> go p.Pred.body | None -> ()))
  in
  go muclp.query;
  (defs, seen)

(** [in_class muclp]: the syntactic test, linear in the problem: the query and
    every predicate reachable from it are quantifier-free *)
let in_class (muclp : Problem.t) =
  Formula.is_quantifier_free muclp.query
  &&
  let defs, seen = reachable_preds muclp in
  Hash_set.for_all seen ~f:(fun s ->
      match Hashtbl.find defs s with
      | Some p -> Formula.is_quantifier_free p.Pred.body
      | None -> false)

(* An instantiation fixes, for each universally read binder an evaluation
   meets, a finite list of values to try: [inst ~owner x sort] is that list
   for the variable [x] bound in the body of [owner] (a predicate's name, or
   ["query"] for the query), or [None] to refuse.  See [refute_instance]. *)
type instantiation = owner:string -> Ident.tvar -> Sort.t -> Value.t list option

(* [ground_bf ?inst ~owner ~pol env phi]: [phi] under the values [env] of its
   free variables, as a positive Boolean formula over ground atoms.  A
   conjunction stops at a false conjunct and a disjunction at a true
   disjunct, so an atom behind a decided guard is never reached: the
   reachable set is the one unfolding from the query actually needs.  Raises
   [Decline] on anything that is not a constant combination of theory atoms
   and predicate applications.

   Without [inst] a quantifier is refused and the result is [phi]'s exact
   value.  With [inst], [pol] is the polarity of [phi] in the body ([Some
   true] positive, [Some false] negative, [None] both, under [<=>] or
   [xor]), and a binder read universally at that polarity -- [forall] in a
   positive position, [exists] in a negative one -- is replaced by the
   conjunction (resp. disjunction) of its body over every combination of the
   values [inst] gives its variables, at most [max_combos] of them.  Every
   such replacement is implied by the binder it replaces, under every
   valuation and every interpretation of the predicates, so the result is
   implied by [phi]'s exact value (a weakening), and is exact only when no
   binder was met.  Any other binder, and a binder under [None] polarity,
   is refused. *)
let rec ground_bf ?inst ?(max_combos = 0) ~owner ~pol env phi =
  let recur = ground_bf ?inst ~max_combos ~owner in
  let flip = Option.map ~f:not in
  match phi with
  | Formula.Atom (Atom.True _, _) -> T
  | Formula.Atom (Atom.False _, _) -> F
  | Formula.Atom (Atom.App (Predicate.Var (pv, _), ts, _), _) ->
      A (pv, List.map ts ~f:(Evaluator.eval_term ~env))
  | Formula.Atom ((Atom.App (Predicate.Psym _, _, _) as atm), _) ->
      if Evaluator.eval_atom ~env atm then T else F
  | Formula.Atom (Atom.App (Predicate.Fixpoint _, _, _), _) ->
      raise (Decline "an inline fixpoint")
  | Formula.UnaryOp (Formula.Not, phi', _) -> (
      match recur ~pol:(flip pol) env phi' with
      | T -> F
      | F -> T
      | _ -> raise (Decline "a negated predicate application"))
  | Formula.BinaryOp (Formula.And, p1, p2, _) -> (
      match recur ~pol env p1 with
      | F -> F
      | b1 -> mk_and [ b1; recur ~pol env p2 ])
  | Formula.BinaryOp (Formula.Or, p1, p2, _) -> (
      match recur ~pol env p1 with
      | T -> T
      | b1 -> mk_or [ b1; recur ~pol env p2 ])
  | Formula.BinaryOp (Formula.Imply, p1, p2, _) -> (
      match recur ~pol:(flip pol) env p1 with
      | F -> T
      | T -> recur ~pol env p2
      | _ -> raise (Decline "a predicate application under an implication"))
  | Formula.BinaryOp (((Formula.Iff | Formula.Xor) as op), p1, p2, _) -> (
      match (recur ~pol:None env p1, recur ~pol:None env p2) with
      | ((T | F) as b1), ((T | F) as b2) ->
          let eq =
            match (b1, b2) with T, T | F, F -> true | _ -> false
          in
          let r = match op with Formula.Iff -> eq | _ -> not eq in
          if r then T else F
      | _ ->
          raise (Decline "a predicate application under an equivalence"))
  | Formula.LetFormula (x, _, def, body, _) ->
      recur ~pol
        (Map.Poly.set env ~key:x ~data:(Evaluator.eval_term ~env def))
        body
  | Formula.Bind (binder, senv, body, _) -> (
      match (inst, binder, pol) with
      | Some inst, Formula.Forall, Some true
      | Some inst, Formula.Exists, Some false ->
          let choices =
            List.map senv ~f:(fun (x, s) ->
                match inst ~owner x s with
                | Some (_ :: _ as vs) -> List.map vs ~f:(fun v -> (x, v))
                | Some [] | None ->
                    raise
                      (Decline
                         ("no values to instantiate " ^ Ident.name_of_tvar x)))
          in
          let n =
            List.fold choices ~init:1 ~f:(fun n vs ->
                if n > max_combos then n else n * List.length vs)
          in
          if n > max_combos then
            raise (Decline "a binder with too many value combinations");
          let conj =
            match binder with Formula.Forall -> true | _ -> false
          in
          (* the combinations, enumerated with the short-circuit of the
             connective they are joined by *)
          let rec go acc env = function
            | [] -> recur ~pol env body :: acc
            | vs :: rest ->
                List.fold vs ~init:acc ~f:(fun acc (x, v) ->
                    match acc with
                    | F :: _ when conj -> acc
                    | T :: _ when not conj -> acc
                    | _ -> go acc (Map.Poly.set env ~key:x ~data:v) rest)
          in
          let bs = go [] env choices in
          if conj then mk_and (List.rev bs) else mk_or (List.rev bs)
      | _ -> raise (Decline "a quantifier"))
  | Formula.LetRec _ -> raise (Decline "a local recursive definition")

(** [decide ~atom_budget muclp]: see the head of this file for what an answer
    guarantees.  Requires [atom_budget >= 0].  Never raises except for the
    asynchronous exceptions [Common.Timer.is_async] names. *)
let rec decide ~atom_budget (muclp : Problem.t) : outcome * stats =
  decide_gen ~atom_budget ~inst:None muclp

(* [decide_gen ~inst:None] is [decide]; with [~inst:(Some (inst,
   max_combos))] the class test is skipped and every body is read by
   [ground_bf ~inst], so [Decided b] is the query's value in the weakened
   problem (see [refute_instance]) *)
and decide_gen ~atom_budget ~inst (muclp : Problem.t) : outcome * stats =
  let outcome, stats, _ = decide_full ~atom_budget ~inst muclp in
  (outcome, stats)

(* [decide_full]: [decide_gen], and with a [Decided] answer the reached atoms
   with their truth values in the solution that reads [fix] as greatest *)
and decide_full ~atom_budget ~inst (muclp : Problem.t) :
    outcome * stats * (Ident.pvar * Value.t list * bool) list option =
  let ground_bf ~owner env phi =
    match inst with
    | None -> ground_bf ~owner ~pol:(Some true) env phi
    | Some (inst, max_combos) ->
        ground_bf ~inst ~max_combos ~owner ~pol:(Some true) env phi
  in
  if Option.is_none inst && not (in_class muclp) then
    ( Declined "the query or a predicate reachable from it has a quantifier",
      empty_stats,
      None )
  else
    let defs = Hashtbl.create (module String) in
    List.iteri muclp.preds ~f:(fun i p ->
        Hashtbl.set defs ~key:(Ident.name_of_pvar p.Pred.name) ~data:(i, p));
    let ids = Hashtbl.create (module String) in
    let atoms = Stdlib.Dynarray.create () in
    let todo = Queue.create () in
    let intern (pv, vs) =
      let name = Ident.name_of_pvar pv in
      let key =
        String.concat ~sep:"\001" (name :: List.map vs ~f:key_of_value)
      in
      match Hashtbl.find ids key with
      | Some id -> A id
      | None ->
          let id = Stdlib.Dynarray.length atoms in
          if id >= atom_budget then raise Budget;
          let idx, pred =
            match Hashtbl.find defs name with
            | Some d -> d
            | None -> raise (Decline ("an undefined predicate " ^ name))
          in
          if List.length pred.Pred.args <> List.length vs then
            raise (Decline ("an arity mismatch at " ^ name));
          Hashtbl.set ids ~key ~data:id;
          Stdlib.Dynarray.add_last atoms (idx, pred, vs);
          Queue.enqueue todo id;
          A id
    in
    let bodies = Hashtbl.create (module Int) in
    let count () = Stdlib.Dynarray.length atoms in
    try
      let query =
        bind_bf ~f:intern (ground_bf ~owner:"query" Map.Poly.empty muclp.query)
      in
      while not (Queue.is_empty todo) do
        let id = Queue.dequeue_exn todo in
        let _, pred, vs = Stdlib.Dynarray.get atoms id in
        let env =
          Map.Poly.of_alist_exn
            (List.map2_exn pred.Pred.args vs ~f:(fun (x, _) v -> (x, v)))
        in
        Hashtbl.set bodies ~key:id
          ~data:
            (bind_bf ~f:intern
               (ground_bf ~owner:(Ident.name_of_pvar pred.Pred.name) env
                  pred.Pred.body))
      done;
      let n = count () in
      let has_mu_or_nu = ref false in
      let eqns ~mu_or_nu_as_nu =
        Array.init n ~f:(fun i ->
            let idx, pred, _ = Stdlib.Dynarray.get atoms i in
            let nu =
              match pred.Pred.kind with
              | Predicate.Mu -> false
              | Predicate.Nu -> true
              | Predicate.MuOrNu ->
                  has_mu_or_nu := true;
                  mu_or_nu_as_nu
            in
            Bes.{ rank = idx; nu; body = Hashtbl.find_exn bodies i })
      in
      let e1 = eqns ~mu_or_nu_as_nu:true in
      let comps = Bes.sccs e1 in
      let cyclic =
        List.filter comps ~f:(function
          | [ v ] ->
              let self = ref false in
              iter_atoms e1.(v).body ~f:(fun j -> if j = v then self := true);
              !self
          | _ -> true)
      in
      let stats =
        {
          atoms = n;
          sccs = List.length cyclic;
          largest_scc =
            List.fold cyclic ~init:0 ~f:(fun m c -> Int.max m (List.length c));
        }
      in
      let answer eqns =
        let v = Bes.solve eqns in
        (eval_bf ~f:(fun j -> v.(j)) query, v)
      in
      let b1, v1 = answer e1 in
      let valued () =
        Some
          (List.init n ~f:(fun i ->
               let _, pred, vs = Stdlib.Dynarray.get atoms i in
               (pred.Pred.name, vs, v1.(i))))
      in
      if !has_mu_or_nu then
        let b2, _ = answer (eqns ~mu_or_nu_as_nu:false) in
        if Bool.equal b1 b2 then (Decided b1, stats, valued ())
        else
          ( Declined
              "the answer depends on whether [fix] is read as a least or a \
               greatest fixpoint",
            stats,
            None )
      else (Decided b1, stats, valued ())
    with
    | Budget ->
        (Over_budget atom_budget, { empty_stats with atoms = count () }, None)
    | Decline reason ->
        (Declined reason, { empty_stats with atoms = count () }, None)
    | exn when not (Common.Timer.is_async exn) ->
        ( Declined ("an evaluation failed: " ^ Exn.to_string exn),
          { empty_stats with atoms = count () },
          None )

(** [true_atoms ~atom_budget muclp]: when [decide ~atom_budget muclp]
    answers [Decided true], the ground atoms reached from the query that are
    true in the solution reading [fix] as greatest, each as its predicate and
    its argument values, in the order they were reached; otherwise [Error]
    with the reason.

    Guarantees, under [decide]'s guarantee: the assignment [I] mapping each
    predicate [P] to the set of value tuples [vs] with [P(vs)] in the list
    satisfies [I(P)(vs) => body_P(vs)[I]] for every [P] and every [vs], and
    makes the query true; that is, [I] is a post-fixpoint of every equation
    read as a greatest fixpoint.  For [vs] outside [I(P)] the implication is
    trivial.  For [P(vs)] in the list, the BES solution [v] satisfies
    [v(P(vs)) = v(body)] (a solution of a Boolean equation system satisfies
    every equation whatever its sign), the body's theory atoms evaluate as
    [decide] evaluated them, and every atom the body mentions was reached
    and is read under [I] exactly as [v] reads it.  Every atom reached from
    the query through conjunctions only is true, so for a transition
    system's encoding (no disjunction among applications) every reachable
    state is among the atoms.  Reading [fix] as least gives the same query
    value ([decide] answers only then) but is not used.  The cost is
    [decide]'s once more. *)
let true_atoms ~atom_budget (muclp : Problem.t) :
    ((Ident.pvar * Value.t list) list, string) result =
  match decide_full ~atom_budget ~inst:None muclp with
  | Decided true, _, Some valued ->
      Ok
        (List.filter_map valued ~f:(fun (p, vs, b) ->
             if b then Some (p, vs) else None))
  | Decided true, _, None -> Error "no solution was kept"
  | Decided false, _, _ -> Error "the query is not valid"
  | Declined reason, _, _ -> Error reason
  | Over_budget k, _, _ -> Error (sprintf "more than %d reachable atoms" k)

(** {1 The step as an engine selects it} *)

(* Every muCLP engine (MuVal, MuStrat, MuCyc, Mu2CHC) has a field of this type
   named [ground_query_solve], and every one takes its default from
   [Config.default], so the one definition below decides for all of them
   whether a ground query is decided before the engine's own method runs.

   With [Ground_solve], a problem whose query is a Boolean combination of
   ground predicate applications, and whose predicates reachable from it have
   no quantifier, is decided by solving the parity game over the ground atoms
   reachable from the query ([decide]) when there are at most [atom_budget] of
   them; otherwise, or when an evaluation is refused, the problem goes to the
   engine unchanged.  The budget counts atoms, not time: the work spent
   before the problem is handed on is at most the budget times the largest
   predicate body.  The default budget, 20,000 atoms, is twice the largest
   reachable set decided on 265 closed termination and muCLP inputs (10,102
   atoms); the closed inputs it did not decide stayed over budget at 1,000,000
   atoms too, so a larger budget only buys more interning (4-17 us per atom)
   before the same hand-on.

   The default is on.  An answer is exact (the class and [decide]'s guarantee
   above), and on any other problem the step hands the problem on unchanged
   after at most the budget's work, so it is engine-independent: the same
   default serves every engine.  A decided answer does not come from the
   engine's method (no reduction, no strategy, no proof search), so a
   configuration that must run one method only (a paper's arm) states
   [No_ground_solve] explicitly. *)
module Config = struct
  let default_atom_budget = 20000

  type t =
    | No_ground_solve
    | Ground_solve of { atom_budget : int; [@default default_atom_budget] }
  [@@deriving yojson]

  (** the default of every engine's [ground_query_solve] field *)
  let default = Ground_solve { atom_budget = default_atom_budget }
end

(** [run ~phase ~report config muclp]: under [Ground_solve], the verdict
    [decide] reaches on [muclp], or [None] when it declines or the budget is
    exceeded; under [No_ground_solve], [None] without looking at [muclp].

    Sound for any muCLP: [decide]'s answer is the truth value of [muclp]'s
    query under the muCLP fixpoint semantics, so it is the answer of every
    problem equivalent to [muclp].  An engine calls it on the problem it is
    about to solve, or on an equivalent one (its optimizer's output); on
    [None] it solves that problem as it would have.  Assumes nothing else of
    [muclp]: free variables in the query, undefined predicates, quantifiers and
    interpretation-dependent evaluations are all refusals, never answers.
    The time spent is recorded under the phase [phase]; [report] receives one
    line saying what happened (outcome, atoms, cyclic components, seconds).
    Raises only the asynchronous exceptions [Common.Timer.is_async] names. *)
let run ~phase ~report (config : Config.t) (muclp : Problem.t) :
    Problem.solution option =
  match config with
  | Config.No_ground_solve -> None
  | Config.Ground_solve { atom_budget } ->
      let t0 = Common.PhaseTime.now () in
      let outcome, stats =
        Common.PhaseTime.with_phase phase @@ fun () ->
        decide ~atom_budget muclp
      in
      let what =
        match outcome with
        | Decided b -> if b then "valid" else "invalid"
        | Declined reason -> "declined (" ^ reason ^ ")"
        | Over_budget k -> sprintf "over budget (%d atoms)" k
      in
      report
        (sprintf
           "ground-solve: %s atoms=%d cyclic_sccs=%d largest_scc=%d time=%.3f"
           what stats.atoms stats.sccs stats.largest_scc
           (Common.PhaseTime.now () -. t0));
      (match outcome with
      | Decided true -> Some Problem.Valid
      | Decided false -> Some Problem.Invalid
      | Declined _ | Over_budget _ -> None)

(** {1 Refuting one instance of the universal binders} *)

(** [refute_instance ~atom_budget ~max_combos ~inst muclp]: [`Refuted] only
    when [muclp]'s query is false; [`Not_refuted reason] says nothing.

    The problem decided is the *weakening* [muclp'] of [muclp]: every binder
    read universally where it occurs (a [forall] in a positive position of the
    query or of a reachable predicate body, an [exists] in a negative one) is
    replaced by the conjunction (resp. disjunction) of its body over the
    values [inst] gives (at most [max_combos] combinations per binder; [inst]
    sees the owner's name, ["query"] for the query).  Each replacement is
    implied by what it replaces under every valuation and every
    interpretation of the predicates, and every body is monotone in the
    predicates, so by monotonicity of the nested fixpoints in their bodies
    the solution of [muclp] is pointwise below that of [muclp'], and the
    query of [muclp] (itself weakened the same way) implies the query of
    [muclp'].  So [muclp'] false makes [muclp] false, whatever [inst] chose:
    the values only decide whether a refutation is found, never whether it
    is right.  [muclp'] true says nothing about [muclp] and is reported as
    [`Not_refuted].  [muclp'] is decided by [decide_gen] (both readings of
    [fix], the atom budget); a binder of any other kind, at a mixed polarity
    or with no values is a refusal.  Raises only the asynchronous exceptions
    [Common.Timer.is_async] names. *)
let refute_instance ~atom_budget ~max_combos ~(inst : instantiation)
    (muclp : Problem.t) =
  let outcome, stats =
    decide_gen ~atom_budget ~inst:(Some (inst, max_combos)) muclp
  in
  ( (match outcome with
    | Decided false -> `Refuted
    | Decided true -> `Not_refuted "the weakened query holds"
    | Declined reason -> `Not_refuted ("declined (" ^ reason ^ ")")
    | Over_budget k -> `Not_refuted (sprintf "over budget (%d atoms)" k)),
    stats )
