(* Confirming a refutation of an EHMTT verification problem by running the
   program on concrete input trees.

   The semantics is the call-by-name operational semantics of EHMTTs of Unno,
   Tabuchi and Kobayashi, "Verification of tree-processing programs via
   higher-order model checking" (APLAS 2010, Fig. 2 and Definition 3), which
   coincides with that of Kobayashi, Tabuchi and Unno (POPL 2010) on programs
   without coercions.  A problem (P, M1, ..., Mk, M) fails when, for some
   input trees Ti accepted by Mi,
   (1) the program reaches a term whose output prefix -- its outermost
       constructors, every other subterm read as the leaf [⊥] -- is rejected
       by M with [⊥] accepted from every state, or
   (2) it reaches a coercion [coerce_L t] in an evaluation position and [t]
       reaches a term whose output prefix is not a prefix of any tree of L
       (the coercion's assertion fails).
   [search] looks for such inputs.  It enumerates finite input trees from the
   input automaton, smallest first, evaluates the program on each tuple, and
   checks the explored prefix of the output, and of every coerced tree the
   evaluation demands, against the automata.  Whatever it reports is a real
   violation, for these reasons:
   - every value it computes is reached by reductions of the semantics in
     evaluation positions (under an output constructor, in a case's
     scrutinee, under a coercion, or in the head of an application), so the
     explored prefix is below the output prefix of a reachable term; a
     subterm left unexplored (out of budget, or never demanded) is [⊥], which
     only makes the check accept more;
   - the trees accepted with [⊥] read as an accepting leaf are closed under
     replacing subtrees by [⊥], so a prefix rejected below a reachable
     term's prefix means the reachable term's prefix is rejected too;
   - a shared argument is evaluated once and its value reused (call by
     need); the semantics is deterministic apart from [gen] (refused below),
     so the value is the one each copy would reach;
   - an enumerated input tree is built from the automaton's transitions, so
     it is accepted.
   A search that finds nothing proves nothing: the inputs and the budgets
   are bounded, and the inputs of the problem may be infinite trees (the
   input automata are trivial automata, APLAS 2010, Definitions 2 and 3)
   while only finite ones are enumerated, so a violation reached only on an
   input a state accepts as an infinite tree (as [qs cons -> qa qs] with no
   leaf transition accepts only infinite lists) is never confirmed.  The
   finite trees are among the inputs, so whatever is found is a violation
   under that reading too.

   What is evaluated is the program the reduction checks: the input's rules
   (one per name: the reduction refuses a non-terminal defined twice) and the
   tree copier, under its own fresh name, standing for [copy t].  A case
   whose input node matches no branch is the reduction's failure terminal
   (passed as [~fail], drawn fresh against the program's names, so no state
   accepts it), as in the semantics and the reduction.  Not handled, and
   reported as such: [gen] (a nondeterministic choice of an input tree), a
   main type with a function-typed parameter (the search has no concrete
   functions to pass), and an ill-sorted term (a case on an output tree, an
   application of an input tree).

   The terminal [br] is the language's nondeterministic choice, a [br] node
   standing for the set of its children: the output and the coerced trees
   are checked against the automaton with [q br -> q q] added for every
   state [q] (the reduction refuses an automaton with a [br] transition of
   its own), so a [br] node is accepted exactly when every choice is; and a
   case analysis of a [br] node resolves the choice, continuing with one
   child, as the recursion schemes with finite data of Kobayashi, Tabuchi
   and Unno (POPL 2010) reduce [br u1 ... un] to some [ui].  Each case
   analysis resolves independently.  A run takes its choices from a list
   (the second child where it says [true], the first once it is used up),
   and [search] tries every choice list up to a small length, so a violation
   reported is the outcome of one sequence of choices the semantics allows. *)
open Core
open Common.Ext
open Ast
open Automata
open EHMTT

let name = Ident.name_of_tvar

(* A finite prefix of a tree: [Bot] stands for a subtree not computed. *)
type prefix = Node of string * prefix list | Bot

let rec pr_prefix ppf = function
  | Bot -> Format.fprintf ppf "_"
  | Node (a, []) -> Format.fprintf ppf "%s" a
  | Node (a, ts) -> Format.fprintf ppf "%s(%a)" a (List.pr pr_prefix ",") ts

(* A finite input tree. *)
type itree = I of string * itree list

let rec prefix_of_itree (I (a, ts)) = Node (a, List.map ts ~f:prefix_of_itree)

(* The evaluator's budget ran out. *)
exception Out_of_fuel

(* A coercion's assertion fails: the coercion's state and the prefix of the
   coerced tree that no tree of its language extends. *)
exception Coercion_failed of string * prefix

(* The program is outside what the evaluator handles. *)
exception Unsupported of string

type thunk = { mutable st : st }

and st =
  | Delayed of term * env
  | O2i of thunk  (** an output tree read as an input tree *)
  | Value of whnf
  | Gave_up  (** forcing it ran out of budget once; it stays [⊥] *)

and whnf =
  | Con of string * thunk list
      (** a terminal applied to its arguments so far: an output tree when they
          are all there *)
  | In of string * thunk list  (** an input tree's node *)
  | Pap of string * thunk list
      (** a non-terminal applied to fewer arguments than it has parameters *)

and env = thunk String.Map.t

type program = {
  rules : (string, string list * term) Hashtbl.t;
  mutable fuel : int;
  fail : string;  (** the terminal of a case with no branch for its node *)
  mutable choices : bool list;
      (** the choices still to take at a case on a [br] node: [true] for the
          second child; the first child once the list is used up *)
  mutable chosen : int;  (** how many such choices the run has made *)
}

let tick p =
  if p.fuel <= 0 then raise Out_of_fuel;
  p.fuel <- p.fuel - 1

(* [budgeted p n f] runs [f] with at most [n] of the remaining budget and
   answers [None] when that runs out; the steps [f] took are spent. *)
let budgeted p n f =
  let outer = p.fuel in
  let n = min n outer in
  p.fuel <- n;
  let restore () = p.fuel <- outer - (n - p.fuel) in
  match f () with
  | r ->
      restore ();
      Some r
  | exception Out_of_fuel ->
      restore ();
      None
  | exception e ->
      restore ();
      raise e

let unsupported fmt = Printf.ksprintf (fun s -> raise (Unsupported s)) fmt

(* The automata: [trs] lists every state's transitions. *)
type automaton = {
  trs : TTA.trs;
  nonempty : String.Set.t;
  ranks : (string, int) List.Assoc.t;  (** each terminal's number of children *)
}

let transitions a q =
  Option.value ~default:[] (List.Assoc.find ~equal:String.equal a.trs q)

(* The states that accept some tree, finite or infinite: the greatest set
   [X] such that every state of [X] has a transition whose children's states
   are all in [X] (an accepting run is then built top-down inside [X]). *)
let nonempty_states (trs : TTA.trs) =
  let rec go x =
    let x' =
      Set.filter x ~f:(fun q ->
          List.exists
            (Option.value ~default:[]
               (List.Assoc.find ~equal:String.equal trs q))
            ~f:(fun (_, qs) -> List.for_all qs ~f:(Set.mem x)))
    in
    if Set.equal x x' then x else go x'
  in
  let all =
    String.Set.of_list
      (List.concat_map trs ~f:(fun (q, body) ->
           q :: List.concat_map body ~f:snd))
  in
  go all

(* The terminal of nondeterministic choice, which the input language
   reserves: a [br] node stands for the set of its children, and the
   specification accepts it from a state when both children are accepted
   from it, as the reduction reads it. *)
let br_symbol = "br"
let with_choice (trs : TTA.pre_trs) = TTA.add_br_transitions ~br:br_symbol trs

let automaton_of trs =
  {
    trs;
    nonempty = nonempty_states trs;
    ranks =
      List.concat_map trs ~f:(fun (_, body) ->
          List.map body ~f:(fun (c, qs) -> (c, List.length qs)));
  }

(* [accepting a ~bot p] is the set of states from which the automaton has a
   run on the prefix [p] in which a leaf [Bot] may take any state of [bot]:
   bottom-up, a node [c(p1, ..., pn)] takes [q] when some transition
   [q c -> q1 ... qn] has every [qi] accepting [pi].  [None] stands for
   every state. *)
let rec accepting a ~bot = function
  | Bot -> bot
  | Node (c, ps) ->
      let accs = List.map ps ~f:(accepting a ~bot) in
      let ok qs =
        List.length qs = List.length accs
        && List.for_all2_exn qs accs ~f:(fun q acc ->
            match acc with None -> true | Some s -> Set.mem s q)
      in
      Some
        (String.Set.of_list
           (List.filter_map a.trs ~f:(fun (q, body) ->
                if
                  List.exists body ~f:(fun (c', qs) ->
                      String.equal c c' && ok qs)
                then Some q
                else None)))

(* membership in a set of states where [None] stands for every state *)
let mem_or_all q = function None -> true | Some s -> Set.mem s q

(* Condition (1): a prefix of the output is accepted with [Bot] read as an
   accepting leaf from any state. *)
let output_accepts a q p = mem_or_all q (accepting a ~bot:None p)

(* Condition (2): a prefix of a coerced tree is a prefix of some tree of the
   coercion's language, i.e. [Bot] may stand for any tree accepted from its
   state, which needs a state that accepts something. *)
let coercion_accepts a q p = mem_or_all q (accepting a ~bot:(Some a.nonempty) p)

let rec eval p (aut : automaton) env t =
  tick p;
  match t with
  | Var (x, _) -> force p aut (lookup env x)
  | Nonterm f -> enter p aut (name f) []
  | Term c -> Con (name c, [])
  | App _ ->
      let head, args = fun_and_args t in
      let args = List.map args ~f:(fun a -> { st = Delayed (a, env) }) in
      apply p aut (eval p aut env head) args
  | Case (x, pats) -> (
      let c, children = resolve p aut (lookup env x) in
      match List.find pats ~f:(fun (c', _) -> String.equal (name c') c) with
      | Some (_, (ys, body)) ->
          if List.length ys <> List.length children then
            unsupported
              "a case branch for %s binds %d variables, the node has %d" c
              (List.length ys) (List.length children);
          let env =
            List.fold2_exn ys children ~init:env ~f:(fun env y th ->
                Map.set env ~key:(name y) ~data:th)
          in
          eval p aut env body
      | None -> Con (p.fail, []))
  | Coerce (q, t', _) -> coerce p aut (name q) { st = Delayed (t', env) }
  | Tree q -> unsupported "gen %s" (name q)
  | Copy _ -> unsupported "copy not expanded"
  | Fd _ | VarOrTerm _ -> unsupported "a term of the reduction's own syntax"

and lookup env x =
  match Map.find env (name x) with
  | Some th -> th
  | None -> unsupported "unbound variable %s" (name x)

and enter p aut f args =
  match Hashtbl.find p.rules f with
  | None -> unsupported "no rule for %s" f
  | Some (xs, body) ->
      let n = List.length xs in
      if List.length args < n then Pap (f, args)
      else
        let now, rest = List.split_n args n in
        let env =
          List.fold2_exn xs now ~init:String.Map.empty ~f:(fun env x th ->
              Map.set env ~key:x ~data:th)
        in
        let w = eval p aut env body in
        if List.is_empty rest then w else apply p aut w rest

and apply p aut w args =
  match w with
  | Pap (f, args0) -> enter p aut f (args0 @ args)
  | Con (c, args0) -> Con (c, args0 @ args)
  | In (c, _) -> unsupported "the input tree %s applied" c

and force p aut th =
  match th.st with
  | Value w -> w
  | Gave_up -> raise Out_of_fuel
  | Delayed (t, env) ->
      let w = eval p aut env t in
      th.st <- Value w;
      w
  | O2i th' ->
      let w =
        match force p aut th' with
        | Con (c, cs) -> In (c, List.map cs ~f:(fun c -> { st = O2i c }))
        | In _ as w -> w
        | Pap (f, _) -> unsupported "the function %s read as a tree" f
      in
      th.st <- Value w;
      w

(* [resolve p aut th] is the node a case analysis of [th] reads: a [br]
   node is a choice, resolved by the next entry of [p.choices], and the
   chosen child is read in its place, so the node returned is never [br]. *)
and resolve p aut th =
  match force_input p aut th with
  | c, [ l; r ] when String.equal c br_symbol ->
      let second =
        match p.choices with
        | b :: rest ->
            p.choices <- rest;
            b
        | [] -> false
      in
      p.chosen <- p.chosen + 1;
      resolve p aut (if second then r else l)
  | node -> node

and force_input p aut th =
  match force p aut th with
  | In (c, cs) -> (c, cs)
  | Con (c, _) -> unsupported "a case on the output tree %s" c
  | Pap (f, _) -> unsupported "a case on the function %s" f

(* [coerce_L t] in an evaluation position: the assertion is checked on the
   prefix of [t] explored within a budget, then [t] is read as an input
   tree. *)
and coerce p aut q th =
  let pre = explore p aut th ~budget:assert_budget in
  if not (coercion_accepts aut q pre) then raise (Coercion_failed (q, pre));
  match force p aut th with
  | Con (c, cs) -> In (c, List.map cs ~f:(fun c -> { st = O2i c }))
  | In _ as w -> w
  | Pap (f, _) -> unsupported "coerce of the function %s" f

(* [explore p aut th ~budget] is a prefix of the output tree [th] evaluates
   to, its depth doubled while the budget lasts; a subtree whose
   evaluation runs out of its share is [Bot] for good. *)
and explore p aut th ~budget =
  let per_node = max 1 (budget / 4) in
  let rec go depth th =
    if depth = 0 then (Bot, true)
    else (
      (* visiting a node already computed costs a step too, so that
         re-reading the prefix at each deepening is paid for *)
      tick p;
      match th.st with
      | Gave_up -> (Bot, false)
      | _ -> (
          match budgeted p per_node (fun () -> force p aut th) with
          | None ->
              th.st <- Gave_up;
              (Bot, false)
          | Some (Con (c, cs))
            when match List.Assoc.find ~equal:String.equal aut.ranks c with
                 | Some n -> n <> List.length cs
                 | None -> false ->
              (* not a ranked tree, so not an output Definition 3 speaks of *)
              unsupported "the terminal %s with %d children" c (List.length cs)
          | Some (Con (c, cs)) ->
              let ps, cut =
                List.fold_right cs ~init:([], false) ~f:(fun c (ps, cut) ->
                    let p', cut' = go (depth - 1) c in
                    (p' :: ps, cut || cut'))
              in
              (Node (c, ps), cut)
          | Some (In (c, _)) -> unsupported "an input tree %s in the output" c
          | Some (Pap (f, _)) -> unsupported "a function %s in the output" f))
  in
  let result = ref Bot in
  (match
     budgeted p budget (fun () ->
         let rec deepen d =
           let pre, cut = go d th in
           result := pre;
           if cut then deepen (2 * d)
         in
         deepen 1)
   with
  | Some () | None -> ());
  !result

and assert_budget = 20_000

(* [trees_of_size trs ~cap q n] lists the trees with [n] nodes that the
   automaton [trs] accepts from [q], at most [cap] of them (those found
   first), memoised. *)
let trees_of_size (trs : TTA.trs) ~cap =
  let memo = Hashtbl.Poly.create () in
  let rec trees q n =
    if n <= 0 then []
    else
      match Hashtbl.find memo (q, n) with
      | Some ts -> ts
      | None ->
          let body =
            Option.value ~default:[] (List.Assoc.find ~equal:String.equal trs q)
          in
          let ts =
            Sequence.of_list body
            |> Sequence.concat_map ~f:(fun (c, qs) ->
                Sequence.map (forests qs (n - 1)) ~f:(fun ts -> I (c, ts)))
            |> Fn.flip Sequence.take cap |> Sequence.to_list
            |> List.dedup_and_sort ~compare:Stdlib.compare
          in
          Hashtbl.set memo ~key:(q, n) ~data:ts;
          ts
  (* the tuples of trees accepted from [qs], of total size [n] *)
  and forests qs n =
    match qs with
    | [] -> if n = 0 then Sequence.singleton [] else Sequence.empty
    | q :: rest ->
        Sequence.range 1 (n + 1)
        |> Sequence.concat_map ~f:(fun k ->
            Sequence.of_list (trees q k)
            |> Sequence.concat_map ~f:(fun t ->
                Sequence.map (forests rest (n - k)) ~f:(fun ts -> t :: ts)))
  in
  (trees, forests)

(* A confirmed counterexample: the input trees and the violation. *)
type witness = {
  inputs : itree list;
  violation : [ `Output of prefix | `Coercion of string * prefix ];
}

let pr_witness ppf w =
  Format.fprintf ppf "on the input%s %a, "
    (if List.length w.inputs = 1 then "" else "s")
    (List.pr pr_prefix ", ")
    (List.map w.inputs ~f:prefix_of_itree);
  match w.violation with
  | `Output p ->
      Format.fprintf ppf
        "the program's output begins %a, which the output automaton rejects"
        pr_prefix p
  | `Coercion (q, p) ->
      Format.fprintf ppf
        "a coercion to %s is applied to a tree beginning %a, which no tree \
         accepted from %s extends"
        q pr_prefix p q

let program_of ~fail ~choices rules =
  let tbl = Hashtbl.create (module String) in
  List.iter rules ~f:(fun (f, (xs, body)) ->
      (* names are unique (the reduction refuses a duplicate) *)
      if not (Hashtbl.mem tbl (name f)) then
        Hashtbl.set tbl ~key:(name f) ~data:(List.map xs ~f:name, body));
  { rules = tbl; fuel = 0; fail; choices; chosen = 0 }

(* [run ~rules ~fail ~choices ~aut ~main ~result inputs ~fuel] evaluates
   the main non-terminal [main] on the input trees [inputs] with at most
   [fuel] steps, taking the choices at a case on a [br] node from [choices],
   and answers the violation found, if any, the explored output prefix
   ([Bot] after a failed coercion), the steps taken and the number of
   choices made.  The output is checked from the state [result].  [rules]
   must have [copy t] expanded; [fail] is the terminal of an unmatched case,
   one [aut] does not read.  Raises [Unsupported]. *)
let run ~rules ~fail ?(choices = []) ~(aut : automaton) ~main ~result inputs
    ~fuel =
  let p = program_of ~fail ~choices rules in
  p.fuel <- fuel;
  let rec thunk_of (I (c, ts)) =
    { st = Value (In (c, List.map ts ~f:thunk_of)) }
  in
  let var i = "in" ^ string_of_int i in
  let out =
    {
      st =
        Delayed
          ( apps (Nonterm (Ident.Tvar main))
              (List.mapi inputs ~f:(fun i _ ->
                   Var (Ident.Tvar (var i), ref EHMTT.In))),
            String.Map.of_alist_exn
              (List.mapi inputs ~f:(fun i t -> (var i, thunk_of t))) );
    }
  in
  let violation, pre =
    match explore p aut out ~budget:fuel with
    | pre ->
        if output_accepts aut result pre then (None, pre)
        else (Some (`Output pre), pre)
    | exception Coercion_failed (q, pre) -> (Some (`Coercion (q, pre)), Bot)
  in
  (violation, pre, fuel - p.fuel, p.chosen)

(* The output prefix of the main non-terminal on [inputs], for testing the
   evaluator against the generated recursion scheme.  Raises [Unsupported]
   and [Coercion_failed]. *)
let output_prefix ~rules ~fail ~trs ~main inputs ~fuel =
  let _, pre, _, _ =
    run ~rules ~fail
      ~aut:(automaton_of (TTA.make (with_choice trs)))
      ~main ~result:"" inputs ~fuel
  in
  pre

(* The search's bounds: the total size of an input tuple, the number of
   tuples, the steps per tuple and the steps in all. *)
type bounds = {
  max_size : int;
  max_candidates : int;
  fuel_per_run : int;
  total_fuel : int;
  max_choices : int;
      (** the length of the longest choice list tried on one input tuple *)
}

(* Every list of [k] choices but the all-[false] one, which the run taking
   every first child has covered. *)
let choice_lists k =
  let rec all k =
    if k = 0 then [ [] ]
    else List.concat_map (all (k - 1)) ~f:(fun l -> [ false :: l; true :: l ])
  in
  List.filter (all k) ~f:(List.exists ~f:Fn.id)

let default_bounds =
  {
    max_size = 20;
    max_candidates = 5_000;
    fuel_per_run = 1_000_000;
    total_fuel = 50_000_000;
    max_choices = 4;
  }

(* [search ?bounds ~rules ~copier ~fail trs (main, typ)] looks for input
   trees on which the EHMTT [rules] (with [copy t] not expanded; [copier]
   the tree copier's name, whose rule [rules] must contain; [fail] the
   reduction's terminal of an unmatched case) violates the
   specification [typ] over the automaton [trs].  [Ok (Some w)] is a real
   counterexample; [Ok None] means none was found within [bounds]; [Error]
   says why the program cannot be searched. *)
let search ?(bounds = default_bounds) ~rules ~copier ~fail (trs : TTA.pre_trs)
    (main, typ) =
  match RefType.args_and_ret typ with
  | args, RefType.Base result -> (
      let arg_states =
        List.map args ~f:(function
          | RefType.Base q -> Some (name q)
          | Func _ -> None)
      in
      match Option.all arg_states with
      | None ->
          Error
            "the main type has a function-typed parameter, for which the \
             search has no concrete function"
      | Some arg_states -> (
          let rules = expandCopy ~copier rules in
          let table = TTA.make trs in
          (* inputs are read from the automaton as given, outputs and
             coerced trees checked with [br] read as choice *)
          let aut = automaton_of (TTA.make (with_choice trs)) in
          let _, forests = trees_of_size table ~cap:bounds.max_candidates in
          let candidates =
            Sequence.range 0 (bounds.max_size + 1)
            |> Sequence.concat_map ~f:(forests arg_states)
            |> Fn.flip Sequence.take bounds.max_candidates
          in
          let total = ref bounds.total_fuel in
          try
            Ok
              (Sequence.find_map candidates ~f:(fun inputs ->
                   if !total <= 0 then None
                   else
                     let attempt choices =
                       if !total <= 0 then (None, 0)
                       else
                         let violation, _, used, chosen =
                           run ~rules ~fail ~choices ~aut ~main:(name main)
                             ~result:(name result) inputs
                             ~fuel:(min bounds.fuel_per_run !total)
                         in
                         total := !total - used;
                         (violation, chosen)
                     in
                     (* the run taking every first child, then, if it made
                        choices, every other choice list as long as the
                        number it made, up to [max_choices] *)
                     let found =
                       match attempt [] with
                       | (Some _ as v), _ -> v
                       | None, 0 -> None
                       | None, chosen ->
                           let k = min chosen bounds.max_choices in
                           List.find_map (choice_lists k) ~f:(fun cs ->
                               fst (attempt cs))
                     in
                     Option.map found ~f:(fun violation ->
                         { inputs; violation })))
          with Unsupported msg -> Error msg))
  | _ -> Error "the main type does not end in a state"
