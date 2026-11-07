(* When a refutation of the HORS problems an EHMTT is reduced to is a
   refutation of the EHMTT itself.

   The reduction (Kobayashi, Tabuchi and Unno, "Higher-order multi-parameter
   tree transducers and recursion schemes for program verification", POPL
   2010; Unno, Tabuchi and Kobayashi, "Verification of tree-processing
   programs via higher-order model checking", APLAS 2010) abstracts an input
   tree by the state of the input automaton it is accepted from, and makes a
   fresh nondeterministic choice of a transition at every case analysis.  It
   is sound for every program: a satisfied problem set means a satisfied
   EHMTT.  Input trees may be infinite (the input automata are trivial
   automata, APLAS 2010, Definitions 2 and 3), and the reduction reads the
   input automaton over them: a transition with a child state that accepts
   no tree, finite or infinite, is dropped, so a case analysis explores only
   transitions some input uses.  It is complete only under three conditions
   (and with every input state of the main type accepting some tree), and a
   refutation outside them may be spurious:

   - the program is an HMTT, i.e. contains no coercion: a coercion's result is
     replaced by an arbitrary tree of the coercion's language, which may hold
     trees the program never builds;
   - the program is linear: along every reduction, each input tree is case
     analysed at most once.  Two case analyses of one tree make two
     independent choices in the abstraction, so a branch combination no real
     tree takes is explored;
   - the output automaton is deterministic, i.e. no state has two transitions
     on one symbol (the reduction adds a branching symbol to the output, and a
     nondeterministic automaton may reject a branching tree each of whose
     alternatives it accepts).  This concerns every state that reads a tree
     the program builds: those reached from the result state, and those
     reached from a state an argument passed to a function-typed parameter of
     the main type is checked against.

   Linearity is a semantic condition and in general undecidable; [check]
   decides a syntactic sufficient condition, so a program it calls nonlinear
   may still be linear, and then a refutation is only reported as not
   confirmed.  The condition:
   - the program analysed is the one the reduction checks: the input's rules,
     the tree copier, the rules standing for the most general values of the
     main type's function-typed parameters, and a start term applying the
     main non-terminal to its most general arguments (an input tree [Tree q]
     for a base type);
   - a closure analysis (0-CFA) computes which partial applications of
     non-terminals may flow into each parameter and result, so that an
     argument passed to a variable reaches the parameters of the
     non-terminals the variable may stand for;
   - a term is *tainted* when it may contain an input tree: a variable bound
     by a case pattern, a parameter that some call passes a tainted term,
     [gen q] or [coerce q t] (and an application with a tainted part);
   - every tainted variable occurs at most once along every path of its
     scope, counting a case analysis of it as an occurrence, summing over the
     arguments of an application and taking the maximum over the branches of
     a case.  Then no rewriting step duplicates a term holding an input
     tree, so every input tree has at most one occurrence along a path, and
     a case analysis consumes that occurrence: no tree is analysed twice;
   - [gen q] in the input's own rules is refused outright: whether two
     evaluations of one [gen q] are one tree or two is not settled here;
   - a program that writes the terminal [br] itself is refused outright too:
     the input language reads a program's [br] as nondeterministic choice, an
     extension of the papers' languages (which add [br] only in the
     reduction), and neither paper's completeness theorem covers it, so a
     refutation of such a program is reported only when a concrete run
     confirms it. *)
open Core
open Common.Ext
open Common.Combinator
open Ast
open Automata
open EHMTT

module S = Set.Make (String)

let name = Ident.name_of_tvar

(* Sets of abstract closures: [(f, k)] is the non-terminal [f] applied to
   its first [k] arguments, [k] below its arity. *)
module VS = struct
  type t = (string * int) Set.Poly.t

  let empty : t = Set.Poly.empty
  let singleton (v : string * int) : t = Set.Poly.singleton v
end

type state = {
  arity : (string, int) Hashtbl.t;
  bodies : (string, Ident.tvar list * term) Hashtbl.t;
  vals : (string, VS.t) Hashtbl.t;  (** "f#i" -> closures the parameter takes *)
  res : (string, VS.t) Hashtbl.t;  (** "f" -> closures its body evaluates to *)
  taint : (string, unit) Hashtbl.t;  (** "f#i" of every tainted parameter *)
  mutable changed : bool;
}

let key f i = f ^ "#" ^ string_of_int i
let get tbl k = Option.value ~default:VS.empty (Hashtbl.find tbl k)

let flow st tbl k vs =
  let old = get tbl k in
  if not (Set.is_subset vs ~of_:old) then (
    Hashtbl.set tbl ~key:k ~data:(Set.union old vs);
    st.changed <- true)

let mark st k =
  if not (Hashtbl.mem st.taint k) then (
    Hashtbl.set st.taint ~key:k ~data:();
    st.changed <- true)

(* A local environment maps a variable to [Some k], the parameter key it
   names, or [None] for a variable bound by a case pattern (an input
   tree). *)
let rec tainted st env = function
  | Var (x, _) -> (
      match Map.find env (name x) with
      | Some (Some k) -> Hashtbl.mem st.taint k
      | Some None -> true
      | None -> false)
  | Coerce _ | Tree _ -> true
  | Copy t -> tainted st env t
  | App (t1, t2) -> tainted st env t1 || tainted st env t2
  | Case (_, pats) ->
      List.exists pats ~f:(fun (_, (ys, t)) -> tainted st (bind env ys) t)
  | Nonterm f -> (
      (* a non-terminal without parameters is evaluated where it occurs *)
      match (Hashtbl.find st.arity (name f), Hashtbl.find st.bodies (name f)) with
      | Some 0, Some (_, body) -> tainted_closed st f body
      | _ -> false)
  | Fd _ | Term _ -> false
  | VarOrTerm _ -> failwith "Completeness.tainted"

and tainted_closed st f body =
  (* a parameterless rule taints through [gen] or [coerce] only; recursion
     through itself adds nothing *)
  let rec go seen = function
    | Coerce _ | Tree _ -> true
    | Copy t -> go seen t
    | App (t1, t2) -> go seen t1 || go seen t2
    | Case (_, pats) -> List.exists pats ~f:(fun (_, (_, t)) -> go seen t)
    | Nonterm g when not (Set.mem seen (name g)) -> (
        match
          (Hashtbl.find st.arity (name g), Hashtbl.find st.bodies (name g))
        with
        | Some 0, Some (_, b) -> go (Set.add seen (name g)) b
        | _ -> false)
    | Nonterm _ | Var _ | Fd _ | Term _ -> false
    | VarOrTerm _ -> failwith "Completeness.tainted_closed"
  in
  go (S.singleton (name f)) body

and bind env ys =
  List.fold ys ~init:env ~f:(fun env y -> Map.set env ~key:(name y) ~data:None)

(* [apply st env vs args]: the closures [vs] applied to [args]; flows the
   arguments' closures and taint into the parameters they reach and returns
   the closures of the result. *)
let rec apply st env vs args =
  Set.fold vs ~init:VS.empty ~f:(fun acc (f, k) ->
      let n = Option.value ~default:0 (Hashtbl.find st.arity f) in
      let rec go k = function
        | [] -> if k < n then VS.singleton (f, k) else get st.res f
        | a :: rest when k < n ->
            flow st st.vals (key f k) (eval st env a);
            if tainted st env a then mark st (key f k);
            go (k + 1) rest
        | rest -> apply st env (get st.res f) rest
      in
      Set.union acc (go k args))

(* [eval st env t]: the closures [t] may evaluate to, flowing what its
   applications pass. *)
and eval st env t =
  match t with
  | Var (x, _) -> (
      match Map.find env (name x) with
      | Some (Some k) -> get st.vals k
      | _ -> VS.empty)
  | Nonterm f -> (
      match Hashtbl.find st.arity (name f) with
      | Some 0 -> get st.res (name f)
      | Some _ -> VS.singleton (name f, 0)
      | None -> VS.empty)
  | App _ -> (
      let head, args = fun_and_args t in
      (* Arguments can contain calls even when the head is a terminal passed
         through a variable, for which there is no abstract closure. *)
      List.iter args ~f:(fun a -> ignore (eval st env a : VS.t));
      match head with
      | Term _ -> VS.empty
      | _ -> apply st env (eval st env head) args)
  | Case (_, pats) ->
      List.fold pats ~init:VS.empty ~f:(fun acc (_, (ys, t)) ->
          Set.union acc (eval st (bind env ys) t))
  | Coerce (_, t, _) | Copy t ->
      ignore (eval st env t : VS.t);
      VS.empty
  | Fd _ | Term _ | Tree _ -> VS.empty
  | VarOrTerm _ -> failwith "Completeness.eval"

let start_name = "__start"

let analyse (rules : t) start =
  let st =
    {
      arity = Hashtbl.create (module String);
      bodies = Hashtbl.create (module String);
      vals = Hashtbl.create (module String);
      res = Hashtbl.create (module String);
      taint = Hashtbl.create (module String);
      changed = true;
    }
  in
  (* the program's names are unique (the reduction refuses a non-terminal
     defined twice); the start rule's name is none of them *)
  let rules = (Ident.Tvar start_name, ([], start)) :: rules in
  List.iter rules ~f:(fun (f, (xs, body)) ->
      if not (Hashtbl.mem st.arity (name f)) then (
        Hashtbl.set st.arity ~key:(name f) ~data:(List.length xs);
        Hashtbl.set st.bodies ~key:(name f) ~data:(xs, body)));
  let env_of f xs =
    List.foldi xs ~init:String.Map.empty ~f:(fun i env x ->
        Map.set env ~key:(name x) ~data:(Some (key f i)))
  in
  while st.changed do
    st.changed <- false;
    Hashtbl.iteri st.bodies ~f:(fun ~key:f ~data:(xs, body) ->
        flow st st.res f (eval st (env_of f xs) body))
  done;
  (st, env_of)

(* The occurrences of each variable along the worst path of [t]: a sum over
   the parts of an application, a maximum over the branches of a case, and
   one for the analysed variable of a case.  Variables bound inside [t] are
   left out. *)
let rec occurrences t : int String.Map.t =
  let sum = Map.merge_skewed ~combine:(fun ~key:_ a b -> a + b) in
  match t with
  | Var (x, _) -> String.Map.singleton (name x) 1
  | App (t1, t2) -> sum (occurrences t1) (occurrences t2)
  | Coerce (_, t, _) | Copy t -> occurrences t
  | Case (x, pats) ->
      let branches =
        List.map pats ~f:(fun (_, (ys, t)) ->
            List.fold ys ~init:(occurrences t) ~f:(fun m y ->
                Map.remove m (name y)))
      in
      sum
        (String.Map.singleton (name x) 1)
        (List.fold branches ~init:String.Map.empty
           ~f:(Map.merge_skewed ~combine:(fun ~key:_ a b -> max a b)))
  | Fd _ | Nonterm _ | Term _ | Tree _ -> String.Map.empty
  | VarOrTerm _ -> failwith "Completeness.occurrences"

(* The tainted variables that may be used more than once along a path, as
   ["F.x"]. *)
let duplicated st env_of =
  let bad = ref [] in
  let check f scope vars =
    let m = occurrences scope in
    List.iter vars ~f:(fun x ->
        match Map.find m (name x) with
        | Some k when k > 1 -> bad := (f ^ "." ^ name x) :: !bad
        | _ -> ())
  in
  let rec binders f = function
    | Case (_, pats) ->
        List.iter pats ~f:(fun (_, (ys, t)) ->
            check f t ys;
            binders f t)
    | App (t1, t2) ->
        binders f t1;
        binders f t2
    | Coerce (_, t, _) | Copy t -> binders f t
    | Var _ | Fd _ | Nonterm _ | Term _ | Tree _ -> ()
    | VarOrTerm _ -> failwith "Completeness.duplicated"
  in
  Hashtbl.iteri st.bodies ~f:(fun ~key:f ~data:(xs, body) ->
      let env = env_of f xs in
      check f body
        (List.filter xs ~f:(fun x ->
             match Map.find env (name x) with
             | Some (Some k) -> Hashtbl.mem st.taint k
             | _ -> false));
      binders f body);
  List.sort ~compare:String.compare !bad

let rec has_gen = function
  | Tree _ -> true
  | App (t1, t2) -> has_gen t1 || has_gen t2
  | Coerce (_, t, _) | Copy t -> has_gen t
  | Case (_, pats) -> List.exists pats ~f:(fun (_, (_, t)) -> has_gen t)
  | Fd _ | Nonterm _ | Term _ | Var _ -> false
  | VarOrTerm _ -> failwith "Completeness.has_gen"

(* [writes_br t] holds when [t] contains the terminal [br], the input
   language's nondeterministic choice. *)
let rec writes_br = function
  | Term a -> String.equal (name a) "br"
  | App (t1, t2) -> writes_br t1 || writes_br t2
  | Coerce (_, t, _) | Copy t -> writes_br t
  | Case (_, pats) -> List.exists pats ~f:(fun (_, (_, t)) -> writes_br t)
  | Fd _ | Nonterm _ | Tree _ | Var _ -> false
  | VarOrTerm _ -> failwith "Completeness.writes_br"

(* [checked_states typ] is the states the reduction's most general value of
   a main-type parameter of type [typ] checks an argument against, in the
   output automaton: for [typ = t1 -> ... -> tn -> q], the result state of
   each [ti] (the argument the program passes in that position), and those
   of the most general values it hands to a function-typed [ti] in turn.  It
   follows [EHMTT.of_type] and [EHMTT.check_arg].  The argument is a tree
   the program builds, with choice nodes where it analyses an input, so a
   nondeterministic state among these breaks completeness as one reached
   from the result does: the choice is read from one transition for all of
   its alternatives. *)
let rec checked_states typ =
  List.concat_map (fst (RefType.args_and_ret typ)) ~f:(fun arg ->
      let args, ret = RefType.args_and_ret arg in
      List.map (RefType.attr_of ret) ~f:name
      @ List.concat_map args ~f:checked_states)

(* [check ~program ~start ~user_rules trs typ] is [Ok ()] when the
   conditions above hold, so a refutation of the HORS problems refutes the
   EHMTT, and otherwise [Error reasons], each reason a clause.  [program]
   and [start] are the program the reduction checks and its start term,
   [user_rules] the input's own rules, [trs] the automaton and [typ] the
   main type, whose result state the output automaton starts from. *)
let check ~(program : t) ~start ~(user_rules : t) (trs : TTA.pre_trs) typ =
  let reasons = ref [] in
  let add r = reasons := r :: !reasons in
  let ncoerce =
    List.sum (module Int) user_rules ~f:(snd >> snd >> count_coerce)
  in
  if ncoerce > 0 then
    add
      (sprintf
         "the program has %d coercion(s), whose results the reduction \
          over-approximates"
         ncoerce);
  if List.exists user_rules ~f:(snd >> snd >> has_gen) then
    add "the program uses gen";
  (* guarantees: [Ok ()] only for a program whose own rules never write
     [br], so an [unsat] for a program that does rests on a confirming run *)
  if List.exists user_rules ~f:(snd >> snd >> writes_br) then
    add
      "the program writes br (nondeterministic choice), for which the \
       reduction's completeness is not established";
  (let st, env_of = analyse program start in
   match duplicated st env_of with
   | [] -> ()
   | vs ->
       add
         (sprintf
            "linearity is not established: %s may be used more than once"
            (String.concat ~sep:", " vs)));
  (* the theorems take every input state to stand for some input; the
     reduction answers a base parameter whose state accepts no tree, finite
     or infinite, as vacuously satisfied before any refutation, but a state
     of a function-typed parameter accepting no tree leaves open which
     functions the type holds *)
  (let inhabited = inhabited_states trs in
   match
     List.filter
       (List.dedup_and_sort ~compare:String.compare
          (List.concat_map (fst (RefType.args_and_ret typ))
             ~f:(RefType.attr_of >> List.map ~f:name)))
       ~f:(Set.mem inhabited >> not)
   with
   | [] -> ()
   | qs ->
       add
         (sprintf
            "the input state(s) %s of the main type accept no tree, finite or \
             infinite"
            (String.concat ~sep:", " qs)));
  (match RefType.args_and_ret typ with
  | params, RefType.Base q -> (
      let table = TTA.make trs in
      (* the output automaton reads the program's result from [q] and every
         argument the program hands a function-typed parameter from the
         state its type demands ([checked_states]); a choice node may sit
         under either *)
      let reach =
        List.reachable
          (name q :: List.concat_map params ~f:checked_states)
          (fun s ->
            match List.Assoc.find ~equal:String.equal table s with
            | Some body -> TTA.next_ids_body body
            | None -> [])
      in
      let nondet =
        List.filter reach ~f:(fun s ->
            match List.Assoc.find ~equal:String.equal table s with
            | Some body ->
                List.contains_dup ~compare:String.compare (List.map ~f:fst body)
            | None -> false)
      in
      match nondet with
      | [] -> ()
      | ss ->
          add
            (sprintf
               "the output automaton is not deterministic (state(s) %s have \
                two transitions on one symbol)"
               (String.concat ~sep:", " ss)))
  | _ -> ());
  match List.rev !reasons with [] -> Ok () | rs -> Error rs
