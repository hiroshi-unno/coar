(* The effect annotation the framework reads: the shared interface of the MB
   effect analysis (the symbol A and its fields comp, pure, ans, modifies,
   kind, sig, clause), read off the elaborated tree.

   Where the fields come from: the elaboration ([CpsElab]) runs the MB
   constraint generation of [RCaml.MBcgen] and its solver [RCaml.MBcsol], and
   stores at every computation node the solved computation sort of the
   node's position ([comp.ty]); an operation call's kind and a clause's kind
   are stored on the node by the elaboration from [MBcgen]'s own decision.
   This module only interprets those sorts.

   Fields not available from today's analysis, said here so that no consumer
   assumes them: [own] (the sort a node's own rule derives, before
   subsumption) and therefore [emb] (an embedding of a pure computation where
   an impure one is expected) -- [MBcgen]'s callbacks see only the expected
   sort.  A scheme that needs [emb] (the selective one of OOPSLA 2025) must
   refuse until the analysis exposes it.

   The contract of the interface, as postconditions a consumer may check:
   (A2) groundness -- no sort, effect or row variable in any annotation;
   (A4) kind discipline -- an ATP call is handled only by a TR or forwarding
   clause.  [check] reports every violation; it decides nothing, since
   today's analysis leaves unconstrained variables (it is not (A2)-complete)
   and today's clause kinds are syntactic. *)

open Core
open Ast.LogicOld
open CpsLang

let comp (m : comp) = m.ty
let pure (m : comp) = Sort.is_pure m.ty.cont_eff

(* [ans m]: the initial and final answer types of an impure node *)
let ans (m : comp) =
  match m.ty.cont_eff with Sort.Eff (c1, c2) -> Some (c1, c2) | _ -> None

(* [modifies m]: proper answer-type modification, compared syntactically on
   the solved sorts (two equal sorts written differently count as
   modifying, which only over-reports) *)
let modifies m =
  match ans m with
  | Some (c1, c2) ->
      not (String.equal (Term.str_of_triple c1) (Term.str_of_triple c2))
  | None -> false

let kind (m : comp) = match m.desc with Op (_, _, k) -> Some k | _ -> None

(* [sig_of h m]: the operations a handling construct [with h handle m]
   handles, each with its clause kind *)
let sig_of (h : handler) = List.map h.clauses ~f:(fun c -> (c.op, c.kind))

let clause (h : handler) op =
  List.find_map h.clauses ~f:(fun c ->
      if String.equal c.op op then Some c.kind else None)

(* the latent non-handler effect of a node (a proposed field, not part of the
   MB analysis): [Cont] when the node may reach [rand], [fail], an event or an
   [assert], or calls a function (conservatively: a call may reach one).
   Contract: an over-approximation -- every node that can reach such an
   effect is marked. *)
type latent = LNone | LCont

let rec latent (m : comp) =
  match m.desc with
  | Rand _ | Fail | Event _ | Assert _ | App _ -> LCont
  | Return _ | Op _ -> LNone
  | Let (_, m1, m2) | If (_, m1, m2) -> join (latent m1) (latent m2)
  | Handle (h, body) ->
      List.fold h.clauses
        ~init:(join (latent body) (latent (snd h.ret)))
        ~f:(fun acc c -> join acc (latent c.body))

and join a b = match (a, b) with LNone, LNone -> LNone | _ -> LCont

(** {2 Contract checks} *)

let rec ground_sort = function
  | Sort.SVar _ -> false
  | Sort.SArrow (s, c) -> ground_sort s && ground_triple c
  | Sort.SPoly (_, s) -> ground_sort s
  | T_tuple.STuple ss -> List.for_all ss ~f:ground_sort
  | _ -> true

and ground_triple (c : Sort.c) =
  ground_opsig c.op_sig && ground_sort c.val_type && ground_eff c.cont_eff

and ground_eff = function
  | Sort.EVar _ -> false
  | Sort.Eff (c1, c2) -> ground_triple c1 && ground_triple c2
  | _ -> true

and ground_opsig = function
  | Sort.OpSig (map, rv) ->
      Option.is_none rv && List.for_all map ~f:(fun (_, s) -> ground_sort s)
  | _ -> true

(* [check prog]: the violations of (A2) and (A4) on an elaborated program,
   one line each (empty when none) *)
let check (prog : program) =
  let out = ref [] in
  let report fmt = ksprintf (fun s -> out := s :: !out) fmt in
  let rec go handlers (m : comp) =
    if not (ground_triple m.ty) then
      report "A2: non-ground sort %s at %s" (Term.str_of_triple m.ty)
        (String.prefix (str_of_comp m) 60);
    match m.desc with
    | Return v | Assert v -> value handlers v
    | Let (_, m1, m2) ->
        go handlers m1;
        go handlers m2
    | If (v, m1, m2) ->
        value handlers v;
        go handlers m1;
        go handlers m2
    | App (v, w) ->
        value handlers v;
        value handlers w
    | Op (o, vs, k) -> (
        List.iter vs ~f:(value handlers);
        match k with
        | ATP -> (
            match List.find_map handlers ~f:(fun h -> clause h o) with
            | Some Clause_ATM ->
                report "A4: ATP call of %s handled by an ATM clause" o
            | _ -> ())
        | ATM -> ())
    | Handle (h, body) ->
        go (h :: handlers) body;
        go handlers (snd h.ret);
        List.iter h.clauses ~f:(fun c -> go handlers c.body)
    | Fail | Rand _ | Event _ -> ()
  and value handlers = function
    | Fun (_, m) ->
        go [] m (* a function body runs under its caller's handlers *)
    | Tuple vs -> List.iter vs ~f:(value handlers)
    | Var _ | Const _ -> ()
  in
  List.iter prog.items ~f:(fun it -> go [] it.body);
  List.rev !out
