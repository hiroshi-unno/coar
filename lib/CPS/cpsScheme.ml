(* A CPS scheme is a rule table; the traversal that applies it is one and the
   same for every scheme.

   [SCHEME] fixes, for one transformation, the target of a value ([v]) and of
   a computation ([c], for the two-level schemes a static function from the
   contextual argument to a target term), the traversal state passed down
   ([st]: what is in scope, how fresh names are drawn), and one rule per
   construct of [CpsLang].  A rule receives its children already translated;
   a child under a binder is passed as a function of the state, so that the
   scheme alone decides which variables the binder (and the scheme's own
   handler and continuation parameters) adds to the state.  The selection of
   direct style versus CPS, the eta-expansion and the coercions are the
   rules' business, read from the node's annotation ([CpsAnnot]).

   [Traverse (S)] is the generic traversal.  Contract: it visits every node of
   the input exactly once, bottom-up through the rules (a child under a binder
   when the rule calls its function), and passes each rule the node it
   translates, so a rule can read the node's sort; it adds nothing of its own
   to the output.  Hence (rule identity) the output of [Traverse (S)] is the
   composition of [S]'s rules along the term, and a scheme whose rules are a
   transcription of a paper's figure produces that figure's image.

   [Identity] is the scheme whose rules rebuild their node: [Traverse
   (Identity)] is the identity on terms, which is the test that the
   traversal reaches every node and every binder. *)

open Core
open CpsLang

module type SCHEME = sig
  type st
  type v
  type c

  val name : string
  val var : st -> tvar -> var_info -> v
  val const : st -> const -> v

  val fun_ : st -> binder -> comp -> (st -> c) -> v
  (** [fun_ st x body k]: the function [fun x -> body], [k] translating the body
      in the state the rule chooses *)

  val tuple : st -> v list -> v
  val return_ : st -> comp -> v -> c
  val let_ : st -> comp -> binder -> c -> (st -> c) -> c
  val app : st -> comp -> v -> v -> c
  val if_ : st -> comp -> v -> c -> c -> c
  val assert_ : st -> comp -> v -> c
  val op : st -> comp -> string -> v list -> op_kind -> c

  val handle :
    st -> comp -> handler -> ret:(st -> c) -> clauses:(st -> c) list -> c -> c
  (** [handle st m h ~ret ~clauses body]: [clauses] in the order of [h.clauses]
  *)

  val fail : st -> comp -> c
  val rand : st -> comp -> Ast.LogicOld.Sort.t -> c
  val event : st -> comp -> string -> c
end

module Traverse (S : SCHEME) = struct
  let rec value st = function
    | Var (x, i) -> S.var st x i
    | Const c -> S.const st c
    | Fun (b, m) -> S.fun_ st b m (fun st' -> comp st' m)
    | Tuple vs -> S.tuple st (List.map vs ~f:(value st))

  and comp st (m : comp) =
    match m.desc with
    | Return v -> S.return_ st m (value st v)
    | Let (b, m1, m2) -> S.let_ st m b (comp st m1) (fun st' -> comp st' m2)
    | App (v, w) -> S.app st m (value st v) (value st w)
    | If (v, m1, m2) -> S.if_ st m (value st v) (comp st m1) (comp st m2)
    | Assert v -> S.assert_ st m (value st v)
    | Op (o, vs, k) -> S.op st m o (List.map vs ~f:(value st)) k
    | Handle (h, body) ->
        S.handle st m h
          ~ret:(fun st' -> comp st' (snd h.ret))
          ~clauses:(List.map h.clauses ~f:(fun cl st' -> comp st' cl.body))
          (comp st body)
    | Fail -> S.fail st m
    | Rand s -> S.rand st m s
    | Event a -> S.event st m a
end

module Identity :
  SCHEME with type st = unit and type v = value and type c = comp = struct
  type st = unit
  type v = value
  type c = comp

  let name = "identity"
  let var () x i = Var (x, i)
  let const () c = Const c
  let fun_ () b _ k = Fun (b, k ())
  let tuple () vs = Tuple vs
  let return_ () m v = { m with desc = Return v }
  let let_ () m b c1 k2 = { m with desc = Let (b, c1, k2 ()) }
  let app () m v w = { m with desc = App (v, w) }
  let if_ () m v c1 c2 = { m with desc = If (v, c1, c2) }
  let assert_ () m v = { m with desc = Assert v }
  let op () m o vs k = { m with desc = Op (o, vs, k) }

  let handle () m h ~ret ~clauses body =
    let x, _ = h.ret in
    let clauses =
      List.map2_exn h.clauses clauses ~f:(fun cl k -> { cl with body = k () })
    in
    { m with desc = Handle ({ ret = (x, ret ()); clauses }, body) }

  let fail () m = m
  let rand () m _ = m
  let event () m _ = m
end
