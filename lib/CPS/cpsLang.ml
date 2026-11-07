(* The source calculus of the CPS-transformation framework and the target
   terms its schemes build.

   Source: a fine-grain call-by-value calculus with algebraic effects and
   deep handlers, the common shape of the calculi of Sekiyama and Unno
   ("Higher-Order Model Checking of Effect-Handling Programs with Answer-Type
   Modification", OOPSLA 2024), Sekiyama, Dal Lago and Unno ("On Higher-Order
   Model Checking of Effectful Answer-Type-Polymorphic Programs", OOPSLA 2025)
   and Kawamata, Unno, Sekiyama and Terauchi ("Answer Refinement
   Modification", POPL 2024):

     values        V ::= x | c | fun x -> M | (V1, ..., Vn)
     computations  M ::= return V | let x = M in N | V W | if V then M else N
                       | assert V | op(V1, ..., Vn) | with H handle M
                       | fail | rand_s | event a
     handlers      H ::= {return x -> M} + {op_i(y_i; k_i) -> M_i}

   Every computation node carries the computation sort at which it is used
   ([comp.ty], the field [comp] of the effect annotation), so a scheme reads
   the effect analysis through the node and never through OCaml syntax.
   Whether an operation call is answer-type preserving (ATP) or modifying
   (ATM), and whether a clause is tail-resumptive (TR), are fields too
   ([op_kind], [clause_kind]); the elaboration fills them from the effect
   analysis.

   Contract: constructors only, plus three total functions on them -- [vars]
   (every variable a term mentions, bound or free, which a scheme draws fresh
   names against), [equal_alpha] (syntactic equality up to the renaming of
   bound variables) and [eval_comp] (a reference interpreter: deep handlers,
   multi-shot continuations, [rand] as a nondeterministic choice explored
   left to right).  [run_program]'s result is an effect tree printed to a
   fuel bound; it is the meaning against which the elaboration is tested.

   Target: [tterm], a two-level lambda-calculus.  [TLam (captured, params,
   body)] is a dynamic abstraction that the HORS back end lifts to a
   nonterminal taking [captured @ params] and replaces by that nonterminal
   applied to [captured]; static abstractions are OCaml functions inside the
   schemes and never reach a [tterm], so no administrative redex survives a
   scheme (the two-level discipline of the papers above). *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

type tvar = Ident.tvar

(* A binder.  [scoped] says whether the variable is passed on to the
   abstractions lifted below it (an ordinary program variable), or is a
   parameter only of the abstraction that binds it (an intermediate result of
   A-normalisation, used once at the place it is bound). *)
type binder = { var : tvar; scoped : bool }

type const =
  | Bool of bool
  | Unit
  | Prim of string
      (** a Boolean primitive by its translation name: [Not], [And], [Or],
          [Imply], [Iff], [Xor] *)

type op_kind = ATM | ATP
type clause_kind = Clause_ATM | Clause_TR | Clause_FWD

type value =
  | Var of tvar * var_info
  | Const of const
  | Fun of binder * comp
      (** the function's own sort is the [ty.val_type] of the computation that
          returns it; the body carries its own sort *)
  | Tuple of value list

and var_info = {
  handled_rec : bool;
      (** a recursive variable used under a handler: today's generator inserts a
          coercion there *)
  at : Sort.c option;  (** the sort of the [return] that uses it *)
}

and comp = { desc : comp_desc; ty : Sort.c }

and comp_desc =
  | Return of value
  | Let of binder * comp * comp
  | App of value * value
  | If of value * comp * comp
  | Assert of value  (** [if V then return () else fail] *)
  | Op of string * value list * op_kind
  | Handle of handler * comp
  | Fail
  | Rand of Sort.t
  | Event of string

and handler = { ret : binder * comp; clauses : clause list }

and clause = {
  op : string;
  params : binder list;
  kont : binder;  (** the captured continuation (a placeholder when unused) *)
  body : comp;
  kind : clause_kind;
}

(* A top-level item: [let x = M] (the program's structure items, after the
   OCaml type checker).  A pure item is a definition; an impure one is run, in
   order, under the top-level handlers. *)
type item = { name : tvar; is_pure : bool; is_rec : bool; body : comp }

type program = {
  items : item list;
  eff_ops : (string * Sort.t) list option;
      (** the operations of the program's [eff] datatype in declaration order,
          with the CPS sort the effect analysis gives a handler of each (the
          fixed total order of operation names of the schemes) *)
  op_results : (string * Sort.t) list;
      (** the result sort each constructor of the [eff] GADT declares (its
          index), for the constructors whose index is a type; a top-level
          clause's node has one child per value of this sort, so its arity is
          a function of the declaration, as the specification's ranked
          alphabet is, and never of the instance at which this program
          performs the operation *)
}

let mk_comp ty desc = { desc; ty }
let var ?(handled_rec = false) ?at x = Var (x, { handled_rec; at })

(** {2 Variables} *)

let rec vars_value acc = function
  | Var (x, _) -> Set.add acc x
  | Const _ -> acc
  | Fun (b, m) -> vars_comp (Set.add acc b.var) m
  | Tuple vs -> List.fold vs ~init:acc ~f:vars_value

and vars_comp acc m =
  match m.desc with
  | Return v | Assert v -> vars_value acc v
  | Let (b, m1, m2) -> vars_comp (vars_comp (Set.add acc b.var) m1) m2
  | App (v, w) -> vars_value (vars_value acc v) w
  | If (v, m1, m2) -> vars_comp (vars_comp (vars_value acc v) m1) m2
  | Op (_, vs, _) -> List.fold vs ~init:acc ~f:vars_value
  | Handle (h, m) ->
      let x, mr = h.ret in
      let acc = vars_comp (vars_comp (Set.add acc x.var) mr) m in
      List.fold h.clauses ~init:acc ~f:(fun acc c ->
          let acc =
            List.fold c.params ~init:acc ~f:(fun a b -> Set.add a b.var)
          in
          vars_comp (Set.add acc c.kont.var) c.body)
  | Fail | Rand _ | Event _ -> acc

(* every variable, bound or free, of a program *)
let vars_program prog =
  List.fold prog.items ~init:Set.Poly.empty ~f:(fun acc it ->
      vars_comp (Set.add acc it.name) it.body)

(** {2 Alpha-equivalence} *)

(* [equal_alpha m1 m2]: the two terms are equal once bound variables are
   renamed consistently; sorts are not compared (they are annotations).
   Contract: an equivalence relation on terms; free variables must match by
   name. *)
let equal_alpha_comp m1 m2 =
  let lookup env x =
    match List.Assoc.find env x ~equal:Ident.tvar_equal with
    | Some y -> `Bound y
    | None -> `Free x
  in
  let eqv env1 env2 x y =
    match (lookup env1 x, lookup env2 y) with
    | `Bound i, `Bound j -> Ident.tvar_equal i j
    | `Free a, `Free b -> Ident.tvar_equal a b
    | _ -> false
  in
  let counter = ref 0 in
  let bind env1 env2 (b1 : binder) (b2 : binder) =
    incr counter;
    let z = Ident.Tvar (sprintf "#%d" !counter) in
    ((b1.var, z) :: env1, (b2.var, z) :: env2)
  in
  let rec value env1 env2 v1 v2 =
    match (v1, v2) with
    | Var (x, i1), Var (y, i2) ->
        eqv env1 env2 x y && Bool.equal i1.handled_rec i2.handled_rec
    | Const c1, Const c2 -> Stdlib.( = ) c1 c2
    | Fun (b1, m1), Fun (b2, m2) ->
        let env1, env2 = bind env1 env2 b1 b2 in
        comp env1 env2 m1 m2
    | Tuple vs1, Tuple vs2 -> (
        match List.for_all2 vs1 vs2 ~f:(value env1 env2) with
        | Ok b -> b
        | Unequal_lengths -> false)
    | _ -> false
  and comp env1 env2 m1 m2 =
    match (m1.desc, m2.desc) with
    | Return v1, Return v2 | Assert v1, Assert v2 -> value env1 env2 v1 v2
    | Let (b1, a1, c1), Let (b2, a2, c2) ->
        comp env1 env2 a1 a2
        &&
        let env1, env2 = bind env1 env2 b1 b2 in
        comp env1 env2 c1 c2
    | App (v1, w1), App (v2, w2) ->
        value env1 env2 v1 v2 && value env1 env2 w1 w2
    | If (v1, a1, b1), If (v2, a2, b2) ->
        value env1 env2 v1 v2 && comp env1 env2 a1 a2 && comp env1 env2 b1 b2
    | Op (o1, vs1, k1), Op (o2, vs2, k2) -> (
        String.equal o1 o2 && Stdlib.( = ) k1 k2
        &&
        match List.for_all2 vs1 vs2 ~f:(value env1 env2) with
        | Ok b -> b
        | Unequal_lengths -> false)
    | Handle (h1, c1), Handle (h2, c2) -> (
        comp env1 env2 c1 c2
        && (let (x1, r1), (x2, r2) = (h1.ret, h2.ret) in
            let env1, env2 = bind env1 env2 x1 x2 in
            comp env1 env2 r1 r2)
        &&
        match
          List.for_all2 h1.clauses h2.clauses ~f:(fun c1 c2 ->
              String.equal c1.op c2.op
              && Stdlib.( = ) c1.kind c2.kind
              &&
              match List.zip c1.params c2.params with
              | Unequal_lengths -> false
              | Ok ps ->
                  let env1, env2 =
                    List.fold ps ~init:(env1, env2) ~f:(fun (e1, e2) (p1, p2) ->
                        bind e1 e2 p1 p2)
                  in
                  let env1, env2 = bind env1 env2 c1.kont c2.kont in
                  comp env1 env2 c1.body c2.body)
        with
        | Ok b -> b
        | Unequal_lengths -> false)
    | Fail, Fail -> true
    | Rand _, Rand _ -> true
    | Event a, Event b -> String.equal a b
    | _ -> false
  in
  comp [] [] m1 m2

(** {2 Printing} *)

let rec str_of_value = function
  | Var (x, i) -> Ident.name_of_tvar x ^ if i.handled_rec then "!" else ""
  | Const (Bool b) -> Bool.to_string b
  | Const Unit -> "()"
  | Const (Prim p) -> p
  | Fun (b, m) ->
      sprintf "(fun %s -> %s)" (Ident.name_of_tvar b.var) (str_of_comp m)
  | Tuple vs -> "(" ^ String.concat_map_list ~sep:", " vs ~f:str_of_value ^ ")"

and str_of_comp m =
  match m.desc with
  | Return v -> "return " ^ str_of_value v
  | Let (b, m1, m2) ->
      sprintf "let %s = %s in %s" (Ident.name_of_tvar b.var) (str_of_comp m1)
        (str_of_comp m2)
  | App (v, w) -> sprintf "%s %s" (str_of_value v) (str_of_value w)
  | If (v, m1, m2) ->
      sprintf "if %s then %s else %s" (str_of_value v) (str_of_comp m1)
        (str_of_comp m2)
  | Assert v -> "assert " ^ str_of_value v
  | Op (o, vs, k) ->
      sprintf "%s%s(%s)" o
        (match k with ATP -> "@atp" | ATM -> "")
        (String.concat_map_list ~sep:", " vs ~f:str_of_value)
  | Handle (h, m) ->
      let x, mr = h.ret in
      sprintf "(with {return %s -> %s; %s} handle %s)"
        (Ident.name_of_tvar x.var) (str_of_comp mr)
        (String.concat_map_list ~sep:"; " h.clauses ~f:(fun c ->
             sprintf "%s(%s; %s)%s -> %s" c.op
               (String.concat_map_list ~sep:", " c.params ~f:(fun b ->
                    Ident.name_of_tvar b.var))
               (Ident.name_of_tvar c.kont.var)
               (match c.kind with
               | Clause_ATM -> ""
               | Clause_TR -> "@tr"
               | Clause_FWD -> "@fwd")
               (str_of_comp c.body)))
        (str_of_comp m)
  | Fail -> "fail"
  | Rand _ -> "rand"
  | Event a -> "event " ^ a

(** {2 Reference semantics} *)

(* Run-time values.  [RCont] is a captured continuation: resuming it
   re-installs the handler it was captured under (deep handlers). *)
type rvalue =
  | RBool of bool
  | RUnit
  | RTuple of rvalue list
  | RClos of (rvalue -> result)
  | RPrim of string * rvalue list
  | RCont of (rvalue -> result)

(* An effect tree: a computation returns, fails, emits an event, makes a
   nondeterministic choice, or calls an operation no handler catches, with
   the tree of each possible resumption. *)
and result =
  | Done of rvalue
  | Failed
  | Ev of string * (unit -> result)
  | Choice of (rvalue -> result)
  | Call of string * rvalue list * (rvalue -> result)

exception Stuck of string

let rec str_of_rvalue = function
  | RBool b -> if b then "tt" else "ff"
  | RUnit -> "unit"
  | RTuple vs -> "(" ^ String.concat_map_list ~sep:"," vs ~f:str_of_rvalue ^ ")"
  | RClos _ -> "<fun>"
  | RPrim (p, _) -> "<" ^ p ^ ">"
  | RCont _ -> "<cont>"

let prim p args =
  match (p, args) with
  | "Not", [ RBool b ] -> RBool (not b)
  | "And", [ RBool a; RBool b ] -> RBool (a && b)
  | "Or", [ RBool a; RBool b ] -> RBool (a || b)
  | "Imply", [ RBool a; RBool b ] -> RBool ((not a) || b)
  | "Iff", [ RBool a; RBool b ] -> RBool (Bool.equal a b)
  | "Xor", [ RBool a; RBool b ] -> RBool (not (Bool.equal a b))
  | _ -> RPrim (p, args)

let arity_of_prim = function "Not" -> 1 | _ -> 2

let rec bind r f =
  match r with
  | Done v -> f v
  | Failed -> Failed
  | Ev (a, k) -> Ev (a, fun () -> bind (k ()) f)
  | Choice k -> Choice (fun v -> bind (k v) f)
  | Call (o, vs, k) -> Call (o, vs, fun v -> bind (k v) f)

(* [eval_comp env m]: the effect tree of [m] in the environment [env] (an
   association list; a recursive definition is a closure that looks itself up
   through a reference).  Contract: [m]'s free variables are bound in [env];
   a free variable, an ill-typed application or an operation with the wrong
   number of arguments raises [Stuck]. *)
let rec eval_value env = function
  | Var (x, _) -> (
      match List.Assoc.find env x ~equal:Ident.tvar_equal with
      | Some v -> Lazy.force v
      | None -> raise (Stuck ("free variable " ^ Ident.name_of_tvar x)))
  | Const (Bool b) -> RBool b
  | Const Unit -> RUnit
  | Const (Prim p) -> RPrim (p, [])
  | Fun (b, body) ->
      RClos (fun v -> eval_comp ((b.var, Lazy.from_val v) :: env) body)
  | Tuple vs -> RTuple (List.map vs ~f:(eval_value env))

and apply f a =
  match f with
  | RClos f | RCont f -> f a
  | RPrim (p, args) ->
      let args = args @ [ a ] in
      Done
        (if List.length args >= arity_of_prim p then prim p args
         else RPrim (p, args))
  | _ -> raise (Stuck "application of a non-function")

and eval_comp env m =
  match m.desc with
  | Return v -> Done (eval_value env v)
  | Let (b, m1, m2) ->
      bind (eval_comp env m1) (fun v ->
          eval_comp ((b.var, Lazy.from_val v) :: env) m2)
  | App (v, w) -> apply (eval_value env v) (eval_value env w)
  | If (v, m1, m2) -> (
      match eval_value env v with
      | RBool true -> eval_comp env m1
      | RBool false -> eval_comp env m2
      | _ -> raise (Stuck "if on a non-Boolean"))
  | Assert v -> (
      match eval_value env v with
      | RBool true -> Done RUnit
      | RBool false -> Failed
      | _ -> raise (Stuck "assert on a non-Boolean"))
  | Op (o, vs, _) -> Call (o, List.map vs ~f:(eval_value env), fun v -> Done v)
  | Handle (h, body) -> handle env h (eval_comp env body)
  | Fail -> Failed
  | Rand _ -> Choice (fun v -> Done v)
  | Event a -> Ev (a, fun () -> Done RUnit)

and handle env h r =
  match r with
  | Done v ->
      let x, mr = h.ret in
      eval_comp ((x.var, Lazy.from_val v) :: env) mr
  | Failed -> Failed
  | Ev (a, k) -> Ev (a, fun () -> handle env h (k ()))
  | Choice k -> Choice (fun v -> handle env h (k v))
  | Call (o, vs, k) -> (
      match List.find h.clauses ~f:(fun c -> String.equal c.op o) with
      | None -> Call (o, vs, fun v -> handle env h (k v))
      | Some c -> (
          let resume = RCont (fun v -> handle env h (k v)) in
          match List.zip c.params vs with
          | Ok ps ->
              let env =
                (c.kont.var, Lazy.from_val resume)
                :: List.map ps ~f:(fun (b, v) -> (b.var, Lazy.from_val v))
                @ env
              in
              eval_comp env c.body
          | Unequal_lengths -> raise (Stuck ("arity of operation " ^ o))))

(* [show ~fuel r]: an effect tree printed to depth [fuel]; an escaping
   operation's resumptions are shown for the results [tt], [ff] and [unit],
   an ill-typed resumption as [!]. *)
let rec show ~fuel r =
  if fuel <= 0 then "..."
  else
    let sub r = try show ~fuel:(fuel - 1) r with Stuck _ -> "!" in
    match r with
    | Done v -> str_of_rvalue v
    | Failed -> "fail"
    | Ev (a, k) -> sprintf "%s(%s)" a (sub (k ()))
    | Choice k ->
        sprintf "rand(%s|%s)" (sub (k (RBool true))) (sub (k (RBool false)))
    | Call (o, vs, k) ->
        let res v = try sub (k v) with Stuck _ -> "!" in
        sprintf "%s[%s](%s|%s|%s)" o
          (String.concat_map_list ~sep:"," vs ~f:str_of_rvalue)
          (res (RBool true)) (res (RBool false)) (res RUnit)

(* [run_program ?fuel prog]: the printed effect tree of running the items of
   [prog] in order (pure ones as definitions, a recursive one bound to
   itself), whose answer is the last item's value *)
let run_program ?(fuel = 30) (prog : program) =
  let rec go env = function
    | [] -> Done RUnit
    | [ it ] when not it.is_pure -> eval_comp env it.body
    | it :: rest ->
        if it.is_pure && it.is_rec then (
          let self = ref (lazy (raise (Stuck "recursive value"))) in
          let env' = (it.name, lazy (Lazy.force !self)) :: env in
          let v =
            lazy
              (match eval_comp env' it.body with
              | Done v -> v
              | _ -> raise (Stuck "pure item"))
          in
          self := v;
          if List.is_empty rest then Done (Lazy.force v) else go env' rest)
        else
          bind (eval_comp env it.body) (fun v ->
              if List.is_empty rest then Done v
              else go ((it.name, Lazy.from_val v) :: env) rest)
  in
  try show ~fuel (go [] prog.items) with Stuck m -> "stuck: " ^ m

(** {2 Target terms} *)

type tterm =
  | TVar of tvar
  | TNt of tvar  (** a nonterminal with a fixed name (a top-level rule) *)
  | TTerm of string  (** a terminal of the generated tree *)
  | TApp of tterm * tterm
  | TLam of string * tvar list * tvar list * tterm
      (** [TLam (hint, captured, params, body)]: a dynamic abstraction; the HORS
          back end lifts it to a nonterminal named after [hint] with parameters
          [captured @ params] *)

let tapps t ts = List.fold ts ~init:t ~f:(fun t a -> TApp (t, a))
let tvar x = TVar x
