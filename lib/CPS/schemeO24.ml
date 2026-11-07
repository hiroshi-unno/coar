(* Scheme O24: the CPS transformation of Sekiyama and Unno, "Higher-Order
   Model Checking of Effect-Handling Programs with Answer-Type Modification"
   (OOPSLA 2024), Fig. 7, as a rule table for [CpsScheme.Traverse].

   A computation is translated to a static function of its contextual
   argument [ctx = { hs; k }]: one handler per operation slot, in the fixed
   order of the program's [eff] datatype, and a continuation.  The rules
   (Fig. 7; [ [[M]][vh | vk] ] is [comp m ctx]):

     [[return V]][vh | vk]          = vk [[V]]
     [[let x = M1 in M2]][vh | vk]  = [[M1]][vh | lam x. [[M2]][vh | vk]]
     [[V1 V2]][vh | vk]             = [[V1]] [[V2]] vh vk
     [[op(V)]][vh | vk]             = vh_op [[V]] vk
     [[with H handle M]][vh | vk]   = [[M]][V1..Vn | lam x. [[M_r]]] vh vk,
                                      Vi = lam x_i, k_i. [[M_i]]
     [[fun x -> M]]                 = lam x, h, k. [[M]][h | k]

   with every dynamic abstraction lifted to a nonterminal over the variables
   in scope ([TLam]'s captured list, the order of the HORS EffCaml has
   always produced).  The operation rule is the figure's non-eta-expanded
   form ([vk] passed as it is): it is eta-equal to the expanded one, and the
   continuation here is always a lifted nonterminal.  ATP calls are
   translated as ATM calls (O24 has no ATP operations).

   Two places where the HORS target needs more than the figure, and how each
   is decided:
   - [if] and [assert]: the terminal [if] takes ground arguments, so each
     branch is applied to eta parameters, one handler per slot and a
     continuation per contextual layer of the answer, and the lifted
     continuation that binds the condition takes them as parameters.  The
     number of layers is [eta_mode]: [Legacy_guess] is one layer exactly when
     the node's signature is non-empty, today's generator's choice (it
     ignores the answer type, a suspected defect); [Answer_type] counts the
     layers of the final answer type, the figure's reading.  [fail] under k
     layers is a closed abstraction over the eta parameters.
   - A recursive variable used under a handler is wrapped in the coercion
     [Cast1 f x hs1 k1 hs2 k2 = f x hs2 (Cast2 k1 hs2 k2)],
     [Cast2 k1 hs2 k2 x = k1 x hs2 k2]: the call runs with the outer handlers
     [hs2] and drops [hs1].  It is the shape of OOPSLA 2025 Example 6.2's
     coercion and is right only when the handler's clauses for the callee's
     operations forward unchanged; it is kept, unchanged, so that this scheme
     reproduces today's generator.

   Contract: [comp st m ctx] is the image of [m]; it requires (G2-legacy)
   that [ctx.hs] holds a handler for every operation [m] performs, and
   refuses (exception [Refused]) a construct with no rule here ([rand],
   [event]), a handled operation with no clause, and a node whose
   translation would need eta parameters in a position no lifted
   continuation binds.  Fresh names avoid [st.taken] and the scope (G4). *)

open Core
open Ast
open Ast.LogicOld
open CpsLang

exception Refused of string

let refuse fmt = ksprintf (fun s -> raise (Refused s)) fmt

type eta_mode = Legacy_guess | Answer_type

type st = {
  scope : tvar list;  (** the variables a lifted abstraction captures *)
  ntenv : (tvar, tterm) Map.Poly.t;
      (** top-level pure definitions: a variable stands for its nonterminal *)
  taken : tvar -> bool;
  eff_ops : (string * Sort.t) list option;
  eta_mode : eta_mode;
}

type ctx = { hs : (string * tterm) list; k : tterm }
type v = tterm
type c = ctx -> tterm * tvar list

let name = "O24"

(* the operation slots of a signature: the program's [eff] operations when
   it declares them, else the signature's own entries *)
let slots st (o : Sort.o) =
  match st.eff_ops with
  | Some ops -> List.map ops ~f:fst
  | None -> (
      match o with Sort.OpSig (map, _) -> List.map map ~f:fst | _ -> [])

let fresh st prefix =
  Ident.mk_fresh_tvar_avoiding ~prefix
    ~taken:(fun v -> st.taken v || List.mem st.scope v ~equal:Ident.tvar_equal)
    ()

let fresh_hs st (o : Sort.o) =
  List.map (slots st o) ~f:(fun op -> (op, fresh st "h"))

let rec layers (c : Sort.c) =
  match c.cont_eff with
  | Sort.Eff (_, c_fin) -> 1 + layers c_fin
  | _ -> if Sort.is_empty_opsig c.op_sig then 0 else 1

let eta_params st (m : comp) =
  let n =
    match st.eta_mode with
    | Legacy_guess -> (
        match m.ty.op_sig with
        | Sort.OpSig (map, _) -> if List.is_empty map then 0 else 1
        | _ -> 0)
    | Answer_type -> (
        match m.ty.cont_eff with Sort.Eff (_, c_fin) -> layers c_fin | _ -> 0)
  in
  List.concat
  @@ List.init n ~f:(fun _ ->
      List.map (fresh_hs st m.ty.op_sig) ~f:snd @ [ fresh st "k" ])

let no_extra what (t, extra) =
  if List.is_empty extra then t
  else refuse "[O24] %s: eta parameters with no continuation to bind them" what

let var st x (info : var_info) =
  let xt = match Map.Poly.find st.ntenv x with Some t -> t | None -> TVar x in
  if not info.handled_rec then xt
  else
    let n =
      match info.at with Some c -> List.length (slots st c.op_sig) | None -> 0
    in
    let f = Ident.Tvar "f" and x = Ident.Tvar "x" in
    let hs1 = List.init n ~f:(fun i -> Ident.Tvar ("h1_" ^ string_of_int i)) in
    let hs2 = List.init n ~f:(fun i -> Ident.Tvar ("h2_" ^ string_of_int i)) in
    let k1 = Ident.Tvar "k1" and k2 = Ident.Tvar "k2" in
    let cast2 =
      TLam
        ( "Cast2",
          (k1 :: hs2) @ [ k2 ],
          [ x ],
          tapps (TVar k1) (List.map ((x :: hs2) @ [ k2 ]) ~f:tvar) )
    in
    let cast1 =
      TLam
        ( "Cast1",
          [],
          (f :: x :: hs1) @ (k1 :: hs2) @ [ k2 ],
          tapps (TVar f) (List.map (x :: hs2) ~f:tvar @ [ cast2 ]) )
    in
    TApp (cast1, xt)

let const _st = function
  | Bool true -> TTerm "tt"
  | Bool false -> TTerm "ff"
  | Unit -> TTerm "unit"
  | Prim p -> TNt (Ident.Tvar p)

let fun_ st (b : binder) (body : comp) k =
  let hs = fresh_hs st body.ty.op_sig in
  let kv = fresh st "k" in
  let params = (b.var :: List.map hs ~f:snd) @ [ kv ] in
  let t =
    no_extra "function body"
    @@ k
         { st with scope = st.scope @ params }
         { hs = List.map hs ~f:(fun (op, h) -> (op, TVar h)); k = TVar kv }
  in
  TLam ("Lam", st.scope, params, t)

let tuple _st vs = tapps (TTerm ("tuple" ^ string_of_int (List.length vs))) vs
let return_ _st _m v ctx = (TApp (ctx.k, v), [])

let let_ st _m (b : binder) c1 k2 ctx =
  let st2 = if b.scoped then { st with scope = st.scope @ [ b.var ] } else st in
  let t2, extra = k2 st2 ctx in
  let kl = TLam ("Klet", st.scope, b.var :: extra, t2) in
  (no_extra "let-bound computation" (c1 { ctx with k = kl }), [])

(* handlers restricted to the slots of the node's own signature, in slot
   order (the arity discipline |h| = |C.Sigma|, under the slot order above) *)
let restrict st (m : comp) ctx =
  List.map (slots st m.ty.op_sig) ~f:(fun op ->
      match List.Assoc.find ctx.hs op ~equal:String.equal with
      | Some h -> h
      | None -> refuse "[O24] %s handler not passed" op)

let app st m v w ctx = (tapps v ((w :: restrict st m ctx) @ [ ctx.k ]), [])

let if_ st m v c1 c2 ctx =
  let etas = eta_params st m in
  let branch c = tapps (no_extra "branch" (c ctx)) (List.map etas ~f:tvar) in
  (tapps (TTerm "if") [ v; branch c1; branch c2 ], etas)

let assert_ st m v ctx =
  let etas = eta_params st m in
  ( tapps (TTerm "if")
      [
        v;
        tapps (TApp (ctx.k, TTerm "unit")) (List.map etas ~f:tvar);
        TTerm "fail";
      ],
    etas )

let fail st m _ctx =
  match eta_params st m with
  | [] -> (TTerm "fail", [])
  | etas -> (TLam ("Kasr", [], etas, TTerm "fail"), [])

let op _st _m o vs _kind ctx =
  match List.Assoc.find ctx.hs o ~equal:String.equal with
  | Some h -> (tapps h (vs @ [ ctx.k ]), [])
  | None -> refuse "[O24] %s handler not passed" o

let handle st (m : comp) (h : handler) ~ret ~clauses c_body ctx =
  let body = match m.desc with Handle (_, body) -> body | _ -> assert false in
  let x_r, m_r = h.ret in
  let hs_r = fresh_hs st m_r.ty.op_sig in
  let k_r = fresh st "k" in
  let params_r = (x_r.var :: List.map hs_r ~f:snd) @ [ k_r ] in
  let t_r =
    no_extra "return clause"
    @@ ret
         { st with scope = st.scope @ params_r }
         { hs = List.map hs_r ~f:(fun (op, h) -> (op, TVar h)); k = TVar k_r }
  in
  let term_r = TLam ("Kret", st.scope, params_r, t_r) in
  let terms_h =
    List.map (slots st body.ty.op_sig) ~f:(fun op ->
        match
          List.find_mapi h.clauses ~f:(fun i cl ->
              if String.equal cl.op op then Some (cl, List.nth_exn clauses i)
              else None)
        with
        | None -> refuse "[O24] %s not found among the handler's clauses" op
        | Some (cl, k_cl) ->
            let hs_c = fresh_hs st cl.body.ty.op_sig in
            let k_c = fresh st "k" in
            let params =
              List.map cl.params ~f:(fun b -> b.var)
              @ (cl.kont.var :: List.map hs_c ~f:snd)
              @ [ k_c ]
            in
            let t =
              no_extra "clause"
              @@ k_cl
                   { st with scope = st.scope @ params }
                   {
                     hs = List.map hs_c ~f:(fun (op, h) -> (op, TVar h));
                     k = TVar k_c;
                   }
            in
            (op, TLam ("Khnd", st.scope, params, t)))
  in
  let t_b = no_extra "handled body" (c_body { hs = terms_h; k = term_r }) in
  (tapps t_b (List.map ctx.hs ~f:snd @ [ ctx.k ]), [])

let rand _ _ _ _ = refuse "[O24] rand has no rule"
let event _ _ _ _ = refuse "[O24] events have no rule"
