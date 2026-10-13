(* A satisfiability question that constrains an array only cell by cell, asked
   with the array eliminated.

   WHY.  The counterexample question for a candidate invariant that states a
   universal over the cells of an array -- [forall t. a[t] = t \/ G(t)], with
   [G] linear over [t] and the clause's integers -- asks for an array meeting a
   universal, together with a few reads [a[s]] at ground indices.  A model
   needs [a] to be the identity at all but finitely many cells, which a
   solver's function graph (finite entries and one constant default) cannot
   write: Z3 (5.1.0) runs such a question to any budget given, asked as an
   array or with the array as an uninterpreted function.  The question with
   the array eliminated below is quantifier-free in the array and is answered
   in milliseconds.

   THE REWRITE.  Let [a : Array Int Int] be a free variable of [psi] whose
   every occurrence, after reading over writes, is a read [a[s]], where either
   [s] mentions no bound variable (a GROUND read) or the read lies in a
   top-level conjunct [forall t. B(t)] of one integer variable with [s] being
   [t] itself.  Write [S = {s1..sn}] for the distinct ground indices, [v_i]
   for fresh integers, [Phi(t, v)] for the conjunction of the universals'
   bodies with [a[t]] replaced by [v] and every [a[s_i]] by [v_i].  Then

     exists a. psi(a)
       <=> exists v1..vn.  psi'  /\  /\_i Phi(s_i, v_i)
                           /\ /\_{i<j} (s_i = s_j -> v_i = v_j)
                           /\ forall t. (\/_i t = s_i) \/ exists v. Phi(t, v)

   where [psi'] is [psi] without the universals and with [a[s_i]] replaced by
   [v_i].  Left to right, take [v_i = a[s_i]].  Right to left, in the standard
   array structure (arrays of [Int] to [Int] are all functions), take [a(t) =
   v_i] at [t = s_i] (well defined by the consistency conjuncts) and a witness
   of [exists v. Phi(t, v)] elsewhere; every read of [a] is then accounted for.
   A countermodel in the standard structure is a countermodel of the clause,
   and a refutation of the rewritten question refutes the original in every
   model of the array theory (the left-to-right direction holds in every
   model), so [sat] and [unsat] both carry over.

   [exists v. Phi(t, v)] is eliminated exactly when [Phi] is quantifier-free
   and [v] occurs in it only in integer (dis)equations [l = r] in which [v]
   has coefficient 1 or -1, each then solved as [v = e_j] with [e_j] free of
   [v]: since [Int] is infinite, some value differs from every [e_j], and
   at that value every such equation is false, so

     exists v. Phi(t, v)  <=>  \/_j Phi(t, e_j)  \/  Phi(t, generic)

   with [Phi(t, generic)] being [Phi] with each equation [v = e_j] false (each
   disequation true).  An array outside this fragment is left to the solver.

   BEFORE THE ELIMINATION.  A top-level conjunct that is a Boolean equation
   with the literal [true] or [false] on one side is read as the formula on the
   other (an [ite] of formulas as its two cases); a top-level disjunction one
   of whose disjuncts equates an array variable to a term is split into one
   question per disjunct (at most [max_cases]); in each, an equation [x = t]
   between a free array variable and a term without [x] is solved by
   substituting [t] for [x] (the one-point rule), and a top-level existential
   is replaced by fresh free variables.  Each step is satisfiability
   preserving, and a model of the result extends to one of the input.

   CONTRACT.  [rewrite psi] returns [Error reason] when no array was
   eliminated in any case (nothing is gained), and otherwise the cases, whose
   disjunction is equisatisfiable with [psi]; [read_back c m] turns a model of
   case [c]'s formula into a model of [psi] -- every free variable of [psi]
   given a value (an eliminated array a [lambda], a substituted one its
   defining term evaluated there), the fresh variables dropped.  Nothing here
   asks a solver. *)

open Core
open Common.Ext
open LogicOld

exception Skip of string

let max_cases = 8

(* ---- reading Boolean equations as formulas ---- *)

let rec formula_of_bool_term (t : Term.t) : Formula.t option =
  match t with
  | Term.FunApp (T_bool.Formula phi, [], _) -> Some phi
  | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _) -> (
      match (formula_of_bool_term c, formula_of_bool_term a, formula_of_bool_term b)
      with
      | Some c, Some a, Some b ->
          Some
            (Formula.mk_or (Formula.mk_and c a)
               (Formula.mk_and (Formula.mk_neg c) b))
      | _ -> None)
  | _ -> None

let bool_literal (t : Term.t) =
  match formula_of_bool_term t with
  | Some phi when Formula.is_true phi -> Some true
  | Some phi when Formula.is_false phi -> Some false
  | _ -> None

(* an atom [lit = t] or [lit != t] with [lit] a Boolean literal, read as the
   formula [t] stands for *)
let view_atom (atm : Atom.t) : Formula.t option =
  match atm with
  | Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as op), [ t1; t2 ], _)
    -> (
      let side lit t =
        match (bool_literal lit, formula_of_bool_term t) with
        | Some b, Some phi ->
            let pos =
              match op with T_bool.Eq -> b | _ -> not b
            in
            Some (if pos then phi else Formula.mk_neg phi)
        | _ -> None
      in
      match side t1 t2 with Some _ as r -> r | None -> side t2 t1)
  | _ -> None

(* [phi] with the viewable atoms at its Boolean skeleton (not under a binder,
   where the array's occurrences are classified as they stand) rewritten,
   then in negation normal form *)
let prepare phi =
  let rec go = function
    | Formula.Atom (atm, _) as phi -> (
        match view_atom atm with Some phi' -> go phi' | None -> phi)
    | Formula.UnaryOp (Formula.Not, p, info) -> Formula.mk_neg ~info (go p)
    | Formula.BinaryOp (op, p, q, info) ->
        Formula.mk_binop ~info op (go p) (go q)
    | phi -> phi
  in
  Formula.nnf_of (go phi)

(* ---- the shapes the preparation acts on ---- *)

let is_array_sort = function T_array.SArray _ -> true | _ -> false

let array_def phi =
  match phi with
  | Formula.Atom
      (Atom.App (Predicate.Psym T_bool.Eq, [ Term.Var (x, s, _); t ], _), _)
    when is_array_sort s && not (Set.mem (Term.tvs_of t) x) ->
      Some (x, s, t)
  | Formula.Atom
      (Atom.App (Predicate.Psym T_bool.Eq, [ t; Term.Var (x, s, _) ], _), _)
    when is_array_sort s && not (Set.mem (Term.tvs_of t) x) ->
      Some (x, s, t)
  | _ -> None

let has_array_def phi =
  List.exists (Formula.conjuncts_list_of phi) ~f:(fun c ->
      Option.is_some (array_def c))

(* ---- one case: substitution, skolemisation, elimination ---- *)

type elim = {
  arr : Ident.tvar;
  arr_sort : Sort.t;
  reads : (Term.t * Ident.tvar) list;  (** ground index, its value's name *)
  tv : Ident.tvar;  (** the universal's variable *)
  vv : Ident.tvar;  (** the cell value's variable in [phi] *)
  phi : Formula.t;  (** [Phi(tv, vv)], quantifier-free *)
  sols : Term.t list;  (** the [e_j] *)
}

type case = {
  formula : Formula.t;
  defs : (Ident.tvar * Sort.t * Term.t) list;  (** one-point substitutions *)
  elims : elim list;  (** in the order made *)
  fresh : Ident.tvar Set.Poly.t;  (** names this rewrite introduced *)
}

type t = { cases : case list; input_fvs : (Ident.tvar * Sort.t) list }

let subst1 x t phi = Formula.subst (Map.Poly.singleton x t) phi

(* the conjuncts after the one-point rule for array equations and the
   skolemisation of top-level existentials, with the substitutions made and
   the fresh names drawn *)
let normalise conjs =
  let defs = ref [] and fresh = ref Set.Poly.empty in
  let rec loop conjs =
    match
      List.find_mapi conjs ~f:(fun i c ->
          match c with
          | Formula.Bind (Formula.Exists, senv, body, _) -> Some (i, `Ex (senv, body))
          | _ -> (
              match array_def c with
              | Some d -> Some (i, `Def d)
              | None -> None))
    with
    | None -> conjs
    | Some (i, `Ex (senv, body)) ->
        let map =
          List.fold senv ~init:Map.Poly.empty ~f:(fun m (x, s) ->
              let y = Ident.mk_fresh_tvar () in
              fresh := Set.add !fresh y;
              Map.Poly.set m ~key:x ~data:(Term.mk_var y s))
        in
        let body = Formula.subst map body in
        let rest = List.filteri conjs ~f:(fun j _ -> j <> i) in
        loop (rest @ Formula.conjuncts_list_of body)
    | Some (i, `Def (x, s, t)) ->
        let rest = List.filteri conjs ~f:(fun j _ -> j <> i) in
        defs :=
          (x, s, t)
          :: List.map !defs ~f:(fun (y, sy, u) ->
              (y, sy, Term.subst (Map.Poly.singleton x t) u));
        loop
          (List.concat_map rest ~f:(fun c ->
               Formula.conjuncts_list_of (subst1 x t c)))
  in
  let conjs = loop conjs in
  (conjs, List.rev !defs, !fresh)

(* ---- classifying an array's occurrences ---- *)

type usage = { mutable ground : Term.t list; mutable univ : int list; mutable bad : bool }

let int_array = function
  | T_array.SArray (T_int.SInt, T_int.SInt) -> true
  | _ -> false

let has_select t =
  Set.exists (Term.funsyms_of t) ~f:(function T_array.ASelect _ -> true | _ -> false)

(* every free [Array Int Int] variable's usage in the conjuncts; [univ] lists
   the indices of the single-variable universal conjuncts that read it at
   that variable *)
let classify conjs =
  let tbl : (Ident.tvar, usage) Hashtbl.Poly.t = Hashtbl.Poly.create () in
  let get x = Hashtbl.Poly.find_or_add tbl x ~default:(fun () ->
      { ground = []; univ = []; bad = false })
  in
  let rec term ~top ~bound (t : Term.t) =
    match t with
    | Term.Var (x, s, _) ->
        if int_array s && not (Set.mem bound x) then (get x).bad <- true
    | Term.FunApp (T_array.ASelect _, [ Term.Var (x, s, _); i ], _)
      when int_array s && not (Set.mem bound x) ->
        let u = get x in
        let ivs = Term.tvs_of i in
        (if Set.is_empty (Set.inter ivs bound) then (
           if has_select i then u.bad <- true
           else if not (List.mem u.ground i ~equal:Stdlib.( = )) then
             u.ground <- u.ground @ [ i ])
         else
           match (top, i) with
           | Some (k, tv, shadowed), Term.Var (y, _, _)
             when Stdlib.(y = tv) && not shadowed ->
               if not (List.mem u.univ k ~equal:Int.equal) then
                 u.univ <- u.univ @ [ k ]
           | _ -> u.bad <- true);
        term ~top ~bound i
    | Term.FunApp (T_bool.Formula phi, [], _) -> formula ~top ~bound phi
    | Term.FunApp (T_array.ALambda ((y, _), _), args, _) ->
        let top = Option.map top ~f:(fun (k, tv, sh) -> (k, tv, sh || Stdlib.(y = tv))) in
        List.iter args ~f:(term ~top ~bound:(Set.add bound y))
    | Term.FunApp (_, args, _) -> List.iter args ~f:(term ~top ~bound)
    | Term.LetTerm _ -> raise (Skip "a let")
  and formula ~top ~bound (phi : Formula.t) =
    match phi with
    | Formula.Atom (Atom.App (Predicate.Psym _, args, _), _) ->
        List.iter args ~f:(term ~top ~bound)
    | Formula.Atom (Atom.App _, _) -> raise (Skip "a predicate variable")
    | Formula.Atom _ -> ()
    | Formula.UnaryOp (_, p, _) -> formula ~top ~bound p
    | Formula.BinaryOp (_, p, q, _) ->
        formula ~top ~bound p;
        formula ~top ~bound q
    | Formula.Bind (_, senv, p, _) ->
        let top =
          Option.map top ~f:(fun (k, tv, sh) ->
              (k, tv, sh || List.exists senv ~f:(fun (y, _) -> Stdlib.(y = tv))))
        in
        formula ~top
          ~bound:(Set.union bound (Set.Poly.of_list (List.map senv ~f:fst)))
          p
    | Formula.LetRec _ | Formula.LetFormula _ -> raise (Skip "a let")
  in
  List.iteri conjs ~f:(fun k c ->
      match c with
      | Formula.Bind (Formula.Forall, [ (tv, T_int.SInt) ], body, _) ->
          formula ~top:(Some (k, tv, false)) ~bound:(Set.Poly.singleton tv) body
      | _ -> formula ~top:None ~bound:Set.Poly.empty c);
  tbl

(* ---- solving an equation for the cell value ---- *)

(* [t] as [c * v + r] with [c] an integer, when [v] occurs linearly *)
let rec linear v (t : Term.t) : (Z.t * Term.t) option =
  let no_v t = not (Set.mem (Term.tvs_of t) v) in
  match t with
  | Term.Var (x, _, _) when Stdlib.(x = v) -> Some (Z.one, T_int.zero ())
  | _ when no_v t -> Some (Z.zero, t)
  | Term.FunApp (T_int.Add, [ a; b ], _) ->
      Option.map2 (linear v a) (linear v b) ~f:(fun (ca, ra) (cb, rb) ->
          (Z.(ca + cb), T_int.mk_add ra rb))
  | Term.FunApp (T_int.Sub, [ a; b ], _) ->
      Option.map2 (linear v a) (linear v b) ~f:(fun (ca, ra) (cb, rb) ->
          (Z.(ca - cb), T_int.mk_sub ra rb))
  | Term.FunApp (T_int.Neg, [ a ], _) ->
      Option.map (linear v a) ~f:(fun (c, r) -> (Z.neg c, T_int.mk_neg r))
  | Term.FunApp (T_int.Mul, [ Term.FunApp (T_int.Int n, [], _); a ], _)
  | Term.FunApp (T_int.Mul, [ a; Term.FunApp (T_int.Int n, [], _) ], _) ->
      Option.map (linear v a) ~f:(fun (c, r) ->
          (Z.(n * c), T_int.mk_mul (T_int.mk_int n) r))
  | _ -> None

(* [v = e] for an equation [l = r] in which [v] has coefficient 1 or -1 *)
let solve_for v l r =
  match (linear v l, linear v r) with
  | Some (cl, rl), Some (cr, rr) ->
      let c = Z.(cl - cr) in
      (* c * v + (rl - rr) = 0 *)
      if Z.equal c Z.one then Some (T_int.mk_sub rr rl)
      else if Z.equal c Z.minus_one then Some (T_int.mk_sub rl rr)
      else None
  | _ -> None

(* the atoms of [phi] that mention [v], as the solutions they give; [None]
   when one is not an integer (dis)equation solvable for [v] *)
let solutions v phi =
  let ok = ref true and sols = ref [] in
  ignore
    (Formula.map_atom phi ~f:(fun atm ->
         (if Set.mem (Atom.tvs_of atm) v then
            match atm with
            | Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ l; r ], _)
              -> (
                match solve_for v l r with
                | Some e ->
                    if not (List.mem !sols e ~equal:Stdlib.( = )) then
                      sols := !sols @ [ e ]
                | None -> ok := false)
            | _ -> ok := false);
         Formula.mk_atom atm));
  if !ok then Some !sols else None

(* [phi] at a value of [v] distinct from every solution: each equation over
   [v] false, each disequation true *)
let generic v phi =
  Formula.map_atom phi ~f:(fun atm ->
      if Set.mem (Atom.tvs_of atm) v then
        match atm with
        | Atom.App (Predicate.Psym T_bool.Eq, _, _) -> Formula.mk_false ()
        | Atom.App (Predicate.Psym T_bool.Neq, _, _) -> Formula.mk_true ()
        | _ -> assert false
      else Formula.mk_atom atm)

(* replace the reads of [x]: at a ground index by its value's variable, at
   [Var tv] (when given) by [vv] *)
let replace_reads x ~reads ?at phi =
  let rec tr (t : Term.t) =
    match t with
    | Term.FunApp (T_array.ASelect _, [ Term.Var (y, _, _); i ], _)
      when Stdlib.(x = y) -> (
        let at_tv =
          match (at, i) with
          | Some (tv, vv), Term.Var (z, _, _) when Stdlib.(z = tv) -> Some vv
          | _ -> None
        in
        match at_tv with
        | Some vv -> Term.mk_var vv T_int.SInt
        | None -> (
            match List.Assoc.find reads i ~equal:Stdlib.( = ) with
            | Some v -> Term.mk_var v T_int.SInt
            | None -> raise (Skip "a read the classification did not see")))
    | Term.FunApp (T_bool.Formula phi, [], info) ->
        Term.mk_fsym_app ~info (T_bool.Formula (fm phi)) []
    | Term.FunApp (sym, args, info) ->
        Term.mk_fsym_app ~info sym (List.map args ~f:tr)
    | t -> t
  and fm (phi : Formula.t) =
    match phi with
    | Formula.Atom (Atom.App (p, args, ai), info) ->
        Formula.mk_atom ~info (Atom.mk_app ~info:ai p (List.map args ~f:tr))
    | Formula.Atom _ -> phi
    | Formula.UnaryOp (op, p, info) -> Formula.mk_unop ~info op (fm p)
    | Formula.BinaryOp (op, p, q, info) ->
        Formula.mk_binop ~info op (fm p) (fm q)
    | Formula.Bind (b, senv, p, info) -> Formula.mk_bind ~info b senv (fm p)
    | _ -> raise (Skip "a let")
  in
  fm phi

(* one elimination of [x] from the conjuncts, or [None] when its universal
   is outside the fragment *)
let eliminate conjs x sort (u : usage) =
  let reads = List.map u.ground ~f:(fun s -> (s, Ident.mk_fresh_tvar ())) in
  let tv = Ident.mk_fresh_tvar () and vv = Ident.mk_fresh_tvar () in
  let univ, rest =
    List.mapi conjs ~f:(fun k c -> (k, c))
    |> List.partition_map ~f:(fun (k, c) ->
        if List.mem u.univ k ~equal:Int.equal then
          match c with
          | Formula.Bind (Formula.Forall, [ (t0, _) ], body, _) ->
              First (subst1 t0 (Term.mk_var tv T_int.SInt) body)
          | _ -> assert false
        else Second c)
  in
  let phi =
    Formula.and_of univ
    |> replace_reads x ~reads ~at:(tv, vv)
    |> Formula.elim_ite
  in
  if not (Formula.is_quantifier_free phi) then None
  else if Set.mem (Formula.tvs_of phi) x then None
  else
    match solutions vv phi with
    | None -> None
    | Some sols when List.exists sols ~f:has_select -> None
    | Some sols ->
        let at_v e = subst1 vv e phi in
        let exists_v =
          Formula.or_of (List.map sols ~f:at_v @ [ generic vv phi ])
        in
        let tvar = Term.mk_var tv T_int.SInt in
        let at_reads =
          List.map reads ~f:(fun (s, v) ->
              Formula.subst
                (Map.Poly.of_alist_exn [ (tv, s); (vv, Term.mk_var v T_int.SInt) ])
                phi)
        in
        let consistent =
          List.concat_mapi reads ~f:(fun i (si, vi) ->
              List.filter_mapi reads ~f:(fun j (sj, vj) ->
                  if j <= i then None
                  else
                    Some
                      (Formula.mk_or (Formula.neq si sj)
                         (Formula.eq (Term.mk_var vi T_int.SInt)
                            (Term.mk_var vj T_int.SInt)))))
        in
        let outside =
          Formula.mk_forall
            [ (tv, T_int.SInt) ]
            (Formula.or_of
               (List.map reads ~f:(fun (s, _) -> Formula.eq tvar s) @ [ exists_v ]))
        in
        let rest = List.map rest ~f:(replace_reads x ~reads) in
        Some
          ( rest @ at_reads @ consistent @ [ outside ],
            { arr = x; arr_sort = sort; reads; tv; vv; phi; sols } )

let rewrite_case conjs =
  let conjs, defs, fresh =
    normalise (List.concat_map conjs ~f:Formula.conjuncts_list_of)
  in
  let conjs =
    List.concat_map conjs ~f:(fun c ->
        Formula.conjuncts_list_of (ArrayAsFun.row_formula c))
  in
  let rec loop conjs elims tried =
    let tbl = classify conjs in
    let cand =
      Hashtbl.Poly.to_alist tbl
      |> List.sort ~compare:(fun (a, _) (b, _) ->
          String.compare (Ident.name_of_tvar a) (Ident.name_of_tvar b))
      |> List.find ~f:(fun (x, u) ->
          (not u.bad) && (not (List.is_empty u.univ))
          && not (Set.mem tried x))
    in
    match cand with
    | None -> (conjs, List.rev elims)
    | Some (x, u) -> (
        match eliminate conjs x (T_array.SArray (T_int.SInt, T_int.SInt)) u with
        | None -> loop conjs elims (Set.add tried x)
        | Some (conjs, e) -> loop conjs (e :: elims) (Set.add tried x))
  in
  let conjs, elims = loop conjs [] Set.Poly.empty in
  let fresh =
    List.fold elims ~init:fresh ~f:(fun acc e ->
        Set.union acc
          (Set.Poly.of_list (e.tv :: e.vv :: List.map e.reads ~f:snd)))
  in
  { formula = Formula.and_of conjs; defs; elims; fresh }

let rewrite (psi : Formula.t) : (t, string) Result.t =
  try
    let psi = prepare psi in
    let conjs = Formula.conjuncts_list_of psi in
    let cases =
      List.fold conjs ~init:[ [] ] ~f:(fun acc c ->
          let ds = Formula.disjuncts_list_of c in
          if List.length ds > 1 && List.exists ds ~f:has_array_def then
            List.concat_map acc ~f:(fun case ->
                List.map ds ~f:(fun d -> case @ [ d ]))
          else List.map acc ~f:(fun case -> case @ [ c ]))
    in
    if List.length cases > max_cases then Error "too many cases"
    else
      let cases = List.map cases ~f:rewrite_case in
      if List.for_all cases ~f:(fun c -> List.is_empty c.elims) then
        Error "no array eliminated"
      else
        Ok
          {
            cases;
            input_fvs = Set.to_list (Formula.term_sort_env_of psi);
          }
  with
  | Skip reason -> Error reason
  | exn_ when not (Common.Timer.is_async exn_) ->
      Error ("not rewritten: " ^ Exn.to_string exn_)

(* ---- reading a model back ---- *)

let abs_term t = T_bool.ifte (Formula.geq t (T_int.zero ())) t (T_int.mk_neg t)

(* the array [e] denotes, as a [lambda] whose free variables are those of
   the case formula's model *)
let array_term (e : elim) =
  let x = Ident.mk_fresh_tvar () in
  let xv = Term.mk_var x T_int.SInt in
  let g =
    List.fold e.sols ~init:(T_int.one ()) ~f:(fun acc s -> T_int.mk_add acc (abs_term s))
  in
  let witness =
    List.fold_right e.sols ~init:g ~f:(fun s acc ->
        T_bool.ifte (subst1 e.vv s e.phi) s acc)
    |> Term.subst (Map.Poly.singleton e.tv xv)
  in
  let body =
    List.fold_right e.reads ~init:witness ~f:(fun (s, v) acc ->
        T_bool.ifte (Formula.eq xv s) (Term.mk_var v T_int.SInt) acc)
  in
  T_array.mk_lambda (x, T_int.SInt) T_int.SInt body

let read_back (r : t) (c : case) (model : model) : model option =
  try
    let value = Hashtbl.Poly.create () in
    List.iter model ~f:(fun ((x, s), v) ->
        Hashtbl.Poly.set value ~key:x
          ~data:(match v with Some v -> v | None -> Term.mk_dummy s));
    let lookup x s =
      Hashtbl.Poly.find_or_add value x ~default:(fun () -> Term.mk_dummy s)
    in
    let close t =
      let env = Term.term_sort_env_of t in
      Term.subst
        (Map.Poly.of_alist_exn
           (List.map (Set.to_list env) ~f:(fun (x, s) -> (x, lookup x s))))
        t
    in
    (* Latest elimination first.  An array eliminated earlier keeps, in its
       [phi], the reads of an array that was still free then and was
       eliminated later (the [outside] conjunct carried them on), while a
       later elimination never mentions an earlier array, whose reads were
       already replaced.  Closing the earlier array first looked the later one
       up before it had a value, so its witness was chosen against a dummy
       array and the read-back model violated the universal it was built
       for: a "countermodel" that is not one. *)
    List.iter (List.rev c.elims) ~f:(fun e ->
        Hashtbl.Poly.set value ~key:e.arr ~data:(close (array_term e)));
    List.iter c.defs ~f:(fun (x, _, t) ->
        Hashtbl.Poly.set value ~key:x ~data:(close t));
    Some
      (List.map r.input_fvs ~f:(fun (x, s) -> ((x, s), Some (lookup x s))))
  with exn_ when not (Common.Timer.is_async exn_) -> None
