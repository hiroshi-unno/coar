open Core
open Ast.LogicOld

(* A validity proof of an unknown-free clause by matching alone, without a
   solver: the clause's conclusion is, up to the equalities among its premises
   and the names of bound variables, a conjunction of its own premises.

   [valid phi] reads [phi] (its free variables universal, a leading
   [forall] prefix dropped) as the disjunction [d_1 \/ ... \/ d_n] of the
   top-level disjuncts of its negation normal form, and then
   1. repeatedly takes a disjunct whose complement is an equality [x = t]
      with [x] a variable not occurring in [t] (the premise [x = t]), drops
      it and substitutes [t] for [x] in the others (the one-point rule:
      [(x <> t) \/ R] is valid exactly when [R[t/x]] is, since an assignment
      with [x = t] reads [R] as [R[t/x]] reads it), at most [max_steps] times;
   2. answers [true] when some disjunct [d] is covered by the complements of
      the other disjuncts (the premises), where a formula is covered when it
      is literally [true] or an equation [t = t], when it is a conjunction
      whose conjuncts are all covered, when it is a disjunction one of whose
      disjuncts is, when it is a universal whose body is, and when, read as
      the universal closure over [d]'s own variables (those of [phi] that no
      other disjunct has) and the universals it was under, it is
      alpha-equivalent to a conjunct of a premise read as the universal
      closure over the universals of its positive part (those under no
      existential and no negation, lifted to the front).
   Contract: [true] only when [phi] is valid in every model of every theory.
   Under an assignment falsifying every disjunct but [d], each premise holds
   for that assignment; a premise's lifted universals are lifted soundly
   ([forall y. A] /\ [B] and [(forall y. A) \/ B] are [forall y. (A /\ B)]
   and [forall y. (A \/ B)] for [y] not in [B], each lifted variable renamed
   apart first); a variable of [d] alone does not occur in a premise, so the
   premise holds for every value of it, and a covered leaf holds for every
   value of the variables it is closed over, in particular for the
   assignment's; so (by induction on coverage) [d] holds.  The closure of a
   leaf and of a premise conjunct are compared with their closed-over
   variables renamed by the order of their first occurrence and every bound
   variable by position, so equal forms are alpha-equivalent closed
   formulas.  Step 1 is an equivalence.  [false] says nothing.
   Nothing is unfolded or interpreted, so the proof holds for every
   interpretation of every symbol in [phi], defined or not.
   Cost: one pass over [phi] per substitution, and a comparison of each leaf
   of the conclusion with each premise conjunct of the same size, each
   canonicalised once.

   Why: the obligation a call site leaves after predicate elimination often
   restates a premise (a callee's postcondition, an [assume] of the very
   formula) over variables the premises equate with the premise's own.  With
   the definitions it applies inlined, the solver is asked a quantified
   question it does not decide within its budget, although the conclusion is
   the premise verbatim once the equalities are applied.  The clause that
   reaches the zero-unknown verdict has the conclusion's universals made
   clause variables, while the premise's stay bound under its negation, so
   the two are compared as universal closures. *)

let max_steps = 2000
let dump_count = Atomic.make 0

(* a literal with its negation pushed into the atom where the atom has one, so
   that [not (x = y)] and [x <> y] are one form *)
let norm_leaf phi =
  match phi with
  | Formula.UnaryOp (Formula.Not, Formula.Atom (atom, info), _) -> (
      match Atom.negate atom with Some na -> Formula.mk_atom ~info na | None -> phi)
  | _ -> phi

(* [norm_leaf] at every literal, beneath connectives and binders too: the
   premise side is a double negation of what was written and the conclusion
   side is not, so one reaches an atom as [not (x <> y)] where the other has
   [x = y]; an equivalence *)
let rec deep_norm phi =
  match phi with
  | Formula.UnaryOp (Formula.Not, Formula.Atom _, _) -> norm_leaf phi
  | Formula.UnaryOp (op, phi', info) -> Formula.mk_unop ~info op (deep_norm phi')
  | Formula.BinaryOp (op, phi1, phi2, info) ->
      Formula.mk_binop ~info op (deep_norm phi1) (deep_norm phi2)
  | Formula.Bind (b, senv, body, info) ->
      Formula.mk_bind ~info b senv (deep_norm body)
  | _ -> phi

let complement phi =
  match phi with
  | Formula.UnaryOp (Formula.Not, phi', _) -> norm_leaf phi'
  | Formula.Atom (atom, info) -> (
      match Atom.negate atom with
      | Some na -> Formula.mk_atom ~info na
      | None -> Formula.nnf_of (Formula.mk_neg phi))
  | _ -> Formula.nnf_of (Formula.mk_neg phi)

(* [x = t] (either way round) with [x] a variable not free in [t] *)
let definition_of phi =
  match phi with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _) -> (
      let def x t =
        if Set.mem (Term.fvs_of t) x then None else Some (x, t)
      in
      match (t1, t2) with
      | Term.Var (x, _, _), _ -> (
          match def x t2 with
          | Some d -> Some d
          | None -> (
              match t2 with Term.Var (y, _, _) -> def y t1 | _ -> None))
      | _, Term.Var (y, _, _) -> def y t1
      | _ -> None)
  | _ -> None

let rec strip_forall = function
  | Formula.Bind (Formula.Forall, _, body, _) -> strip_forall body
  | phi -> phi

(* bound variables renamed by position, from names no input carries *)
let canon phi =
  let n = ref 0 in
  Formula.aconv_tvar_norm_scoped
    (fun () ->
      incr n;
      Ast.Ident.Tvar (sprintf "#congruence_match%d" !n))
    phi

(* structural equality of two canonical forms; a value that cannot be compared
   structurally (a closure inside a symbol) is taken as different, which only
   loses a match *)
let same phi1 phi2 =
  try Stdlib.( = ) phi1 phi2
  with exn_ when not (Common.Timer.is_async exn_) -> false

let trivially_true phi =
  match phi with
  | Formula.Atom (Atom.True _, _) -> true
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _) -> (
      try Stdlib.( = ) t1 t2
      with exn_ when not (Common.Timer.is_async exn_) -> false)
  | _ -> false

(* [(disjuncts, steps)]: the disjuncts left after step 1 *)
let propagate ds =
  let rec go steps ds =
    if steps >= max_steps then (ds, steps)
    else
      let rec pick before = function
        | [] -> None
        | d :: after -> (
            match definition_of (complement d) with
            | Some def -> Some (def, List.rev_append before after)
            | None -> pick (d :: before) after)
      in
      match pick [] ds with
      | None -> (ds, steps)
      | Some ((x, t), rest) ->
          let map = Map.Poly.singleton x t in
          go (steps + 1)
            (List.concat_map rest ~f:(fun d ->
                 Formula.disjuncts_list_of
                 @@ Formula.nnf_of (Formula.subst map d)))
  in
  go 0 ds

(* [lift phi]: [(vars, body)], the universals of [phi]'s positive part
   lifted to the front, each renamed to a fresh name first so that no two
   lifted binders share one and none captures a free variable *)
let lift_count = Atomic.make 0

let lift phi =
  let lifted = ref [] in
  let rec go phi =
    match phi with
    | Formula.Bind (Formula.Forall, senv, body, _) ->
        let ren =
          List.map senv ~f:(fun (x, sort) ->
              let y =
                Ast.Ident.Tvar
                  (sprintf "#congruence_lift%d"
                     (Atomic.fetch_and_add lift_count 1))
              in
              lifted := (y, sort) :: !lifted;
              (x, Term.mk_var y sort))
        in
        go
          (Formula.subst
             (Map.Poly.of_alist_reduce ren ~f:(fun _ later -> later))
             body)
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), phi1, phi2, info)
      ->
        Formula.mk_binop ~info op (go phi1) (go phi2)
    | _ -> phi
  in
  let body = go phi in
  (List.rev !lifted, body)

(* the position of the first occurrence of [name] as a whole token in [s] *)
let first_occurrence s name =
  let is_ident c = Char.is_alphanum c || Char.equal c '_' || Char.equal c '#' || Char.equal c '$' in
  let n = String.length s and m = String.length name in
  let rec from pos =
    match String.substr_index s ~pattern:name ~pos with
    | None -> None
    | Some i ->
        let before_ok = i = 0 || not (is_ident s.[i - 1]) in
        let after_ok = i + m >= n || not (is_ident s.[i + m]) in
        if before_ok && after_ok then Some i else from (i + 1)
  in
  from 0

(* [phi] read as its universal closure over [vars] (with their sorts): the
   variables of [vars] that occur, renamed in the order of their first
   occurrence, then every bound variable renamed by position *)
let closed vars phi =
  let text = Formula.str_of phi in
  let occurring =
    List.filter_map vars ~f:(fun (x, sort) ->
        Option.map
          (first_occurrence text (Ast.Ident.name_of_tvar x))
          ~f:(fun i -> (i, x, sort)))
    |> List.sort ~compare:(fun (i, _, _) (j, _, _) -> Int.compare i j)
  in
  let map =
    List.mapi occurring ~f:(fun k (_, x, sort) ->
        (x, Term.mk_var (Ast.Ident.Tvar (sprintf "#congruence_closed%d" k)) sort))
  in
  canon
    (if List.is_empty map then phi
     else Formula.subst (Map.Poly.of_alist_exn map) phi)

let valid phi =
  let ds =
    Formula.disjuncts_list_of @@ Formula.nnf_of @@ strip_forall phi
  in
  let ds, steps = propagate ds in
  let ds = Array.of_list ds in
  (* each disjunct's complement, split into its conjuncts, each read as the
     closure over its lifted universals and canonical *)
  let premises =
    Array.map ds ~f:(fun d ->
        List.concat_map
          (Formula.conjuncts_list_of (deep_norm (complement d)))
          ~f:(fun p ->
            let vars, body = lift p in
            List.map (Formula.conjuncts_list_of body) ~f:(fun q ->
                let q = closed vars q in
                (Formula.ast_size q, q))))
  in
  (* each disjunct's own variables: those no other disjunct has *)
  let own =
    let envs = Array.map ds ~f:(fun d -> Formula.term_sort_env_of d) in
    let count = Hashtbl.Poly.create () in
    Array.iter envs ~f:(fun env ->
        Set.iter env ~f:(fun (x, _) -> Hashtbl.Poly.incr count x));
    Array.map envs ~f:(fun env ->
        Set.to_list
          (Set.filter env ~f:(fun (x, _) -> Hashtbl.Poly.find_exn count x = 1)))
  in
  let dumping = Option.is_some (Sys.getenv "COAR_CONGRUENCE_MATCH_DUMP") in
  let misses = ref [] in
  (* the sizes a premise conjunct has: a formula of another size is not
     compared, which spares building its closed form *)
  let sizes =
    Array.fold premises ~init:Int.Set.empty ~f:(fun acc ps ->
        List.fold ps ~init:acc ~f:(fun acc (s, _) -> Set.add acc s))
  in
  let covered_by i vars phi =
    let phi = deep_norm phi in
    Set.mem sizes (Formula.ast_size phi)
    &&
    let leaf = closed (own.(i) @ vars) phi in
    let size = Formula.ast_size leaf in
    let found =
      Array.existsi premises ~f:(fun j ps ->
          j <> i
          && List.exists ps ~f:(fun (s, p) -> s = size && same leaf p))
    in
    if dumping && not found then misses := (i, size, leaf) :: !misses;
    found
  in
  (* a formula is first compared whole, then taken apart: a premise conjunct
     can be a disjunction (a clause of a definition's body) or a conjunction *)
  let rec covered i vars phi =
    covered_by i vars phi
    ||
    match phi with
    | Formula.BinaryOp (Formula.And, _, _, _) ->
        List.for_all (Formula.conjuncts_list_of phi) ~f:(covered i vars)
    | Formula.BinaryOp (Formula.Or, _, _, _) ->
        List.exists (Formula.disjuncts_list_of phi) ~f:(covered i vars)
    | Formula.Bind (Formula.Forall, _, _, _) ->
        let vars', body = lift phi in
        covered i (vars @ vars') body
    | _ -> trivially_true (norm_leaf phi)
  in
  let proved = Array.existsi ds ~f:(fun i d -> covered i [] d) in
  (* [COAR_CONGRUENCE_MATCH_DUMP=dir] (instrument only): each clause tried is
     written as [dir/cm-PID-N.txt], its disjuncts after the equalities and the
     canonical premise conjuncts with their sizes; the answer is unchanged *)
  Option.iter (Sys.getenv "COAR_CONGRUENCE_MATCH_DUMP") ~f:(fun dir ->
      let n = Atomic.fetch_and_add dump_count 1 in
      Out_channel.with_file
        (sprintf "%s/cm-%d-%d.txt" dir (Common.ForkGuard.self_pid ()) n)
        ~f:(fun oc ->
          fprintf oc "proved %b steps %d disjuncts %d\n" proved steps
            (Array.length ds);
          Array.iteri ds ~f:(fun i d ->
              fprintf oc "D %d %d %s\n" i (Formula.ast_size d)
                (Formula.str_of (canon (deep_norm d)));
              List.iter premises.(i) ~f:(fun (sz, p) ->
                  fprintf oc "P %d %d %s\n" i sz (Formula.str_of p)));
          List.iter (List.rev !misses) ~f:(fun (i, sz, leaf) ->
              fprintf oc "M %d %d %s\n" i sz (Formula.str_of leaf))));
  proved
