(* Positive existentials over sequences replaced by finitely many instances.

   WHY.  A guarded example whose guard quantifies over sequences -- a Horn
   premise stating a universally quantified relation over [(a, s, n)], with the
   relation instantiated to a chain of [store]s keyed by sequence literals --
   enters a synthesis constraint as [guard => atoms], so the guard's universals
   become existentials under the example's own universals:
     forall $1 .. $k.  ... \/ exists s : Seq Int, y. phi(s, y, $) \/ ...
   With the template parameters free, Z3 (4.15.2) has to find, in effect, a
   Skolem function from the [$] to sequences, and on one such query it did not
   answer in 100 s under any seed, assertion order, arithmetic solver or
   preprocessing tactic tried; the same query with each such existential
   replaced by the disjunction of its instances below answered [sat] in half a
   second, and with each replaced by [false] it answered [unsat] -- so the
   existentials are needed and their witnesses are among a few terms.

   THE REWRITE.  Under [not], [and], [or] and [=>], where polarity is defined,
   a block [exists x1 .. xn. phi] in positive position (or [forall x1 .. xn. phi]
   in negative position) that binds at least one [Seq Int] variable is replaced
   by the disjunction (the conjunction) of [phi] at every choice of
     - for a [Seq Int] binder: every sequence literal of [phi] (a term built from
       [seq.empty], [seq.unit] of an integer literal and [seq.++]), every prefix
       and suffix of one, the empty sequence, and one literal none of those equals
       (three copies of an integer larger than any literal of [phi]);
     - for an [Int] binder: the integer literals of [phi], and 0;
     - for a binder of any other sort: the enclosing binders of that sort and the
       free variables of the whole formula of that sort;
   after a binder defined by an equation has been substituted away -- first by
   [Evaluator.elim_onepoint_and_split_binders] over the whole formula, an
   equivalence, then by a conjunct [x = t] (a disjunct [not (x = t)] for a
   universal), [t] mentioning no binder of the block.
   A block is left as it is when a binder has no candidate or the number of
   instances would exceed [max_instances].  Nothing under [<=>], [xor], an atom,
   a [let] or a recursive definition is rewritten.

   THE CLAIM: the result IMPLIES the input, in every model.  Each instance
   implies its existential, a disjunction of such instances does too, and a
   universal implies the conjunction of its instances; the rewritten positions
   are positive or negative, so the implication propagates to the whole
   formula.  So a model of the rewritten synthesis constraint is a model of the
   original one -- a candidate it yields satisfies the examples -- while an
   unsatisfiable rewritten constraint says nothing about the original: the
   rewrite can cost candidates, never admit a wrong one.

   WHEN IT IS EXACT.  When [phi] reads its sequence binders only by comparing
   them, or a concatenation of them with literals, against the literals of
   [phi] -- a read of a store chain keyed by literals is such a comparison --
   the value of [phi] depends only on which literals the binder equals, and the
   candidates meet every such class but "equal to none of them" through the
   one fresh literal.  A binder of another sort is exact only when some
   enclosing binder or free variable can play its role; a witness required to
   differ from all of them is lost.

   CONTRACT.  Raises nothing but asynchronous exceptions; draws no fresh names;
   returns the input physically when no block is rewritten. *)

open Core
open Common.Ext
open LogicOld

let seq_int = T_seq.SSeq T_int.SInt

(* the elements of a ground sequence literal over integers *)
let rec elems_of (t : Term.t) : Z.t list option =
  match t with
  | Term.FunApp (T_seq.SqEmpty _, [], _) -> Some []
  | Term.FunApp (T_seq.SqUnit _, [ e ], _) when T_int.is_int e ->
      Some [ T_int.let_int e ]
  | Term.FunApp (T_seq.SqConcat _, [ a; b ], _) -> (
      match (elems_of a, elems_of b) with
      | Some xs, Some ys -> Some (xs @ ys)
      | _ -> None)
  | _ -> None

let seq_of_elems (xs : Z.t list) : Term.t =
  match List.rev xs with
  | [] -> T_seq.mk_empty T_int.SInt
  | last :: rest ->
      List.fold rest
        ~init:(T_seq.mk_unit T_int.SInt (T_int.mk_int last))
        ~f:(fun acc x ->
          T_seq.mk_concat T_int.SInt (T_seq.mk_unit T_int.SInt (T_int.mk_int x)) acc)

let seq_candidates (phi : Formula.t) : Term.t list =
  let lits =
    Set.to_list
    @@ Formula.filtered_terms_of phi ~f:(fun t ->
        Option.is_some (elems_of t))
  in
  let lists =
    List.concat_map lits ~f:(fun t ->
        let xs = Option.value_exn (elems_of t) in
        List.concat_map (List.range 0 (List.length xs + 1)) ~f:(fun k ->
            [ List.take xs k; List.drop xs k ]))
  in
  let ints =
    List.concat_map lists ~f:Fn.id
    @ List.map ~f:T_int.let_int
        (Set.to_list @@ Formula.filtered_terms_of phi ~f:T_int.is_int)
  in
  let fresh =
    let m = List.fold ints ~init:Z.zero ~f:Z.max in
    List.init 3 ~f:(fun _ -> Z.succ m)
  in
  List.map ~f:seq_of_elems
  @@ List.dedup_and_sort ~compare:(List.compare Z.compare)
  @@ ([] :: fresh :: lists)

let int_candidates (phi : Formula.t) : Term.t list =
  List.map ~f:T_int.mk_int
  @@ List.dedup_and_sort ~compare:Z.compare
  @@ (Z.zero
     :: List.map ~f:T_int.let_int
          (Set.to_list @@ Formula.filtered_terms_of phi ~f:T_int.is_int))

(* [x = t] with [x] one of [bound] and [t] mentioning none of them *)
let definition_of bound (phi : Formula.t) =
  let bvs = Set.Poly.of_list (List.map bound ~f:fst) in
  let def t1 t2 =
    if Term.is_var t1 then
      let (x, _), _ = Term.let_var t1 in
      if Set.mem bvs x && Set.is_empty (Set.inter bvs (Term.tvs_of t2)) then
        Some (x, t2)
      else None
    else None
  in
  if Formula.is_eq phi then
    let t1, t2, _ = Formula.let_eq phi in
    match def t1 t2 with Some d -> Some d | None -> def t2 t1
  else None

(* destructive equality resolution: substitute away the binders a conjunct
   (for an existential) or a negated disjunct (for a universal) defines *)
let rec eliminate_defined ~exists bound body =
  let parts =
    if exists then Formula.conjuncts_list_of body
    else Formula.disjuncts_list_of body
  in
  let defn =
    List.find_map parts ~f:(fun p ->
        if exists then definition_of bound p
        else
          match p with
          | Formula.UnaryOp (Formula.Not, q, _) -> definition_of bound q
          | _ -> None)
  in
  match defn with
  | None -> (bound, body)
  | Some (x, t) ->
      eliminate_defined ~exists
        (List.filter bound ~f:(fun (y, _) -> not (Ident.tvar_equal x y)))
        (Formula.subst (Map.Poly.singleton x t) body)

let rewrite ~max_instances (input : Formula.t) : Formula.t =
  (* an equivalence first: the one-point rule removes a binder an equation
     such as [n - 2437 = 0] defines, which the syntactic [x = t] test below does
     not see, and which would otherwise multiply the instances *)
  let phi = Evaluator.elim_onepoint_and_split_binders input in
  let free = Set.to_list (Formula.term_sort_env_of phi) in
  let changed = ref false in
  let rec tr pos env phi =
    match phi with
    | Formula.UnaryOp (Formula.Not, p, info) ->
        Formula.mk_neg ~info (tr (not pos) env p)
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, info) ->
        Formula.mk_binop ~info op (tr pos env p) (tr pos env q)
    | Formula.BinaryOp (Formula.Imply, p, q, info) ->
        Formula.mk_imply ~info (tr (not pos) env p) (tr pos env q)
    | Formula.Bind (((Formula.Forall | Formula.Exists) as b), senv, p, info) ->
        let body = tr pos (senv @ env) p in
        let exists = Stdlib.(b = Formula.Exists) in
        let keep () = Formula.mk_bind ~info b senv body in
        if
          Bool.(exists <> pos)
          || not (List.exists senv ~f:(fun (_, s) -> Stdlib.(s = seq_int)))
        then keep ()
        else
          let bound, body = eliminate_defined ~exists senv body in
          let cands =
            List.map bound ~f:(fun (x, s) ->
                ( x,
                  if Stdlib.(s = seq_int) then seq_candidates body
                  else if Stdlib.(s = T_int.SInt) then int_candidates body
                  else
                    List.map ~f:(fun (y, s) -> Term.mk_var y s)
                    @@ List.filter (env @ free) ~f:(fun (y, s') ->
                        Stdlib.(s = s')
                        && not
                             (List.exists senv ~f:(fun (z, _) ->
                                  Ident.tvar_equal y z))) ))
          in
          let count =
            List.fold cands ~init:1 ~f:(fun n (_, cs) ->
                if n > max_instances then n else n * List.length cs)
          in
          if List.exists cands ~f:(fun (_, cs) -> List.is_empty cs) || count > max_instances
          then keep ()
          else (
            changed := true;
            let insts =
              List.map (List.n_cartesian_product (List.map cands ~f:snd))
                ~f:(fun ts ->
                  Formula.subst
                    (Map.Poly.of_alist_exn
                       (List.zip_exn (List.map cands ~f:fst) ts))
                    body)
            in
            if exists then Formula.or_of insts else Formula.and_of insts)
    | _ -> phi
  in
  let res = tr true [] phi in
  if !changed then res else input
