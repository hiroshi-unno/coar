open Core
open Ast
open Ast.LogicOld

(** Affine equalities among an unknown's integer observables that every clause
    deriving it preserves: Karr's affine-hull analysis (M. Karr, "Affine
    relationships among variables of a program", Acta Informatica 6, 1976) run
    forward over the clauses, with each join computed from solver models as in
    Sharma et al., "A data driven approach for algebraic loop invariants"
    (ESOP 2013): a point outside the current hull is asked for, and the hull is
    the null space of the points found.

    What it is for.  A predicate the input leaves to inference (an iterator's
    [produces] relating a start state, a produced sequence and an end state)
    has relational facts a template reaches only with luck: the length of the
    sequence equals the end's counter minus the start's, [len v = o.0 - s.0], is
    a three-term equation with unit coefficients, and an element equals a field
    of the start state.  The clauses that derive such a predicate -- the empty
    step [P(s, [], s)], the single step [P(cur, [x], fin)] of a [next] whose
    body moves the counter, and the composition of two steps -- state those
    facts point-wise, and the affine hull of what they derive is exactly the
    equalities common to all of them.  Read off the problem's own clauses, they
    enter the vocabulary of that predicate and of no other.

    The observables of an unknown with formal parameters [x1 ... xn]: the
    integer terms its parameters reach through the selectors of
    single-constructor datatypes (the parameters included), and the length of
    every integer sequence they reach -- the total family, defined everywhere.
    A partial family adds one guarded group of coordinates: the first element
    [seq.nth s 0] of such a sequence under [len s > 0], and the integer payloads
    of one constructor of a multi-constructor datatype under its tester.  Each
    family has its own hull, over the points at which its guard holds.

    The analysis.  Every family starts empty (bottom).  For a clause whose only
    head atom is [P(t)], each family of [P] asks, for the clause's condition,
    its body atoms each constrained by the current hulls of their predicate
    ([guard => equalities] per family; a body predicate whose total family is
    still empty makes the clause contribute nothing yet), the family's guard at
    [t], and the negated conjunction of its current equalities at [t]: a model
    is a new point, raising the hull's dimension; [Unsat] or no answer ends the
    family's turn at that clause.  A predicate that grows puts the clauses
    reading it back on the work list.  It ends when the list is empty or the
    question budget is spent.

    Contract.  The result maps an unknown to equalities over [x1 ... xn] (its
    formals, named by [sort_env_list_of_sorts]), each [sum a_i c_i + b = 0] with
    coprime integer coefficients, a basis of each family's hull read off the
    reduced row echelon form with the coordinates in a fixed order (the reached
    scalars, then lengths, then the partial coordinates, then the constant), so
    that a length or an element is written as a combination of the others.
    Nothing is certified: a question without an answer counts as no point, so
    a cut-off run (by the budget or a timeout) may return equalities the least
    solution violates.  They are offered as vocabulary only, and a candidate
    built from them is validated against the clauses like any other, so the
    result cannot bear on the soundness of a verdict. *)

(** {1 Rational linear algebra} *)

(* The basis of the null space of the rows [rows] (each of length [n]), one
   vector per non-pivot column of the reduced row echelon form, with a one at
   that column.  [rows] empty gives the [n] unit vectors. *)
let null_space n (rows : Q.t array list) : Q.t array list =
  let m = Array.of_list (List.map rows ~f:Array.copy) in
  let nrows = Array.length m in
  let pivots = ref [] in
  let r = ref 0 in
  for c = 0 to n - 1 do
    if !r < nrows then
      match
        List.find (List.range !r nrows) ~f:(fun i -> not (Q.equal m.(i).(c) Q.zero))
      with
      | None -> ()
      | Some i ->
          let tmp = m.(i) in
          m.(i) <- m.(!r);
          m.(!r) <- tmp;
          let p = m.(!r).(c) in
          m.(!r) <- Array.map m.(!r) ~f:(fun x -> Q.div x p);
          for i' = 0 to nrows - 1 do
            if i' <> !r && not (Q.equal m.(i').(c) Q.zero) then
              let f = m.(i').(c) in
              m.(i') <- Array.mapi m.(i') ~f:(fun j x -> Q.sub x (Q.mul f m.(!r).(j)))
          done;
          pivots := (c, !r) :: !pivots;
          incr r
  done;
  let pivots = List.rev !pivots in
  List.filter_map (List.range 0 n) ~f:(fun f ->
      if List.exists pivots ~f:(fun (c, _) -> c = f) then None
      else
        let w = Array.create ~len:n Q.zero in
        w.(f) <- Q.one;
        List.iter pivots ~f:(fun (c, row) -> w.(c) <- Q.neg m.(row).(f));
        Some w)

(* [w] scaled to coprime integers, the first non-zero entry positive *)
let integral (w : Q.t array) : Z.t array =
  let l = Array.fold w ~init:Z.one ~f:(fun acc q -> Z.lcm acc (Q.den q)) in
  let zs = Array.map w ~f:(fun q -> Z.div (Z.mul (Q.num q) l) (Q.den q)) in
  let g = Array.fold zs ~init:Z.zero ~f:Z.gcd in
  let zs = if Z.equal g Z.zero then zs else Array.map zs ~f:(fun z -> Z.div z g) in
  match Array.find zs ~f:(fun z -> not (Z.equal z Z.zero)) with
  | Some z when Z.lt z Z.zero -> Array.map zs ~f:Z.neg
  | _ -> zs

(** {1 Observables} *)

type family = {
  guard : Formula.t;  (** over the formals *)
  coords : Term.t list;  (** integer terms over the formals *)
  mutable points : Q.t array list;
  mutable eqs : Z.t array list option;
      (** [None]: no point yet (bottom); each equality has one entry per
          coordinate and the constant last *)
}

type pinfo = { pvar : Ident.pvar; formals : sort_env_list; fams : family list }

let rec reach t s d acc =
  let acc = (t, s) :: acc in
  match s with
  | T_dt.SDT dt when d > 0 -> (
      match Datatype.conses_of dt with
      | [ cons ] ->
          List.fold (Datatype.sels_of_cons cons) ~init:acc ~f:(fun acc sel ->
              reach
                (T_dt.mk_sel dt (Datatype.name_of_sel sel) t)
                (Datatype.sort_of_sel dt sel) (d - 1) acc)
      | _ -> acc)
  | _ -> acc

let dedup_terms ts =
  let seen = Hash_set.create (module String) in
  List.filter ts ~f:(fun t ->
      let k = Term.str_of t in
      if Hash_set.mem seen k then false
      else (
        Hash_set.add seen k;
        true))

(* The families of an unknown with formals [formals]: the total one first.
   [max_coords] caps the total family's coordinates (in order). *)
let families_of ~max_coords (formals : sort_env_list) : family list =
  let reached =
    List.concat_map formals ~f:(fun (x, s) ->
        List.rev (reach (Term.mk_var x s) s 3 []))
  in
  let ints =
    List.filter_map reached ~f:(fun (t, s) ->
        if Term.is_int_sort s then Some t else None)
  in
  let seqs =
    List.filter_map reached ~f:(fun (t, s) ->
        match s with
        | T_seq.SSeq se when Term.is_int_sort se -> Some (se, t)
        | _ -> None)
  in
  let totals =
    List.take
      (dedup_terms (ints @ List.map seqs ~f:(fun (se, t) -> T_seq.mk_len se t)))
      max_coords
  in
  let mk guard coords = { guard; coords; points = []; eqs = None } in
  let first_elems =
    List.map seqs ~f:(fun (se, t) ->
        mk
          (Formula.mk_atom (T_int.mk_gt (T_seq.mk_len se t) (T_int.zero ())))
          (totals @ [ T_seq.mk_nth se t (T_int.zero ()) ]))
  in
  let payloads =
    List.concat_map reached ~f:(fun (t, s) ->
        match s with
        | T_dt.SDT dt when List.length (Datatype.conses_of dt) > 1 ->
            List.filter_map (Datatype.conses_of dt) ~f:(fun cons ->
                let sels =
                  List.filter (Datatype.sels_of_cons cons) ~f:(fun sel ->
                      Term.is_int_sort (Datatype.sort_of_sel dt sel))
                in
                if List.is_empty sels then None
                else
                  Some
                    (mk
                       (Formula.mk_atom
                          (T_dt.mk_is_cons dt (Datatype.name_of_cons cons) t))
                       (totals
                       @ List.map sels ~f:(fun sel ->
                             T_dt.mk_sel dt (Datatype.name_of_sel sel) t))))
        | _ -> [])
  in
  mk (Formula.mk_true ()) totals :: (first_elems @ payloads)

(** {1 The analysis} *)

let linear (coords : Term.t list) (e : Z.t array) : Term.t =
  let n = List.length coords in
  let monos =
    List.filter_mapi (coords @ [ T_int.one () ]) ~f:(fun i c ->
        let a = e.(i) in
        if Z.equal a Z.zero then None
        else if i = n then Some (T_int.mk_int a)
        else if Z.equal a Z.one then Some c
        else Some (T_int.mk_mul (T_int.mk_int a) c))
  in
  match monos with [] -> T_int.zero () | t :: ts -> T_int.mk_sum t ts

let eq_formula coords e = Formula.eq (linear coords e) (T_int.zero ())

let instantiate (info : pinfo) (args : Term.t list) =
  let sub =
    Map.Poly.of_alist_exn
      (List.map2_exn info.formals args ~f:(fun (x, _) t -> (x, t)))
  in
  (Formula.subst sub, Term.subst sub)

(* the current hull of [info] at [args], [None] when its total family is
   still empty *)
let hull_at (info : pinfo) args : Formula.t option =
  let fsub, tsub = instantiate info args in
  match info.fams with
  | { eqs = None; _ } :: _ -> None
  | fams ->
      Some
        (Formula.and_of
        @@ List.map fams ~f:(fun f ->
               match f.eqs with
               | None -> Formula.mk_neg (fsub f.guard)
               | Some es ->
                   Formula.mk_imply (fsub f.guard)
                     (Formula.and_of
                        (List.map es ~f:(fun e ->
                             eq_formula (List.map f.coords ~f:tsub) e)))))

let value_of = function
  | Some (Term.FunApp (T_int.Int n, [], _)) -> Some (Q.of_bigint n)
  | Some (Term.FunApp (T_int.Neg, [ Term.FunApp (T_int.Int n, [], _) ], _)) ->
      Some (Q.of_bigint (Z.neg n))
  | _ -> None

type result = (Ident.pvar, Formula.t list) Map.Poly.t

(** [analyze ~id ~fenv ~max_coords ~budget clauses]: the hull equalities of
    every unknown that heads a clause of [clauses], over its formals
    [x1 ... xn].  At most [budget] solver questions are asked, each with a
    one-second timeout. *)
let analyze ~id ~fenv ~max_coords ~budget (clauses : ClauseOld.t list) : result =
  let infos : (string, pinfo) Hashtbl.t = Hashtbl.create (module String) in
  let info_of p sorts =
    Hashtbl.find_or_add infos (Ident.name_of_pvar p) ~default:(fun () ->
        let formals = sort_env_list_of_sorts sorts in
        { pvar = p; formals; fams = families_of ~max_coords formals })
  in
  let app = function
    | Atom.App (Predicate.Var (p, sorts), ts, _) -> Some (p, sorts, ts)
    | _ -> None
  in
  (* the clauses with one head atom, each with its body atoms *)
  let rules =
    List.filter_map clauses ~f:(fun (_senv, ps, ns, phi) ->
        match Set.to_list ps with
        | [ h ] -> (
            match (app h, Option.all (List.map (Set.to_list ns) ~f:app)) with
            | Some head, Some body ->
                Some (Formula.mk_neg phi, head, body)
            | _ -> None)
        | _ -> None)
    |> Array.of_list
  in
  let asked = ref 0 in
  (* every clause reading [p] in its body, by index into [rules] *)
  let readers p =
    List.filter (List.range 0 (Array.length rules)) ~f:(fun i ->
        let _, _, body = rules.(i) in
        List.exists body ~f:(fun (q, _, _) -> Ident.pvar_equal p q))
  in
  let queue = Queue.of_list (List.range 0 (Array.length rules)) in
  let queued = Hash_set.of_list (module Int) (List.range 0 (Array.length rules)) in
  while (not (Queue.is_empty queue)) && !asked < budget do
    let i = Queue.dequeue_exn queue in
    Hash_set.remove queued i;
    let cond, (p, sorts, args), body = rules.(i) in
    let hulls =
      Option.all
        (List.map body ~f:(fun (q, qsorts, qargs) ->
             hull_at (info_of q qsorts) qargs))
    in
    match hulls with
    | None -> ()
    | Some hulls ->
        let info = info_of p sorts in
        let fsub, tsub = instantiate info args in
        let grew = ref false in
        List.iter info.fams ~f:(fun fam ->
            let n = List.length fam.coords in
            let coords = List.map fam.coords ~f:tsub in
            let ks =
              List.map coords ~f:(fun _ -> Term.mk_var (Ident.mk_fresh_tvar ()) T_int.SInt)
            in
            let defs = List.map2_exn ks coords ~f:Formula.eq in
            let continue = ref true in
            let steps = ref 0 in
            while !continue && !steps <= n + 1 && !asked < budget do
              incr steps;
              let outside =
                match fam.eqs with
                | None -> Some (Formula.mk_true ())
                | Some [] -> None
                | Some es ->
                    Some
                      (Formula.or_of
                         (List.map es ~f:(fun e ->
                              Formula.mk_neg (eq_formula coords e))))
              in
              match outside with
              | None -> continue := false
              | Some outside -> (
                  let phis = (cond :: hulls) @ (fsub fam.guard :: outside :: defs) in
                  let phi = Formula.and_of phis in
                  if Z3Smt.Z3interface.may_not_return phi then continue := false
                  else (
                    incr asked;
                    (* a question the solver cannot take (it raises) is a
                       question without an answer: no point; a timeout or an
                       interrupt is passed on *)
                    match
                      try
                        Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 1000)
                          fenv [ phi ]
                      with exn when not (Common.Timer.is_async exn) -> `Unknown ""
                    with
                    | `Sat model -> (
                        let vals =
                          List.map ks ~f:(fun k ->
                              match k with
                              | Term.Var (x, s, _) ->
                                  value_of
                                    (Option.join (LogicOld.model_find model (x, s)))
                              | _ -> None)
                        in
                        match Option.all vals with
                        | None -> continue := false
                        | Some vs ->
                            let pt = Array.of_list (vs @ [ Q.one ]) in
                            fam.points <- pt :: fam.points;
                            fam.eqs <-
                              Some
                                (List.map ~f:integral
                                   (null_space (n + 1) fam.points));
                            grew := true)
                    | _ -> continue := false))
            done);
        if !grew then
          List.iter (readers p) ~f:(fun j ->
              if not (Hash_set.mem queued j) then (
                Hash_set.add queued j;
                Queue.enqueue queue j))
  done;
  Hashtbl.fold infos ~init:Map.Poly.empty ~f:(fun ~key:_ ~data:info acc ->
      match info.fams with
      | { eqs = None; _ } :: _ -> acc
      | fams ->
          let eqs =
            List.concat_map fams ~f:(fun f ->
                match f.eqs with
                | None -> []
                | Some es ->
                    List.filter_map es ~f:(fun e ->
                        (* an equality on the constant alone is [1 = 0]
                           or trivial; one coordinate alone is a fact about a
                           constant, kept after the relational ones *)
                        let support =
                          Array.counti e ~f:(fun i z ->
                              i < Array.length e - 1 && not (Z.equal z Z.zero))
                        in
                        if support = 0 then None
                        else Some (support, eq_formula f.coords e)))
            |> List.stable_sort ~compare:(fun (a, _) (b, _) ->
                   Int.compare (if a >= 2 then 0 else 1) (if b >= 2 then 0 else 1))
            |> List.map ~f:snd
          in
          Map.Poly.set acc ~key:info.pvar ~data:eqs)
