open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* Range invariants of the integer arguments that carry machine words.

   A frontend that emits a machine word as an [Int] and reads it through
   [(_ int_to_bv n)] states its range [0 <= x < 2^n] where the word enters (a
   function's parameter, a fact clause), and every step keeps it, but nothing
   carries the range along the unknowns: a body atom [P(.., x, ..)] puts no
   bound on [x].  A question about such a clause then ranges over every
   integer [x], and the bit-vector reading of [x] cannot be separated from
   its integer reading.

   The procedure.  For an unknown [P] of the ordinary kind, an integer
   argument position [i] and a width [n] that some [int_to_bv] of the problem
   uses, write [R_P(x)] for the conjunction of [0 <= x_i < 2^n] over the
   triples [(P, i, n)] kept.  Start from every triple and drop, until nothing
   changes, a triple [(P, i, n)] for which some clause with a head atom
   [P(u)] does not make

     [not phi /\ /\_(Q(t) in the body) R_Q(t)  ==>  0 <= u_i < 2^n]

   valid (asked of Z3 with a budget; a question not answered [Valid] drops the
   triple).  What remains is inductive: every clause, with [R] assumed of its
   body atoms, establishes [R] of each of its head atoms.

   The use.  Let [p'] be the problem with [R_Q(t)] added as a premise of every
   body atom [Q(t)].  Then [p] and [p'] are equisatisfiable:
   - a solution [s] of [p] solves [p'], whose clauses have more premises;
   - for a solution [s'] of [p'], [s' /\ R] solves [p]: in a clause with
     [s'(Q)(t) /\ R_Q(t)] for each body atom, [p']'s clause gives some head
     [s'(P)(u)], and inductiveness gives [R_P(u)] for every head atom.
   So an [unsat] of [p'] is an [unsat] of [p], and a [sat] of [p'] is turned
   into one of [p] by conjoining [R] ([strengthen_solution]).  The argument
   uses only that the clauses hold; for an unknown of another kind (a
   functional predicate, a well-founded relation) conjoining [R] may break the
   kind's condition, which is why only the ordinary kind is touched.  The
   pure part may not mention an unknown; a problem in which one does is left
   alone ([infer] returns nothing).

   What it buys: with each body word bounded at the top level of a clause,
   the conversion to Z3 can hand the word to Z3 as a bit-vector
   ([Z3interface.set_int_to_bv_range]'s bounded rule) instead of splitting it
   into a bit-vector and an unbounded quotient. *)

(** the argument list of an application of an unknown *)
let pvar_args (atm : Atom.t) =
  match atm with
  | Atom.App (Predicate.Var (p, sorts), ts, _) -> Some (p, sorts, ts)
  | _ -> None

(** the widths [n] of every [int_to_bv n] the formulas mention *)
let widths_of (phis : Formula.t list) =
  List.concat_map phis ~f:(fun phi ->
      Set.to_list
      @@ Set.Poly.filter_map (Formula.funsyms_of phi) ~f:(function
        | T_irb.IntToBV (Some n) when n > 0 -> Some n
        | _ -> None))
  |> List.dedup_and_sort ~compare:Int.compare

(** [0 <= t /\ t < 2^n] *)
let range_of n t =
  Formula.and_of
    [
      Formula.mk_atom (T_int.mk_geq t (T_int.zero ()));
      Formula.mk_atom (T_int.mk_lt t (T_int.mk_int Z.(shift_left one n)));
    ]

let triple_equal (p, i, n) (q, j, m) = Ident.pvar_equal p q && i = j && n = m

(** [R_P(ts)] for the triples of [P] in [kept] *)
let ranges_at kept p ts =
  List.filter_map kept ~f:(fun (q, i, n) ->
      if Ident.pvar_equal p q then Option.map (List.nth ts i) ~f:(range_of n)
      else None)

(** the body ranges of a clause under [kept] *)
let body_ranges kept ns =
  List.concat_map (Set.to_list ns) ~f:(fun atm ->
      match pvar_args atm with
      | Some (p, _, ts) -> ranges_at kept p ts
      | None -> [])

(** The triples [(P, i, n)] for the integer argument positions of the ordinary
    unknowns of [clauses] and the widths [ws]. *)
let candidates ~is_ord ws (clauses : ClauseOld.t list) =
  List.concat_map clauses ~f:(fun (_, ps, ns, _) ->
      List.filter_map (Set.to_list (Set.union ps ns)) ~f:pvar_args)
  |> List.dedup_and_sort ~compare:(fun (p, _, _) (q, _, _) ->
      String.compare (Ident.name_of_pvar p) (Ident.name_of_pvar q))
  |> List.concat_map ~f:(fun (p, sorts, _) ->
      if not (is_ord p) then []
      else
        List.concat
        @@ List.filter_mapi sorts ~f:(fun i s ->
            match s with
            | T_int.SInt -> Some (List.map ws ~f:(fun n -> (p, i, n)))
            | _ -> None))

(** The greatest inductive subset of [cands] (see the head of this file).
    [valid phi] answers whether [phi] is valid; anything but [true] drops the
    triple asked about. Returns [[]] when a clause's pure part applies an
    unknown, since the argument above assumes it does not. *)
let infer ~valid ~cands (clauses : ClauseOld.t list) =
  if
    List.exists clauses ~f:(fun (_, _, _, phi) ->
        not (Set.is_empty (Formula.pvs_of phi)))
  then []
  else
    let rec loop kept =
      let dropped =
        List.concat_map clauses ~f:(fun (_, ps, ns, phi) ->
            if Set.is_empty ps then []
            else
              let prem = Formula.and_of (body_ranges kept ns) in
              List.concat_map (Set.to_list ps) ~f:(fun atm ->
                  match pvar_args atm with
                  | None -> []
                  | Some (p, _, ts) ->
                      List.filter kept ~f:(fun (q, i, n) ->
                          Ident.pvar_equal p q
                          &&
                          match List.nth ts i with
                          | None -> true
                          | Some t ->
                              not
                              @@ valid
                                   (Formula.or_of
                                      [ phi; Formula.mk_neg prem; range_of n t ]))))
      in
      if List.is_empty dropped then kept
      else
        loop
          (List.filter kept ~f:(fun c ->
               not (List.mem dropped c ~equal:triple_equal)))
    in
    loop cands

(** [p'] of the head of this file: [R_Q(t)] as a premise of every body atom
    [Q(t)], that is [not R_Q(t)] as a disjunct of the clause's pure part. *)
let strengthen_clause kept ((senv, ps, ns, phi) : ClauseOld.t) : ClauseOld.t =
  match body_ranges kept ns with
  | [] -> (senv, ps, ns, phi)
  | rs -> (senv, ps, ns, Formula.or_of (phi :: List.map rs ~f:Formula.mk_neg))

(** [s' /\ R] for a solution [s'] of [p'], given each unknown's sort in
    [exi_senv]: the solution of an unknown with kept triples becomes
    [fun x. s'(P)(x) /\ R_P(x)]; any other is unchanged. *)
let strengthen_solution kept exi_senv (sol : Logic.term_subst_map) =
  Map.Poly.mapi sol ~f:(fun ~key ~data ->
      let p = Ident.tvar_to_pvar key in
      if not (List.exists kept ~f:(fun (q, _, _) -> Ident.pvar_equal p q)) then
        data
      else
        match Map.Poly.find exi_senv key with
        | None -> data
        | Some sort ->
            let args = Logic.Sort.args_of sort in
            let xs =
              List.map args ~f:(fun s ->
                  (Ident.mk_fresh_tvar ~prefix:(Some "w") (), s))
            in
            let old_xs =
              List.map xs ~f:(fun (x, s) ->
                  Term.mk_var x (Logic.ExtTerm.to_old_sort s))
            in
            let r = Formula.and_of (ranges_at kept p old_xs) in
            Logic.Term.mk_lambda xs
            @@ Logic.BoolTerm.and_of
                 [
                   Logic.Term.beta_reduction
                     (Logic.Term.mk_apps data
                        (List.map xs ~f:(fun (x, _) -> Logic.Term.mk_var x)));
                   Logic.ExtTerm.of_old_formula r;
                 ])
