(* A guess for the witnesses of guarded body universals: the last index.

   A body universal [forall q. lo <= q < hi => A(q)] over an unknown is
   skolemised into a functional witness [w(x, q)], and the clause then reads
   [not w(x, q) \/ (lo <= q /\ q < hi /\ not A(q)) \/ ...].  The witness that
   proves such a clause for a loop that stops at the first [q] with a property
   is typically [hi - 1]: the last index is where the property would fail if
   it failed anywhere the clause cares about.  [seeds] reads, for each
   witness, an upper bound [hi] off the guard of one of its clauses -- a
   conjunct [q < hi] (or [hi > q], or [q <= h], read as [hi = h + 1]) of a
   disjunct of the clause's pure part, with [hi] over the witness's own
   arguments -- and defines the witness as [w(x, r) := r = hi(x) - 1].

   A definition so chosen is a total, single-valued function of the
   witness's arguments, so substituting it is choosing one value of the
   witness: a solution of the problem with every seeded witness substituted,
   together with the definitions, is a solution of the problem.  So only a
   [sat] of the seeded problem may be read; an [unsat] says only that this
   choice fails. *)

open Core
open Common.Ext
open Ast

(* the upper bound [hi] a conjunct of [conj] places on the variable [y] *)
let upper_bound y conj =
  let open LogicOld in
  List.find_map (Formula.conjuncts_list_of conj) ~f:(function
    | Formula.Atom (Atom.App (Predicate.Psym T_int.Lt, [ Term.Var (v, _, _); hi ], _), _)
    | Formula.Atom (Atom.App (Predicate.Psym T_int.Gt, [ hi; Term.Var (v, _, _) ], _), _)
      when Ident.tvar_equal v y ->
        Some hi
    | Formula.Atom (Atom.App (Predicate.Psym T_int.Leq, [ Term.Var (v, _, _); h ], _), _)
    | Formula.Atom (Atom.App (Predicate.Psym T_int.Geq, [ h; Term.Var (v, _, _) ], _), _)
      when Ident.tvar_equal v y ->
        Some (T_int.mk_add h (T_int.from_int 1))
    | _ -> None)

(* Whether a [Logic] disjunct [d] may give [upper_bound y] a bound after its
   conversion.  [upper_bound y] reads a top-level conjunct that is a
   comparison atom with [Var y] as one of its two arguments.  The conversion
   keeps a conjunction's operands as the conjuncts and an application of a
   symbol as an atom over the converted arguments, so such an atom comes only
   from a conjunct whose head is a symbol (under type applications) and among
   whose arguments is [Var y].  A conjunct of any other shape (a [let], a
   lambda redex, a binder) is kept, since its conversion is not read off its
   syntax here.  So a disjunct this says [false] of gives no bound, and leaving
   it unconverted changes no answer. *)
(* The candidates of [may_bound] in [d]: [Some v] for each variable [v] that
   is an argument of a top-level conjunct with a symbol head, [None] for each
   conjunct whose conversion is not read off its syntax.  A quantifier at the
   top of a conjunct converts to a binder, never to an atom, and gives
   nothing. *)
let bound_args d =
  let rec symbol_head = function
    | Logic.Con _ | Logic.Var _ -> true
    | Logic.TyApp (t, _, _) -> symbol_head t
    | _ -> false
  in
  List.concat_map (Logic.BoolTerm.conjuncts_of d) ~f:(fun c ->
      match Logic.Term.let_apps c with
      | Logic.Bin ((Logic.Forall | Logic.Exists), _, _, _, _), [] -> []
      | head, args when symbol_head head ->
          List.filter_map args ~f:(function
            | Logic.Var (v, _) -> Some (Some v)
            | _ -> None)
      | _ -> [ None ])

let may_bound y d =
  List.exists (bound_args d) ~f:(function
    | None -> true
    | Some v -> Ident.tvar_equal v y)

(* The converted disjuncts of [pure] (a [Logic] formula) that may give an
   upper bound on [y] ([may_bound]), in their order: a sublist of the
   [LogicOld] disjuncts of the conversion of [pure] that keeps every one
   [upper_bound y] reads a bound from, since a disjunction converts to the
   disjunction of the converted parts.  Why: on Rust-derived inputs with large
   pure parts, converting every pure part whole, once per witness atom of each
   clause of the normal form (82,000 to 475,000 conversions), took 87 s to more
   than 300 s before any solving began. *)
let disjuncts_mentioning exi_senv uni_senv y pure =
  List.concat_map (Logic.BoolTerm.disjuncts_of pure) ~f:(fun d ->
      if may_bound y d then
        LogicOld.Formula.disjuncts_list_of
          (Logic.ExtTerm.to_old_fml exi_senv uni_senv d)
      else [])

(* Whether an input formula [phi] may give a seed: [false] only when no
   functional unknown of [fns] is applied in [phi] with a last argument [Var y]
   that is also a direct argument of an application of a theory symbol (or of
   a variable that is not an unknown), and [phi] holds no [let] and no lambda
   redex.  A seed is read off an atom [y < hi] (or its variants) of a clause of
   the normal form of [phi]; the negation normal form and the clausal form
   keep every atom's arguments (an atom may be negated or its comparison
   flipped, never rebuilt over other terms), so such an atom is an application
   of a theory symbol with [Var y] among its arguments already in [phi].  So a
   formula this says [false] of gives no seed, and its normal form, the
   costliest step, need not be built. *)
let formula_may_seed exi_senv fns phi =
  let args_of_symbols = Hash_set.Poly.create () in
  let witness_lasts = ref [] in
  let opaque = ref false in
  let rec go t =
    match t with
    | Logic.Let (_, _, def, body, _) ->
        opaque := true;
        go def;
        go body
    | Logic.Bin (_, _, _, body, _) -> go body
    | Logic.TyApp (t, _, _) -> go t
    | Logic.App _ -> (
        let head, args = Logic.Term.let_apps t in
        List.iter args ~f:go;
        let rec base = function Logic.TyApp (t, _, _) -> base t | t -> t in
        match base head with
        | Logic.Var (v, _) when Map.Poly.mem exi_senv v -> (
            if Set.mem fns v then
              match List.last args with
              | Some (Logic.Var (y, _)) -> witness_lasts := y :: !witness_lasts
              | _ -> ())
        | Logic.Var _ | Logic.Con _ ->
            List.iter args ~f:(function
              | Logic.Var (y, _) -> Hash_set.add args_of_symbols y
              | _ -> ())
        | head ->
            opaque := true;
            go head)
    | _ -> ()
  in
  go phi;
  !opaque || List.exists !witness_lasts ~f:(Hash_set.mem args_of_symbols)

(* [(w, definition)] for every functional unknown of [pcsp] with a bound; the
   definition is a [Logic] lambda over the unknown's sort.  With
   [filter_disjuncts], a formula [formula_may_seed] rules out is not put in
   clausal form, an atom whose last argument no disjunct of its clause may
   bound is passed over, and only the disjuncts of a pure part that may bound
   it are converted ([disjuncts_mentioning]); the result is the same. *)
let seeds ?(filter_disjuncts = false) pcsp =
  let fns = PCSP.Problem.fnpvs_of pcsp in
  let exi_senv = PCSP.Problem.senv_of pcsp in
  if Set.is_empty fns then []
  else
    let found = Hashtbl.Poly.create () in
    Set.iter (PCSP.Problem.formulas_of pcsp) ~f:(fun (uni_senv, phi) ->
        if filter_disjuncts && not (formula_may_seed exi_senv fns phi) then ()
        else
        try
          Set.iter
            (Common.PhaseTime.with_phase "cnf" (fun () ->
                 Logic.ExtTerm.cnf_of exi_senv uni_senv
                   (Logic.ExtTerm.nnf_of phi)))
            ~f:(fun (_, ns, pure) ->
              (* with [filter_disjuncts], the variables any disjunct of
                 [pure] may bound, computed once for the clause: an atom whose
                 last argument is not among them (and no disjunct is opaque)
                 gives no seed and is passed over unconverted *)
              let may_bound_clause =
                lazy
                  (let cands =
                     List.concat_map (Logic.BoolTerm.disjuncts_of pure)
                       ~f:bound_args
                   in
                   let opaque = List.exists cands ~f:Option.is_none in
                   let vars =
                     Hash_set.Poly.of_list (List.filter_opt cands)
                   in
                   fun y -> opaque || Hash_set.mem vars y)
              in
              Set.iter ns ~f:(fun atm ->
                  match Logic.ExtTerm.let_apps atm with
                  | Logic.Var (w, _), args
                    when Set.mem fns w && not (Hashtbl.Poly.mem found w) -> (
                      match List.rest_last args with
                      | _, Logic.Var (y, _)
                        when filter_disjuncts
                             && not (Lazy.force may_bound_clause y) ->
                          ()
                      | ins, Logic.Var (y, _) -> (
                          let arg_vars =
                            List.map ins ~f:(function
                              | Logic.Var (x, _) -> Some x
                              | _ -> None)
                          in
                          let disjuncts =
                            Common.PhaseTime.with_phase "to-old" (fun () ->
                                if filter_disjuncts then
                                  disjuncts_mentioning exi_senv uni_senv y pure
                                else
                                  LogicOld.Formula.disjuncts_list_of
                                    (Logic.ExtTerm.to_old_fml exi_senv uni_senv
                                       pure))
                          in
                          match List.find_map disjuncts ~f:(upper_bound y) with
                          | Some hi
                            when Set.for_all (LogicOld.Term.tvs_of hi)
                                   ~f:(fun v ->
                                     List.exists arg_vars ~f:(function
                                       | Some x -> Ident.tvar_equal x v
                                       | None -> false)) ->
                              let sort = Map.Poly.find_exn exi_senv w in
                              let sorts = Logic.Sort.args_of sort in
                              let xs =
                                List.map sorts ~f:(fun s ->
                                    (Ident.mk_fresh_tvar (), s))
                              in
                              let params, (r, rs) = List.rest_last xs in
                              (* each variable of [hi] read at the first
                                 position that holds it *)
                              let sub =
                                Map.Poly.of_alist_exn
                                @@ List.filter_map
                                     (Set.to_list (LogicOld.Term.tvs_of hi))
                                     ~f:(fun v ->
                                       List.find_mapi arg_vars ~f:(fun i -> function
                                         | Some x when Ident.tvar_equal x v ->
                                             let p, s = List.nth_exn params i in
                                             Some
                                               ( v,
                                                 LogicOld.Term.mk_var p
                                                   (Logic.ExtTerm.to_old_sort s) )
                                         | _ -> None))
                              in
                              let value =
                                LogicOld.T_int.mk_sub
                                  (LogicOld.Term.subst sub hi)
                                  (LogicOld.T_int.from_int 1)
                              in
                              let body =
                                Logic.ExtTerm.of_old_formula
                                  (LogicOld.Formula.eq
                                     (LogicOld.Term.mk_var r
                                        (Logic.ExtTerm.to_old_sort rs))
                                     value)
                              in
                              Hashtbl.Poly.set found ~key:w
                                ~data:(Logic.Term.mk_lambda xs body)
                          | _ -> ())
                      | _ -> ()
                      | exception _ -> ())
                  | _ -> ()
                  | exception _ -> ()))
        with exn_ when not (Common.Timer.is_async exn_) -> ());
    Hashtbl.Poly.to_alist found
    |> List.sort ~compare:(fun (a, _) (b, _) -> Ident.tvar_compare a b)
