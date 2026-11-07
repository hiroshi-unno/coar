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

(* [Some (v, hi)] when the formula [c] is an atom [v < hi] (or [hi > v], or
   [v <= h], read as [hi = h + 1]); an atom bounds at most one variable this
   way, its comparison having one variable side *)
let bound_of_conjunct c =
  let open LogicOld in
  match c with
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Lt, [ Term.Var (v, _, _); hi ], _), _)
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Gt, [ hi; Term.Var (v, _, _) ], _), _) ->
      Some (v, hi)
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Leq, [ Term.Var (v, _, _); h ], _), _)
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Geq, [ h; Term.Var (v, _, _) ], _), _) ->
      Some (v, T_int.mk_add h (T_int.from_int 1))
  | _ -> None

(* the upper bound [hi] the first conjunct of [conj] that bounds the variable
   [y] places on it *)
let upper_bound y conj =
  List.find_map (LogicOld.Formula.conjuncts_list_of conj) ~f:(fun c ->
      match bound_of_conjunct c with
      | Some (v, hi) when Ident.tvar_equal v y -> Some hi
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

(* whether every variable of [hi] is one of the witness's arguments
   [arg_vars] ([None] for an argument that is not a variable) *)
let hi_over_args arg_vars hi =
  Set.for_all (LogicOld.Term.tvs_of hi) ~f:(fun v ->
      List.exists arg_vars ~f:(function
        | Some x -> Ident.tvar_equal x v
        | None -> false))

(* [hi - 1] with each variable of [hi] read at the first position of
   [arg_vars] that holds it, as the variable [param i s] of that position [i]
   (of [Logic] sort [s] among the witness's argument sorts [sorts]) *)
let value_at_positions sorts arg_vars hi ~param =
  let sub =
    Map.Poly.of_alist_exn
    @@ List.filter_map (Set.to_list (LogicOld.Term.tvs_of hi)) ~f:(fun v ->
        List.find_mapi arg_vars ~f:(fun i -> function
          | Some x when Ident.tvar_equal x v ->
              let s = List.nth_exn sorts i in
              Some (v, LogicOld.Term.mk_var (param i) (Logic.ExtTerm.to_old_sort s))
          | _ -> None))
  in
  LogicOld.T_int.mk_sub (LogicOld.Term.subst sub hi) (LogicOld.T_int.from_int 1)

(* the seed of the witness [w] read off its application to [arg_vars] (then
   its last argument) and the bound [hi] on that last argument:
   [w(x, r) := r = hi(x) - 1], a [Logic] lambda over [w]'s sort with fresh
   parameters *)
let definition exi_senv w arg_vars hi =
  let sorts = Logic.Sort.args_of (Map.Poly.find_exn exi_senv w) in
  let xs = List.map sorts ~f:(fun s -> (Ident.mk_fresh_tvar (), s)) in
  let params, (r, rs) = List.rest_last xs in
  let value =
    value_at_positions (List.map params ~f:snd) arg_vars hi ~param:(fun i ->
        fst (List.nth_exn params i))
  in
  let body =
    Logic.ExtTerm.of_old_formula
      (LogicOld.Formula.eq
         (LogicOld.Term.mk_var r (Logic.ExtTerm.to_old_sort rs))
         value)
  in
  Logic.Term.mk_lambda xs body

(* [definition] up to the names of its parameters: two seeds of one witness
   are the same function iff their keys are equal *)
let definition_key exi_senv w arg_vars hi =
  let sorts = Logic.Sort.args_of (Map.Poly.find_exn exi_senv w) in
  let params, _ = List.rest_last sorts in
  value_at_positions params arg_vars hi ~param:(fun i ->
      Ident.Tvar (sprintf "#witness_seed_position%d" i))

(* structural equality of two [LogicOld] terms; [false] where the
   comparison cannot be made (a term holding a functional value), which
   callers read as "may differ" *)
let same_term a b =
  try Stdlib.( = ) a b with exn_ when not (Common.Timer.is_async exn_) -> false

let add_term his hi =
  if List.exists his ~f:(same_term hi) then his else his @ [ hi ]

(* The seeds of the formula [phi] (in NNF), for the witnesses of [fns] not
   yet in [found], read without building the clausal form; [None] when this
   reading cannot tell that its answer is the one [seeds]'s walk over the
   clausal form gives, which then makes that walk.

   The walk takes, for each clause in its order and each negated witness
   atom [w(ins, y)] of it in order, the first bound on [y] that [upper_bound]
   reads off a disjunct of the clause's pure part, and keeps the first seed
   for [w] whose bound is over [ins].  [Logic.BoolTerm.neg_atom_pure_contexts]
   gives, for each negated atom, every bound on its last argument read off
   any disjunct of the pure part of any clause holding it (each disjunct's
   first bound per variable, [f] below; a pure part's disjuncts are its
   parts' disjuncts, so this [f] is disjunctive).  When an atom's bounds are
   all over [ins] and give one definition, every clause holding it in which
   the walk finds a bound gives that seed; when none is over [ins], none
   does; and when every atom of [w] that gives a seed gives the same one, the
   walk's first seed for [w] is that one, whatever the order.  Otherwise the
   answer may depend on the order, and this says [None]. *)
let seeds_without_cnf exi_senv uni_senv fns found phi =
  let module Phys = Stdlib.Hashtbl.Make (struct
    type t = Logic.term

    let equal = phys_equal
    let hash = Common.Ext.Hashtbl.phys_hash
  end) in
  let memo = Phys.create 64 in
  let f part =
    match Phys.find_opt memo part with
    | Some m -> m
    | None ->
        let m =
          List.fold (Logic.BoolTerm.disjuncts_of part) ~init:Map.Poly.empty
            ~f:(fun acc d ->
              List.fold
                (LogicOld.Formula.disjuncts_list_of
                   (Logic.ExtTerm.to_old_fml exi_senv uni_senv d))
                ~init:acc
                ~f:(fun acc d' ->
                  (* the first bound per variable of this disjunct *)
                  let firsts =
                    List.fold (LogicOld.Formula.conjuncts_list_of d')
                      ~init:Map.Poly.empty ~f:(fun firsts c ->
                        match bound_of_conjunct c with
                        | Some (v, hi) when not (Map.Poly.mem firsts v) ->
                            Map.Poly.set firsts ~key:v ~data:hi
                        | _ -> firsts)
                  in
                  Map.Poly.fold firsts ~init:acc ~f:(fun ~key ~data acc ->
                      Map.Poly.update acc key ~f:(function
                        | None -> [ data ]
                        | Some his -> add_term his data))))
        in
        Phys.add memo part m;
        m
  in
  let union m1 m2 =
    Map.Poly.merge m1 m2 ~f:(fun ~key:_ -> function
      | `Left a | `Right a -> Some a
      | `Both (a, b) -> Some (List.fold b ~init:a ~f:add_term))
  in
  let exception Undecided in
  try
    match
      Logic.BoolTerm.neg_atom_pure_contexts exi_senv uni_senv phi
        ~empty:Map.Poly.empty ~union ~f
    with
    | None -> None
    | Some atoms ->
        (* per witness, the first atom's seed and every seed's key *)
        let seeds = Hashtbl.Poly.create () in
        List.iter atoms ~f:(fun (atm, bounds) ->
            match Logic.ExtTerm.let_apps atm with
            | Logic.Var (w, _), args
              when Set.mem fns w && not (Hashtbl.Poly.mem found w) -> (
                match List.rest_last_opt args with
                | Some (ins, Logic.Var (y, _)) -> (
                    let arg_vars =
                      List.map ins ~f:(function
                        | Logic.Var (x, _) -> Some x
                        | _ -> None)
                    in
                    let his = Option.value ~default:[] (Map.Poly.find bounds y) in
                    match List.partition_tf his ~f:(hi_over_args arg_vars) with
                    | [], _ -> ()
                    | hi :: his', [] ->
                        let key = definition_key exi_senv w arg_vars hi in
                        if
                          not
                            (List.for_all his' ~f:(fun hi' ->
                                 same_term key
                                   (definition_key exi_senv w arg_vars hi')))
                        then raise Undecided;
                        Hashtbl.Poly.update seeds w ~f:(function
                          | None -> (key, arg_vars, hi)
                          | Some ((key0, _, _) as first) ->
                              if same_term key0 key then first
                              else raise Undecided)
                    | _ :: _, _ :: _ -> raise Undecided)
                | _ -> ())
            | _ -> ());
        Some
          (Hashtbl.Poly.to_alist seeds
          |> List.map ~f:(fun (w, (_, arg_vars, hi)) ->
              (w, definition exi_senv w arg_vars hi)))
  with
  | Undecided -> None
  | exn_ when not (Common.Timer.is_async exn_) -> None

(* [(w, definition)] for every functional unknown of [pcsp] with a bound; the
   definition is a [Logic] lambda over the unknown's sort.  With
   [filter_disjuncts], a formula [formula_may_seed] rules out is not put in
   clausal form, an atom whose last argument no disjunct of its clause may
   bound is passed over, and only the disjuncts of a pure part that may bound
   it are converted ([disjuncts_mentioning]); the result is the same.

   Each formula's seeds are first read without its clausal form
   ([seeds_without_cnf]), and the clausal form is built and walked only for a
   formula that reading leaves undecided (or always, with
   [via_clausal_form]); the seeds are the same up to the names of the
   definitions' parameters.  Why: the clausal form of a disjunction is the
   product of its operands' clause sets, and the dual of a nondeterministic
   integer transition system (a disjunction over transitions, each a
   conjunction of guards and witness applications) gave a formula of 22,835
   nodes whose clausal form has about 2 x 10^10 clauses (counting a
   conjunction's as the sum of its operands' and a disjunction's as their
   product): building it took the whole of a 300 s run. *)
let seeds ?(filter_disjuncts = false) ?(via_clausal_form = false) pcsp =
  let fns = PCSP.Problem.fnpvs_of pcsp in
  let exi_senv = PCSP.Problem.senv_of pcsp in
  if Set.is_empty fns then []
  else
    let found = Hashtbl.Poly.create () in
    Set.iter (PCSP.Problem.formulas_of pcsp) ~f:(fun (uni_senv, phi) ->
        if filter_disjuncts && not (formula_may_seed exi_senv fns phi) then ()
        else
        match Logic.ExtTerm.nnf_of phi with
        | exception exn_ when not (Common.Timer.is_async exn_) -> ()
        | nnf -> (
        match
          if via_clausal_form then None
          else
            Common.PhaseTime.with_phase "contexts" (fun () ->
                seeds_without_cnf exi_senv uni_senv fns found nnf)
        with
        | Some defs ->
            List.iter defs ~f:(fun (w, def) ->
                Hashtbl.Poly.set found ~key:w ~data:def)
        | None ->
        try
          Set.iter
            (Common.PhaseTime.with_phase "cnf" (fun () ->
                 Logic.ExtTerm.cnf_of exi_senv uni_senv nnf))
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
                          | Some hi when hi_over_args arg_vars hi ->
                              Hashtbl.Poly.set found ~key:w
                                ~data:(definition exi_senv w arg_vars hi)
                          | _ -> ())
                      | _ -> ()
                      | exception exn_ when not (Common.Timer.is_async exn_)
                        ->
                          ())
                  | _ -> ()
                  | exception exn_ when not (Common.Timer.is_async exn_) ->
                      ()))
        with exn_ when not (Common.Timer.is_async exn_) -> ()));
    Hashtbl.Poly.to_alist found
    |> List.sort ~compare:(fun (a, _) (b, _) -> Ident.tvar_compare a b)
