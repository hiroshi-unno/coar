(* A diagnostic census of what the validator's counterexamples refute a
   quantified candidate FOR: the array contents or the indices.  Enabled by
   [COAR_REFUTATION_CENSUS=1]; otherwise nothing here runs and nothing the loop
   does changes.  It writes one line per validation round to stderr.

   The candidates it reads are the read-back of a cell template,
   [P(x) := forall j. D1 \/ ... \/ Dm] with each [Di] a conjunction of
   literals.  A literal is a VALUE literal when it reads an array ([a[j] <= 0],
   [a[j] = b[k]]) and an INDEX literal otherwise ([j >= n], [k = j + i]).

   The classification of one refuted atom asks whether array contents could
   have saved the candidate there -- a question about the index literals alone,
   so the atom's array arguments never enter it:

   - an atom the candidate had to make TRUE (a positive example, or the
     conclusion of an implication) and made false: the refutation is about
     INDICES when some cell falsifies an index literal in every disjunct, since
     no contents make the candidate true at that cell; otherwise every cell it
     fails at has a disjunct whose index literals all hold, and the refutation
     is about VALUES;
   - an atom it had to make FALSE (a negative example) and made true: the
     refutation is about VALUES when some cell lets contents falsify every
     disjunct (each has a value literal or an already false index literal);
     otherwise no contents make it false anywhere, and it is about INDICES.

   A parametric atom's parameters and the cell variables are all free in these
   queries, so both are existential; the atom's guard is conjoined.  An atom
   whose query is not decided is counted as undecided, never as either. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let enabled =
  Lazy.from_val
    (match Sys.getenv "COAR_REFUTATION_CENSUS" with
    | Some ("1" | "2" | "true" | "yes") -> true
    | _ -> false)

let on () = Lazy.force enabled

(* [2] also prints, for each refutation about indices of an atom that had to
   hold, the cell the query found: the indices no contents can save *)
(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let detail =
  Lazy.from_val
    (match Sys.getenv "COAR_REFUTATION_CENSUS" with
    | Some "2" -> true
    | _ -> false)

let round = ref 0

(* every integer an array term stores or defaults to, through stores *)
let rec array_values acc = function
  | Term.FunApp (T_array.AStore _, [ a; _; v ], _) ->
      array_values (array_values acc v) a
  | Term.FunApp (T_array.AConst _, [ v ], _) -> array_values acc v
  | Term.FunApp (T_int.Int n, [], _) -> Set.add acc n
  | Term.FunApp (T_int.Neg, [ Term.FunApp (T_int.Int n, [], _) ], _) ->
      Set.add acc (Z.neg n)
  | _ -> acc

let reads_array phi =
  let found = ref false in
  Formula.iter_term phi ~f:(fun t -> if T_array.is_select t then found := true);
  !found

(* the arrays a literal reads, by their printed form, which is only used to
   count how many distinct ones there are *)
let arrays_read phi =
  let arrs = ref Set.Poly.empty in
  Formula.iter_term phi ~f:(function
    | Term.FunApp (T_array.ASelect _, [ a; _ ], _) ->
        arrs := Set.add !arrs (Term.str_of a)
    | _ -> ());
  !arrs

type literal_class = Index | IndexRel | ValueBound | ValueRel

let class_of bound lit =
  if reads_array lit then
    if Set.length (arrays_read lit) >= 2 then ValueRel else ValueBound
  else if Set.length (Set.inter (Formula.tvs_of lit) bound) >= 2 then IndexRel
  else Index

(* [(bound variables, disjuncts as literal lists)] of a candidate body *)
let shape_of phi =
  (* the read-back nests one binder per cell, so every leading [forall] is
     stripped, not only the outermost *)
  let rec strip bound phi =
    if Formula.is_forall phi then
      let senv, body, _ = Formula.let_forall phi in
      strip (Set.union bound (Set.Poly.of_list (List.map senv ~f:fst))) body
    else (bound, phi)
  in
  let bound, body = strip Set.Poly.empty phi in
  (bound, List.map (Formula.disjuncts_list_of body) ~f:Formula.conjuncts_list_of)

type verdict = About_values | About_indices | Undecided

let classify ~id fenv ~must_hold (params, phi) cond terms =
  let bound, disjuncts = shape_of phi in
  let sub =
    Map.Poly.of_alist_exn
    @@ List.map2_exn params terms ~f:(fun (x, _) t -> (x, t))
  in
  let index_lits d = List.filter d ~f:(Fn.non reads_array) in
  let some_false lits =
    Formula.or_of
    @@ List.map lits ~f:(fun l -> Formula.mk_neg (Formula.subst sub l))
  in
  let query =
    Formula.and_of
    @@ cond
       :: List.map disjuncts ~f:(fun d ->
           if must_hold then some_false (index_lits d)
           else if List.exists d ~f:reads_array then Formula.mk_true ()
           else some_false (index_lits d))
  in
  match
    try Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 2000) fenv [ query ]
    with exn_ when not (Common.Timer.is_async exn_) -> `Unknown ""
  with
  | `Sat model ->
      if must_hold && Lazy.force detail then
        eprintf "[refutation-census]   uncovered cell: %s\n%!"
          (String.concat ~sep:", "
          @@ List.filter_map model ~f:(fun ((x, _), v) ->
              if Set.mem bound x then
                Some
                  (sprintf "%s=%s" (Ident.name_of_tvar x)
                     (match v with Some t -> Term.str_of t | None -> "_"))
              else None));
      if must_hold then About_indices else About_values
  | `Unsat -> if must_hold then About_values else About_indices
  | _ -> Undecided

let seen_values = ref Set.Poly.empty

(* One line for the round: the candidate's literals by class, then per kind of
   refuted atom how many refutations were about values, about indices, or
   undecided, then the distinct integers the round's counterexample arrays
   hold, new ones and all ones seen so far. *)
let report ~id fenv (cand : CandSolOld.t) (exs : ExClause.t list) =
  incr round;
  let preds =
    Map.Poly.of_alist_reduce ~f:(fun a _ -> a) @@ Set.to_list (snd cand)
  in
  let lits = Array.create ~len:4 0 in
  Map.Poly.iter preds ~f:(fun (_, phi) ->
      let bound, disjuncts = shape_of phi in
      List.iter (List.concat disjuncts) ~f:(fun l ->
          let i =
            match class_of bound l with
            | Index -> 0
            | IndexRel -> 1
            | ValueBound -> 2
            | ValueRel -> 3
          in
          lits.(i) <- lits.(i) + 1));
  (* kind -> (values, indices, undecided) *)
  let tally = Hashtbl.Poly.create () in
  let bump kind v =
    let a, b, c = Hashtbl.find tally kind |> Option.value ~default:(0, 0, 0) in
    Hashtbl.set tally ~key:kind
      ~data:
        (match v with
        | About_values -> (a + 1, b, c)
        | About_indices -> (a, b + 1, c)
        | Undecided -> (a, b, c + 1))
  in
  let values = ref Set.Poly.empty in
  let atom_parts = function
    | ExAtom.PApp ((pvar, _), terms) -> Some (pvar, Formula.mk_true (), terms)
    | ExAtom.PPApp ((_, cond), ((pvar, _), terms)) -> Some (pvar, cond, terms)
    | ExAtom.FCon _ -> None
  in
  let visit kind ~must_hold atm =
    match atom_parts atm with
    | None -> ()
    | Some (pvar, cond, terms) -> (
        List.iter terms ~f:(fun t ->
            if T_array.is_sarray (Term.sort_of t) then
              values := array_values !values t);
        match Map.Poly.find preds pvar with
        | None -> ()
        | Some cand_p ->
            bump kind (classify ~id fenv ~must_hold cand_p cond terms))
  in
  List.iter exs ~f:(fun ex ->
      let pos = ex.ExClause.positive and neg = ex.ExClause.negative in
      if Set.is_empty neg then Set.iter pos ~f:(visit "pos" ~must_hold:true)
      else if Set.is_empty pos then
        Set.iter neg ~f:(visit "neg" ~must_hold:false)
      else Set.iter pos ~f:(visit "impl" ~must_hold:true));
  let fresh = Set.diff !values !seen_values in
  seen_values := Set.union !seen_values !values;
  let str kind =
    let a, b, c = Hashtbl.find tally kind |> Option.value ~default:(0, 0, 0) in
    sprintf "%s values=%d indices=%d undecided=%d" kind a b c
  in
  eprintf
    "[refutation-census] round %d cand index=%d index-rel=%d value-bound=%d \
     value-rel=%d | %s | %s | %s | array-values round=%d new=%d seen=%d\n\
     %!"
    !round lits.(0) lits.(1) lits.(2) lits.(3) (str "pos") (str "neg")
    (str "impl") (Set.length !values) (Set.length fresh)
    (Set.length !seen_values)
