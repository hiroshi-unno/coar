(* Does a known solution satisfy the example clauses as the synthesis query
   states them?

   A template synthesizer over array cells does not see an example atom
   [P(t)]: it sees [P(t, c_1, ..., c_q)], the atom with some of its arrays'
   cells appended, and a candidate is a formula over those columns that is read
   back as its universal closure over them.  So a solution whose universal
   holds of every cell can still be excluded by an example: the example asks
   the candidate only at the cells it offers, and if every offered cell
   satisfies the solution's matrix while the example demands it be false (a
   body atom), no candidate whose read-back is that solution is left.  Whether
   that happens for a given solution is decidable from the examples alone, and
   this module decides it, so that "the examples exclude the intended
   invariant" can be told apart from "the search does not reach it".

   The solution is given as it would be written for the unknown, a formula over
   its parameters in which the universals are ordinary [forall]s over the
   arrays' indices.  Restricting it to an atom's offered cells means replacing
   each such [forall] block by the conjunction of its instances at the index
   tuples the atom offers: a block whose binders are, in order, the index sorts
   of one array path is instantiated at every cell of every path with those
   index sorts, and a block of several such groups at every combination.  The
   array reads inside the body are left as they are and so are evaluated on the
   example's own array, which gives the cell's value wherever the cell was read
   from that array -- every cell but a sequence's sentinel, whose value is a
   placeholder the read-back guards off.  The conjunction over every
   combination of offered cells is itself a matrix whose read-back is the
   solution, so a clause this finds violated is violated by at least that
   matrix; whether some other matrix with the same read-back satisfies it is
   not asked.  A block that matches no path, a block too large to expand, and a
   quantifier inside an equivalence are left quantified and reported.  A block
   is split longest group first, so a block of several cells whose sorts admit
   another split is best written as nested [forall]s, one per cell.

   Nothing here writes any state: every function is a pure computation over its
   arguments, and the one effect a caller supplies is the evaluation of a
   formula. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

type oracle_pred = sort_env_list * Formula.t

type verdict =
  | Holds
  | Violated
  | Undecided  (** the evaluation returned no answer *)
  | Skipped of string  (** the clause could not be stated; the reason *)

(* The most instances one quantifier block is expanded into; a larger block is
   left quantified and reported, since its expansion would cost more than the
   question is worth to a diagnostic. *)
let max_instances = 4096

(** The index tuples a celled atom offers, per array path, in the order of
    [paths]: the atom's arguments past [arity] are its cells, path-major and
    then cell by cell, each cell its path's index columns followed by its value
    column. [Error] when the columns do not divide into whole cells; [Ok] with
    every path empty when there are none. *)
let offered_cells ~(paths : CellQual.array_path list) ~arity
    (args : Term.t list) : (Term.t list list list, string) result =
  let extras = List.drop args arity in
  let width = CellQual.total_cell_width paths in
  if List.is_empty extras then Ok (List.map paths ~f:(fun _ -> []))
  else if width = 0 || List.length extras mod width <> 0 then
    Error
      (sprintf "%d cell column(s) do not divide into cells of total width %d"
         (List.length extras) width)
  else
    let qpa = List.length extras / width in
    Ok
      (snd
      @@ List.fold_map paths ~init:extras ~f:(fun rest path ->
          let w = CellQual.cell_width path in
          let mine, rest = List.split_n rest (qpa * w) in
          ( rest,
            List.map (List.chunks_of mine ~length:w) ~f:(fun cell ->
                List.take cell (w - 1)) )))

let str_of_sorts sorts =
  String.concat_map_list ~sep:"," sorts ~f:Term.str_of_sort

(* Split a quantifier block's binders into consecutive groups, each the index
   sorts of some path offering cells, longest group first; [None] when no
   split exists. *)
let rec segment pool_of = function
  | [] -> Some []
  | binders ->
      List.find_map
        (List.rev (List.range 1 (List.length binders + 1)))
        ~f:(fun n ->
          let group, rest = List.split_n binders n in
          match pool_of (List.map group ~f:snd) with
          | None -> None
          | Some tuples ->
              Option.map (segment pool_of rest) ~f:(fun groups ->
                  (group, tuples) :: groups))

(** [phi] with every [forall] block over offered index sorts replaced by the
    conjunction of its instances at the offered tuples. [phi] is expected in
    negation normal form, so that every [forall] it holds is universal. The
    second component lists what was left quantified, and why. *)
let restrict ~(pools : (Sort.t list * Term.t list list) list) (phi : Formula.t)
    : Formula.t * string list =
  let notes = ref [] in
  let note s = notes := s :: !notes in
  let pool_of sorts =
    let key = str_of_sorts sorts in
    match
      List.concat_map pools ~f:(fun (s, tuples) ->
          if String.equal (str_of_sorts s) key then tuples else [])
    with
    | [] -> None
    | tuples -> Some tuples
  in
  let rec has_forall = function
    | Formula.Bind (Formula.Forall, _, _, _) -> true
    | Formula.Bind (_, _, body, _)
    | Formula.UnaryOp (_, body, _)
    | Formula.LetFormula (_, _, _, body, _) ->
        has_forall body
    | Formula.BinaryOp (_, a, b, _) -> has_forall a || has_forall b
    | _ -> false
  in
  let rec go phi =
    match phi with
    | Formula.Bind (Formula.Forall, senv, body, info) -> (
        let body = go body in
        match segment pool_of senv with
        | None ->
            note
              (sprintf
                 "a forall over (%s) matches no offered cell; left quantified"
                 (str_of_sorts (List.map senv ~f:snd)));
            Formula.mk_forall ~info senv body
        | Some groups ->
            let count =
              List.fold groups ~init:1 ~f:(fun acc (_, tuples) ->
                  acc * List.length tuples)
            in
            if count > max_instances then (
              note
                (sprintf "a forall over (%s) has %d instances; left quantified"
                   (str_of_sorts (List.map senv ~f:snd))
                   count);
              Formula.mk_forall ~info senv body)
            else (
              if List.length groups > 1 then
                note
                  (sprintf "a forall over (%s) was read as %d cells: %s"
                     (str_of_sorts (List.map senv ~f:snd))
                     (List.length groups)
                     (String.concat ~sep:" "
                     @@ List.map groups ~f:(fun (g, _) ->
                         "(" ^ str_of_sorts (List.map g ~f:snd) ^ ")")));
              let subs =
                List.fold_right groups ~init:[ [] ]
                  ~f:(fun (group, tuples) acc ->
                    List.concat_map tuples ~f:(fun tuple ->
                        let bind =
                          List.map2_exn group tuple ~f:(fun (x, _) t -> (x, t))
                        in
                        List.map acc ~f:(fun rest -> bind @ rest)))
              in
              Formula.and_of
              @@ List.map subs ~f:(fun sub ->
                  Formula.subst (Map.Poly.of_alist_exn sub) body)))
    | Formula.Bind (b, senv, body, info) ->
        Formula.mk_bind ~info b senv (go body)
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), a, b, info) -> (
        match op with
        | Formula.And -> Formula.mk_and ~info (go a) (go b)
        | _ -> Formula.mk_or ~info (go a) (go b))
    | Formula.BinaryOp (_, _, _, _) as phi ->
        if has_forall phi then
          note "a forall under an equivalence is left as it is";
        phi
    | Formula.LetFormula (x, s, d, body, info) ->
        Formula.mk_let_formula ~info x s d (go body)
    | phi -> phi
  in
  let phi = go phi in
  (phi, List.rev !notes)

(** The solution [oracle] for an atom [P(args)] of sorts [sorts] whose first
    [arity] arguments are the unknown's own, restricted to the cells the rest
    offer; [paths] are the array paths of those first [arity] sorts. *)
let instance ~(oracle : oracle_pred) ~arity ~paths (sorts : Sort.t list)
    (args : Term.t list) : (Formula.t * string list, string) result =
  let params, phi = oracle in
  let psorts = List.map params ~f:snd in
  if List.length params <> arity then
    Error
      (sprintf "the solution has %d parameter(s) (%s), the unknown %d (%s)"
         (List.length params) (str_of_sorts psorts) arity
         (str_of_sorts (List.take sorts arity)))
  else if List.length args < arity || List.length sorts < arity then
    Error "the atom has fewer arguments than the unknown"
  else if
    not
      (String.equal (str_of_sorts psorts)
         (str_of_sorts (List.take sorts arity)))
  then
    Error
      (sprintf "the solution's parameter sorts (%s) are not the unknown's (%s)"
         (str_of_sorts psorts)
         (str_of_sorts (List.take sorts arity)))
  else
    let unbound =
      Set.diff (Formula.tvs_of phi) (Set.Poly.of_list (List.map params ~f:fst))
    in
    if not (Set.is_empty unbound) then
      Error
        (sprintf
           "the solution mentions %s, which is not a parameter of the unknown \
            (removed by the preprocessor?)"
           (String.concat_map_set ~sep:"," unbound ~f:Ident.name_of_tvar))
    else
      match offered_cells ~paths ~arity args with
      | Error e -> Error e
      | Ok cells ->
          let sub =
            Map.Poly.of_alist_exn
            @@ List.zip_exn (List.map params ~f:fst) (List.take args arity)
          in
          let pools =
            List.map2_exn paths cells ~f:(fun path tuples ->
                (path.CellQual.index_sorts, tuples))
          in
          Ok (restrict ~pools (Formula.subst sub (Formula.nnf_of phi)))

(** The example clause with every predicate application replaced by [oracle]'s
    restricted instance, as the formula a candidate must make valid (a guarded
    atom's guard is its premise); with the notes of each instance. *)
let clause_formula ~(oracle_of : Ident.pvar -> oracle_pred option)
    ~(arity_of : Ident.pvar -> int option)
    ~(paths_of : Sort.t list -> CellQual.array_path list) (clause : ExClause.t)
    : (Formula.t * string list, string) result =
  let lit pos atom =
    let sign phi = if pos then phi else Formula.mk_neg phi in
    let app cond ((pvar, sorts), args) =
      match oracle_of pvar with
      | None ->
          Error (sprintf "no solution given for %s" (Ident.name_of_pvar pvar))
      | Some oracle -> (
          let arity =
            Option.value (arity_of pvar) ~default:(List.length (fst oracle))
          in
          let paths = paths_of (List.take sorts arity) in
          match instance ~oracle ~arity ~paths sorts args with
          | Error e -> Error (sprintf "%s: %s" (Ident.name_of_pvar pvar) e)
          | Ok (phi, notes) ->
              let phi = sign phi in
              Ok
                ( (match cond with
                  | None -> phi
                  | Some cond -> Formula.mk_imply cond phi),
                  List.map notes ~f:(sprintf "%s: %s" (Ident.name_of_pvar pvar))
                ))
    in
    match atom with
    | ExAtom.FCon (_, phi) -> Ok (sign phi, [])
    | ExAtom.PApp papp -> app None papp
    | ExAtom.PPApp ((_, cond), papp) ->
        app (if Formula.is_true cond then None else Some cond) papp
  in
  let lits =
    List.map (Set.to_list clause.ExClause.positive) ~f:(lit true)
    @ List.map (Set.to_list clause.ExClause.negative) ~f:(lit false)
  in
  match Result.all lits with
  | Error e -> Error e
  | Ok lits ->
      Ok
        ( Formula.or_of (List.map lits ~f:fst),
          List.dedup_and_sort ~compare:String.compare
            (List.concat_map lits ~f:snd) )

(** Whether [oracle] satisfies [clause] as the synthesis query states it, [eval]
    deciding the validity of the resulting formula. *)
let check ~eval ~oracle_of ~arity_of ~paths_of clause : verdict * string list =
  match clause_formula ~oracle_of ~arity_of ~paths_of clause with
  | Error e -> (Skipped e, [])
  | Ok (phi, notes) -> (
      match eval phi with
      | Some true -> (Holds, notes)
      | Some false -> (Violated, notes)
      | None -> (Undecided, notes))

(** The first of [clauses] that [oracle] violates, with its notes. *)
let first_violated ~eval ~oracle_of ~arity_of ~paths_of clauses =
  List.find_map clauses ~f:(fun clause ->
      match check ~eval ~oracle_of ~arity_of ~paths_of clause with
      | Violated, notes -> Some (clause, notes)
      | _ -> None)

(** The cells each predicate application of [clause] offers, for a report. *)
let str_of_offered ~arity_of ~paths_of (clause : ExClause.t) =
  let atoms = Set.to_list (ExClause.exatoms_of clause) in
  String.concat ~sep:"; "
  @@ List.filter_map atoms ~f:(fun atom ->
      match atom with
      | ExAtom.PApp ((pvar, sorts), args)
      | ExAtom.PPApp (_, ((pvar, sorts), args)) -> (
          match arity_of pvar with
          | None -> None
          | Some arity -> (
              let paths = paths_of (List.take sorts arity) in
              match offered_cells ~paths ~arity args with
              | Error e -> Some (sprintf "%s: %s" (Ident.name_of_pvar pvar) e)
              | Ok cells ->
                  Some
                    (sprintf "%s: %s" (Ident.name_of_pvar pvar)
                       (String.concat ~sep:" "
                       @@ List.map2_exn paths cells ~f:(fun path tuples ->
                           sprintf "path(param %d, index %s)={%s}"
                             path.CellQual.param
                             (str_of_sorts path.CellQual.index_sorts)
                             (String.concat ~sep:" "
                             @@ List.map tuples ~f:(fun t ->
                                 "("
                                 ^ String.concat_map_list ~sep:","
                                     ~f:Term.str_of t
                                 ^ ")")))))))
      | ExAtom.FCon _ -> None)
