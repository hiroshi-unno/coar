open Core
open Common.Ext
open Common.Combinator
open LogicOld

(* Whether [Term.mk_dummy] of [si] is a closed term.  For a sort variable it
   is a fresh variable that no template parameter binds, so a qualifier over it
   is dropped by every template generator (a hole is a function of the
   parameters and must not leave another variable free); an arrow sort is
   treated the same way. *)
let closed_dummy_sort = function Sort.SVar _ | Sort.SArrow _ -> false | _ -> true

(* The terms an index position of sort [si] is read at: the term map's terms of
   that sort, the sort's default instance, and [1] beside [0] for an integer
   index.  With [~closed_dummy_only] the default instance is left out where it
   would be a variable (see [closed_dummy_sort]). *)
let index_terms ~closed_dummy_only term_map si =
  let si_terms =
    match Map.Poly.find term_map si with
    | Some si_terms -> si_terms
    | None -> Set.Poly.empty
  in
  let si_terms =
    if closed_dummy_only && not (closed_dummy_sort si) then si_terms
    else Set.add si_terms (Term.mk_dummy si (*ToDo*), [])
  in
  if Term.is_int_sort si then Set.add si_terms (T_int.one () (*ToDo*), [])
  else si_terms

(* The index and element sorts of each curried position of an array sort,
   outermost first: [a -> b -> bool] gives [[(a, b -> bool); (b, bool)]]. *)
let rec curried_positions = function
  | T_array.SArray (si, se) -> (si, se) :: curried_positions se
  | _ -> []

(* Leaf reads of a curried array.  For [x : S1 -> ... -> Sk -> L] with [k >= 2]
   and [L] either [bool] or [int], every [x[t1]...[tk]] with each [ti] taken
   from [index_terms] of [Si], filed under [L] only: the intermediate arrays
   are not added.  One step of the term map thereby reaches the leaf, where the
   ordinary update reaches one index level per step, so at depth 1 a curried
   argument had no read of its value at all.  Nothing is added when the number
   of reads, the array terms times the product of the index-term sets, exceeds
   [limit]; the product grows as the k-th power of the index sets. *)
let add_curried_leaf_reads ~limit sort terms term_map =
  let positions = curried_positions sort in
  match List.last positions with
  | Some (_, leaf)
    when List.length positions >= 2
         && (Term.is_bool_sort leaf || Term.is_int_sort leaf) ->
      let idx =
        List.map positions ~f:(fun (si, se) ->
            (si, se, index_terms ~closed_dummy_only:true term_map si))
      in
      let size =
        List.fold idx ~init:(Set.length terms) ~f:(fun n (_, _, ts) ->
            if n > limit then n else n * Set.length ts)
      in
      if size > limit || size = 0 then term_map
      else
        let reads =
          List.fold idx ~init:terms ~f:(fun acc (si, se, si_terms) ->
              Set.fold acc ~init:Set.Poly.empty ~f:(fun ret (t, conds) ->
                  Set.fold si_terms ~init:ret ~f:(fun ret (i, conds1) ->
                      Set.add ret (T_array.mk_select si se t i, conds @ conds1))))
        in
        Map.Poly.update term_map leaf ~f:(function
          | Some ts -> Set.union ts reads
          | None -> reads)
  | _ -> term_map

(* One step of the qualifier term map for the array terms [terms] of [sort]:
   one [select] level (filed under the element sort) and one [store] level.
   [curried_leaf_reads] (a limit, off when [None]) additionally reads a
   curried array to its leaf in the same step ([add_curried_leaf_reads]) and
   takes no default instance of a sort-variable or arrow index sort. *)
let update_term_map ?(depth = 0) ?curried_leaf_reads sort
    (terms : (Term.t * Formula.t list) Set.Poly.t)
    (term_map : (Sort.t, (Term.t * Formula.t list) Set.Poly.t) Map.Poly.t) =
  if depth = 0 || Set.length terms > 1000 then term_map
  else
    match sort with
    | T_array.SArray (si, se) ->
        let si_terms =
          index_terms
            ~closed_dummy_only:(Option.is_some curried_leaf_reads)
            term_map si
        in
        let se_terms =
          match Map.Poly.find term_map se with
          | Some se_terms -> se_terms
          | None -> Set.Poly.empty
        in
        let store_terms =
          Set.union terms
          @@ Set.fold terms ~init:Set.Poly.empty ~f:(fun ret (t, conds) ->
                 Set.fold si_terms ~init:ret ~f:(fun ret (si_term, conds1) ->
                     Set.fold se_terms ~init:ret
                       ~f:(fun ret (se_term, conds2) ->
                         Set.add ret
                           ( T_array.mk_store si se t si_term se_term,
                             conds @ conds1 @ conds2 ))))
        in
        let select_terms =
          Set.union se_terms
          @@ Set.fold terms ~init:Set.Poly.empty ~f:(fun ret (t, conds) ->
                 Set.union ret
                 @@ Set.Poly.map si_terms ~f:(fun (si_term, conds1) ->
                        (T_array.mk_select si se t si_term, conds @ conds1)))
        in
        if false then
          print_endline
          @@ sprintf "#store_terms: %d, #select_terms: %d"
               (Set.length store_terms) (Set.length store_terms);
        let term_map =
          Map.Poly.set ~key:se ~data:select_terms
          @@ Map.Poly.set ~key:sort ~data:store_terms term_map
        in
        (match curried_leaf_reads with
        | None -> term_map
        | Some limit -> add_curried_leaf_reads ~limit sort terms term_map)
    | _ -> term_map

let qualifiers_of sort (terms : (Term.t * Formula.t list) Set.Poly.t) =
  if false then (
    print_endline @@ sprintf "terms: %d" (Set.length terms);
    Set.iter terms ~f:(fun t -> print_endline @@ Term.str_of @@ fst t));
  if false then
    assert (
      T_array.is_sarray sort
      && Set.for_all terms ~f:(fst >> Term.sort_of >> Stdlib.( = ) sort));
  match sort with
  | T_array.SArray _ ->
      Set.Poly.of_list @@ Formula.eqs @@ Set.to_list
      @@ Set.Poly.filter_map terms ~f:(fun (t, _) ->
             if Term.is_var t (*ToDo*) then Some t else None)
  | _ -> Set.Poly.empty
