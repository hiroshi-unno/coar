open Core
open Common.Ext
open Common.Combinator
open LogicOld

let update_term_map ?(depth = 0) sort
    (terms : (Term.t * Formula.t list) Set.Poly.t)
    (term_map : (Sort.t, (Term.t * Formula.t list) Set.Poly.t) Map.Poly.t) =
  if depth = 0 || Set.length terms > 1000 then term_map
  else
    match sort with
    | T_array.SArray (si, se) ->
        let si_terms =
          Set.add
            (match Map.Poly.find term_map si with
            | Some si_terms -> si_terms
            | None -> Set.Poly.empty)
          @@ (Term.mk_dummy si (*ToDo*), [])
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
        Map.Poly.set ~key:se ~data:select_terms
        @@ Map.Poly.set ~key:sort ~data:store_terms term_map
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
