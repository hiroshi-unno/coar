(* Qualifier propagation between unknowns along the clauses: a qualifier of one
   unknown, written over its parameters [x1 ... xn], is offered to another
   unknown applied in the same clause to some of the same arguments, renamed
   onto the positions where those arguments occur there.

   Inputs.  A [pair] is [(p1, p2, sub, ids1, ids2)]: in some clause [p1] and
   [p2] are applied to argument lists that share arguments; [ids2] are the
   positions of [p2] holding a shared argument, [ids1] the positions of [p1]
   holding one, and [sub] maps the name [x(i+1)] of each position [i] in
   [ids2] to the names of every position of [p1] holding the same argument
   (more than one where [p1] takes that argument twice).  A qualifier is
   [(ids, phi)]: [phi] over the names [x(i+1)], [ids] the positions it is
   allowed to need.

   What [fixpoint] computes.  The least map [Q] above the input such that,
   for every pair and every [(ids, phi)] in [Q p2] with [ids] non-empty and
   contained in [ids2] (and every cell column [phi] mentions belonging to a
   renamed parameter), [Q p1] holds [(ids1, phi')] for every [phi'] obtained
   by renaming each position of [p2] to one of the positions [sub] gives it.
   It is computed semi-naively: each round sends along every pair only the
   qualifiers its source gained in the round before, so a qualifier crosses
   a pair once.

   [fast] changes how the rounds are computed, not what they compute: every
   qualifier a pair produces carries the pair's own [ids1], so the renaming
   back from the temporary names depends on the pair alone and is built once
   per pair rather than once per produced qualifier (whose cost grew with
   [ids1], up to a hundred positions for a skolem witness over a large
   clause), and a pair's new qualifiers are found by membership in the
   target's sets rather than by forming their union per pair.  The results
   are equal. *)

open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open PCSatCommon

type qual = int Set.Poly.t * Formula.t

type pair =
  Ident.pvar
  * Ident.pvar
  * (Ident.tvar, Ident.tvar Set.Poly.t) Map.Poly.t
  * int Set.Poly.t
  * int Set.Poly.t

let x_i i = Ident.Tvar (sprintf "x%d" (i + 1))
let header = "###_"

(* The qualifiers [pair] produces from [quals], the source's new ones. *)
let images ~fast ((_, _, sub, ids1_set, ids2_set) : pair)
    (quals : qual Set.Poly.t) : qual Set.Poly.t =
  let sub =
    Map.Poly.map sub
      ~f:(Set.Poly.map ~f:(fun (Ident.Tvar s) -> Ident.Tvar (header ^ s)))
  in
  let qs =
    let sub1, sub2 =
      Map.Poly.partition_map sub ~f:(function xs ->
          if Set.is_singleton xs then First (Set.choose_exn xs) else Second xs)
    in
    (* a cell column belongs to a parameter, so it travels with that
       parameter's renaming; one whose parameter this pair does not rename
       would arrive naming a position that need not be an array at the other
       predicate *)
    let sub1 = CellQual.extend_renaming sub1 in
    Set.concat_map quals ~f:(fun (ids, qual) ->
        if
          Fn.non Set.is_empty ids
          && Set.is_subset ids ~of_:ids2_set
          && CellQual.renaming_covers sub1 qual
        then
          let init = Set.Poly.singleton @@ Formula.rename sub1 qual in
          Set.Poly.map ~f:(fun q -> (ids1_set, q))
          @@ Map.Poly.fold sub2 ~init ~f:(fun ~key ~data acc ->
              if Set.exists ids ~f:(x_i >> Ident.tvar_equal key) then
                Set.concat_map data ~f:(fun x ->
                    let ren = Map.Poly.singleton key x in
                    Set.Poly.map acc ~f:(Formula.rename ren))
              else acc)
        else Set.Poly.empty)
  in
  let ren_of ids =
    Map.of_set_exn
    @@ Set.Poly.map ids ~f:(fun i ->
        let xi = x_i i in
        (Ident.Tvar (header ^ Ident.name_of_tvar xi), xi))
  in
  if fast then
    (* every element of [qs] carries [ids1_set] *)
    let ren = lazy (ren_of ids1_set) in
    Set.Poly.map qs ~f:(fun (ids, q) ->
        (ids, Formula.rename (Lazy.force ren) q))
  else
    Set.Poly.map qs ~f:(fun (ids, q) ->
        let ren = ren_of ids in
        (ids, Formula.rename ren q))

(* the census behind [COAR_PROPAGATE_CENSUS]: per round, the pairs visited,
   the qualifiers produced and how many were new *)
let census = lazy (Option.is_some (Sys.getenv "COAR_PROPAGATE_CENSUS"))

let fixpoint ?(print = fun (_ : string lazy_t) -> ()) ~fast
    (pairs : pair Set.Poly.t)
    (quals_map : (Ident.pvar, qual Set.Poly.t) Map.Poly.t) =
  let census = Lazy.force census in
  let round = ref 0 in
  let rec inner quals_map =
    incr round;
    let t_round = Common.Clock.now_s () in
    let visited = ref 0 and generated = ref 0 and fresh_total = ref 0 in
    let quals_map' =
      let count = ref 0 in
      Set.fold pairs ~init:quals_map
        ~f:(fun acc ((pvar1, pvar2, _, _, _) as pair) ->
          count := !count + 1;
          match Map.Poly.find acc pvar2 with
          | None -> acc
          | Some (_, _, quals) ->
              if Set.is_empty quals then acc
              else (
                print
                @@ lazy
                     (sprintf "propagating %d qualifiers from %s to %s (%d/%d)"
                        (Set.length quals) (Ident.name_of_pvar pvar2)
                        (Ident.name_of_pvar pvar1) !count (Set.length pairs));
                let qs = images ~fast pair quals in
                if census then (
                  incr visited;
                  generated := !generated + Set.length qs);
                Map.Poly.update acc pvar1 ~f:(function
                  | None ->
                      if census then fresh_total := !fresh_total + Set.length qs;
                      (qs, Set.Poly.empty, Set.Poly.empty)
                  | Some (added, processed, work) ->
                      let fresh =
                        if fast then
                          Set.filter qs ~f:(fun q ->
                              not (Set.mem processed q || Set.mem work q))
                        else Set.diff qs (Set.union processed work)
                      in
                      if census then (
                        let before = Set.length added in
                        let added' = Set.union added fresh in
                        fresh_total := !fresh_total + Set.length added' - before;
                        (added', processed, work))
                      else (Set.union added fresh, processed, work))))
    in
    if census then
      eprintf
        "[propagate-census] round=%d visited=%d generated=%d new=%d known=%d \
         secs=%.3f\n\
         %!"
        !round !visited !generated !fresh_total
        (Map.Poly.fold quals_map' ~init:0 ~f:(fun ~key:_ ~data:(_, p, w) n ->
             n + Set.length p + Set.length w))
        (Common.Clock.now_s () -. t_round);
    if Map.Poly.for_all quals_map' ~f:(fst3 >> Set.is_empty) then
      Map.Poly.map quals_map' ~f:(fun (_, processed, work) ->
          Set.union processed work)
    else
      inner
      @@ Map.Poly.map quals_map' ~f:(fun (added, processed, work) ->
          (Set.Poly.empty, Set.union processed work, added))
  in
  if census then
    eprintf "[propagate-census] pairs=%d unknowns_with_quals=%d quals=%d\n%!"
      (Set.length pairs)
      (Map.Poly.length quals_map)
      (Map.Poly.fold quals_map ~init:0 ~f:(fun ~key:_ ~data acc ->
           acc + Set.length data));
  inner
  @@ Map.Poly.map quals_map ~f:(fun quals ->
      (Set.Poly.empty (*added*), Set.Poly.empty (*processed*), quals (*work*)))
