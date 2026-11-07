open Core
open Common.Ext
open Common.Combinator
open Automata

(** Regular tree expressions *)

type ('sym, 'lab) t =
  | Nil
  | Symbol of 'sym
  | Label of 'lab * ('sym, 'lab) t
  | Concat of ('sym, 'lab) t * ('sym, 'lab) t
  | Alter of ('sym, 'lab) t * ('sym, 'lab) t
  | Kleene of ('sym, 'lab) t
  | Option of ('sym, 'lab) t

(** [canonize t] flattens the top-level alternatives of [t] (the [Alter]
    nodes reachable without entering any other constructor) into one sorted,
    duplicate-free list and rebuilds a left-nested [Alter] from it.  It
    denotes the same tree language as [t], and two expressions that differ
    only in the order, nesting or repetition of their top-level alternatives
    canonize to the same value.  Each element of the list is the matched
    subterm itself, not [t]. *)
let canonize t =
  let rec aux = function
    | (Nil | Symbol _ | Label (_, _) | Concat (_, _) | Kleene _ | Option _) as
      t' ->
        [ t' ]
    | Alter (t1, t2) ->
        let x = aux t1 @ aux t2 in
        let x' = List.dedup_keep_last x in
        (*let _ = assert (x = x') in*)
        x'
  in
  match List.sort ~compare:Stdlib.compare @@ aux t with
  | [] -> failwith "canonize"
  | [ x ] -> x
  | x :: xs -> List.fold_left ~init:x xs ~f:(fun x y -> Alter (x, y))

let rec pr ppf = function
  | Nil -> Format.fprintf ppf "()"
  | Symbol id -> Format.pp_print_string ppf id
  | Label (id, t) -> Format.fprintf ppf "%a[%a]" Format.pp_print_string id pr t
  | Concat (t1, t2) -> Format.fprintf ppf "(%a, %a)" pr t1 pr t2
  | Alter (t1, t2) -> Format.fprintf ppf "(%a | %a)" pr t1 pr t2
  | Kleene t -> Format.fprintf ppf "%a*" pr t
  | Option t -> Format.fprintf ppf "%a?" pr t

let gen_nt =
  let cnt = ref 0 in
  fun () ->
    cnt := !cnt + 1;
    "%N" ^ string_of_int !cnt

let rec elim_kleene t sub =
  match t with
  | Nil -> (Nil, sub)
  | Symbol id -> (Symbol id, sub)
  | Label (id, t) ->
      let t, sub = elim_kleene t sub in
      (Label (id, t), sub)
  | Concat (t1, t2) ->
      let t1, sub = elim_kleene t1 sub in
      let t2, sub = elim_kleene t2 sub in
      (Concat (t1, t2), sub)
  | Alter (t1, t2) ->
      let t1, sub = elim_kleene t1 sub in
      let t2, sub = elim_kleene t2 sub in
      (Alter (t1, t2), sub)
  | Kleene t -> (
      let t, sub = elim_kleene t sub in
      try (Symbol (List.Assoc.find_exn ~equal:Stdlib.( = ) sub t), sub)
      with Not_found_s _ ->
        let id = gen_nt () in
        (Symbol id, sub @ [ (t, id) ]))
  | Option t ->
      let t, sub = elim_kleene t sub in
      (Option t, sub)

let elim_kleene_env env =
  let sub, env =
    List.fold_left ~init:([], []) env ~f:(fun (sub, env) (id, t) ->
        let t, sub = elim_kleene t sub in
        (sub, env @ [ (id, t) ]))
  in
  env
  @ List.map ~f:(fun (t, id) -> (id, Alter (Concat (t, Symbol id), Nil))) sub

let rec elim_option t sub =
  match t with
  | Nil -> (Nil, sub)
  | Symbol id -> (Symbol id, sub)
  | Label (id, t) ->
      let t, sub = elim_option t sub in
      (Label (id, t), sub)
  | Concat (t1, t2) ->
      let t1, sub = elim_option t1 sub in
      let t2, sub = elim_option t2 sub in
      (Concat (t1, t2), sub)
  | Alter (t1, t2) ->
      let t1, sub = elim_option t1 sub in
      let t2, sub = elim_option t2 sub in
      (Alter (t1, t2), sub)
  | Kleene t ->
      let t, sub = elim_option t sub in
      (Kleene t, sub)
  | Option t -> (
      let t, sub = elim_option t sub in
      try (Symbol (List.Assoc.find_exn ~equal:Stdlib.( = ) sub t), sub)
      with Not_found_s _ ->
        let id = gen_nt () in
        (Symbol id, sub @ [ (t, id) ]))

let elim_option_env env =
  let sub, env =
    List.fold_left ~init:([], []) env ~f:(fun (sub, env) (id, t) ->
        let t, sub = elim_option t sub in
        (sub, env @ [ (id, t) ]))
  in
  env @ List.map sub ~f:(fun (t, id) -> (id, Alter (t, Nil)))

(** [add wl wl' t] names the expression [t]: a symbol names itself; an
    expression already named in the worklist [wl] or in the done list [wl']
    reuses that name; otherwise a fresh name is appended to [wl].  The lookup
    and the stored expression are both the canonical form of [t], so two
    expressions that differ only in the order or repetition of their
    alternatives share one name (and so one automaton state). *)
let add wl wl' t =
  let t = canonize t in
  match t with
  | Symbol id -> (id, wl)
  | _ -> (
      try
        let id, _ = List.find_exn (wl @ wl') ~f:(snd >> Stdlib.( = ) t) in
        (id, wl)
      with Not_found_s _ ->
        let id = gen_nt () in
        (id, wl @ [ (id, t) ]))

let rec to_ta env t wl wl' rho =
  match t with
  | Nil -> (RTA.Leaf, wl, wl')
  | Symbol id ->
      if List.mem ~equal:Stdlib.( = ) rho t then (RTA.Emp, wl, wl')
      else
        to_ta env
          (List.Assoc.find_exn ~equal:Stdlib.( = ) env id)
          wl wl' (t :: rho)
  | Label (id1, t) ->
      let id3, wl = add wl wl' Nil in
      let id2, wl = add wl wl' t in
      (RTA.Label (id1, id2, id3), wl, wl')
  | Concat (Nil, t) -> to_ta env t wl wl' rho
  | Concat (Symbol id, t1) ->
      if List.mem ~equal:Stdlib.( = ) rho t then (RTA.Emp, wl, wl')
      else
        to_ta env
          (Concat (List.Assoc.find_exn ~equal:Stdlib.( = ) env id, t1))
          wl wl' (t :: rho)
  | Concat (Label (id1, t1), t2) ->
      let id3, wl = add wl wl' t2 in
      let id2, wl = add wl wl' t1 in
      (RTA.Label (id1, id2, id3), wl, wl')
  | Concat (Concat (t1, t2), t3) ->
      to_ta env (Concat (t1, Concat (t2, t3))) wl wl' rho
  | Concat (Alter (t1, t2), t3) ->
      let u1, wl, wl' = to_ta env (Concat (t1, t3)) wl wl' rho in
      let u2, wl, wl' = to_ta env (Concat (t2, t3)) wl wl' rho in
      (RTA.Alter (u1, u2), wl, wl')
  (* [tta_of] runs [elim_kleene_env] and [elim_option_env] before this, so a
     [Kleene] or an [Option] left here means the elimination missed a position
     -- these arms used to raise with an empty message, which said nothing *)
  | Concat (Kleene _, _) ->
      failwith "[to_ta] a Kleene star survived elim_kleene_env, under a Concat"
  | Concat (Option _, _) ->
      failwith "[to_ta] an Option survived elim_option_env, under a Concat"
  | Option _ -> failwith "[to_ta] an Option survived elim_option_env"
  | Alter (t1, t2) ->
      let u1, wl, wl' = to_ta env t1 wl wl' rho in
      let u2, wl, wl' = to_ta env t2 wl wl' rho in
      (RTA.Alter (u1, u2), wl, wl')
  | Kleene _t -> failwith "[to_ta] a Kleene star survived elim_kleene_env"

let rec to_ta_env env wl wl' rs =
  if false then (
    List.iter rs ~f:(fun (id, u) ->
        Format.printf "%s -> %a@," id (RTA.pr_body Format.pp_print_string) u);
    List.iter wl ~f:(fun (id, t) -> Format.printf "%s -> %a@," id pr t);
    Format.printf "@,");
  match wl with
  | [] -> rs
  | (id, t) :: wl ->
      let u, wl, wl' = to_ta env t wl ((id, t) :: wl') [] in
      to_ta_env env wl wl' (rs @ [ (id, u) ])

(** [tta_of env] is a trivial tree automaton accepting the trees of the type
    the first definition of [env] names, in the binary encoding where a label
    has its content as first child and its following siblings as second, and
    [leaf] ends a sequence.  Requires [env] non-empty, every referenced type
    defined, and each type defined once (the first definition of a name is the
    one used).  The states are [q0], [q1], ... with [q0] the initial state;
    unreachable states are removed, and two states are merged when their
    transitions coincide once the two are identified (repeatedly, to a fixed
    point). *)
let tta_of env =
  let env = elim_kleene_env env in
  let env = elim_option_env env in
  if false then (
    List.iter env ~f:(fun (id, t) -> Format.printf "type %s = %a@," id pr t);
    Format.printf "@,");
  let trs = to_ta_env env env [] [] in
  let trs = List.map trs ~f:(fun (id, u) -> (id, RTA.canonize_body u)) in
  let trs =
    TreeAutomaton.remove_unreachable ~next_ids_body:RTA.next_ids_body
      [ fst @@ List.hd_exn trs ]
      trs
  in
  if false then RTA.pr Format.pp_print_string Format.std_formatter trs;
  let trs = RTA.minimize trs in
  let rn = List.mapi trs ~f:(fun i (id, _) -> (id, "q" ^ string_of_int i)) in
  let trs =
    List.map trs ~f:(fun (id, u) ->
        (List.Assoc.find_exn ~equal:Stdlib.( = ) rn id, RTA.rename_body rn u))
  in
  if false then RTA.pr Format.pp_print_string Format.std_formatter trs;
  RTA.tta_of trs


(* The type names an expression refers to. *)
let rec symbols = function
  | Nil -> []
  | Symbol id -> [ id ]
  | Label (_, t) | Kleene t | Option t -> symbols t
  | Concat (t1, t2) | Alter (t1, t2) -> symbols t1 @ symbols t2

(* [groups env] partitions the definitions of [env] into the classes of the
   symmetric, transitive closure of "one refers to the other", each class in
   definition order and the classes ordered by their first definition. *)
let groups env =
  let names = List.map env ~f:fst in
  let neighbours n =
    let refs =
      Option.value_map ~default:[] ~f:symbols
      @@ List.Assoc.find ~equal:String.equal env n
    in
    let back =
      List.filter_map env ~f:(fun (m, t) ->
          if List.mem (symbols t) n ~equal:String.equal then Some m else None)
    in
    refs @ back
  in
  let rec close seen = function
    | [] -> seen
    | n :: ns ->
        if List.mem seen n ~equal:String.equal then close seen ns
        else close (n :: seen) (neighbours n @ ns)
  in
  List.fold names ~init:[] ~f:(fun gs n ->
      if
        List.exists gs
          ~f:(List.exists ~f:(fun (m, _) -> String.equal m n))
      then gs
      else
        let cls = close [] [ n ] in
        gs @ [ List.filter env ~f:(fun (m, _) -> List.mem cls m ~equal:String.equal) ])

(** [named_tta_of env] is a trivial tree automaton with a state for every type
    [env] defines, in the encoding [tta_of] uses: the state named [T] accepts
    exactly the trees of type [T] (a sequence ended by [leaf]), and the other
    states accept the languages of the sub-expressions the translation needs.
    It requires what [tta_of] requires and, in addition, that every type name
    begins with an upper-case letter.

    The definitions are translated one group at a time, a group being a class
    of definitions connected by references (two schemas written in one
    section, such as a program's input and output types, are two groups): each
    group gives the states [tta_of] gives when started from all its types,
    minimised the same way and listed in the same order (types first, in
    definition order), and the groups' automata are listed one after another.
    So the automaton is the one the original verifier's separate translation
    of each schema produced, state for state; states of different groups are
    never merged, even when their languages coincide.

    Naming contract: a type's state is named by the type's name; every other
    state is named [q<i>], where [i] is its position in the result, so it
    cannot coincide with a type name.  For a single group whose types are all
    reachable from the first, the result is [tta_of]'s with [q0] and the
    other type states renamed to their types.  Minimisation may find two types
    of a group with the same language: the earlier one keeps the state, and
    the later one gets a copy of its transitions under its own name, appended
    at the end, so that every type is still a state. *)
let named_tta_of env =
  let names = List.map env ~f:fst in
  let trs, merges =
    List.unzip
    @@ List.map (groups env) ~f:(fun group ->
           let roots = List.map group ~f:fst in
           let group = elim_kleene_env group in
           let group = elim_option_env group in
           let trs = to_ta_env group group [] [] in
           let trs =
             List.map trs ~f:(fun (id, u) -> (id, RTA.canonize_body u))
           in
           let trs =
             TreeAutomaton.remove_unreachable ~next_ids_body:RTA.next_ids_body
               roots trs
           in
           RTA.minimize_with_merges trs)
  in
  let trs = List.concat trs and merges = List.concat merges in
  let rep id =
    Option.value ~default:id @@ List.Assoc.find ~equal:String.equal merges id
  in
  let rn =
    List.mapi trs ~f:(fun i (id, _) ->
        ( id,
          match List.find names ~f:(fun n -> String.equal (rep n) id) with
          | Some n -> n
          | None -> "q" ^ string_of_int i ))
  in
  let trs =
    List.map trs ~f:(fun (id, u) ->
        (List.Assoc.find_exn ~equal:String.equal rn id, RTA.rename_body rn u))
  in
  let copies =
    List.filter_map names ~f:(fun n ->
        let r = List.Assoc.find_exn ~equal:String.equal rn (rep n) in
        if String.equal r n then None
        else Some (n, List.Assoc.find_exn ~equal:String.equal trs r))
  in
  RTA.tta_of (trs @ copies)
