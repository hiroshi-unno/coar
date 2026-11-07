(* Loop-invariant array reads, read once before the loop.

   A program the new Ptr2Arr has transformed keeps every object whose
   address is taken in a region array, so a value the loop never changes,
   such as a bound read through a pointer, is read from the array in every
   iteration.  Proving termination then needs an invariant about the array
   (this cell keeps its value), where the same value in a scalar needs none.
   llvm2kittel's own hoister moved such loads out of the loop; LLVM's licm
   does not when the load is executed on some iterations only, since there
   it would be speculative.

   In the T2 reading an array has no length and select_array has no effect
   and no undefined behaviour, so a read can be moved freely.  For each loop
   (a strongly connected component of the transition graph that has a cycle
   and does not contain the start location), a read
   select_array(A, i) on a transition inside the loop is replaced by a fresh
   variable when no transition inside the loop assigns A or any variable i
   depends on (i is first rewritten in terms of the values at the start of
   its transition, through the assignments made before it on that
   transition, and must not draw a nondet); every transition that enters the
   loop then ends by assigning the variable that read.  Inside the loop the
   variable equals the read: on entry it is the read of the values the loop
   starts from, and no transition inside the loop changes A or i.  Reads on
   transitions that leave the loop are left as they are.  A loop nested in
   another forms one component with it, so a read invariant only in the
   inner loop is not moved. *)

open Lts
module SS = Set.Make (String)

let rec vars_of = function
  | Var x -> SS.singleton x
  | Const _ | Nondet _ -> SS.empty
  | Neg e -> vars_of e
  | Infix (_, a, b) -> SS.union (vars_of a) (vars_of b)
  | Apply (_, _, args) -> List.fold_left (fun s a -> SS.union s (vars_of a)) SS.empty args

let rec has_nondet = function
  | Nondet _ -> true
  | Var _ | Const _ -> false
  | Neg e -> has_nondet e
  | Infix (_, a, b) -> has_nondet a || has_nondet b
  | Apply (_, _, args) -> List.exists has_nondet args

let rec subst env = function
  | Var x as e -> ( match List.assoc_opt x env with Some e' -> e' | None -> e)
  | (Const _ | Nondet _) as e -> e
  | Neg e -> Neg (subst env e)
  | Infix (op, a, b) -> Infix (op, subst env a, subst env b)
  | Apply (f, p, args) -> Apply (f, p, List.map (subst env) args)

let rec cond_map f = function
  | True -> True
  | Compare (op, a, b) -> Compare (op, f a, f b)
  | And (a, b) -> And (cond_map f a, cond_map f b)
  | Or (a, b) -> Or (cond_map f a, cond_map f b)
  | Not c -> Not (cond_map f c)

let rec cond_vars = function
  | True -> SS.empty
  | Compare (_, a, b) -> SS.union (vars_of a) (vars_of b)
  | And (a, b) | Or (a, b) -> SS.union (cond_vars a) (cond_vars b)
  | Not c -> cond_vars c

(* The strongly connected components of the graph whose edges are [edges]
   (Tarjan's algorithm). *)
let components nodes edges =
  let succ = Hashtbl.create 64 in
  List.iter (fun (a, b) -> Hashtbl.add succ a b) edges;
  let index = Hashtbl.create 64 and low = Hashtbl.create 64 in
  let on_stack = Hashtbl.create 64 and stack = ref [] and next = ref 0 in
  let comps = ref [] in
  let rec visit v =
    Hashtbl.replace index v !next;
    Hashtbl.replace low v !next;
    incr next;
    stack := v :: !stack;
    Hashtbl.replace on_stack v ();
    List.iter
      (fun w ->
        if not (Hashtbl.mem index w) then (
          visit w;
          Hashtbl.replace low v (min (Hashtbl.find low v) (Hashtbl.find low w)))
        else if Hashtbl.mem on_stack w then
          Hashtbl.replace low v (min (Hashtbl.find low v) (Hashtbl.find index w)))
      (Hashtbl.find_all succ v);
    if Hashtbl.find low v = Hashtbl.find index v then (
      let rec pop acc =
        match !stack with
        | w :: rest ->
            stack := rest;
            Hashtbl.remove on_stack w;
            if w = v then w :: acc else pop (w :: acc)
        | [] -> acc
      in
      comps := pop [] :: !comps)
  in
  List.iter (fun v -> if not (Hashtbl.mem index v) then visit v) nodes;
  !comps

let run lts =
  let names =
    List.fold_left
      (fun s { commands; _ } ->
        List.fold_left
          (fun s -> function
            | Assign (x, e) -> SS.add x (SS.union s (vars_of e))
            | Assume c -> SS.union s (cond_vars c))
          s commands)
      SS.empty lts.transitions
  in
  let counter = ref 0 in
  let rec fresh () =
    incr counter;
    let x = Printf.sprintf "hoisted%d" !counter in
    if SS.mem x names then fresh () else x
  in
  let nodes =
    List.sort_uniq compare
      (List.concat_map (fun { src; dst; _ } -> [ src; dst ]) lts.transitions)
  in
  let edges = List.map (fun { src; dst; _ } -> (src, dst)) lts.transitions in
  let loops =
    List.filter
      (fun comp ->
        (not (List.mem lts.start comp))
        && (List.length comp > 1
           || List.exists (fun (a, b) -> a = b && List.mem a comp) edges))
      (components nodes edges)
  in
  (* per transition (by position), its rewritten commands and the
     assignments appended to it *)
  let trs = Array.of_list lts.transitions in
  let appended = Array.make (Array.length trs) [] in
  let new_widths = ref [] in
  List.iter
    (fun comp ->
      let inside l = List.mem l comp in
      let internal i = inside trs.(i).src && inside trs.(i).dst in
      let assigned =
        Array.to_list trs
        |> List.mapi (fun i t -> (i, t))
        |> List.filter (fun (i, _) -> internal i)
        |> List.fold_left
             (fun s (_, t) ->
               List.fold_left
                 (fun s -> function Assign (x, _) -> SS.add x s | Assume _ -> s)
                 s t.commands)
             SS.empty
      in
      (* (array, index at the transition's start, printed) -> variable and its read *)
      let hoisted = ref [] in
      let key e =
        let buf = Buffer.create 32 in
        pp_expr buf e;
        Buffer.contents buf
      in
      let rec rewrite env e =
        match e with
        | Apply ("select_array", [], [ Var a; i ]) -> (
            let i = rewrite env i in
            let i0 = subst env i in
            let invariant =
              (not (SS.mem a assigned))
              && (not (has_nondet i0))
              && SS.is_empty (SS.inter (vars_of i0) assigned)
            in
            if not invariant then Apply ("select_array", [], [ Var a; i ])
            else
              let k = (a, key i0) in
              match List.assoc_opt k !hoisted with
              | Some (h, _) -> Var h
              | None ->
                  let h = fresh () in
                  hoisted := !hoisted @ [ (k, (h, Apply ("select_array", [], [ Var a; i0 ]))) ];
                  (match List.assoc_opt a lts.arrays with
                  | Some w when lts.widths <> [] -> new_widths := (h, w) :: !new_widths
                  | _ -> ());
                  Var h)
        | Var _ | Const _ | Nondet _ -> e
        | Neg e -> Neg (rewrite env e)
        | Infix (op, a, b) -> Infix (op, rewrite env a, rewrite env b)
        | Apply (f, p, args) -> Apply (f, p, List.map (rewrite env) args)
      in
      Array.iteri
        (fun i t ->
          if internal i then (
            let env = ref [] in
            let commands =
              List.map
                (function
                  | Assign (x, e) ->
                      let e = rewrite !env e in
                      env := (x, subst !env e) :: List.remove_assoc x !env;
                      Assign (x, e)
                  | Assume c -> Assume (cond_map (rewrite !env) c))
                t.commands
            in
            trs.(i) <- { t with commands }))
        trs;
      if !hoisted <> [] then
        Array.iteri
          (fun i t ->
            if (not (inside t.src)) && inside t.dst then
              appended.(i) <-
                appended.(i) @ List.map (fun (_, (h, read)) -> Assign (h, read)) !hoisted)
          trs)
    loops;
  let transitions =
    Array.to_list (Array.mapi (fun i t -> { t with commands = t.commands @ appended.(i) }) trs)
  in
  { lts with transitions; widths = lts.widths @ List.rev !new_widths }
