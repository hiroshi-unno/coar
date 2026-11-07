(* The invariants a solution of the direct LLVM translation's loop-head
   predicates gives the C program, as S-expressions over C variables, one
   line per loop head, for the witness composer to map back to the input
   program and print as C.

   A predicate's solution holds of every state reachable at its loop head, in
   terms of the predicate's parameters.  It is cut into its top-level
   conjuncts, and each conjunct is kept or dropped on its own: dropping a
   conjunct only weakens the invariant, so what is kept still holds of every
   reachable state.  A conjunct is dropped when it mentions a parameter that
   holds no C variable (Cmap), or anything outside linear integer arithmetic
   with comparisons and the Boolean connectives (division and remainder,
   which C rounds differently, conditional terms, quantifiers, arrays,
   Booleans held as values).

   In Int mode a C value v of a type of width N is held by any integer
   congruent to v modulo 2^N in [-2^(N-1), 2^N): a signed v also by v + 2^N
   when v < 0, an unsigned v also by v - 2^N when v >= 2^(N-1).  So a conjunct
   phi(x) of the holders becomes the disjunction, over the ways each of its k
   variables can be held, of phi at those holders, each disjunct guarded by
   the condition under which that holder exists: true of every C state whose
   holders satisfy phi.  That is 2^k disjuncts, so a conjunct of more than
   [max_vars] variables is dropped, as is one over a 64-bit variable, whose
   second holder a C [long long] cannot hold.  Done per conjunct, not over
   the whole formula, which would multiply the disjuncts of every conjunct.
   Under the mathematical reading the holders stay in that range only while
   no value leaves its C type's range, which is the assumption the verdict
   is already given under.  In Bv mode nothing is written yet: how a
   bit-vector solution reads as C is not decided.

   A transition of a termination loop head (Certificate) is written the same
   way, over the C variables and their values at an earlier visit, (prev X):
   dropping a conjunct keeps the relation true of every pair of visits and
   transitive, though it may no longer be well founded, in which case a
   validator does not confirm it.  A path of a NO gives one state line per
   visit of a loop head, in the order of the path: each C variable the
   loop head's parameters hold, equal to its value, the holder's value read
   back as the C type's (Int mode). *)

open Ast
open Ast.LogicOld

type sexp = Atom of string | List of sexp list

let rec string_of_sexp = function
  | Atom s -> s
  | List l -> "(" ^ String.concat " " (List.map string_of_sexp l) ^ ")"

let quote s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (fun c ->
      if c = '"' || c = '\\' then Buffer.add_char b '\\';
      Buffer.add_char b (if c = '\n' then ' ' else c))
    s;
  Buffer.add_char b '"';
  Buffer.contents b

exception Skip of string

let skip fmt = Printf.ksprintf (fun s -> raise (Skip s)) fmt
let max_vars = 6
let num z = if Z.sign z < 0 then List [ Atom "-"; Atom (Z.to_string (Z.neg z)) ] else Atom (Z.to_string z)

(* [binary op f a b] is [(op f(a) f(b))] with [f a] evaluated first, so that
   the variables are met in the order they are written. *)
let binary op f a b =
  let a = f a in
  let b = f b in
  List [ Atom op; a; b ]

(* [holder x] is the S-expression a parameter [x] stands for; it raises
   [Skip] for a parameter that holds no C variable. *)
let rec term holder (t : Term.t) =
  match t with
  | Term.Var (Ident.Tvar x, sort, _) ->
      if Stdlib.( <> ) sort T_int.SInt then skip "%s is not an integer" x;
      holder x
  | Term.FunApp (T_int.Int z, [], _) -> num z
  | Term.FunApp (T_int.Add, [ a; b ], _) -> binary "+" (term holder) a b
  | Term.FunApp (T_int.Sub, [ a; b ], _) -> binary "-" (term holder) a b
  | Term.FunApp (T_int.Mul, [ a; b ], _) -> binary "*" (term holder) a b
  | Term.FunApp (T_int.Neg, [ a ], _) -> List [ Atom "-"; term holder a ]
  | _ -> skip "a term outside linear integer arithmetic"

let rec formula holder (phi : Formula.t) =
  match phi with
  | Formula.Atom (Atom.True _, _) -> Atom "true"
  | Formula.Atom (Atom.False _, _) -> Atom "false"
  | Formula.Atom (Atom.App (Predicate.Psym sym, [ a; b ], _), _) ->
      let op =
        match sym with
        | T_bool.Eq -> "="
        | T_bool.Neq -> "distinct"
        | T_int.Leq -> "<="
        | T_int.Geq -> ">="
        | T_int.Lt -> "<"
        | T_int.Gt -> ">"
        | _ -> skip "a predicate outside integer comparisons"
      in
      binary op (term holder) a b
  | Formula.UnaryOp (Formula.Not, f, _) -> List [ Atom "not"; formula holder f ]
  | Formula.BinaryOp (Formula.And, a, b, _) -> binary "and" (formula holder) a b
  | Formula.BinaryOp (Formula.Or, a, b, _) -> binary "or" (formula holder) a b
  | Formula.BinaryOp (Formula.Imply, a, b, _) ->
      let a = formula holder a in
      let b = formula holder b in
      List [ Atom "or"; List [ Atom "not"; a ]; b ]
  | Formula.BinaryOp (Formula.Iff, a, b, _) ->
      let a = formula holder a in
      let b = formula holder b in
      List [ Atom "and"; List [ Atom "or"; List [ Atom "not"; a ]; b ]; List [ Atom "or"; a; List [ Atom "not"; b ] ] ]
  | _ -> skip "a quantifier, a let or a connective outside and, or, not, =>, <=>"

let rec conjuncts (phi : Formula.t) =
  match phi with Formula.BinaryOp (Formula.And, a, b, _) -> conjuncts a @ conjuncts b | _ -> [ phi ]

(* The parameters [phi] mentions, each once, in order of first mention. *)
let mentioned (phi : Formula.t) =
  let seen = ref [] in
  (try ignore (formula (fun x -> if not (List.mem x !seen) then seen := x :: !seen; Atom x) phi) with Skip _ -> ());
  List.rev !seen

(* One conjunct of the solution, over C variables, weakened for the two
   holders of a C value (Int mode).  [params] gives each parameter the C
   variable it holds and how the line refers to that variable's value: its
   name, or (prev NAME) for its value at an earlier visit. *)
let conjunct (params : (string * (Cmap.var * sexp)) list) phi =
  let xs = mentioned phi in
  let vars =
    List.map
      (fun x ->
        match List.assoc_opt x params with
        | Some v -> (x, v)
        | None -> skip "%s holds no C variable" x)
      xs
  in
  ignore (formula (fun x -> Atom x) phi);
  if List.length vars > max_vars then skip "more than %d variables" max_vars;
  List.iter (fun (_, ((v : Cmap.var), _)) -> if v.ctype.width >= 64 then skip "%s is a 64-bit variable" v.name) vars;
  let k = List.length vars in
  let disjunct mask =
    let holders, guards =
      List.split
        (List.mapi
           (fun i (x, ((v : Cmap.var), c)) ->
             if mask land (1 lsl i) = 0 then ((x, c), [])
             else
               let n = v.ctype.width in
               let full = Z.shift_left Z.one n and half = Z.shift_left Z.one (n - 1) in
               if v.ctype.signed then ((x, List [ Atom "+"; c; num full ]), [ List [ Atom "<"; c; num Z.zero ] ])
               else ((x, List [ Atom "-"; c; num full ]), [ List [ Atom ">="; c; num half ] ]))
           vars)
    in
    let body = formula (fun x -> List.assoc x holders) phi in
    match List.concat guards with [] -> body | gs -> List ((Atom "and" :: gs) @ [ body ])
  in
  let vars = List.map (fun (x, (v, _)) -> (x, v)) vars in
  match List.init (1 lsl k) disjunct with [ d ] -> (d, vars) | ds -> (List (Atom "or" :: ds), vars)

type line =
  | Invariant of { point : Cmap.point; vars : Cmap.var list; expr : sexp; dropped : string list }
  | Transition of { point : Cmap.point; vars : Cmap.var list; expr : sexp; dropped : string list }
  | State of { point : Cmap.point; vars : Cmap.var list; expr : sexp }
  | Skipped of { point : Cmap.point; reason : string }

let current (point : Cmap.point) = List.map (fun (x, (v : Cmap.var)) -> (x, (v, Atom v.name))) point.params

let earlier (point : Cmap.point) =
  List.map (fun (x, (v : Cmap.var)) -> (Certificate.prev_name x, (v, List [ Atom "prev"; Atom v.name ]))) point.params

(* The line for one loop head, from a formula over [params] (the
   predicate's parameters under the names the translation gave them, with
   the C value each stands for), built by [make] from what is kept. *)
let of_formula make (mode : Cmap.mode) (point : Cmap.point) params phi =
  match (mode, point.loc) with
  | Bv, _ -> Skipped { point; reason = "a bit-vector solution" }
  | _, None -> Skipped { point; reason = "the IR gives no loop location" }
  | Int, Some _ ->
      let kept, dropped =
        List.fold_left
          (fun (kept, dropped) c ->
            match conjunct params c with
            | e -> (e :: kept, dropped)
            | exception Skip reason -> (kept, reason :: dropped))
          ([], []) (conjuncts phi)
      in
      let kept = List.rev kept and dropped = List.rev dropped in
      if kept = [] then
        Skipped
          {
            point;
            reason =
              (match dropped with
              | [] -> "no conjunct"
              | r :: _ -> "no conjunct can be written over C variables: " ^ r);
          }
      else
        let vars =
          List.fold_left
            (fun acc (_, vs) -> List.fold_left (fun acc (_, v) -> if List.memq v acc then acc else v :: acc) acc vs)
            [] kept
          |> List.rev
        in
        let expr = match List.map fst kept with [ e ] -> e | es -> List (Atom "and" :: es) in
        make ~vars ~expr ~dropped

(* The invariant line of one loop head, from its predicate's solution. *)
let of_solution mode point phi =
  of_formula (fun ~vars ~expr ~dropped -> Invariant { point; vars; expr; dropped }) mode point (current point) phi

(* The transition line of one termination loop head, from its predicate's
   transition: a formula over its parameters and their earlier copies. *)
let of_transition mode point phi =
  of_formula
    (fun ~vars ~expr ~dropped -> Transition { point; vars; expr; dropped })
    mode point
    (current point @ earlier point)
    phi

(* The value [z] a holder of the C type [t] has, read back as that type's
   value, when the holder lies in [-2^(N-1), 2^N) (Int mode). *)
let c_value (t : Cmap.ctype) z =
  let full = Z.shift_left Z.one t.width and half = Z.shift_left Z.one (t.width - 1) in
  let v = if t.signed && Z.geq z half then Z.sub z full else if (not t.signed) && Z.sign z < 0 then Z.add z full else z in
  let lo, hi = if t.signed then (Z.neg half, Z.pred half) else (Z.zero, Z.pred full) in
  if Z.geq v lo && Z.leq v hi then Some v else None

(* The state line of one visit of a loop head on a NO's path, from its
   parameters' values; [None] when no value is that of a C variable. *)
let of_state (mode : Cmap.mode) (point : Cmap.point) (args : (Ident.tvar * Term.t) list) =
  match (mode, point.loc) with
  | Bv, _ | _, None -> None
  | Int, Some _ -> (
      let eqs =
        List.filter_map
          (fun (Ident.Tvar x, value) ->
            match (List.assoc_opt x point.params, value) with
            | Some (v : Cmap.var), Term.FunApp (T_int.Int z, [], _) when v.ctype.width < 64 ->
                Option.map (fun c -> (v, List [ Atom "="; Atom v.name; num c ])) (c_value v.ctype z)
            | _ -> None)
          args
      in
      match eqs with
      | [] -> None
      | _ ->
          let vars = List.map fst eqs in
          let expr = match List.map snd eqs with [ e ] -> e | es -> List (Atom "and" :: es) in
          Some (State { point; vars; expr }))

let string_of_ctype (t : Cmap.ctype) = Printf.sprintf "%s %d" (if t.signed then "signed" else "unsigned") t.width

let string_of_line line =
  let loc (p : Cmap.point) =
    (match p.loc with Some (l, c) -> Printf.sprintf "(loc %d %d) " l c | None -> "")
    ^ Printf.sprintf "(function %s)" (quote p.func)
  in
  let vars vs =
    String.concat ""
      (List.map
         (fun (v : Cmap.var) ->
           Printf.sprintf " (%s %s%s)" v.name (string_of_ctype v.ctype) (if v.global then " global" else ""))
         vs)
  in
  match line with
  | Invariant { point; vars = vs; expr; _ } ->
      Printf.sprintf "(invariant %s (vars%s) %s)" (loc point) (vars vs) (string_of_sexp expr)
  | Transition { point; vars = vs; expr; _ } ->
      Printf.sprintf "(transition %s (vars%s) %s)" (loc point) (vars vs) (string_of_sexp expr)
  | State { point; vars = vs; expr } -> Printf.sprintf "(state %s (vars%s) %s)" (loc point) (vars vs) (string_of_sexp expr)
  | Skipped { point; reason } -> Printf.sprintf "(skipped %s %s)" (loc point) (quote reason)

(* The lines for every loop head of [map], from [solution]: a predicate's
   name -> its solution, over its parameters as the translation named them.
   A loop head whose predicate the solution lacks gets a [Skipped] line. *)
let lines (map : Cmap.t) (solution : string -> Formula.t option) =
  List.map
    (fun (point : Cmap.point) ->
      match solution point.pred with
      | Some sol -> of_solution map.mode point sol
      | None -> Skipped { point; reason = "the solution has no " ^ point.pred })
    map.points

(* The lines a certificate gives the loop heads of [map].  For a YES, per
   loop head, its invariant line, its transition line, or both, and a
   [Skipped] line when the certificate has neither; for a NO, one state line
   per visit of a loop head on the path, in the path's order. *)
let lines_of_certificate (map : Cmap.t) (cert : Certificate.t) =
  let find m (point : Cmap.point) = Core.Map.Poly.find m (Ident.Pvar point.pred) in
  match cert with
  | Holds { invariants; transitions } ->
      List.concat_map
        (fun (point : Cmap.point) ->
          match (find invariants point, find transitions point) with
          | None, None -> [ Skipped { point; reason = "the solution has no " ^ point.pred } ]
          | inv, tr ->
              Option.to_list (Option.map (of_solution map.mode point) inv)
              @ Option.to_list (Option.map (of_transition map.mode point) tr))
        map.points
  | Fails { path; _ } ->
      List.filter_map
        (fun ({ pred = Ident.Pvar name; args; _ } : Certificate.step) ->
          match List.find_opt (fun (p : Cmap.point) -> String.equal p.pred name) map.points with
          | Some point -> of_state map.mode point args
          | None -> None)
        path
  | Cycles _ ->
      (* a non-termination witness needs a cycle segment, which these lines
         cannot say; no line is better than a state line read as a safety
         path's *)
      []

(* What follows the verdict line when the direct frontend built [map]: after
   a verdict whose backend returned its certificate, the certificate's lines
   on standard output, flushed.  Nothing otherwise, which a witness reads as
   no invariant or no path.  Shaped as the [after_verdict] of
   [Solver.solve_muclp_lts]. *)
let after_verdict (map : Cmap.t) (_ : Common.Verdict.t) (cert : Certificate.t option) =
  match cert with
  | Some cert ->
      List.iter (fun line -> print_endline (string_of_line line)) (lines_of_certificate map cert);
      flush stdout
  | None -> ()
