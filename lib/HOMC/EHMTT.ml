(* Extended higher-order macro tree transducers: their syntax, a simple type
   discipline separating input trees from output trees, and the pieces of their
   translation into recursion schemes with finite data.  [rsfd_of] compiles
   pattern matching on an input tree into a nondeterministic branch over the
   input automaton's transitions (an unmatched constructor becomes the [fail]
   terminal); [alphaRules] and [beta_rules] build the two copies of the rules
   used to check the whole program and each coercion separately, and
   [eta_expand] gives each rule as many parameters as its sort demands. *)
open Core
open Common.Ext
open Common.Combinator
open Ast
open Automata

type type_t = TVar of type_t option ref | In | Out | Func of type_t * type_t

let rec pr_type_aux b ppf = function
  | TVar { contents = None } -> Format.fprintf ppf "?"
  | TVar { contents = Some typ } -> pr_type_aux b ppf typ
  | In -> Format.fprintf ppf "i"
  | Out -> Format.fprintf ppf "o"
  | Func (typ1, typ2) ->
      if b then
        Format.fprintf ppf "(%a -> %a)" (pr_type_aux true) typ1
          (pr_type_aux false) typ2
      else
        Format.fprintf ppf "%a -> %a" (pr_type_aux true) typ1 (pr_type_aux b)
          typ2

let pr_type = pr_type_aux false

let rec order_of_type = function
  | TVar { contents = None } -> 0
  | TVar { contents = Some typ } -> order_of_type typ
  | In | Out -> 0
  | Func (t1, t2) -> max (order_of_type t1 + 1) (order_of_type t2)

type term =
  | Fd of int
  | Nonterm of Ident.tvar
  | Var of Ident.tvar * type_t ref
  | Term of Ident.tvar
  | App of term * term
  | Case of Ident.tvar * (Ident.tvar * (Ident.tvar list * term)) list
  | Coerce of Ident.tvar * term * int
  | Copy of term
  | Tree of Ident.tvar
  | VarOrTerm of Ident.tvar

let mk_var x = Var (x, ref (TVar { contents = None }) (*ToDo*))

type rule = Ident.tvar * (Ident.tvar list * term)
type t = rule list

let assoc id rs =
  match List.Assoc.find ~equal:String.equal rs id with
  | Some r -> r
  | None -> failwith ("non-terminal " ^ id ^ " not found")

let reachable id rs =
  let next_nts (_, t) =
    let rec next_nts' = function
      | Fd _n -> []
      | Nonterm id -> [ Ident.name_of_tvar id ]
      | Var _ | Term _ -> []
      | App (t1, t2) -> next_nts' t1 @ next_nts' t2
      | Case (_, pats) -> List.concat_map ~f:(snd >> snd >> next_nts') pats
      | Coerce (_, t, _) -> next_nts' t
      | Tree _ -> []
      | Copy t -> next_nts' t
      | VarOrTerm _ -> failwith "EHMTT.reachable"
    in
    next_nts' t
  in
  List.map ~f:(fun id -> (id, assoc id rs))
  @@ List.reachable [ id ] (fun id -> next_nts (assoc id rs))

let rec coercions = function
  | Fd _n -> []
  | Nonterm _ -> []
  | Var _ -> []
  | Term _ -> []
  | App (t1, t2) -> coercions t1 @ coercions t2
  | Case (_, pats) -> List.concat_map ~f:(snd >> snd >> coercions) pats
  | Coerce (q, t, idx) -> (q, t, idx) :: coercions t
  | Tree _ -> []
  | Copy _ | VarOrTerm _ -> failwith "EHMTT.coercions"

let visit f = function
  | Fd n -> f#fd n
  | Nonterm id -> f#nonterm id
  | Var (id, ty) -> f#var id ty
  | Term id -> f#term id
  | App (t1, t2) -> f#app t1 t2
  | Case (id, pats) -> f#case id pats
  | Coerce (id, t, _) -> f#coerce id t
  | Copy t -> f#copy t
  | Tree id -> f#tree id
  | VarOrTerm id -> f#varorterm id

let rec fold f = function
  | Fd n -> f#fd n
  | Nonterm id -> f#nonterm id
  | Var (id, _) -> f#var id
  | Term id -> f#term id
  | App (t1, t2) -> f#app (fold f t1) (fold f t2)
  | Case (id, pats) ->
      f#case id
        (List.map pats ~f:(fun (id', (ids, t)) -> (id', (ids, fold f t))))
  | Coerce (id, t, idx) -> f#coerce id (fold f t) idx
  | Copy t -> f#copy (fold f t)
  | Tree id -> f#tree id
  | VarOrTerm id -> f#varorterm id

(* let elimVarOrTerm ids t =
   fold
     (object
        method nonterm id = Nonterm id
        method var id = Var id
        method term id = Term id
        method app t1 t2 = App (t1, t2)
        method case id pats = Case (id, buggy !!!pats)
        method coerce id t = Coerce (id, t)
        method copy t = Copy t
        method tree id = Tree id
        method varorterm id = if List.mem id ids then Var id else Term id
     end)
     t
*)

let rec elimVarOrTerm ids = function
  | (Fd _ | Nonterm _ | Var _ | Term _) as t -> t
  | App (t1, t2) -> App (elimVarOrTerm ids t1, elimVarOrTerm ids t2)
  | Case (id, pats) ->
      Case
        ( id,
          List.map pats ~f:(fun (id', (ids', t)) ->
              (id', (ids', elimVarOrTerm (ids @ ids') t))) )
  | Coerce (id, t, idx) -> Coerce (id, elimVarOrTerm ids t, idx)
  | Copy t -> Copy (elimVarOrTerm ids t)
  | Tree _ as t -> t
  | VarOrTerm id ->
      if List.mem ~equal:Ident.tvar_equal ids id then
        Var (id, { contents = TVar { contents = None } })
      else Term id

let trees =
  fold
    (object
       method fd _n = []
       method nonterm _id = []
       method var _id = []
       method term _id = []
       method app t1 t2 = t1 @ t2
       method case _id = List.concat_map ~f:(snd >> snd)
       method coerce id t _ = id :: t
       method copy t = t
       method tree id = [ id ]
       method varorterm _id = failwith "trees"
    end)

let terms =
  fold
    (object
       method fd _n = []
       method nonterm _id = []
       method var _id = []
       method term id = [ id ]
       method app t1 t2 = t1 @ t2
       method case _id = List.concat_map ~f:(fun (id, (_, t)) -> id :: t)
       method coerce _id t _ = t
       method copy t = t
       method tree _id = []
       method varorterm _id = failwith "terms"
    end)

let size =
  fold
    (object
       method fd _n = 1
       method nonterm _ = 1
       method var _ = 1
       method term _ = 1
       method app t1 t2 = t1 + t2

       method case _ pats =
         1 + List.fold_left ~init:0 (List.map ~f:(snd >> snd) pats) ~f:( + )

       method coerce _ t _ = 1 + t
       method copy t = 1 + t
       method tree _id = 1
       method varorterm _id = failwith "size"
    end)

let count_coerce =
  fold
    (object
       method fd _ = 0
       method nonterm _ = 0
       method var _ = 0
       method term _ = 0
       method app t1 t2 = t1 + t2

       method case _ pats =
         List.fold_left ~init:0 (List.map ~f:(snd >> snd) pats) ~f:( + )

       method coerce _ t _ = 1 + t
       method copy t = t
       method tree _id = 0
       method varorterm _id = failwith "count_coerce"
    end)

let size_of_prog (rules : t) =
  List.fold_left ~init:0 ~f:( + ) @@ List.map ~f:(snd >> snd >> size) rules

let terminals (rules : t) =
  List.dedup_keep_last @@ List.concat_map ~f:(snd >> snd >> terms) rules

(* Every spelling in a term, including local binders and global symbols. *)
let rec names_in_term = function
  | Fd _ -> []
  | Nonterm f | Term f | Tree f | VarOrTerm f -> [ f ]
  | Var (x, _) -> [ x ]
  | App (left, right) -> names_in_term left @ names_in_term right
  | Copy body -> names_in_term body
  | Coerce (q, body, _) -> q :: names_in_term body
  | Case (x, patterns) ->
      x
      :: List.concat_map patterns ~f:(fun (a, (xs, body)) ->
          a :: (xs @ names_in_term body))

let rec pr_aux b ppf = function
  | Fd n -> Format.fprintf ppf "%d" n
  | Nonterm id | Term id -> Format.fprintf ppf "%s" (Ident.name_of_tvar id)
  | Var (id, ty) ->
      Format.fprintf ppf "%s:%a" (Ident.name_of_tvar id) pr_type !ty
  | App (t1, t2) ->
      if b then Format.fprintf ppf "(";
      Format.fprintf ppf "%a %a" (pr_aux false) t1 (pr_aux true) t2;
      if b then Format.fprintf ppf ")"
  | Case (id, pats) ->
      if b then Format.fprintf ppf "(";
      let pr_ ppf (id', (ids, t)) =
        Format.fprintf ppf "%s => %a"
          (String.concat_map_list ~sep:" " ~f:Ident.name_of_tvar (id' :: ids))
          (pr_aux false) t
      in
      Format.fprintf ppf "case %s of %a" (Ident.name_of_tvar id)
        (List.pr pr_ " | ") pats;
      if b then Format.fprintf ppf ")"
  | Coerce (id, t, idx) ->
      if b then Format.fprintf ppf "(";
      Format.fprintf ppf "coerce(%d) %s %a" idx (Ident.name_of_tvar id)
        (pr_aux true) t;
      if b then Format.fprintf ppf ")"
  | Copy t ->
      if b then Format.fprintf ppf "(";
      Format.fprintf ppf "copy %a" (pr_aux true) t;
      if b then Format.fprintf ppf ")"
  | Tree id -> Format.fprintf ppf "%s" (Ident.name_of_tvar id)
  | VarOrTerm _ -> failwith "pr_aux"

let pr = pr_aux false

let pr_rules ppf (rules : t) =
  List.iter rules ~f:(fun (id, (ids, t)) ->
      Format.fprintf ppf "%s -> %a.@,"
        (String.concat_map_list ~sep:" " ~f:Ident.name_of_tvar (id :: ids))
        (pr_aux false) t)

let rec fun_and_args = function
  | App (t1, t2) ->
      let t, ts = fun_and_args t1 in
      (t, ts @ [ t2 ])
  | t -> (t, [])

let app t1 t2 = App (t1, t2)
let apps t ts = List.fold_left ~init:t ts ~f:app

(* [flatten_pairs [(x1, y1); (x2, y2); ...]] is [[x1; y1; x2; y2; ...]]:
   the pairs interleaved into one list, not [List.unzip]'s pair of lists. *)
let rec flatten_pairs = function
  | [] -> []
  | (x, y) :: xs -> x :: y :: flatten_pairs xs

(* The names the reduction adds to a program, each chosen by [names_for]
   so that it is none of the program's names and none of them is another,
   except [br]:
   - [br], the terminal of a nondeterministic branch, which every state of
     the output automaton reads into itself on both children.  It is always
     [br], and a program may write it: the input language reserves [br] for
     nondeterministic choice, a [br] node standing for the set of its
     children (a choice resolved where the tree is consumed), and the
     reduction's branches are of the same kind.  This goes beyond the
     formal languages of Kobayashi, Tabuchi and Unno (POPL 2010) and Unno,
     Tabuchi and Kobayashi (APLAS 2010), which add [br] to the alphabet
     only in the reduction, but it is what the programs of the latter's
     experiments write.  An automaton must therefore give [br] no
     transition of its own ([Reducer.rsfds_of_ehmtt] refuses one);
   - [fail], the terminal a case analysis produces for a constructor it has
     no branch for, which no state reads: a program's own terminal [fail]
     may have transitions, and the reduction's failure must stay rejected;
     [fail ^ "_" ^ a] is the variant naming the constructor [a], used when
     [RSFD.verbose_fail] is set;
   - [success], the terminal of a checked leaf of a coercion problem, which
     every state accepts;
   - [arg_check_prefix]: [arg_check_prefix ^ q] labels an argument check
     against state [q] ([arg_check_symbol]);
   - [terminal_prefix]: [terminal_prefix ^ a] is the non-terminal standing
     for the terminal [a] in a coercion problem ([term]);
   - [start], the start non-terminal of every generated problem;
   - [suffix1], [suffix2]: [copy1] and [copy2] append them to a name for
     the two copies of a rule or a parameter.
   A program's own terminal, state, non-terminal or variable spelled like
   one of the others would otherwise be read as the reduction's: a program's
   own [success__] accepted as a checked leaf, two parameters [f] and [f_2]
   of one rule given the same name in the copy. *)
type names = {
  br : Ident.tvar;
  success : Ident.tvar;
  fail : string;
  arg_check_prefix : string;
  terminal_prefix : string;
  start : Ident.tvar;
  suffix1 : string;
  suffix2 : string;
}

(* [names_for taken] chooses the reduction's names given every name the
   program and its automaton use ([taken]: non-terminals, variables,
   terminals, states).  The copies' suffixes are chosen so that no taken
   name ends with either; then a copy ends with its suffix and a taken name
   does not, so copies are fresh, the two copies of one name differ, and a
   name built from taken names without those endings ([terminal_prefix ^ a],
   [start]) is no copy.  The other names are the conventional ones
   ([success__], [fail], [argcheck__], [T_], [RSFDStart], [_1], [_2]) when
   free, and otherwise the first free variant with a number appended; [br]
   is always [br].  Guarantees: [success], [fail] and [start] are not in
   [taken], differ from [br] and from each other; [fail ^ "_" ^ n] is not in
   [taken] for any [n] in [taken]; for every [n] in [taken],
   [arg_check_prefix ^ n] and [terminal_prefix ^ n] are free; neither prefix
   begins [br], [success] or [fail]. *)
let names_for (taken : string list) =
  let taken = String.Set.of_list taken in
  let variant base i = if i = 0 then base else base ^ string_of_int i in
  let rec first ok base i =
    let x = variant base i in
    if ok x then x else first ok base (i + 1)
  in
  let free x = not (Set.mem taken x) in
  let suffix1, suffix2 =
    let ok sep =
      not
        (Set.exists taken ~f:(fun n ->
             String.is_suffix n ~suffix:(sep ^ "1")
             || String.is_suffix n ~suffix:(sep ^ "2")))
    in
    let sep = first ok "_" 0 in
    (sep ^ "1", sep ^ "2")
  in
  (* a name of its own must not end like a copy either *)
  let free x =
    free x
    && (not (String.is_suffix x ~suffix:suffix1))
    && not (String.is_suffix x ~suffix:suffix2)
  in
  let terminals_free prefix =
    Set.for_all taken ~f:(fun n -> free (prefix ^ n))
  in
  let br = "br" in
  let success = first (fun x -> free x && String.(x <> br)) "success__" 0 in
  let fail =
    first
      (fun x ->
        free x
        && String.(x <> br && x <> success)
        && Set.for_all taken ~f:(fun n -> not (Set.mem taken (x ^ "_" ^ n))))
      "fail" 0
  in
  let arg_check_prefix =
    first
      (fun p ->
        terminals_free p
        && not
             (List.exists [ br; success; fail ] ~f:(String.is_prefix ~prefix:p)))
      "argcheck__" 0
  in
  let terminal_prefix =
    first
      (fun p ->
        terminals_free p
        && String.(p <> arg_check_prefix)
        && not
             (List.exists [ br; success; fail ] ~f:(String.is_prefix ~prefix:p)))
      "T_" 0
  in
  let start =
    first
      (fun x ->
        free x
        && (not (String.is_prefix x ~prefix:terminal_prefix))
        && not (String.is_prefix x ~prefix:arg_check_prefix))
      "RSFDStart" 0
  in
  {
    br = Ident.Tvar br;
    success = Ident.Tvar success;
    fail;
    arg_check_prefix;
    terminal_prefix;
    start = Ident.Tvar start;
    suffix1;
    suffix2;
  }

(* Every name a program and its automaton use: its non-terminals, their
   parameters, the variables and terminals of their bodies, the states of
   its coercions and [gen]s, the automaton's states and terminals, and the
   states of the main type [typ]. *)
let names_of_program (rules : t) (trs : TTA.pre_trs) typ =
  let n = Ident.name_of_tvar in
  let term t = List.map (names_in_term t) ~f:n in
  List.concat_map rules ~f:(fun (f, (xs, t)) ->
      (n f :: List.map xs ~f:n) @ term t)
  @ List.concat_map trs ~f:(fun (q, (a, qs)) -> q :: a :: qs)
  @ List.map (RefType.attr_of typ) ~f:n

(* The terminal [arg_check_symbol ~names q] labels a node that the most
   general inhabitants built by [of_type] put around their result: its first
   child is an argument they were given, which must be accepted from state
   [q], and its second child is the result.  [TTA.add_arg_check_transitions]
   gives the output automaton the matching transitions. *)
let arg_check_symbol ~names q =
  Ident.Tvar (names.arg_check_prefix ^ Ident.name_of_tvar q)

(* [of_type ~fresh ~copier typ] is a term that stands for every value of the main
   type's parameter type [typ], with the rules it needs.
   - A base type [q] is the input tree [Tree q], which the input automaton
     reads as any tree it accepts from [q]; no rules.
   - A function type [t1 -> ... -> tn -> q] is a fresh non-terminal [N] (a
     name drawn by [fresh]) with the rule
       [N x1 ... xn -> c1 (... (cn (C (Tree q))))]
     where [C] is the tree copier [copier] and [ci] checks the i-th argument:
     for a base [ti = qi] it is [arg_check_symbol qi (C xi)] applied to the rest, for a function
     [ti] it applies [xi] to [of_type] of each of [ti]'s parameter types and
     checks its result in the same way.  So [N] stands for every function of
     the type: it returns any tree accepted from [q], and records each
     argument it is given as an obligation of the caller, which the output
     automaton checks from the state the type demands.
   Returns the term and the rules of the non-terminals it introduced (those
   of nested function types included), in no particular order.  [C] is
   the tree copier the reduction adds to every program ([make_tree_copier]),
   so the rules belong beside the program's and are to be transformed with
   them.  The [Failure] case cannot arise: [RefType.args_and_ret] always ends
   in a base type. *)
let rec of_type ~names ~fresh ~copier (typ : Ident.tvar RefType.t) :
    term * rule list =
  match RefType.args_and_ret typ with
  | [], RefType.Base rid -> (Tree rid, [])
  | typs, RefType.Base rid ->
      let args =
        List.mapi typs ~f:(fun i typ ->
            (Ident.Tvar ("x" ^ string_of_int i), typ))
      in
      let t, rs =
        List.fold_right args
          ~init:(App (Nonterm copier, Tree rid), [])
          ~f:(fun (aid, typ) (t, rs) ->
            let t', rs' = check_arg ~names ~fresh ~copier aid typ t in
            (t', rs @ rs'))
      in
      let id = fresh () in
      (Nonterm id, (id, (List.map ~f:fst args, t)) :: rs)
  | _ -> failwith "EHMTT.of_type"

(* [check_arg ~fresh x typ t] is [t] with the argument [x] of type [typ]
   checked first, as described at [of_type], and the rules that needs. *)
and check_arg ~names ~fresh ~copier id typ t =
  match RefType.args_and_ret typ with
  | typs, RefType.Base rid ->
      let ts, rss =
        List.unzip @@ List.map ~f:(of_type ~names ~fresh ~copier) typs
      in
      let arg =
        if List.is_empty ts then App (Nonterm copier, Var (id, ref In))
        else apps (Var (id, ref (TVar (ref None)))) ts
      in
      (apps (Term (arg_check_symbol ~names rid)) [ arg; t ], List.concat rss)
  | _ -> failwith "EHMTT.check_arg"

(* [make_tree_copier ~copier terminals] is the rule
     [copier x -> case x of a x1 ... xn => a (copier x1) ... (copier xn) | ...]
   with one branch per terminal [(a, n)] of [terminals]: it turns an input
   tree into the equal output tree, and a node whose terminal is not listed
   into the terminal [fail], as any unmatched case does.  [copier] must be a
   name no rule of the program has: a program's own rule of that name would
   stand for the copier wherever [copy t] or a most general inhabitant
   applies it, and a rule that is not a copier there changes what the
   reduction checks (a constant [Copy x -> e] makes every argument check
   pass). *)
let make_tree_copier ~copier terminals =
  (* The rule's parameter [p] and its pattern variables [p1], [p2], ... are
     spelled like none of the terminals, whose names the bodies apply: one
     scope holds both, so a terminal [x] under a parameter [x] would be
     typed as the parameter and printed as it (the model checkers tell a
     variable from a terminal by the rule's parameter list). *)
  let names = String.Set.of_list (List.map terminals ~f:(fst >> Ident.name_of_tvar)) in
  let arity = List.fold terminals ~init:0 ~f:(fun m (_, n) -> max m n) in
  let rec prefix i =
    let p = if i = 0 then "x" else "x" ^ String.make i 'x' in
    if
      Set.mem names p
      || List.exists (List.range 1 (arity + 1)) ~f:(fun v ->
          Set.mem names (p ^ string_of_int v))
    then prefix (i + 1)
    else p
  in
  let p = prefix 0 in
  let pats =
    List.map terminals ~f:(fun (a, n) ->
        let vs =
          List.init n ~f:(fun v -> Ident.Tvar (p ^ string_of_int (v + 1)))
        in
        let copies =
          List.map vs ~f:(fun v -> App (Nonterm copier, Var (v, ref In)))
        in
        (a, (vs, apps (Term a) copies)))
  in
  (copier, ([ Ident.Tvar p ], Case (Ident.Tvar p, pats)))

(* [expandCopy ~copier rules] replaces every [copy t] by an application of
   the tree copier [copier] ([make_tree_copier]). *)
let expandCopy ~copier (rules : t) =
  let rec f = function
    | (Fd _ | Nonterm _ | Var (_, _) | Term _) as t -> t
    | App (t1, t2) -> App (f t1, f t2)
    | Case (id, pats) ->
        Case (id, List.map pats ~f:(fun (a, (xs, t)) -> (a, (xs, f t))))
    | Coerce (id, t, idx) -> Coerce (id, f t, idx)
    | Copy t -> App (Nonterm copier, f t)
    | Tree _id as t -> t
    | VarOrTerm _id -> failwith "expandCopy"
  in
  List.map ~f:(fun (n, (xs, t)) -> (n, (xs, f t))) rules

let rec subst sub = function
  | (Fd _ | Nonterm _ | Term _) as t -> t
  | Var (id, ty) ->
      let v =
        match List.Assoc.find ~equal:Ident.tvar_equal sub id with
        | Some r -> r
        | None -> id
      in
      Var (v, ty)
  | App (t1, t2) -> App (subst sub t1, subst sub t2)
  | Case (id, pats) ->
      let v =
        match List.Assoc.find ~equal:Ident.tvar_equal sub id with
        | Some r -> r
        | None -> id
      in
      Case
        ( v,
          List.map pats ~f:(fun (a, (xs, t)) ->
              let sub =
                List.filter sub ~f:(fun (x, _) ->
                    not (List.mem ~equal:Ident.tvar_equal xs x))
              in
              (a, (xs, subst sub t))) )
  | Coerce (id, t, idx) -> Coerce (id, subst sub t, idx)
  | Copy t -> Copy (subst sub t)
  | Tree _id as t -> t
  | VarOrTerm _id -> failwith "subst"

let balance = ref true

let nondet_branch br app xs =
  if !balance then
    let rec f xs =
      let partition xs =
        let i = List.length xs / 2 in
        List.split_n xs i
      in
      match xs with
      | [] -> failwith "nondet_branch"
      | [ x ] -> x
      | _ ->
          let ls, rs = partition xs in
          app (app br (f ls)) (f rs)
    in
    f xs
  else
    match List.rev xs with
    | [] -> failwith "nondet_branch"
    | x :: xs ->
        List.fold_right (List.rev xs) ~init:x ~f:(fun x y -> app (app br x) y)

(* [inhabited_states trs] is the set of states of the input automaton [trs]
   that accept some tree, finite or infinite: the greatest set [X] of states
   each with a transition whose children's states are all in [X] (an
   accepting run is then built top-down inside [X], possibly forever).

   Input trees may be infinite.  The input automata are trivial automata,
   Buechi tree automata whose every run is accepting, a tree being accepted
   by a run whose domain is the tree's whole domain (Unno, Tabuchi and
   Kobayashi, "Verification of tree-processing programs via higher-order
   model checking", APLAS 2010, Definition 2), and the verification problem
   quantifies over every tree each input automaton accepts (Definition 3).
   So [qe e -> qe] accepts the infinite tree [e(e(...))], and only a state
   outside [X] stands for no input.  The least set holding the source of
   every transition whose children are in it, the states accepting a
   finite tree, is smaller and would drop the inputs that are only
   infinite, turning a violated property into a satisfied one. *)
let inhabited_states (trs : TTA.pre_trs) =
  let all =
    String.Set.of_list (List.concat_map trs ~f:(fun (q, (_, qs)) -> q :: qs))
  in
  let rec go x =
    let x' =
      Set.filter x ~f:(fun q ->
          List.exists trs ~f:(fun (q', (_, qs)) ->
              String.equal q q' && List.for_all qs ~f:(Set.mem x)))
    in
    if Set.equal x x' then x else go x'
  in
  go all

(* [input_table trs states] is the input automaton [trs] as the reduction
   reads it: every state of [trs] and of [states], each with only its
   transitions whose children are all inhabited ([inhabited_states]), so
   exactly the states accepting no tree, finite or infinite, have no
   transition, and every transition kept is used by the accepting run on
   some input.  A case analysis abstracts an input by the transitions of
   its state, and a transition with an empty child would let it explore a
   branch no input reaches, and refute a satisfied program.  Every state of
   [trs] and of [states] is listed, so a lookup of any of them succeeds. *)
let input_table (trs : TTA.pre_trs) states : TTA.trs =
  let inhabited = inhabited_states trs in
  let table =
    TTA.make
    @@ List.filter trs ~f:(fun (_, (_, qs)) ->
        List.for_all qs ~f:(Set.mem inhabited))
  in
  let listed = String.Set.of_list (List.map table ~f:fst) in
  let missing =
    List.fold (TTA.states trs @ states) ~init:([], listed)
      ~f:(fun (acc, seen) q ->
        if Set.mem seen q then (acc, seen) else ((q, []) :: acc, Set.add seen q))
    |> fst |> List.rev
  in
  table @ missing

(* A case analysis of an input in state [q] is the nondeterministic choice
   among [q]'s transitions in [trs].  When [q] has none, no input is in [q]
   and no run reaches the case: the branch is [names.success], which the
   caller makes every output state accept. *)
let rec rsfd_term_of ~names (trs : TTA.trs) = function
  | Fd n -> RSFD.Fd (Second n)
  | Nonterm id -> RSFD.Nonterm id
  | Var (id, _) -> RSFD.Var id
  | Term id -> RSFD.Term id
  | App (t1, t2) ->
      RSFD.App (rsfd_term_of ~names trs t1, rsfd_term_of ~names trs t2)
  | Case (id1, xs) ->
      let xs' = rsfd_of ~names trs xs in
      Case
        ( id1,
          List.map trs ~f:(fun (_, ys) ->
              if List.is_empty ys then RSFD.Term names.success
              else
                nondet_branch (RSFD.Term names.br) RSFD.app
                  (List.map ys ~f:(fun (id2, ids1) ->
                       match
                         List.Assoc.find xs' (Ident.Tvar id2)
                           ~equal:Ident.tvar_equal
                       with
                       | None -> RSFD.fail ~name:names.fail (Ident.Tvar id2)
                       | Some (ids2, t') ->
                           let sub =
                             List.map2_exn ids1 ids2 ~f:(fun id1 id2 ->
                                 (id2, RSFD.Fd (First (Ident.Tvar id1))))
                           in
                           RSFD.subst sub t'))) )
  | Tree id -> RSFD.Fd (First id)
  | Copy _ | Coerce _ | VarOrTerm _ -> failwith "rsfd_of"

and rsfd_of ~names trs (rules : t) : RSFD.t =
  List.map rules ~f:(fun (id, (ids, t)) ->
      (id, (ids, rsfd_term_of ~names trs t)))

let copy1 ~names x = Ident.Tvar (Ident.name_of_tvar x ^ names.suffix1)
let copy2 ~names x = Ident.Tvar (Ident.name_of_tvar x ^ names.suffix2)

let rec is_intype = function
  | TVar { contents = None } -> false
  | TVar { contents = Some typ } -> is_intype typ
  | In -> true
  | Out -> false
  | Func (_typ1, _typ2) -> false

let rec alpha ~names = function
  | Fd n -> Fd n
  | Term a -> Term a
  (* | Var (x, t) when is_intype !t -> Var (x, t)
     | Var (x, t) -> Var (copy1 x, t) *)
  | Var (_x, _t) as v -> v
  | Nonterm f -> Nonterm (copy1 ~names f)
  | App (t1, t2) -> App (alpha ~names t1, alpha ~names t2)
  | Case (x, pats) ->
      Case (x, List.map pats ~f:(fun (a, (ys, t)) -> (a, (ys, alpha ~names t))))
  | Tree q -> Tree q
  | Coerce (q, _t, _) -> Tree q
  | Copy _ | VarOrTerm _ -> failwith "alpha"

let alphaRules ~names =
  List.map ~f:(fun (f, (xs, t)) -> (copy1 ~names f, (xs, alpha ~names t)))

let rec coerces = function
  | Fd _n -> []
  | Term _a -> []
  | Var (_x, _t) -> []
  | Nonterm _f -> []
  | App (t1, t2) -> coerces t1 @ coerces t2
  | Case (_x, _pats) -> []
  | Tree _q -> []
  | Coerce (q, t, idx) -> [ (q, t, idx) ]
  | Copy _ | VarOrTerm _ -> failwith "coerces"

let term ~names a = Ident.Tvar (names.terminal_prefix ^ Ident.name_of_tvar a)

let rec elim_coerce ~names (q, tm, idx) = function
  | Fd n -> Fd n
  | Term a -> Nonterm (term ~names a)
  | Var (_x, t) as v when is_intype !t -> v
  | Var (x, t) -> Var (copy2 ~names x, t)
  | Nonterm f -> Nonterm (copy2 ~names f)
  | App (t1, t2) ->
      app
        (app (elim_coerce ~names (q, tm, idx) t1) (alpha ~names t2))
        (elim_coerce ~names (q, tm, idx) t2)
  | Case (x, pats) ->
      Case
        ( x,
          List.map pats ~f:(fun (a, (xs, t)) ->
              (a, (xs, beta_term ~names (q, tm, idx) t))) )
  | Tree _q as t -> t
  | Coerce (q', _, _) -> Tree q'
  | Copy _ | VarOrTerm _ -> failwith "beta1"

and beta_term ~names (q, tm, idx) term =
  let cs = coerces term in
  (* A coercion's body may itself evaluate another coercion. Explore its
     obligations as output trees, separately from the data-valued result
     that elim_coerce replaces by the declared input state. *)
  let ec (_, t, _) = beta_term ~names (q, tm, idx) t in
  if List.exists cs ~f:(trd3 >> ( = ) idx) then
    let t1 = alpha ~names tm in
    let t2s = List.map ~f:ec cs in
    let t3 = elim_coerce ~names (q, tm, idx) term in
    nondet_branch (Term names.br) app ((t1 :: t2s) @ [ t3 ])
  else
    let ts = List.map ~f:ec cs in
    let t = elim_coerce ~names (q, tm, idx) term in
    nondet_branch (Term names.br) app (t :: ts)

(* [beta_rules ~names (q, tm, idx) rules terminals] is the program checked
   for the coercion [idx] of [tm] to [q]: the alpha copy of every rule (it
   computes the original output), the beta copy of every rule (it takes each
   argument as its alpha and beta copies and produces a tree of [names.br]
   nodes whose leaves are [names.success] or the alpha copy of [tm] wherever
   the coercion is reached), and the beta copy [term ~names a] of every
   terminal [(a, arity)] of [terminals],
   which must list every terminal the rules apply, the input automaton's
   and any other.  It holds no start rule: the caller starts from the beta
   copy of its start term ([beta_term]), which hands each argument's alpha
   and beta copies to the beta copy of the main non-terminal. *)
let beta_rules ~names (q, tm, idx) rules terminals =
  let make_terminal_fun (a, n) =
    let vs =
      List.init n ~f:(fun v -> Ident.Tvar ("x" ^ string_of_int (v + 1)))
    in
    let vs2 = List.map ~f:(copy2 ~names) vs in
    let vs12 = flatten_pairs (List.zip_exn vs vs2) in
    let vs2' = List.map ~f:(fun v -> Var (v, ref Out)) vs2 in
    let t =
      if n = 0 then Term names.success
      else nondet_branch (Term names.br) app vs2'
    in
    let rule = (term ~names a, (vs12, t)) in
    rule
  in
  let term_rules = List.map ~f:make_terminal_fun terminals in

  let make_copy1 (f, (xs, t)) = (copy1 ~names f, (xs, alpha ~names t)) in
  let rules1 = List.map ~f:make_copy1 rules in

  let make_copy2 (f, (xs, term)) =
    let xs2 = List.map ~f:(copy2 ~names) xs in
    let xs12 = flatten_pairs (List.zip_exn xs xs2) in
    (copy2 ~names f, (xs12, beta_term ~names (q, tm, idx) term))
  in
  let rules2 = List.map ~f:make_copy2 rules in

  let ret = rules1 @ rules2 @ term_rules in
  (* Term.pr_rules Format.err_formatter ret; *)
  ret

(* ToDo: if not supported*)
let eta_expand env rules =
  List.map rules ~f:(fun (id, (ids, t)) ->
      try
        let sorts, _ =
          LogicOld.Sort.args_ret_of @@ LogicOld.Sort.mono_type_of
          @@ Map.Poly.find_exn env id
        in
        let d = List.length sorts - List.length ids in
        assert (d >= 0);
        (* The new parameters sit beside the rule's own, which may be
           program variables spelled like a drawn [x<n>]; a repeated parameter
           would bind the body's occurrence to the wrong one. *)
        let ids' =
          List.init d ~f:(fun _ ->
              Ident.mk_fresh_tvar_avoiding ~prefix:"x"
                ~taken:(List.mem ~equal:Ident.tvar_equal ids)
                ())
        in
        (id, (ids @ ids', apps t (List.map ids' ~f:mk_var)))
      with exn_ when not (Common.Timer.is_async exn_) ->
        failwith (Ident.name_of_tvar id ^ " is not bound"))
