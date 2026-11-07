(* Solving recursion-free Horn clause systems over linear arithmetic, the
   search axis of interpolation: a binary interpolation query [phi1 => I =>
   phi2] is the two-clause system [I(x) <= phi1], [bot <= I(x) /\ not phi2]
   (Unno and Terauchi, "Inferring simple solutions to recursion-free Horn
   clauses via sampling", TACAS 2015, LNCS 9035, footnote 1), and a tree
   interpolant is a solution of a body-disjoint system with one predicate
   per node.

   A system is a list of clauses [H(t) <= P_1(u_1) /\ ... /\ P_k(u_k) /\ phi]
   (or a goal, [bot <= ...]) over declared predicates, each with formal
   parameters; a solution maps every predicate to a quantifier-free formula
   over its own parameters such that every clause, with the solution
   substituted, is valid.  Two searches:

   - [Single_refutation] (the backward search of Unno and Kobayashi,
     "Dependent Type Inference with Interpolants", PPDP 2009, as vhorn's
     backward interpolating solver implements it): the least solution [lb]
     is computed forward with the clauses' own variables kept as existential
     locals, a goal whose body is satisfiable under [lb] proves that no
     solution exists, and otherwise the clauses are visited from the goals
     down; at a clause whose head already has its solution [theta(H)], each
     body occurrence [P_i] in turn receives an interpolant of [lb(P_i)]
     against the rest of the clause -- its formula part, the negated head,
     the interpolants already chosen for the earlier occurrences and the
     lower bounds of the later ones -- asked of the binary interpolation
     leaves ([Interpolant.binary]).  A predicate with several body
     occurrences (a DAG rather than a tree) gets the conjunction of its
     occurrences' interpolants, once every clause it occurs in has been
     visited (vhorn's [merge_and]).  Every query is unsatisfiable by
     induction: [lb(P)] implies each of [P]'s occurrence interpolants, hence
     their conjunction, so the query at a clause [P] heads is unsatisfiable;
     and a clause holds under the conjunctions because a stronger body only
     weakens what it must imply.  So a leaf that answers gives the next
     solution.  A refutation comes with a witness: a model [sigma] of the
     refuted goal's body under the least solution, unfolded as a tree of
     clause instances, and the derivation [D] read off [sigma] by evaluating,
     at each node of the tree, which defining clause's disjunct [sigma]
     satisfies.
   - [Atomic_template] (TACAS 2015's [A_atom], its section 3.3): one linear
     atom [c_0 + c . x >= 0] per predicate with unknown rational
     coefficients, every clause turned by Farkas' lemma (Motzkin's
     transposition theorem for a goal with strict atoms) into linear
     constraints over the unknowns and fresh multipliers, the multiplier of
     each body template fixed to 1 so that the constraint stays linear, and
     the constraints solved by [CoeffSolver].  The formula parts are first
     put in disjunctive normal form, one clause per cube.  Sound on any
     recursion-free system; the paper proves it decides atomic solvability
     of conjunctive body-disjoint systems over the rationals (its Theorem 4)
     and that conjunctive body- and head-disjoint systems have an atomic
     solution or none (its Lemma 4).

   Before either search the system is sliced (vhorn's forward and backward
   slicing): a predicate that no fact reaches gets [false], and one from
   which no goal is reached gets [true] and loses its clauses.  Every answer
   is checked against the whole input system by Z3 before it is returned, so
   a leaf, a coefficient solution or a slicing step that is wrong costs an
   answer, never a wrong one.

   Ported from vhorn [eee5708e] ([src/hcssolver/HCSSolver.ml]'s slicing,
   [tbHCSSolver.ml], [fwHCSSolver.ml]'s forward lower bounds and
   [bwCIPHCSSolver.ml]), restructured. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld
open Linarith

(* A predicate application [P(t_1, ..., t_n)]. *)
type app = { pred : Ident.pvar; args : Term.t list }

(* [head <= body_1 /\ ... /\ body_k /\ phi]; [head = None] is a goal. *)
type clause = { head : app option; body : app list; phi : Formula.t }

(* [preds]: every predicate with its formal parameters, which are the only
   free variables its solution may mention; [clauses]: the system.
   Invariant expected by every function here: each application's arity is
   its predicate's, and its arguments have the parameters' sorts. *)
type system = {
  preds : (Ident.pvar * (Ident.tvar * Sort.t) list) list;
  clauses : clause list;
}

(* A solution: one formula per predicate, over that predicate's parameters. *)
type solution = (Ident.pvar * Formula.t) list
type search = Single_refutation | Atomic_template [@@deriving yojson]

(* A derivation: a clause of the system, the renaming of its variables to
   the instance's own (the identity on a goal, which keeps its variables),
   and one derivation per body application, in order.  The instance of a
   node is its clause's formula part renamed, and the arguments of each body
   application, renamed, equal the child's head arguments, renamed by the
   child's renaming. *)
type derivation = {
  clause : clause;
  renaming : (Ident.tvar, Term.t) Map.Poly.t;
  children : derivation list;
}

(* A refutation's witness: [sigma] assigns a value to every variable of the
   derivation's instances, and every instance holds under it
   ([derivation_holds]); so the derivation is a ground resolution proof of
   [false] from the system, and no solution exists whatever the formula
   language (PPDP 2009's Lemma A.1 read contrapositively). *)
type witness = {
  sigma : ((Ident.tvar * Sort.t) * Term.t) list;
  derivation : derivation;  (** rooted at the refuted goal *)
  refuted : Formula.t;
      (** the refuted goal's formula part and body under the least solution,
          unfolded ([F(G^i(bot))] of PPDP 2009, section 4.2): its free variables
          are the goal's own and the unfolding's fresh ones, and [sigma]
          satisfies it *)
}

type outcome =
  | Solved of solution
      (** every clause, the solution substituted, was checked valid by Z3, and
          each formula mentions only its predicate's parameters *)
  | No_solution of witness
      (** a goal's body is satisfiable under the least solution (decided by Z3
          in the system's own theory); the witness's instances were checked to
          hold under its [sigma] by evaluation *)
  | Declined of string  (** neither, with the reason *)

exception Decline of string

let decline fmt = ksprintf (fun s -> raise (Decline s)) fmt

let params_of sys p =
  match List.Assoc.find sys.preds p ~equal:Ident.pvar_equal with
  | Some ps -> ps
  | None -> decline "undeclared predicate %s" (Ident.name_of_pvar p)

let lookup theta p = List.Assoc.find theta p ~equal:Ident.pvar_equal

(* [instance params phi args]: [phi] (over [params]) at [args], substituted
   simultaneously.  Pre: [phi]'s free variables among [params] (else they
   stay free). *)
let instance params phi args =
  Formula.subst
    (Map.Poly.of_alist_exn
       (List.map2_exn params args ~f:(fun (v, _) t -> (v, t))))
    phi

let app_formula sys theta a =
  match lookup theta a.pred with
  | Some phi -> instance (params_of sys a.pred) phi a.args
  | None -> decline "no solution for %s" (Ident.name_of_pvar a.pred)

(* The clause with [theta] substituted, as an implication. *)
let clause_formula sys theta c =
  Formula.mk_imply
    (Formula.and_of (c.phi :: List.map c.body ~f:(app_formula sys theta)))
    (match c.head with
    | Some h -> app_formula sys theta h
    | None -> Formula.mk_false ())

(* The variables of a clause, with sorts. *)
let clause_env c =
  let apps = Option.to_list c.head @ c.body in
  Set.Poly.union_list
    (Formula.term_sort_env_of c.phi
    :: List.concat_map apps ~f:(fun a ->
        List.map a.args ~f:Term.term_sort_env_of))

let fvs phi = Set.Poly.map (Formula.term_sort_env_of phi) ~f:fst

(* [is_solution ?timeout ~id sys theta]: every predicate of [sys] has a
   quantifier-free formula in [theta] over its own parameters, and every
   clause with [theta] substituted is valid by Z3.  [false] when Z3 does not
   decide. *)
let is_solution ?timeout ~id sys theta =
  try
    List.for_all sys.preds ~f:(fun (p, ps) ->
        match lookup theta p with
        | None -> false
        | Some phi ->
            Formula.is_quantifier_free phi
            && Set.is_subset (fvs phi)
                 ~of_:(Set.Poly.of_list (List.map ps ~f:fst)))
    && List.for_all sys.clauses ~f:(fun c ->
        Z3Smt.Z3interface.is_valid ~timeout ~id (get_fenv ())
          (clause_formula sys theta c))
  with Decline _ -> false

(** {2 Shape} *)

let body_preds sys =
  List.concat_map sys.clauses ~f:(fun c -> List.map c.body ~f:(fun a -> a.pred))

let head_preds sys =
  List.filter_map sys.clauses ~f:(fun c ->
      Option.map c.head ~f:(fun a -> a.pred))

let occurs_more_than_once ps =
  List.contains_dup
    ~compare:(fun p q ->
      String.compare (Ident.name_of_pvar p) (Ident.name_of_pvar q))
    ps

(* Body-disjoint: no predicate occurs twice in bodies (TACAS 2015, § 2: no
   body-joining predicate); head-disjoint: no predicate heads two clauses. *)
let is_body_disjoint sys = not (occurs_more_than_once (body_preds sys))
let is_head_disjoint sys = not (occurs_more_than_once (head_preds sys))

(* Conjunctive: every formula part a conjunction of comparisons. *)
let is_conjunctive sys =
  List.for_all sys.clauses ~f:(fun c ->
      List.for_all (Formula.conjuncts_list_of c.phi) ~f:(function
        | Formula.Atom _ -> true
        | _ -> false))

(* The predicates in dependency order, every predicate after the body
   predicates of the clauses it heads.  [None] when the system is recursive. *)
let topological sys =
  let state = Hashtbl.Poly.create () in
  let order = ref [] in
  let exception Recursive in
  let rec visit p =
    match Hashtbl.find state p with
    | Some `Done -> ()
    | Some `Visiting -> raise Recursive
    | None ->
        Hashtbl.set state ~key:p ~data:`Visiting;
        List.iter sys.clauses ~f:(fun c ->
            match c.head with
            | Some h when Ident.pvar_equal h.pred p ->
                List.iter c.body ~f:(fun a -> visit a.pred)
            | _ -> ());
        Hashtbl.set state ~key:p ~data:`Done;
        order := p :: !order
  in
  try
    List.iter sys.preds ~f:(fun (p, _) -> visit p);
    Some (List.rev !order)
  with Recursive -> None

let is_recursion_free sys = Option.is_some (topological sys)

(** {2 Slicing} *)

(* [slice sys]: [(sys', partial)] where [partial] gives [false] to every
   predicate no fact reaches (it heads no clause whose body predicates are
   all reached) and [true] to every reached predicate from which no goal is
   reached, and [sys'] keeps the clauses that mention neither kind (with
   [sys']'s [preds] the rest).
   Post: [theta'] solves [sys'] exactly when [partial @ theta'] solves [sys]:
   a dropped clause has a [false] body predicate or a [true] head, so it is
   valid under [partial] whatever [theta'] is; the predicates of a kept
   clause are all kept. *)
let slice sys =
  let mem set p = Set.mem set (Ident.name_of_pvar p) in
  let reached =
    let rec grow set =
      let set' =
        List.fold sys.clauses ~init:set ~f:(fun set c ->
            match c.head with
            | Some h when List.for_all c.body ~f:(fun a -> mem set a.pred) ->
                Set.add set (Ident.name_of_pvar h.pred)
            | _ -> set)
      in
      if Set.length set' = Set.length set then set else grow set'
    in
    grow Set.Poly.empty
  in
  let useful =
    let rec grow set =
      let set' =
        List.fold sys.clauses ~init:set ~f:(fun set c ->
            let live =
              match c.head with None -> true | Some h -> mem set h.pred
            in
            if live then
              List.fold c.body ~init:set ~f:(fun set a ->
                  Set.add set (Ident.name_of_pvar a.pred))
            else set)
      in
      if Set.length set' = Set.length set then set else grow set'
    in
    grow Set.Poly.empty
  in
  let partial =
    List.filter_map sys.preds ~f:(fun (p, _) ->
        if not (mem reached p) then Some (p, Formula.mk_false ())
        else if not (mem useful p) then Some (p, Formula.mk_true ())
        else None)
  in
  let sliced p = Option.is_some (lookup partial p) in
  let clauses =
    List.filter sys.clauses ~f:(fun c ->
        (not (List.exists c.body ~f:(fun a -> sliced a.pred)))
        && not (Option.exists c.head ~f:(fun h -> sliced h.pred)))
  in
  ( { preds = List.filter sys.preds ~f:(fun (p, _) -> not (sliced p)); clauses },
    partial )

(** {2 Fresh names} *)

(* A source of variables fresh for [sys] and for every name drawn before. *)
let namer sys =
  let taken =
    ref
      (Set.Poly.union_list
         (Set.Poly.of_list
            (List.concat_map sys.preds ~f:(fun (_, ps) -> List.map ps ~f:fst))
         :: List.map sys.clauses ~f:(fun c ->
             Set.union
               (Formula.names_spelled_in c.phi)
               (Set.Poly.map (clause_env c) ~f:fst))))
  in
  fun prefix ->
    let v = Ident.mk_fresh_tvar_avoiding ~prefix ~taken:(Set.mem !taken) () in
    taken := Set.add !taken v;
    v

let rename_map fresh env =
  Map.Poly.of_alist_exn
    (List.map (Set.to_list env) ~f:(fun (v, s) ->
         (v, Term.mk_var (fresh "sh") s)))

(** {2 The least solution} *)

(* [lower_bounds fresh sys order]: for every predicate, the formula over its
   parameters and fresh existential locals (every other free variable) whose
   existential closure is the least solution: the disjunction over the
   clauses it heads of the clause's body, renamed apart, with the head's
   arguments equated to the parameters and each body predicate's bound in
   place of its application.  Pre: [order] is [topological sys]. *)
let lower_bounds fresh sys order =
  let lbs = Hashtbl.Poly.create () in
  let inst p args =
    let params = params_of sys p in
    let lb = Hashtbl.find_exn lbs (Ident.name_of_pvar p) in
    let pset = Set.Poly.of_list (List.map params ~f:fst) in
    let locals =
      Set.filter (Formula.term_sort_env_of lb) ~f:(fun (v, _) ->
          not (Set.mem pset v))
    in
    Formula.subst
      (Map.force_merge (rename_map fresh locals)
         (Map.Poly.of_alist_exn
            (List.map2_exn params args ~f:(fun (v, _) t -> (v, t)))))
      lb
  in
  List.iter order ~f:(fun p ->
      let params = params_of sys p in
      let disjuncts =
        List.filter_map sys.clauses ~f:(fun c ->
            match c.head with
            | Some h when Ident.pvar_equal h.pred p ->
                let sub = rename_map fresh (clause_env c) in
                let st = Term.subst sub in
                Some
                  (Formula.and_of
                     (List.map2_exn params h.args ~f:(fun (v, s) t ->
                          Formula.eq (Term.mk_var v s) (st t))
                     @ List.map c.body ~f:(fun a ->
                         inst a.pred (List.map a.args ~f:st))
                     @ [ Formula.subst sub c.phi ]))
            | _ -> None)
      in
      Hashtbl.set lbs ~key:(Ident.name_of_pvar p)
        ~data:(Formula.or_of disjuncts));
  inst

(** {2 The least solution unfolded, and the witness of a refutation} *)

(* The least solution of one application, unfolded as a tree: for every
   clause heading its predicate, that clause renamed apart, with its head's
   arguments equated to the application's and one subtree per body
   application.  Its formula ([unfolded_formula]) is equivalent, under the
   existential closure of the fresh variables, to [lower_bounds]'s formula at
   the same arguments; the tree is kept so that a model can be read back as
   a derivation.  Pre: [sys] recursion-free. *)
type unfolded = { alts : alt list }

and alt = {
  a_clause : clause;
  a_renaming : (Ident.tvar, Term.t) Map.Poly.t;
  a_local : Formula.t;
      (** the head arguments equated to the application's, and the clause's
          formula part, both renamed *)
  a_children : unfolded list;
}

let rec unfold fresh sys (a : app) =
  {
    alts =
      List.filter_map sys.clauses ~f:(fun c ->
          match c.head with
          | Some h when Ident.pvar_equal h.pred a.pred ->
              let sub = rename_map fresh (clause_env c) in
              let st = Term.subst sub in
              Some
                {
                  a_clause = c;
                  a_renaming = sub;
                  a_local =
                    Formula.and_of
                      (List.map2_exn a.args h.args ~f:(fun t u ->
                           Formula.eq t (st u))
                      @ [ Formula.subst sub c.phi ]);
                  a_children =
                    List.map c.body ~f:(fun b ->
                        unfold fresh sys { b with args = List.map b.args ~f:st });
                }
          | _ -> None);
  }

let rec unfolded_formula u = Formula.or_of (List.map u.alts ~f:alt_formula)

and alt_formula a =
  Formula.and_of (a.a_local :: List.map a.a_children ~f:unfolded_formula)

(* [holds sigma phi]: [phi] evaluates to true when every free variable takes
   its value in [sigma], or a dummy value of its sort when [sigma] has none;
   [false] when evaluation fails. *)
let holds sigma phi =
  try
    let env =
      Map.Poly.of_alist_reduce
        ~f:(fun first _ -> first)
        (List.map
           (Set.to_list (Formula.term_sort_env_of phi))
           ~f:(fun (v, s) ->
             let t =
               match
                 List.find_map sigma ~f:(fun ((x, _), t) ->
                     if Ident.tvar_equal x v then Some t else None)
               with
               | Some t -> t
               | None -> Term.mk_dummy s
             in
             (v, Evaluator.eval_term t)))
    in
    Evaluator.eval ~env phi
  with exn when not (Common.Timer.is_async exn) -> false

(* The instance of a derivation node: its renamed formula part, and each
   body application's renamed arguments equal to the child's renamed head
   arguments. *)
let rec derivation_instances d =
  let st = Term.subst d.renaming in
  let here =
    Formula.and_of
      (Formula.subst d.renaming d.clause.phi
      :: List.concat
           (List.map2_exn d.clause.body d.children ~f:(fun b child ->
                match child.clause.head with
                | Some h ->
                    List.map2_exn b.args h.args ~f:(fun t u ->
                        Formula.eq (st t) (Term.subst child.renaming u))
                | None -> [ Formula.mk_false () ])))
  in
  here :: List.concat_map d.children ~f:derivation_instances

(* [derivation_holds w]: every instance of [w.derivation] evaluates to true
   under [w.sigma] (a ground check, no solver). *)
let derivation_holds w =
  List.for_all (derivation_instances w.derivation) ~f:(holds w.sigma)

(* Reads the derivation off [sigma]: at each node the first alternative
   whose whole formula holds.  Pre: the node's formula holds under [sigma],
   so some alternative does. *)
let rec read_derivation sigma (u : unfolded) =
  match List.find u.alts ~f:(fun a -> holds sigma (alt_formula a)) with
  | Some a ->
      {
        clause = a.a_clause;
        renaming = a.a_renaming;
        children = List.map a.a_children ~f:(read_derivation sigma);
      }
  | None -> decline "a refutation's model satisfies no alternative"

(* [refutation_witness ~timeout ~id fresh sys goal]: [Some w] when [goal]'s
   body is satisfiable under the least solution, with [w] its witness; [None]
   when it is not.  Z3's model is completed by dummy values; when the
   completed model does not satisfy the goal's formula (a variable Z3 left
   unassigned mattered), the unassigned variables are asked of Z3 again with
   the assigned ones fixed, at most twice, and then the search declines.
   Post: [derivation_holds w]. *)
let refutation_witness ~timeout ~id fresh sys goal =
  let children = List.map goal.body ~f:(unfold fresh sys) in
  let phi =
    Formula.and_of (goal.phi :: List.map children ~f:unfolded_formula)
  in
  let env = Formula.term_sort_env_of phi in
  let ask phis =
    match Z3Smt.Z3interface.check_sat ~timeout ~id (get_fenv ()) phis with
    | `Sat model ->
        `Sat
          (List.filter_map model ~f:(function
            | (x, s), Some t when Set.mem env (x, s) -> Some ((x, s), t)
            | _ -> None))
    | `Unsat -> `Unsat
    | _ -> `Unknown
  in
  let rec complete tries sigma =
    if holds sigma phi then sigma
    else if tries = 0 then
      decline "a refutation's model does not evaluate: %s"
        (String.prefix (Formula.str_of phi) 400)
    else
      let fixed =
        List.map sigma ~f:(fun ((x, s), t) -> Formula.eq (Term.mk_var x s) t)
      in
      match ask (phi :: fixed) with
      | `Sat more ->
          complete (tries - 1)
            (sigma
            @ List.filter more ~f:(fun (b, _) ->
                not (List.exists sigma ~f:(fun (b', _) -> Stdlib.(b = b')))))
      | _ -> decline "a refutation's model does not evaluate"
  in
  match ask [ phi ] with
  | `Unsat -> None
  | `Unknown -> decline "a goal under the least solution: undecided"
  | `Sat sigma ->
      let sigma = complete 2 sigma in
      let sigma =
        sigma
        @ List.filter_map (Set.to_list env) ~f:(fun (x, s) ->
            if List.exists sigma ~f:(fun ((y, _), _) -> Ident.tvar_equal x y)
            then None
            else Some ((x, s), Term.mk_dummy s))
      in
      let w =
        {
          sigma;
          derivation =
            {
              clause = goal;
              renaming = Map.Poly.empty;
              children = List.map children ~f:(read_derivation sigma);
            };
          refuted = phi;
        }
      in
      if not (derivation_holds w) then
        decline "a refutation's derivation does not hold";
      Some w

(** {2 Single_refutation} *)

let check_sat ~timeout ~id phi =
  match Z3Smt.Z3interface.check_sat ~timeout ~id (get_fenv ()) [ phi ] with
  | `Sat _ -> `Sat
  | `Unsat -> `Unsat
  | _ -> `Unknown

(* The backward search (see the header).  Pre: [sys] recursion-free.
   Returns a candidate for every predicate of [sys], or [`No_solution w]
   with [derivation_holds w]; the caller checks the candidate. *)
let single_refutation ~timeout ~id ~leaves ~solve_chc ~qelim sys =
  let order =
    match topological sys with Some o -> o | None -> decline "recursive"
  in
  let fresh = namer sys in
  let lb = lower_bounds fresh sys order in
  let lb_app a = lb a.pred a.args in
  (* A goal satisfiable under the least solution: no solution exists. *)
  let goals = List.filter sys.clauses ~f:(fun c -> Option.is_none c.head) in
  match List.find_map goals ~f:(refutation_witness ~timeout ~id fresh sys) with
  | Some w -> `No_solution w
  | None ->
      let theta = Hashtbl.Poly.create () in
      let set p phi = Hashtbl.set theta ~key:(Ident.name_of_pvar p) ~data:phi in
      let get p = Hashtbl.find theta (Ident.name_of_pvar p) in
      (* how many body occurrences each predicate has, and the interpolants
       its occurrences received so far; a predicate's solution is set, as
       their conjunction, once every occurrence has one *)
      let uses = Hashtbl.Poly.create () in
      List.iter (body_preds sys) ~f:(fun p ->
          Hashtbl.update uses (Ident.name_of_pvar p) ~f:(function
            | None -> 1
            | Some n -> n + 1));
      let received = Hashtbl.Poly.create () in
      let receive p phi =
        let key = Ident.name_of_pvar p in
        let got = phi :: Option.value (Hashtbl.find received key) ~default:[] in
        Hashtbl.set received ~key ~data:got;
        if List.length got = Hashtbl.find_exn uses key then
          set p
            (match got with
            | [ phi ] -> phi
            | _ -> Formula.and_of (List.rev got))
      in
      List.iter sys.preds ~f:(fun (p, _) ->
          if not (Hashtbl.mem uses (Ident.name_of_pvar p)) then
            set p (Formula.mk_true ()));
      let theta_app a =
        match get a.pred with
        | Some phi -> instance (params_of sys a.pred) phi a.args
        | None -> decline "no solution yet for %s" (Ident.name_of_pvar a.pred)
      in
      let solve_clause c =
        let psi =
          Formula.and_of
            [
              c.phi;
              (match c.head with
              | Some h -> Formula.mk_neg (theta_app h)
              | None -> Formula.mk_true ());
            ]
        in
        match check_sat ~timeout ~id psi with
        | `Unsat ->
            (* the clause holds whatever its body predicates are *)
            List.iter c.body ~f:(fun a -> receive a.pred (Formula.mk_true ()))
        | `Sat | `Unknown ->
            if List.is_empty c.body then
              decline "a fact violates its head's interpolant";
            let n = List.length c.body in
            (* this clause's interpolants, by occurrence, at their arguments *)
            let local = Array.create ~len:n (Formula.mk_true ()) in
            List.iteri c.body ~f:(fun i a ->
                let params = params_of sys a.pred in
                let xs = List.map params ~f:(fun (_, s) -> (fresh "shx", s)) in
                let xs_terms = List.map xs ~f:(fun (v, s) -> Term.mk_var v s) in
                let side =
                  Formula.and_of
                    ((psi :: List.map2_exn xs_terms a.args ~f:Formula.eq)
                    @ List.filter_mapi c.body ~f:(fun j b ->
                        if j < i then Some local.(j)
                        else if j > i && j < n then Some (lb_app b)
                        else None))
                in
                match
                  Interpolant.binary ~leaves ~solve_chc ~qelim xs
                    (lb a.pred xs_terms) (Formula.mk_neg side)
                with
                | Interpolant.Interpolant itp ->
                    (* the CHC leaf's solution may carry quantifiers (Spacer
                       returns existentially quantified solutions), and a
                       quantified formula fed back into a later query is one
                       Spacer then answers unknown; eliminate, or decline *)
                    let itp =
                      if Formula.is_quantifier_free itp then itp
                      else Evaluator.simplify (qelim itp)
                    in
                    if not (Formula.is_quantifier_free itp) then
                      decline "a quantified interpolant";
                    if
                      not
                        (Set.is_subset (fvs itp)
                           ~of_:(Set.Poly.of_list (List.map xs ~f:fst)))
                    then decline "an interpolant outside its vocabulary";
                    let itp =
                      Formula.subst
                        (Map.Poly.of_alist_exn
                           (List.map2_exn xs params ~f:(fun (x, _) (v, s) ->
                                (x, Term.mk_var v s))))
                        itp
                    in
                    local.(i) <- instance params itp a.args;
                    receive a.pred itp
                | Interpolant.No_interpolant ->
                    decline "a leaf found the query satisfiable"
                | Interpolant.Declined ->
                    decline "every leaf declined at %s"
                      (Ident.name_of_pvar a.pred))
      in
      (* clauses in the order their heads are solved: goals first, then the
       clauses of each predicate once every occurrence of it has its
       interpolant *)
      let rec loop pending =
        match
          List.partition_tf pending ~f:(fun c ->
              match c.head with
              | None -> true
              | Some h -> Option.is_some (get h.pred))
        with
        | [], [] -> ()
        | [], _ -> decline "a clause whose head is never solved"
        | ready, rest ->
            List.iter ready ~f:solve_clause;
            loop rest
      in
      loop sys.clauses;
      `Candidate
        (List.map sys.preds ~f:(fun (p, _) ->
             match get p with
             | Some phi -> (p, phi)
             | None -> decline "no solution for %s" (Ident.name_of_pvar p)))

(** {2 Atomic_template} *)

(* [affine zs t]: [t] as rational coefficients over [zs] and a constant. *)
let affine zs t =
  match
    try Rows.affine_over zs t
    with exn when not (Common.Timer.is_async exn) -> None
  with
  | Some d -> d
  | None -> decline "a non-linear argument %s" (Term.str_of t)

let rterm q c = T_real.mk_rmul (T_real.mk_real q) c
let rsum ts = T_real.mk_rsum (T_real.rzero ()) ts

(* A template atom at the arguments [args]: the coefficient of each column of
   [zs] and the constant, as real terms linear in the atom's unknowns. *)
let template_at zs (a : Template.atom) args =
  let ds = List.map args ~f:(affine zs) in
  let var (v, s) = Term.mk_var v s in
  let columns =
    List.mapi zs ~f:(fun j _ ->
        rsum
          (List.map2_exn a.coeffs ds ~f:(fun c (ks, _) ->
               rterm (List.nth_exn ks j) (var c))))
  in
  let constant =
    rsum
      (var a.const
      :: List.map2_exn a.coeffs ds ~f:(fun c (_, k0) -> rterm k0 (var c)))
  in
  (columns, constant)

(* The constraints of one conjunctive clause (TACAS 2015's [constr], with
   strict atoms by Motzkin's transposition theorem).  With [E] the sum of
   the body templates at their arguments, of the multiplier-weighted rows of
   [phi] (each read as [b - k . z >= 0], or [> 0]) and of the negated head
   template: every column of [E] is 0, and its constant is [<= 0] for a
   definite clause (the negated head is a strict row of weight 1), [< 0], or
   [<= 0] with positive weight on a strict row, for a goal. *)
let clause_constraints ~taken templates c =
  let zs = Set.to_list (clause_env c) in
  if
    not
      (List.for_all zs ~f:(fun (_, s) -> Term.is_real_sort s)
      || List.for_all zs ~f:(fun (_, s) -> Term.is_int_sort s))
  then decline "a clause mixing sorts";
  let rows =
    match Rows.cube_rows_over zs c.phi with
    | Some rows ->
        if List.for_all zs ~f:(fun (_, s) -> Term.is_int_sort s) then
          List.map rows ~f:(Rows.tighten_integer zs)
        else rows
    | None -> decline "a formula part that is not a linear cube"
  in
  let tmpl a = Option.value_exn (lookup templates a.pred) in
  let num = Farkas.Num.real_num in
  (* [comb] combines the rows [k . z <= b]; their sum as [b - k . z >= 0] has
     column [- comb.column j] and constant [comb.bound] *)
  let comb =
    Farkas.combination ~num ~taken ~prefix:"SM"
      (List.map rows ~f:(fun (r : Rows.row) -> (r.coeffs, r.bound)))
  in
  let body = List.map c.body ~f:(fun a -> template_at zs (tmpl a) a.args) in
  let head = Option.map c.head ~f:(fun h -> template_at zs (tmpl h) h.args) in
  let neg t = T_real.mk_rneg t in
  let column j =
    rsum
      (neg (comb.column j)
       :: List.map body ~f:(fun (cols, _) -> List.nth_exn cols j)
      @ Option.to_list
          (Option.map head ~f:(fun (cols, _) -> neg (List.nth_exn cols j))))
  in
  let constant =
    rsum
      ((comb.bound :: List.map body ~f:snd)
      @ Option.to_list (Option.map head ~f:(fun (_, k) -> neg k)))
  in
  let zero = T_real.rzero () in
  let strict_weight =
    rsum
      (List.filter_map (List.zip_exn rows comb.multipliers) ~f:(fun (r, l) ->
           if r.strict then Some l else None))
  in
  let closing =
    match c.head with
    | Some _ -> Formula.leq constant zero
    | None ->
        Formula.or_of
          [
            Formula.lt constant zero;
            Formula.and_of
              [ Formula.leq constant zero; Formula.gt strict_weight zero ];
          ]
  in
  ( (closing :: comb.nonneg)
    @ List.init (List.length zs) ~f:(fun j -> Formula.eq (column j) zero),
    List.map comb.multipliers ~f:(fun l -> fst (Term.let_var l)) )

(* [A_atom] on [sys] (see the header): the candidate, or a decline when no
   atomic solution exists or the coefficient solver does not decide. *)
let atomic_template ~timeout ~id ~coeff_mode sys =
  let templates =
    List.map sys.preds ~f:(fun (p, ps) ->
        if
          not
            (List.for_all ps ~f:(fun (_, s) -> Term.is_int_sort s)
            || List.for_all ps ~f:(fun (_, s) -> Term.is_real_sort s))
        then
          decline "parameters of %s not all integer or all real"
            (Ident.name_of_pvar p);
        (p, Template.atom ~unknown_sort:T_real.SReal ~prefix:"SC" ps))
  in
  let cubes c =
    match Interpolant.literal_dnf ~pos:true c.phi with
    | Some cs ->
        List.map cs ~f:(fun lits -> { c with phi = Formula.and_of lits })
    | None -> decline "a formula part outside linear comparisons"
  in
  let template_unknowns =
    List.concat_map templates ~f:(fun (_, a) -> Template.unknowns_of_atom a)
  in
  let taken = Set.Poly.of_list (List.map template_unknowns ~f:fst) in
  let constraints, multipliers =
    List.unzip
      (List.map
         (List.concat_map sys.clauses ~f:cubes)
         ~f:(clause_constraints ~taken templates))
  in
  let unknowns = template_unknowns @ List.concat multipliers in
  match
    CoeffSolver.solve ~mode:coeff_mode ?timeout ~id unknowns
      (Formula.and_of (List.concat constraints))
  with
  | CoeffSolver.Solved sol ->
      let value (v, _) =
        match List.Assoc.find sol v ~equal:Ident.tvar_equal with
        | Some t -> Value.cast_real_of (Evaluator.eval_term t)
        | None -> Q.zero
      in
      `Candidate
        (List.map templates ~f:(fun (p, a) ->
             let sort =
               match a.vars with
               | (_, s) :: _ when Term.is_int_sort s -> T_int.SInt
               | _ -> T_real.SReal
             in
             (* [c_0 + c . x >= 0] is [(-c) . x <= c_0] *)
             ( p,
               Evaluator.simplify
                 (Interpolant.affine_formula ~sort a.vars
                    ( List.map a.coeffs ~f:(fun c -> Q.neg (value c)),
                      value a.const,
                      false )) )))
  | CoeffSolver.No_solution -> decline "no atomic solution"
  | CoeffSolver.Unknown r -> decline "the coefficient solver: %s" r

(** {2 The entry point} *)

(* [solve ~search ~leaves ~solve_chc ~qelim ?coeff_mode ?timeout ~id sys].
   [leaves], [solve_chc] and [qelim] are [Interpolant.binary]'s, used by
   [Single_refutation]; [coeff_mode] is [CoeffSolver]'s, used by
   [Atomic_template]; [timeout] (milliseconds) bounds each Z3 question.
   Pre: [sys] recursion-free (else [Declined]), every application's
   predicate declared with its arity, formula parts quantifier-free.
   Post: [Solved theta] only after [is_solution sys theta]; [No_solution w]
   only from [Single_refutation]'s check of a goal under the least solution,
   which is exact for a recursion-free system, with [derivation_holds w]
   (the witness's clauses are those of the sliced system, a subset of
   [sys]'s); [Declined] otherwise. *)
let solve ~search ~leaves ~solve_chc ~qelim ?(coeff_mode = CoeffSolver.Z3)
    ?timeout ~id sys =
  try
    if not (is_recursion_free sys) then decline "recursive";
    let sliced, partial = slice sys in
    let result =
      match search with
      | Single_refutation ->
          single_refutation ~timeout ~id ~leaves ~solve_chc ~qelim sliced
      | Atomic_template -> atomic_template ~timeout ~id ~coeff_mode sliced
    in
    match result with
    | `No_solution w -> No_solution w
    | `Candidate theta ->
        let theta = partial @ theta in
        if is_solution ?timeout ~id sys theta then Solved theta
        else Declined "the candidate failed the whole-system check"
  with Decline reason -> Declined reason
