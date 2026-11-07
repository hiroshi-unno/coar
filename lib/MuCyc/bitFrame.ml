(* A propositional back-end for the cube checks of MuCyc's blocking loop over
   Booleans and fixed-width bit-vectors ([checker] below), and the [minisat]
   instance it is built on. *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

exception Decline of string

let decline fmt = ksprintf (fun s -> raise (Decline s)) fmt

let width_of = function
  | T_bool.SBool -> Some (1, true)
  | T_bv.SBV size -> Some (T_bv.bits_of size, false)
  | _ -> None

let now () = Time_float.(Span.to_sec (to_span_since_epoch (now ())))

(* A [minisat] instance with its variables allocated on demand.  With
   [COAR_BITS_DUMP_DIR=dir] in the environment, every clause added is also
   kept in [log], so that a check can be written out as DIMACS to be asked
   of another SAT solver (see [dump_check]); a diagnostic only *)
type sv = {
  s : Minisat.t;
  mutable next : int;
  log : Minisat.Lit.t list Queue.t option;
}

let bits_dump_dir = Sys.getenv "COAR_BITS_DUMP_DIR"

(* with [COAR_BITS_LEAF_STATS], one line per bit-blasted expression on
   stderr (when, its words, the tactics' time, the clauses and literals
   emitted) and one per solve of a check; a diagnostic only, cheaper than
   [COAR_BITS_DUMP_DIR]'s dumps *)
let bits_leaf_stats = Option.is_some (Sys.getenv "COAR_BITS_LEAF_STATS")
let bits_dump_count = Stdlib.Atomic.make 0

let mk_sv () =
  {
    s = Minisat.create ();
    next = 1;
    log = Option.map bits_dump_dir ~f:(fun _ -> Queue.create ());
  }

(* With [COAR_BITS_DUMP_DIR], writes the instance's clauses with each of
   [assumptions] as a unit clause to its own file [dir/bits_<pid>_<k>.cnf]
   (the directory must exist; k counts the run's dumps, at most 200) and
   prints its size on stderr; the file answers what [solve ~assumptions]
   would, except that minisat's level-0 simplifications are not in it.
   [extra] names the asker on the size line *)
let dump_check ?(extra = "") sv assumptions =
  match (bits_dump_dir, sv.log) with
  | Some dir, Some log ->
      let k = Stdlib.Atomic.fetch_and_add bits_dump_count 1 in
      if k < 200 then (
        let file =
          sprintf "%s/bits_%d_%d.cnf" dir (Pid.to_int (Core_unix.getpid ())) k
        in
        let nvars = sv.next - 1 in
        let nass = Array.length assumptions in
        Out_channel.with_file file ~f:(fun oc ->
            fprintf oc "c %s\np cnf %d %d\n" extra nvars
              (Queue.length log + nass);
            let lit = Minisat.Lit.to_string in
            Queue.iter log ~f:(fun cl ->
                Out_channel.output_string oc
                  (String.concat ~sep:" " (List.map cl ~f:lit) ^ " 0\n"));
            Array.iter assumptions ~f:(fun l ->
                Out_channel.output_string oc (lit l ^ " 0\n")));
        eprintf "BITS_DUMP %s vars=%d clauses=%d assumptions=%d %s\n%!" file
          nvars (Queue.length log) nass extra)
  | _ -> ()

let fresh sv =
  let l = Minisat.Lit.make sv.next in
  sv.next <- sv.next + 1;
  Minisat.ensure_lit_exists sv.s l;
  l

(* A clause addition that makes the instance unsatisfiable at level 0 leaves
   it so ([Minisat.okay] is then false): every later [solve] raises
   [Minisat.Unsat], which is the reading every caller wants *)
let add sv cl =
  Option.iter sv.log ~f:(fun q -> Queue.enqueue q cl);
  try Minisat.add_clause_l sv.s cl with Minisat.Unsat -> ()

let solve_under sv assumptions =
  match Minisat.solve ~assumptions sv.s with
  | () -> true
  | exception Minisat.Unsat -> false

let value sv l =
  match Minisat.value sv.s l with Minisat.V_true -> true | _ -> false

(* A propositional back-end for the cube checks of MuCyc's blocking loop.

   One [minisat] instance per domain holds, under a literal of its own, the
   positive encoding of every formula it was asked about: a conjunction's
   literal implies each member's, a disjunction's the disjunction of its
   members', and any other subformula (a leaf) is bit-blasted once, by Z3's
   tactics [simplify], [bit-blast] and [tseitin-cnf] over one literal per bit
   of each Boolean or bit-vector variable (shared by name and width with
   every other leaf), each resulting clause guarded by the leaf's literal;
   an existential's bound variables are renamed apart and its body encoded,
   and a [let] likewise, as an existential with the defining equation.
   A literal occurs negatively in its own clauses and positively only in the
   clauses of the formulas it is a member of, so assuming the literals of
   some formulas leaves the instance satisfiable exactly when their
   conjunction is (the leaves' auxiliary variables are fresh, and a CNF from
   [tseitin-cnf] is equisatisfiable with its goal): the formulas held but
   not assumed constrain nothing, as the kept Z3 solvers' selectors do.  A
   core of assumed literals is then a set of the assumed formulas whose
   conjunction has no model of bits, which, every bit-vector operator being
   a total function on bit strings, is no model at all.

   Declined ([Decline], and the caller asks Z3 instead): a variable of any
   other sort, a universal quantifier or one below a negation or inside a
   leaf, an uninterpreted or defined function, and
   anything bit-blasting leaves non-propositional.  A [minisat]
   call is not interrupted by MuCyc's timer; it returns first. *)
type checker = {
  cctx : Z3.context;
  csv : sv;
  cwords : (string * int, Minisat.Lit.t array) Hashtbl.t;
  cnodes : (Formula.t, Minisat.Lit.t) Hashtbl.t;
  mutable cbinders : int; (* existential nodes renamed so far *)
  mutable cwords_made : int; (* fresh words made for abstracted operators *)
  mutable cpending : nonlinear list;
      (* abstracted occurrences whose definition is not yet held *)
  cevals : (Formula.t, evaluation) Hashtbl.t;
      (* how [holds] evaluates a formula, made on first use *)
  ctemplates : (int, template) Hashtbl.t;
      (* the CNF templates of [blast_templated], by their expression's id *)
  cdomain : bool;
      (* whether a check decides only the cone of its assumptions (below) *)
  cadj : (int, int list) Hashtbl.t;
      (* with [cdomain]: for the variable of each node literal [l], the
         variables of the clauses added for [l] so far, [l]'s own aside
         (with repetitions); clauses added later for [l], such as a lazily
         added definition, are appended *)
  mutable cmark : int array;
      (* with [cdomain]: the check that last saw a variable *)
  mutable cepoch : int; (* with [cdomain]: the checks so far *)
  mutable cpinned : (int * int list) option;
      (* with [cdomain]: the variable of a pinned literal and its cone, kept
         decision variables across checks until another literal is pinned *)
  mutable cpinmark : bool array;
      (* with [cdomain]: the variables of the pinned cone *)
  mutable cpinfront : int list;
      (* with [cdomain]: variables of clauses added for a pinned variable
         since the pinned cone was last closed *)
  cdef_templates : bool;
      (* whether a definition [lazy_nonlinear] adds is encoded through
         [blast_templated] (see [checker_check]) *)
  cnl_relevant : bool;
      (* whether a round adds only the violated definitions the model's
         value of the assumed formulas depends on (see [nl_relevant]); the
         four tables below are filled only then *)
  cnl_nodes : (int, nl_node) Hashtbl.t;
      (* the members of each and/or node and each [let] node, by the
         variable of its literal *)
  cnl_leaves : (int, Z3.Expr.expr) Hashtbl.t;
      (* each leaf encoded with [lazy_nonlinear], abstracted, without its
         argument equalities, by the variable of its literal *)
  cnl_defs : (string, int) Hashtbl.t;
      (* the leaf [x = t] of each [let]-bound word [x], by [x] *)
  cnl_occs : (string, nonlinear) Hashtbl.t;
      (* each abstracted occurrence by its word [r] *)
  cnl_args : (string, Z3.Expr.expr) Hashtbl.t;
      (* the (abstracted) term each fresh argument word is held equal to *)
  cleaf_ctx : bool;
      (* whether the leaves of one encoding batch are bit-blasted in a Z3
         context of their own, dropped at the batch's end (see [in_batch]) *)
  mutable cbatch_depth : int; (* with [cleaf_ctx]: the open [in_batch]es *)
  mutable cbatch_ctx : Z3.context option;
      (* with [cleaf_ctx]: the open batch's context, made on its first leaf *)
}

(* a node of a checked formula as [nl_relevant] walks it: a conjunction or
   disjunction of member literals, or a [let] whose definition leaf is
   walked only from a read of its word, so only its body is a member *)
and nl_node = Conj of Minisat.Lit.t list | Disj of Minisat.Lit.t list | Let of Minisat.Lit.t

(* a leaf's CNF with its words renamed positionally (see
   [blast_templated]): the renamed expression, the placeholder literals of
   each word's bits, and the clauses over those and the placeholders of
   the auxiliaries *)
and template = {
  texpr : Z3.Expr.expr;
  tbits : Minisat.Lit.t array list;
  tclauses : Minisat.Lit.t list list;
}

(* An occurrence [r = op(a, b)] of a nonlinear operator abstracted in a
   leaf: [r] names a fresh word of [width] in [cwords]; an argument is the
   occurrence's own when it is a numeral, else a fresh word held equal to it
   under the leaf's literal [guard]; the definition itself is not held until
   a model violates it *)
and nonlinear = {
  guard : Minisat.Lit.t;
  op : Z3.FuncDecl.func_decl;
  width : int;
  r : string;
  a : arg;
  b : arg;
}

(* a numeral argument is kept as it is, so that a definition with one, once
   added, is the circuit the eager encoding builds for it (with the
   constant propagated), not that of the operator on two free words *)
and arg = Word of string | Num of Z3.Expr.expr

(* a formula as [holds] evaluates it: a word compared with a numeral
   ([positive] for [=], else [<>]; a Boolean word is one of width 1, a
   negated one compared with 0), decided on the value directly; a formula
   whose operators [compile] knows, by its evaluator; any other formula
   converted once, with its free constants (name, width, whether Boolean),
   substituted by numerals and simplified; [Unevaluable] when the
   conversion fails *)
and evaluation =
  | Compare of (string * int) * Z.t * bool
  | Native of ((string * int, Z.t) Hashtbl.t -> Z.t)
  | Ground of Z3.Expr.expr * (Z3.Expr.expr * string * int * bool) list
  | Unevaluable

external set_decision_var : Minisat.t -> int -> bool -> unit
  = "caml_bitframe_set_decision_var"

let checkers : checker option ref Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> ref None)

(* the checker of the calling domain.  One for the domain's lifetime: the
   variables' bits are shared by name and width only, and a check assumes
   only the literals of its own formulas, so formulas of other queries,
   predicates or problems held in the same instance change no answer *)
let checker ?(domain = false) ?(def_templates = false)
    ?(nl_relevant = false) ?(leaf_ctx = false) () =
  let r = Stdlib.Domain.DLS.get checkers in
  match !r with
  | Some c -> c
  | None ->
      let c =
        {
          cctx = Z3.mk_context [];
          csv = mk_sv ();
          cwords = Hashtbl.Poly.create ();
          cnodes = Common.Ext.Hashtbl.PolyDeep.create ();
          cbinders = 0;
          cwords_made = 0;
          cpending = [];
          cevals = Common.Ext.Hashtbl.PolyDeep.create ();
          ctemplates = Hashtbl.create (module Int);
          cdomain = domain;
          cadj = Hashtbl.create (module Int);
          cmark = [||];
          cepoch = 0;
          cpinned = None;
          cpinmark = [||];
          cpinfront = [];
          cdef_templates = def_templates;
          cnl_relevant = nl_relevant;
          cnl_nodes = Hashtbl.create (module Int);
          cnl_leaves = Hashtbl.create (module Int);
          cnl_defs = Hashtbl.create (module String);
          cnl_occs = Hashtbl.create (module String);
          cnl_args = Hashtbl.create (module String);
          cleaf_ctx = leaf_ctx;
          cbatch_depth = 0;
          cbatch_ctx = None;
        }
      in
      r := Some c;
      c

(* a fresh literal of [c]; with [cdomain] its variable is not a decision
   variable until a check whose cone holds it *)
let cfresh c =
  let l = fresh c.csv in
  if c.cdomain then set_decision_var c.csv.s (Minisat.Lit.to_int l) false;
  l

(* adds the clause [owner => cl] to [c]; with [cdomain], records that the
   clauses of the node literal [owner] mention the variables of [cl].  Every
   clause of [c] is added through it, guarded by a node literal: the domain
   restriction of [checker_check] relies on it *)
let cadd c owner cl =
  if c.cdomain then (
    let key = Minisat.Lit.to_int owner in
    let vs = List.map cl ~f:Minisat.Lit.to_int in
    if key < Array.length c.cpinmark && c.cpinmark.(key) then
      c.cpinfront <- List.rev_append vs c.cpinfront;
    Hashtbl.update c.cadj key ~f:(function
      | None -> vs
      | Some vs' -> List.rev_append vs vs'));
  add c.csv (Minisat.Lit.neg owner :: cl)

(* the names of the free constants of [e]; raises [Decline] on a quantifier
   or an application of a function symbol that is not interpreted *)
let free_consts e =
  let seen = Hashtbl.create (module Int) in
  let names = Hashtbl.create (module String) in
  let rec go e =
    let id = Z3.AST.get_id (Z3.Expr.ast_of_expr e) in
    if not (Hashtbl.mem seen id) then (
      Hashtbl.set seen ~key:id ~data:();
      if Z3.AST.is_quantifier (Z3.Expr.ast_of_expr e) then
        decline "a quantifier"
      else if
        Z3.Expr.is_numeral e || Z3.Boolean.is_true e || Z3.Boolean.is_false e
      then ()
      else if Z3.Expr.is_const e then
        Hashtbl.set names
          ~key:
            (Z3.Symbol.to_string
               (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e)))
          ~data:()
      else
        match Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl e) with
        | Z3enums.OP_UNINTERPRETED ->
            decline "the function %s"
              (Z3.Symbol.to_string
                 (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e)))
        | _ -> List.iter (Z3.Expr.get_args e) ~f:go)
  in
  go e;
  names

(* Adds [emit cl] for each clause of a CNF goal [g] of [ctx] over minisat
   literals, read from Z3's DIMACS print of the goal
   ([Z3_goal_to_dimacs_string] with names; Z3's [display_dimacs], read in
   its 5.1.0 source): a header [p cnf V C], one line per formula of the goal
   in its order with the literals in the order of the formula's disjuncts
   ([false] left out, [true] as [1 -1]), then one line [c v name] per atom.
   An atom named by [bit] is that bit, [true] and [false] are the
   constants, and [k!n] -- the name Z3 prints for a fresh constant made
   with no prefix, which is how [tseitin-cnf] makes its auxiliary variables
   -- is an auxiliary variable, given a fresh literal at its first
   occurrence.  The clauses, and the order in which the auxiliary literals
   are made, are those of a walk over the goal's formulas (the caller's
   fallback), except that a clause of the goal holding [true] comes as a
   tautology instead of not at all, which [minisat] drops on addition.
   Returns [false], having emitted nothing and made no literal, when Z3
   declines the print (a goal not in CNF), when an atom has any other name
   (the walk then classifies it, or declines) or no name line, or when the
   text is not of this shape: the whole text is checked before the first
   clause is emitted.  The point is the cost: the walk makes several calls
   into the bindings per literal occurrence, the print one per goal, and
   the clauses are emitted one at a time rather than held. *)
let dimacs_clauses ~aux:fresh_aux ctx g ~bit ~emit =
  match
    try
      Some
        (Z3native.goal_to_dimacs_string
           (Obj.magic ctx : Z3native.context)
           (Obj.magic g : Z3native.goal)
           true)
    with Z3.Error _ -> None
  with
  | None -> false
  | Some s -> (
      let n = String.length s in
      let pos = ref 0 in
      let expect str =
        let k = String.length str in
        if !pos + k <= n && String.equal (String.sub s ~pos:!pos ~len:k) str
        then pos := !pos + k
        else raise Exit
      in
      let int () =
        while !pos < n && Char.equal s.[!pos] ' ' do
          incr pos
        done;
        let neg = !pos < n && Char.equal s.[!pos] '-' in
        if neg then incr pos;
        let start = !pos in
        let v = ref 0 in
        while !pos < n && Char.is_digit s.[!pos] do
          v := (!v * 10) + Char.get_digit_exn s.[!pos];
          incr pos
        done;
        if !pos = start then raise Exit;
        if neg then - !v else !v
      in
      let eol () =
        while !pos < n && Char.equal s.[!pos] ' ' do
          incr pos
        done;
        if !pos < n then
          if Char.equal s.[!pos] '\n' then incr pos else raise Exit
      in
      let is_aux name =
        String.length name > 2
        && String.is_prefix name ~prefix:"k!"
        && String.for_all (String.drop_prefix name 2) ~f:Char.is_digit
      in
      (* the clause lines from [!pos]: [f] on each literal, [line] at each
         line's end *)
      let clauses nv nc ~f ~line =
        for _ = 1 to nc do
          let rec lits () =
            match int () with
            | 0 -> ()
            | x when x < -nv || x > nv -> raise Exit
            | x ->
                f x;
                lits ()
          in
          lits ();
          eol ();
          line ()
        done
      in
      try
        expect "p cnf ";
        let nv = int () in
        let nc = int () in
        eol ();
        let start = !pos in
        (* a clause line holds digits, signs and spaces only *)
        let defs =
          match
            String.substr_index s ~pos:(Int.max 0 (start - 1)) ~pattern:"\nc "
          with
          | Some i -> i + 1
          | None -> n
        in
        pos := defs;
        let atoms = Array.create ~len:(nv + 1) None in
        while !pos < n do
          expect "c ";
          let v = int () in
          expect " ";
          let stop = Option.value ~default:n (String.index_from s !pos '\n') in
          let name = String.sub s ~pos:!pos ~len:(stop - !pos) in
          pos := Int.min n (stop + 1);
          if v < 1 || v > nv || Option.is_some atoms.(v) then raise Exit;
          atoms.(v) <-
            Some
              (match bit name with
              | Some l -> `Lit l
              | None ->
                  if String.equal name "true" then `True
                  else if String.equal name "false" then `False
                  else if is_aux name then `Aux
                  else raise Exit)
        done;
        (* every atom is to be named: a print whose atoms all have numeric
           names (auxiliaries only) numbers them by those names and prints
           no name lines *)
        for v = 1 to nv do
          if Option.is_none atoms.(v) then raise Exit
        done;
        pos := start;
        clauses nv nc ~f:ignore ~line:ignore;
        if !pos <> defs then raise Exit;
        pos := start;
        let aux = Array.create ~len:(nv + 1) None in
        let atom v =
          match atoms.(v) with
          | Some (`Lit l) -> `Lit l
          | Some `True -> `True
          | Some `False -> `False
          | Some `Aux | None -> (
              match aux.(v) with
              | Some l -> `Lit l
              | None ->
                  let l = fresh_aux () in
                  aux.(v) <- Some l;
                  `Lit l)
        in
        let neg = function
          | `True -> `False
          | `False -> `True
          | `Lit l -> `Lit (Minisat.Lit.neg l)
        in
        let acc = ref [] and sat = ref false in
        clauses nv nc
          ~f:(fun x ->
            if not !sat then
              match if x < 0 then neg (atom (-x)) else atom x with
              | `True -> sat := true
              | `False -> ()
              | `Lit l -> acc := l :: !acc)
          ~line:(fun () ->
            if not !sat then emit !acc;
            acc := [];
            sat := false);
        true
      with Exit -> false)

(* With [COAR_BITS_DUMP_DIR], writes the goal [goal] handed to the leaf
   tactics as an SMT-LIB script [dir/leaf_<pid>_<k>.smt2] (k counts the
   run's leaves; written for the first 200 and for any leaf whose tactics
   took 50 ms or more) and prints on stderr its file and the seconds
   [secs] the tactics took on it, so that a slow leaf can be bit-blasted
   again outside the solver under other tactics; a diagnostic only *)
let leaf_dump_count = Stdlib.Atomic.make 0

let dump_leaf ctx goal secs =
  match bits_dump_dir with
  | Some dir ->
      let k = Stdlib.Atomic.fetch_and_add leaf_dump_count 1 in
      let file =
        sprintf "%s/leaf_%d_%d.smt2" dir (Pid.to_int (Core_unix.getpid ())) k
      in
      if k < 200 || Float.(secs >= 0.05) then (
        let s = Z3.Solver.mk_simple_solver ctx in
        Z3.Solver.add s (Z3.Goal.get_formulas goal);
        Out_channel.write_all file ~data:(Z3.Solver.to_string s));
      eprintf "leaf-dump %s %.3f s\n%!" file secs
  | None -> ()

(* Emits a CNF of a Boolean expression [e] of [ctx] whose free constants
   are the words [words] (name, width, whether Boolean): the [i]th word is
   replaced by its bits [bits i name width], and the result bit-blasted by
   Z3's tactics [simplify], [bit-blast] and [tseitin-cnf], each auxiliary
   of the CNF becoming a literal made by [aux]; the clauses, over those bits
   and auxiliaries, are equisatisfiable with [e] (every model of [e]'s bits
   extends to the auxiliaries, and every model of the clauses is one of
   [e]).  Raises [Decline], having emitted nothing, when that leaves more
   than one subgoal or a non-propositional term *)
let blast_with ctx ~bits:bits_of ~aux:fresh_aux ~emit e
    words =
  let blast_started = now () in
  let n_clauses = ref 0 and n_lits = ref 0 in
  let emit =
    if bits_leaf_stats then (fun cl ->
      incr n_clauses;
      n_lits := !n_lits + List.length cl;
      emit cl)
    else emit
  in
  (* the bits' constants by name, for the DIMACS print of the CNF, and by
     AST id, for the walk over it that reads them back without asking Z3 for
     their names; [bit_consts] keeps them alive to the end, so that no
     constant the tactics create can be given the id of one freed meanwhile *)
  let bit_ids = Hashtbl.create (module Int) in
  let bit_names = Hashtbl.create (module String) in
  let bit_consts = ref [] in
  let from, into =
    List.unzip
    @@ List.mapi words ~f:(fun i (name, w, is_bool) ->
        let bits = bits_of i name w in
        let word =
          let sym = Z3.Symbol.mk_string ctx name in
          if is_bool then Z3.Boolean.mk_const ctx sym
          else Z3.Expr.mk_const ctx sym (Z3.BitVector.mk_sort ctx w)
        in
        let b k =
          let bname = sprintf "bfc!%s!%d!b%d" name w k in
          Hashtbl.set bit_names ~key:bname ~data:bits.(k);
          let bc = Z3.Boolean.mk_const_s ctx bname in
          Hashtbl.set bit_ids
            ~key:(Z3.AST.get_id (Z3.Expr.ast_of_expr bc))
            ~data:bits.(k);
          bit_consts := bc :: !bit_consts;
          bc
        in
        let blasted =
          if is_bool then b 0
          else
            let one = Z3.BitVector.mk_numeral ctx "1" 1 in
            let zero = Z3.BitVector.mk_numeral ctx "0" 1 in
            let bit k = Z3.Boolean.mk_ite ctx (b k) one zero in
            List.fold
              (List.init (w - 1) ~f:(fun j -> w - 2 - j))
              ~init:(bit (w - 1))
              ~f:(fun acc k -> Z3.BitVector.mk_concat ctx acc (bit k))
        in
        (word, blasted))
  in
  let goal = Z3.Goal.mk_goal ctx false false false in
  Z3.Goal.add goal [ Z3.Expr.substitute e from into ];
  let t = Z3.Tactic.mk_tactic ctx in
  let started = now () in
  let res =
    try
      Z3.Tactic.apply
        (Z3.Tactic.and_then ctx (t "simplify") (t "bit-blast")
           [ t "tseitin-cnf" ])
        goal None
    with Z3.Error msg -> decline "bit-blasting: %s" msg
  in
  let tactic_done = now () in
  dump_leaf ctx goal (tactic_done -. started);
  let dumped = now () in
  if Z3.Tactic.ApplyResult.get_num_subgoals res <> 1 then
    decline "bit-blasting gave %d subgoals"
      (Z3.Tactic.ApplyResult.get_num_subgoals res);
  let g = Z3.Tactic.ApplyResult.get_subgoal res 0 in
  let walked () =
    let aux_lits = Hashtbl.create (module Int) in
    List.filter_map (Z3.Goal.get_formulas g) ~f:(fun f ->
        let lits = if Z3.Boolean.is_or f then Z3.Expr.get_args f else [ f ] in
        let rec go acc = function
          | [] -> Some acc
          | e :: es -> (
              let atom e =
                let id = Z3.AST.get_id (Z3.Expr.ast_of_expr e) in
                match Hashtbl.find bit_ids id with
                | Some l -> `Lit l
                | None -> (
                    match Hashtbl.find aux_lits id with
                    | Some l -> `Lit l
                    | None ->
                        if Z3.Boolean.is_true e then `True
                        else if Z3.Boolean.is_false e then `False
                        else if Z3.Expr.is_const e && Z3.Boolean.is_bool e then (
                          let l = fresh_aux () in
                          Hashtbl.set aux_lits ~key:id ~data:l;
                          `Lit l)
                        else
                          decline
                            "bit-blasting left a non-propositional term %s"
                            (Z3.Expr.to_string e))
              in
              let neg = function
                | `True -> `False
                | `False -> `True
                | `Lit l -> `Lit (Minisat.Lit.neg l)
              in
              let a =
                if Z3.Boolean.is_not e then
                  neg (atom (List.hd_exn (Z3.Expr.get_args e)))
                else atom e
              in
              match a with
              | `True -> None
              | `False -> go acc es
              | `Lit l -> go (l :: acc) es)
        in
        go [] lits)
  in
  if
    not
      (dimacs_clauses ~aux:fresh_aux ctx g ~bit:(Hashtbl.find bit_names) ~emit)
  then List.iter (walked ()) ~f:emit;
  (* with [COAR_BITS_DUMP_DIR], the leaf's bit-blast by part: the whole
     (less the dump), building the words' bits and the substitution, and
     the read-back of the clauses after the tactics; a diagnostic only *)
  if Option.is_some bits_dump_dir then
    eprintf
      "leaf-total %.3f s before-tactic %.3f s after-tactic %.3f s dump %.3f s\n%!"
      (now () -. blast_started -. (dumped -. tactic_done))
      (started -. blast_started) (now () -. dumped) (dumped -. tactic_done);
  if bits_leaf_stats then
    eprintf
      "leaf-stats at=%.3f op=%s words=%d bits=%d tactic=%.3f total=%.3f clauses=%d lits=%d z3mem=%d\n%!"
      (now ())
      (Z3.Symbol.to_string (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e)))
      (List.length words)
      (List.sum (module Int) words ~f:(fun (_, w, _) -> w))
      (tactic_done -. started) (now () -. blast_started) !n_clauses !n_lits
      (Int64.to_int_exn (Z3.Statistics.get_estimated_alloc_size ())
      / 1_000_000);
  ignore (Stdlib.Sys.opaque_identity !bit_consts)

(* the bits of the word [name] of width [w] in [cwords], made on first use *)
let word_bits c name w =
  Hashtbl.find_or_add c.cwords (name, w) ~default:(fun () ->
      Array.init w ~f:(fun _ -> cfresh c))

(* Adds the clauses [lit => e] for a Boolean expression [e] of [c]'s
   context whose free constants are the words [words]: [blast_with] over
   their bits in [cwords] and auxiliaries fresh in [c]'s instance, each
   clause guarded by [lit] *)
(* With [cleaf_ctx], [f] is an encoding batch: the leaves bit-blasted while
   it runs (nested batches joining the outermost) are bit-blasted in one
   Z3 context of their own, made on the batch's first leaf and dropped when
   the outermost batch ends, normally or by an exception.  A Z3 context is
   deleted only once the OCaml finalizers of all its objects have run, so
   the end of a batch that made a context runs one full major collection;
   without it the tactics' allocations of every batch stay (17 to 18 MB per
   large leaf were seen kept until the process ran out of memory).  The
   checker's own context then keeps only the leaves' word-level
   expressions, not what the bit-blasting tactics made of them.  Without
   [cleaf_ctx], [f] runs as it is *)
let in_batch c f =
  if not c.cleaf_ctx then f ()
  else (
    c.cbatch_depth <- c.cbatch_depth + 1;
    let release () =
      c.cbatch_depth <- c.cbatch_depth - 1;
      if c.cbatch_depth = 0 && Option.is_some c.cbatch_ctx then (
        c.cbatch_ctx <- None;
        Common.PhaseTime.event "blk-bits-leaf-ctx-dropped";
        Common.PhaseTime.with_phase "leaf-ctx-gc" Stdlib.Gc.full_major;
        if bits_leaf_stats then
          eprintf "leaf-ctx-released z3mem=%d\n%!"
            (Int64.to_int_exn (Z3.Statistics.get_estimated_alloc_size ())
            / 1_000_000))
    in
    match f () with
    | r ->
        release ();
        r
    | exception exn_ ->
        release ();
        raise exn_)

(* the context to bit-blast the expression [e] of [c]'s context in, and
   [e] there: inside an open batch of [cleaf_ctx], the batch's context and
   [e] printed as SMT-LIB and read back, the same term over constants of
   the same names and sorts (so [blast_with]'s substitution of the words'
   bits, made by name, still covers every free constant); otherwise [c]'s
   context and [e] itself.  [Z3.Expr.translate] is not used: the OCaml
   binding wraps its result as an object of the source context, so later
   calls on it run against the wrong context *)
let leaf_ctx c e =
  if c.cbatch_depth = 0 then (c.cctx, e)
  else
    let ctx =
      match c.cbatch_ctx with
      | Some ctx -> ctx
      | None ->
          let ctx = Z3.mk_context [] in
          c.cbatch_ctx <- Some ctx;
          ctx
    in
    Common.PhaseTime.with_phase "leaf-ctx-transfer" @@ fun () ->
    let text =
      let s = Z3.Solver.mk_simple_solver c.cctx in
      Z3.Solver.add s [ e ];
      Z3.Solver.to_string s
    in
    match Z3.SMT.parse_smtlib2_string ctx text [] [] [] [] with
    | v -> (
        match Z3.AST.ASTVector.to_expr_list v with
        | [ e' ] -> (ctx, e')
        | es -> (ctx, Z3.Boolean.mk_and ctx es))
    | exception Z3.Error msg -> decline "leaf transfer: %s" msg

let blast c lit e words =
  let ctx, e = leaf_ctx c e in
  blast_with ctx
    ~bits:(fun _ name w -> word_bits c name w)
    ~aux:(fun () -> cfresh c)
    ~emit:(cadd c lit)
    e words

(* [blast c lit e words] through a CNF kept per shape of [e]: the words are
   renamed positionally ([i]th word to [bft!i] of the same sort), and the
   renamed expression, which Z3 hash-conses, identifies a template, the
   clauses [blast_with] gives for it over placeholder literals (the bits of
   the [i]th word, then the auxiliaries, none of them [c]'s variables).  A
   leaf whose renamed expression is a template's is given that template's
   clauses with the placeholders of the [i]th word's bits replaced by the
   [i]th word's bits in [cwords] and the auxiliaries by fresh literals, each
   clause guarded by [lit], without asking Z3.  Renaming every variable of
   a CNF apart from the rest keeps it equisatisfiable with the renamed
   formula, and the renaming of words is a bijection between the leaf's
   words and the template's (every free constant of [e] is a word, so the
   renamed expression's are exactly [bft!0], [bft!1], ...): the clauses
   added are a CNF of [lit => e] as [blast]'s are, though not necessarily
   the same CNF (Z3's [simplify] orders arguments by AST id, which the
   renaming changes).  A template holds its expression, so that no other
   expression is given its id while it is kept *)
let blast_templated c lit e words =
  let ctx = c.cctx in
  let const (name, w, is_bool) =
    let sym = Z3.Symbol.mk_string ctx name in
    if is_bool then Z3.Boolean.mk_const ctx sym
    else Z3.Expr.mk_const ctx sym (Z3.BitVector.mk_sort ctx w)
  in
  let canon =
    List.mapi words ~f:(fun i (_, w, is_bool) -> (sprintf "bft!%d" i, w, is_bool))
  in
  let ce =
    Common.PhaseTime.with_phase "leaf-template-rename" (fun () ->
        Z3.Expr.substitute e (List.map words ~f:const) (List.map canon ~f:const))
  in
  let t =
    Hashtbl.find_or_add c.ctemplates
      (Z3.AST.get_id (Z3.Expr.ast_of_expr ce))
      ~default:(fun () ->
        Common.PhaseTime.event "blk-bits-template-made";
        let next = ref 0 in
        let placeholder () =
          incr next;
          Minisat.Lit.make !next
        in
        let tbits =
          List.map canon ~f:(fun (_, w, _) ->
              Array.init w ~f:(fun _ -> placeholder ()))
        in
        let tbits_a = Array.of_list tbits in
        let clauses = ref [] in
        Common.PhaseTime.with_phase "leaf-template-make" (fun () ->
            let ctx, ce = leaf_ctx c ce in
            blast_with ctx
              ~bits:(fun i _ _ -> tbits_a.(i))
              ~aux:placeholder
              ~emit:(fun cl -> clauses := cl :: !clauses)
              ce canon);
        { texpr = ce; tbits; tclauses = List.rev !clauses })
  in
  Common.PhaseTime.event "blk-bits-template-used";
  Common.PhaseTime.with_phase "leaf-template-inst" @@ fun () ->
  let real = Hashtbl.create (module Int) in
  List.iter2_exn t.tbits words ~f:(fun tb (name, w, _) ->
      let bits = word_bits c name w in
      Array.iteri tb ~f:(fun k l ->
          Hashtbl.set real ~key:(Minisat.Lit.to_int l) ~data:bits.(k)));
  let inst l =
    let r =
      Hashtbl.find_or_add real
        (Minisat.Lit.to_int (Minisat.Lit.abs l))
        ~default:(fun () -> cfresh c)
    in
    Minisat.Lit.apply_sign (Minisat.Lit.sign l) r
  in
  List.iter t.tclauses ~f:(fun cl ->
      cadd c lit (List.map cl ~f:inst))

(* whether [abstract] replaces an application of the operator of kind [k]
   whose arguments are [t] and [u] (SMT-LIB defines each such operator on
   every pair of bit strings, division and remainder by zero included).
   Only applications whose circuit is quadratic in the width are replaced:
   a division or remainder unless both arguments are numerals (Z3
   bit-blasts it as a restoring divider, one subtractor row per bit,
   whatever the divisor's value), and a multiplication of two non-numerals.
   A multiplication by a numeral [c] is linear: Z3's array multiplier drops
   the rows of [c]'s zero bits, leaving one adder row per one bit, no more
   than the additions around it, which are never replaced; replacing it
   would only cut [simplify]'s rewriting across it and leave the SAT
   solver a free word to search. *)
let abstracted_kind k t u =
  match k with
  | Z3enums.OP_BMUL ->
      not (Z3.Expr.is_numeral t || Z3.Expr.is_numeral u)
  | Z3enums.OP_BUDIV | Z3enums.OP_BUREM | Z3enums.OP_BSDIV | Z3enums.OP_BSREM
  | Z3enums.OP_BSMOD ->
      not (Z3.Expr.is_numeral t && Z3.Expr.is_numeral u)
  | _ -> false

(* [e] with each distinct (by AST id) binary application that
   [abstracted_kind] selects replaced by a fresh word [r], conjoined with [a = t'] for a fresh word
   [a] and each argument [t] that is not a numeral, so rewritten; the fresh
   words, and the occurrences (pending, guarded by [lit]), are returned.  Every model of [e] extends to one of the result
   (give [a], [b], [r] the values of [t], [u] and the application, inner
   occurrences first), and a model of the result that also satisfies every
   occurrence's definition [r = op(a, b)] is one of [e]; so the result is
   an over-approximation of [e] that becomes exact as definitions are
   added.  A ground application is left to [simplify], which folds it. *)
let abstract c lit e =
  let ctx = c.cctx in
  let memo = Hashtbl.create (module Int) in
  let eqs = ref [] and words = ref [] and occs = ref [] in
  let word w =
    c.cwords_made <- c.cwords_made + 1;
    let name = sprintf "bfn!%d" c.cwords_made in
    words := (name, w, false) :: !words;
    (name, Z3.Expr.mk_const_s ctx name (Z3.BitVector.mk_sort ctx w))
  in
  let rec go e =
    let id = Z3.AST.get_id (Z3.Expr.ast_of_expr e) in
    match Hashtbl.find memo id with
    | Some e' -> e'
    | None ->
        let e' =
          if Z3.Expr.get_num_args e = 0 then e
          else
            let args = Z3.Expr.get_args e in
            let args' = List.map args ~f:go in
            let d = Z3.Expr.get_func_decl e in
            match args with
            | [ t; u ]
              when abstracted_kind (Z3.FuncDecl.get_decl_kind d) t u ->
                Common.PhaseTime.event "blk-bits-nl-abstracted";
                if Z3.Expr.is_numeral t || Z3.Expr.is_numeral u then
                  Common.PhaseTime.event "blk-bits-nl-abstracted-numeral-arg";
                let width = Z3.BitVector.get_size (Z3.Expr.get_sort e) in
                let r, rw = word width in
                let arg t' =
                  if Z3.Expr.is_numeral t' then Num t'
                  else
                    let n, w = word width in
                    eqs := (n, t', Z3.Boolean.mk_eq ctx w t') :: !eqs;
                    Word n
                in
                let a = arg (List.nth_exn args' 0) in
                let b = arg (List.nth_exn args' 1) in
                occs := { guard = lit; op = d; width; r; a; b } :: !occs;
                rw
            | _ ->
                if
                  List.for_all2_exn args args' ~f:(fun x y ->
                      Z3.AST.equal (Z3.Expr.ast_of_expr x)
                        (Z3.Expr.ast_of_expr y))
                then e
                else Z3.Expr.update e args'
        in
        Hashtbl.set memo ~key:id ~data:e';
        e'
  in
  let main = go e in
  let e' =
    if List.is_empty !eqs then main
    else
      Z3.Boolean.mk_and ctx (main :: List.map !eqs ~f:(fun (_, _, eq) -> eq))
  in
  if c.cnl_relevant then (
    Hashtbl.set c.cnl_leaves ~key:(Minisat.Lit.to_int lit) ~data:main;
    List.iter !eqs ~f:(fun (n, t', _) -> Hashtbl.set c.cnl_args ~key:n ~data:t');
    List.iter !occs ~f:(fun o -> Hashtbl.set c.cnl_occs ~key:o.r ~data:o));
  (e', !words, !occs)

(* the guarded clauses [lit => phi] of a leaf [phi]; with [lazy_nonlinear],
   of its [abstract]ion, the occurrences abstracted being added to
   [cpending] *)
(* the bound variables of the formulas a checker encodes are renamed to
   names with this prefix, drawn from [cbinders]; no formula given to a
   checker mentions one *)
let witness_prefix = "bfq!"
let is_witness_name x = String.is_prefix (Ident.name_of_tvar x) ~prefix:witness_prefix

let encode_leaf ?(lazy_nonlinear = false) ?(leaf_templates = false) c lit
    phi =
  let blast = if leaf_templates then blast_templated else blast in
  let ctx = c.cctx in
  let senv =
    Common.PhaseTime.with_phase "leaf-senv" (fun () ->
        Set.to_list (Formula.term_sort_env_of phi))
  in
  let e =
    Common.PhaseTime.with_phase "leaf-convert" (fun () ->
        try
          Z3Smt.Z3interface.of_formula ~id:None ctx [] [] Map.Poly.empty
            Set.Poly.empty phi
        with
        | Decline _ as exn_ -> raise exn_
        | exn_ when not (Common.Timer.is_async exn_) ->
            decline "conversion: %s" (Exn.to_string exn_))
  in
  let consts = Common.PhaseTime.with_phase "leaf-consts" (fun () -> free_consts e) in
  let words =
    List.map senv ~f:(fun (v, s) ->
        let name = Ident.name_of_tvar v in
        let w, is_bool =
          match width_of s with
          | Some wb -> wb
          | None -> decline "variable %s of sort %s" name (Term.str_of_sort s)
        in
        Hashtbl.remove consts name;
        (name, w, is_bool))
  in
  (* a constant the conversion named otherwise than the variable would be
     left unconstrained by the bits *)
  (match Hashtbl.keys consts with
  | [] -> ()
  | n :: _ -> decline "a constant %s not among the formula's variables" n);
  Common.PhaseTime.with_phase "leaf-blast" (fun () ->
      if lazy_nonlinear then (
        let e', fresh_words, occs = abstract c lit e in
        blast c lit e' (words @ fresh_words);
        c.cpending <- occs @ c.cpending)
      else blast c lit e words)

(* the value of the word [name] of [width] in the last model *)
let word_value c name width =
  Array.foldi
    (Hashtbl.find_exn c.cwords (name, width))
    ~init:Z.zero
    ~f:(fun k acc l ->
      if value c.csv l then Z.(acc + shift_left one k) else acc)

(* whether the last model satisfies [o]'s definition (Z3's rewriter on the
   numerals) *)
let defined c o =
  let num = function
    | Num e -> e
    | Word name ->
        Z3.BitVector.mk_numeral c.cctx
          (Z.to_string (word_value c name o.width))
          o.width
  in
  let v = Z3.Expr.simplify (Z3.FuncDecl.apply o.op [ num o.a; num o.b ]) None in
  Z3.Expr.is_numeral v
  && Z.equal
       (Z.of_string (Z3.BitVector.numeral_to_string v))
       (word_value c o.r o.width)

(* The words [r] of the abstracted occurrences the last model's value of
   the formulas of [assumed] depends on, or [None] when the walk meets a
   literal or node it does not know (the caller then adds every violated
   definition).

   The walk starts at the assumed literals and descends through the nodes:
   every member of a conjunction, the first true member of a disjunction,
   the body of a [let] (its definition leaf [x = t] is entered only when a
   read of [x] is reached), and each leaf so reached ([cnl_leaves]).  Inside
   a leaf it computes the model's value of each node (the words' values,
   Z3's rewriter on numerals) and enters: the selected branch of an [ite];
   for a conjunction, [bvand] or [bvmul] whose value is zero (false), one
   argument whose value is zero, for a disjunction or [bvor] whose value is
   all ones (true), one argument of that value; every argument otherwise.
   Reaching a word [r] enters the terms its argument words are held equal
   to ([cnl_args]); reaching a [let]-bound word enters its definition leaf.

   Contract: if the last model satisfies the clauses of [c] and the
   definition of every occurrence returned, then the assumed formulas hold
   for the model's values of their free words.  Proof sketch: give each
   [let]-bound word and each abstracted word that is not reached the value
   of its definition, innermost first (the [let] nests are acyclic, each
   bound word has one definition leaf, and each [r] and argument word
   occurs in one leaf only).  This changes no reached word.  By induction on
   the walk, each reached node's value is the value of the node it stands
   for under the new assignment: an entered argument determines the value
   of an absorbing operation, an [ite] the value of its selected branch, a
   returned [r] is its operator on its arguments' values, and a reached
   [let]-bound word equals its definition, which is walked.  So each
   reached leaf holds (its literal is true, and the leaf's clauses force its
   abstraction), each unreached definition leaf holds by construction, and
   by the node structure the assumed formulas hold.  The free words keep
   their values, so a model read from them ([last_model]) is unchanged. *)
let nl_relevant c assumed =
  let ctx = c.cctx in
  let vals = Hashtbl.create (module Int) in
  let marked = Hash_set.create (module Int) in
  let reached = Hash_set.create (module String) in
  let n_leaves = ref 0 and n_nodes = ref 0 in
  let fail () = raise Stdlib.Exit in
  let is_value v =
    Z3.Expr.is_numeral v || Z3.Boolean.is_true v || Z3.Boolean.is_false v
  in
  let name_of e =
    Z3.Symbol.to_string (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e))
  in
  let width_bool e =
    let s = Z3.Expr.get_sort e in
    if Z3.Boolean.is_bool e then (1, true)
    else if Stdlib.(Z3.Sort.get_sort_kind s = Z3enums.BV_SORT) then
      (Z3.BitVector.get_size s, false)
    else fail ()
  in
  let rec ev e =
    let id = Z3.AST.get_id (Z3.Expr.ast_of_expr e) in
    match Hashtbl.find vals id with
    | Some v -> v
    | None ->
        let v =
          if is_value e then e
          else if
            not
              (match Z3.AST.get_ast_kind (Z3.Expr.ast_of_expr e) with
              | Z3enums.APP_AST -> true
              | _ -> false)
          then fail ()
          else if Z3.Expr.get_num_args e = 0 then (
            let w, is_bool = width_bool e in
            match Hashtbl.find c.cwords (name_of e, w) with
            | None -> fail ()
            | Some _ ->
                let v = word_value c (name_of e) w in
                if is_bool then Z3.Boolean.mk_val ctx (not (Z.equal v Z.zero))
                else Z3.BitVector.mk_numeral ctx (Z.to_string v) w)
          else if Z3.Boolean.is_ite e then
            match Z3.Expr.get_args e with
            | [ cnd; x; y ] ->
                let cv = ev cnd in
                if Z3.Boolean.is_true cv then ev x
                else if Z3.Boolean.is_false cv then ev y
                else fail ()
            | _ -> fail ()
          else
            let v =
              Z3.Expr.simplify
                (Z3.FuncDecl.apply (Z3.Expr.get_func_decl e)
                   (List.map (Z3.Expr.get_args e) ~f:ev))
                None
            in
            if is_value v then v else fail ()
        in
        Hashtbl.set vals ~key:id ~data:v;
        v
  in
  let num_is v ~ones =
    Z3.Expr.is_numeral v
    &&
    let n = Z.of_string (Z3.BitVector.numeral_to_string v) in
    if ones then
      Z.equal n Z.(shift_left one (Z3.BitVector.get_size (Z3.Expr.get_sort v)) - one)
    else Z.equal n Z.zero
  in
  let rec mark e =
    let id = Z3.AST.get_id (Z3.Expr.ast_of_expr e) in
    if not (Hash_set.mem marked id) then (
      Hash_set.add marked id;
      if is_value e then ()
      else if Z3.Expr.get_num_args e = 0 then (
        let n = name_of e in
        (match Hashtbl.find c.cnl_occs n with
        | Some o when not (Hash_set.mem reached n) ->
            Hash_set.add reached n;
            List.iter [ o.a; o.b ] ~f:(function
              | Num _ -> ()
              | Word a -> (
                  match Hashtbl.find c.cnl_args a with
                  | Some t -> mark t
                  | None -> fail ()))
        | _ -> ());
        match Hashtbl.find c.cnl_defs n with
        | Some d -> leaf d
        | None -> ())
      else if Z3.Boolean.is_ite e then (
        match Z3.Expr.get_args e with
        | [ cnd; x; y ] ->
            mark cnd;
            if Z3.Boolean.is_true (ev cnd) then mark x else mark y
        | _ -> fail ())
      else
        let args = Z3.Expr.get_args e in
        let absorbing =
          match Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl e) with
          | Z3enums.OP_AND -> Some Z3.Boolean.is_false
          | Z3enums.OP_OR -> Some Z3.Boolean.is_true
          | Z3enums.OP_BAND | Z3enums.OP_BMUL -> Some (num_is ~ones:false)
          | Z3enums.OP_BOR -> Some (num_is ~ones:true)
          | _ -> None
        in
        match absorbing with
        | Some absorbs when absorbs (ev e) -> (
            let cands = List.filter args ~f:(fun a -> absorbs (ev a)) in
            match
              List.find cands ~f:(fun a ->
                  Hash_set.mem marked (Z3.AST.get_id (Z3.Expr.ast_of_expr a)))
            with
            | Some _ -> ()
            | None -> (
                match cands with a :: _ -> mark a | [] -> List.iter args ~f:mark))
        | _ -> List.iter args ~f:mark)
  and leaf key =
    match Hashtbl.find c.cnl_leaves key with
    | Some e ->
        incr n_leaves;
        (* the leaf's literal is true, so its clauses force the
           abstraction; a value other than true means the model's words do
           not determine it (bits the CNF left unconstrained) *)
        if not (Z3.Boolean.is_true (ev e)) then (
          if bits_leaf_stats then
            eprintf "nl-relevant leaf-not-true %s\n%!"
              (String.prefix (Z3.Expr.to_string e) 200);
          fail ());
        mark e
    | None -> fail ()
  in
  let seen = Hash_set.create (module Int) in
  let rec node l =
    let key = Minisat.Lit.to_int l in
    if not (Hash_set.mem seen key) then (
      Hash_set.add seen key;
      incr n_nodes;
      match Hashtbl.find c.cnl_nodes key with
      | Some (Conj ms) -> List.iter ms ~f:node
      | Some (Disj ms) -> (
          match List.find ms ~f:(value c.csv) with
          | Some m -> node m
          | None -> fail ())
      | Some (Let b) -> node b
      | None -> leaf key)
  in
  match List.iter assumed ~f:node with
  | () ->
      if bits_leaf_stats then
        eprintf "nl-relevant walk assumed=%d nodes=%d leaves=%d marked=%d\n%!"
          (List.length assumed) !n_nodes !n_leaves (Hash_set.length marked);
      Some reached
  | exception Stdlib.Exit -> None

(* the literal holding [phi] in [c], encoded on first use; raises [Decline]
   (and then holds nothing new of [phi] that a literal reaches).  With
   [lazy_nonlinear], the leaves encoded now are [abstract]ed (a node encoded
   earlier keeps its encoding) *)
let rec checker_lit ?(lazy_nonlinear = false) ?(leaf_templates = false) c phi =
  in_batch c @@ fun () ->
  match
    Common.PhaseTime.with_phase "node-lookup" (fun () ->
        Hashtbl.find c.cnodes phi)
  with
  | Some l -> l
  | None ->
      let l =
        if Formula.is_and phi then (
          let ms =
            List.map ~f:(checker_lit ~lazy_nonlinear ~leaf_templates c)
            @@ Set.to_list @@ Formula.conjuncts_of phi
          in
          let l = cfresh c in
          List.iter ms ~f:(fun m -> cadd c l [ m ]);
          if c.cnl_relevant then
            Hashtbl.set c.cnl_nodes ~key:(Minisat.Lit.to_int l) ~data:(Conj ms);
          l)
        else if Formula.is_or phi then (
          let ms =
            List.map ~f:(checker_lit ~lazy_nonlinear ~leaf_templates c)
            @@ Set.to_list @@ Formula.disjuncts_of phi
          in
          let l = cfresh c in
          cadd c l ms;
          if c.cnl_relevant then
            Hashtbl.set c.cnl_nodes ~key:(Minisat.Lit.to_int l) ~data:(Disj ms);
          l)
        else if Formula.is_exists phi then (
          (* in a positive position [exists x. psi] is satisfiable with the
             rest exactly when [psi] is with [x] a variable no other formula
             mentions: the bound variables are renamed apart, per node, so
             that two nodes binding the same name get separate witnesses *)
          let params, body, _ = Formula.let_exists phi in
          if List.for_all params ~f:(fun (x, _) -> is_witness_name x) then
            (* the binders are this checker's names already (see the [let]
               arm), which no other node binds *)
            checker_lit ~lazy_nonlinear ~leaf_templates c body
          else (
          c.cbinders <- c.cbinders + 1;
          let map =
            match
              Map.Poly.of_alist
                (List.map params ~f:(fun (x, s) ->
                     ( x,
                       Term.mk_var
                         (Ident.Tvar
                            (sprintf "%s%d!%s" witness_prefix c.cbinders
                               (Ident.name_of_tvar x)))
                         s )))
            with
            | `Ok map -> map
            | `Duplicate_key x ->
                decline "a binder repeating %s" (Ident.name_of_tvar x)
          in
          checker_lit ~lazy_nonlinear ~leaf_templates c
            (Common.PhaseTime.with_phase "node-exists-subst" (fun () ->
                 Formula.subst map body))))
        else if Formula.is_let_formula phi then
          (* [let x = t in psi] is [exists x. x = t /\ psi].  The binders of
             a nest met for the first time are renamed apart in one pass to
             witness names (every binder of the nest, quantifiers included,
             gets a name no other node binds); a [let] whose binder is a
             witness name is then encoded as the conjunction itself.
             Substituting a fresh name into the body at every binder instead
             rebuilds the rest of the nest once per binder, quadratic in the
             length of a [let] chain *)
          match phi with
          | Formula.LetFormula (x, s, def, body, _) when is_witness_name x ->
              let ms =
                [
                  checker_lit ~lazy_nonlinear ~leaf_templates c
                    (Formula.eq (Term.mk_var x s) def);
                  checker_lit ~lazy_nonlinear ~leaf_templates c body;
                ]
              in
              let l = cfresh c in
              List.iter ms ~f:(fun m -> cadd c l [ m ]);
              (if c.cnl_relevant then
                 match ms with
                 | [ d; b ] when Hashtbl.mem c.cnl_leaves (Minisat.Lit.to_int d)
                   ->
                     Hashtbl.set c.cnl_defs ~key:(Ident.name_of_tvar x)
                       ~data:(Minisat.Lit.to_int d);
                     Hashtbl.set c.cnl_nodes ~key:(Minisat.Lit.to_int l)
                       ~data:(Let b)
                 | _ ->
                     Hashtbl.set c.cnl_nodes ~key:(Minisat.Lit.to_int l)
                       ~data:(Conj ms));
              l
          | Formula.LetFormula _ ->
              checker_lit ~lazy_nonlinear ~leaf_templates c
                (Common.PhaseTime.with_phase "node-let-rename" (fun () ->
                     Formula.aconv_tvar_norm_scoped
                       (fun () ->
                         c.cbinders <- c.cbinders + 1;
                         Ident.Tvar (sprintf "%s%d" witness_prefix c.cbinders))
                       phi))
          | _ -> assert false
        else
          let l = cfresh c in
          encode_leaf ~lazy_nonlinear ~leaf_templates c l phi;
          l
      in
      Common.PhaseTime.with_phase "node-lookup" (fun () ->
          Hashtbl.set c.cnodes ~key:phi ~data:l);
      l

(* [solve_under c.csv assumptions]; with [cdomain], deciding only the cone
   of the assumptions (as the SAT solver GipSAT of the hardware model
   checker rIC3 does), that is the variables reachable from them through
   [cadj], computed afresh on each call so that clauses added since (a
   lazily added definition) are in it.  The answer is the same: every
   clause of [c] holds the negation of the node literal it was added for
   ([cadd]), and the cone holds every variable of the clauses of each node
   literal in it; so a model of the cone's clauses extends to all clauses
   (and to the learnt ones, their consequences) by setting every node
   literal outside the cone false, and minisat answers [sat] only with no
   conflict and every decision variable assigned, when each clause over
   decided variables has a true literal.  The variables outside the cone
   are unassigned in the model, which [value] reads as false: a node
   literal outside the cone reads false, as in the extension.
   With [pin] (an assumed literal), the cone of [pin] is decided once and
   kept decided across calls until another literal is pinned; the walk of
   the other assumptions stops at it.  The answer is again the same: the
   pinned cone is kept closed under [cadj] (clauses added later for its
   variables bring their cones in before the next solve), so the decided
   set, the union of two closed sets, is closed, and the extension above
   applies to it *)
let solve_domain ?pin c assumptions =
  if not c.cdomain then solve_under c.csv assumptions
  else (
    Common.PhaseTime.event "blk-bits-domain-solve";
    let grow a init =
      if Array.length a < c.csv.next then
        Array.append a
          (Array.create ~len:(c.csv.next - Array.length a + 1024) init)
      else a
    in
    c.cmark <- grow c.cmark 0;
    c.cpinmark <- grow c.cpinmark false;
    (* the variables reachable from [roots], stopping at the pinned cone *)
    let cone_of roots =
      c.cepoch <- c.cepoch + 1;
      let cone = ref [] in
      let rec visit v =
        if c.cmark.(v) <> c.cepoch && not c.cpinmark.(v) then (
          c.cmark.(v) <- c.cepoch;
          cone := v :: !cone;
          match Hashtbl.find c.cadj v with
          | Some vs -> List.iter vs ~f:visit
          | None -> ())
      in
      List.iter roots ~f:visit;
      !cone
    in
    let pin_all cone =
      List.iter cone ~f:(fun v ->
          c.cpinmark.(v) <- true;
          set_decision_var c.csv.s v true)
    in
    (* the pinned cone stays closed under [cadj]: clauses added since it was
       last closed for a variable in it ([cadd] records their variables in
       [cpinfront]) bring their own cones in, read now that every clause of
       the encoding in flight is added *)
    (match (c.cpinned, c.cpinfront) with
    | Some (pv, cone), (_ :: _ as front) ->
        c.cpinfront <- [];
        Common.PhaseTime.event "blk-bits-domain-pin-grow";
        let more = cone_of front in
        pin_all more;
        c.cpinned <- Some (pv, List.rev_append more cone)
    | _ -> c.cpinfront <- []);
    let roots =
      List.map ~f:Minisat.Lit.to_int
      @@
      match pin with
      | None -> Array.to_list assumptions
      | Some p ->
          let pv = Minisat.Lit.to_int p in
          (match c.cpinned with
          | Some (v, _) when v = pv -> ()
          | old ->
              Option.iter old ~f:(fun (_, cone) ->
                  List.iter cone ~f:(fun v ->
                      c.cpinmark.(v) <- false;
                      set_decision_var c.csv.s v false));
              c.cpinned <- None;
              Common.PhaseTime.event "blk-bits-domain-pin";
              let cone = cone_of [ pv ] in
              pin_all cone;
              c.cpinned <- Some (pv, cone));
          Array.to_list assumptions
          |> List.filter ~f:(fun l -> not (Minisat.Lit.equal l p))
    in
    let cone = cone_of roots in
    List.iter cone ~f:(fun v -> set_decision_var c.csv.s v true);
    Exn.protect
      ~f:(fun () -> solve_under c.csv assumptions)
      ~finally:(fun () ->
        List.iter cone ~f:(fun v -> set_decision_var c.csv.s v false)))

(* whether the formulas of [assumed] (literals of [c]) have a common model;
   if not, the members of a subset that has none.  With [cdomain] and [pin]
   (one of the assumed literals), the cone of [pin] stays decided after the
   check, so that a run of checks sharing [pin] walks it once; it is
   released when a check pins another literal.  Extra decision variables
   keep every answer: the decided set is still closed under [cadj] *)
let checker_check ?pin c assumed =
  let assumptions = List.map assumed ~f:snd |> Array.of_list in
  (* after a [sat] solve, the pending occurrences of the leaves whose
     literal the model makes true and whose definition it violates get
     their definitions, guarded by the leaf's literal, and the solve is
     repeated; [sat] is answered only on a model violating none, which then
     satisfies every such leaf, abstracted or not.  With [cdef_templates] a
     definition is encoded by [blast_templated]: definitions of one operator
     and numeral (and width) share one template, so a round adding many
     asks Z3 once per shape; the clauses are a CNF of the definition as
     [blast]'s are.  Each round adds at least
     one of the finitely many pending definitions.  A definition the
     tactics decline raises [Decline] (it stays pending, those added before
     it stay added) *)
  let rec solve () =
    dump_check
      ~extra:(sprintf "pending=%d" (List.length c.cpending))
      c.csv assumptions;
    let started = Time_float.now () in
    let found = solve_domain ?pin c assumptions in
    if Option.is_some bits_dump_dir || bits_leaf_stats then
      eprintf "BITS_SOLVED %b %.3f s pending=%d at %.3f\n%!" found
        (Time_float.Span.to_sec (Time_float.diff (Time_float.now ()) started))
        (List.length c.cpending) (now ());
    if not found then false
    else
      let violated =
        List.filter c.cpending ~f:(fun o ->
            value c.csv o.guard && not (defined c o))
      in
      let violated =
        if c.cnl_relevant && not (List.is_empty violated) then (
          let started = now () in
          match
            Common.PhaseTime.with_phase "blk-bits-nl-relevant" (fun () ->
                nl_relevant c (Array.to_list assumptions))
          with
          | None ->
              Common.PhaseTime.event "blk-bits-nl-relevant-failed";
              if bits_leaf_stats then
                eprintf "nl-relevant failed violated=%d\n%!"
                  (List.length violated);
              violated
          | Some reached ->
              let kept =
                List.filter violated ~f:(fun o -> Hash_set.mem reached o.r)
              in
              if bits_leaf_stats then
                eprintf
                  "nl-relevant violated=%d reached=%d kept=%d %.3f s\n%!"
                  (List.length violated) (Hash_set.length reached)
                  (List.length kept) (now () -. started);
              if List.is_empty kept then
                Common.PhaseTime.event "blk-bits-nl-relevant-sat";
              kept)
        else violated
      in
      match violated with
      | [] -> true
      | violated ->
          Common.PhaseTime.event "blk-bits-nl-round";
          Common.PhaseTime.with_phase "blk-bits-nl-refine" (fun () ->
              in_batch c @@ fun () ->
              List.iter violated ~f:(fun o ->
                  let word name =
                    Z3.Expr.mk_const_s c.cctx name
                      (Z3.BitVector.mk_sort c.cctx o.width)
                  in
                  let arg = function Num e -> e | Word n -> word n in
                  (if c.cdef_templates then blast_templated else blast)
                    c o.guard
                    (Z3.Boolean.mk_eq c.cctx (word o.r)
                       (Z3.FuncDecl.apply o.op [ arg o.a; arg o.b ]))
                    (List.filter_map [ Word o.r; o.a; o.b ] ~f:(function
                      | Word n -> Some (n, o.width, false)
                      | Num _ -> None));
                  c.cpending <-
                    List.filter c.cpending ~f:(fun o' -> not (phys_equal o o'));
                  Common.PhaseTime.event "blk-bits-nl-defined"));
          solve ()
  in
  if solve () then `Sat
  else
    let core = Minisat.unsat_core c.csv.s in
    let mem l = Array.exists core ~f:(fun l' -> Minisat.Lit.equal l l') in
    `Unsat
      (List.filter_map assumed ~f:(fun (x, l) -> if mem l then Some x else None))

(* The words' values of a [sat] model, kept so that a later check of the
   same antecedent can be answered without a solve.  [model_words phi] are
   the words of [phi]'s free variables (those of a sort the checker does not
   encode are left out: a formula mentioning them is declined anyway);
   [last_model c words] reads their values in the last model, leaving out a
   word with no bits yet.

   Contract: after [checker_check c ((_, root) :: assumed)] answered [`Sat],
   where [root] is the literal of [phi], the values read are a model of
   [phi].  Every clause [c] holds is guarded by a literal ([lit => ...]), an
   and/or node forces its members from its own literal and a leaf's clauses
   are the CNF of the leaf by Z3's [simplify], [bit-blast] and [tseitin-cnf]
   (with [lazy_nonlinear], [`Sat] is answered only on a model satisfying
   the definition of every abstracted operator of a leaf whose literal it
   makes true), so a model with [root] true, read on the words' bits,
   satisfies [phi]: the bound variables of an existential or a [let] are
   renamed apart and not read.  This assumes the three tactics give
   definitional extensions (each of their models, restricted to the
   original bits, satisfies the goal), as their documentation describes *)
let model_words phi =
  Set.to_list (Formula.term_sort_env_of phi)
  |> List.filter_map ~f:(fun (v, s) ->
      Option.map (width_of s) ~f:(fun (w, _) -> (Ident.name_of_tvar v, w)))

let last_model c words =
  let m = Hashtbl.Poly.create () in
  List.iter words ~f:(fun (name, w) ->
      if Hashtbl.mem c.cwords (name, w) then
        Hashtbl.set m ~key:(name, w) ~data:(word_value c name w));
  m

exception Unvalued

(* [compile e]: an evaluator of the Boolean or bit-vector expression [e] of
   Z3 on the words' values (a constant of [e] is the word of its name and
   width, a Boolean one of width 1), giving [e]'s value as an unsigned
   number below 2^width (a Boolean as 0 or 1) with SMT-LIB's semantics
   (division by zero: [bvudiv] all ones, [bvurem] the dividend; a shift by
   the width or more: 0, or all sign bits for [bvashr]); it raises
   [Unvalued] when a word has no value.  [None] when [e] has an operator not
   below or a constant of another sort.  The nodes are evaluated once each,
   in an order where a node's arguments come first, so a shared subterm
   costs once *)
let compile e =
  let index = Hashtbl.create (module Int) in
  let steps = ref [] and count = ref 0 in
  let width e =
    if Z3.Boolean.is_bool e then 1
    else if Z3.BitVector.is_bv e then Z3.BitVector.get_size (Z3.Expr.get_sort e)
    else raise Exit
  in
  let rec go e =
    let id = Z3.AST.get_id (Z3.Expr.ast_of_expr e) in
    match Hashtbl.find index id with
    | Some i -> i
    | None ->
        let args = Array.of_list (List.map (Z3.Expr.get_args e) ~f:go) in
        let w = width e in
        let all_ones = Z.(pred (shift_left one w)) in
        let mask x = Z.extract x 0 w in
        let signed v k = Z.signed_extract v 0 k in
        let arg_width k = width (List.nth_exn (Z3.Expr.get_args e) k) in
        let bool b = if b then Z.one else Z.zero in
        let fold f (v : Z.t array) =
          Array.fold
            (Array.sub args ~pos:1 ~len:(Array.length args - 1))
            ~init:v.(args.(0))
            ~f:(fun acc i -> f acc v.(i))
        in
        let pairwise f (v : Z.t array) =
          bool
            (Array.for_alli args ~f:(fun k i ->
                 k = 0 || f v.(args.(k - 1)) v.(i)))
        in
        let a k (v : Z.t array) = v.(args.(k)) in
        let cmp f signed_ _ (v : Z.t array) =
          let k = arg_width 0 in
          let x, y =
            if signed_ then (signed (a 0 v) k, signed (a 1 v) k)
            else (a 0 v, a 1 v)
          in
          bool (f x y)
        in
        let params () =
          List.map
            (Z3.FuncDecl.get_parameters (Z3.Expr.get_func_decl e))
            ~f:Z3.FuncDecl.Parameter.get_int
        in
        let step : (string * int, Z.t) Hashtbl.t -> Z.t array -> Z.t =
          match Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl e) with
          | Z3enums.OP_UNINTERPRETED when Array.is_empty args ->
              let x =
                ( Z3.Symbol.to_string
                    (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e)),
                  w )
              in
              fun m _ ->
                (match Hashtbl.find m x with Some v -> v | None -> raise Unvalued)
          | Z3enums.OP_TRUE -> fun _ _ -> Z.one
          | Z3enums.OP_FALSE -> fun _ _ -> Z.zero
          | Z3enums.OP_BNUM ->
              let n = Z.of_string (Z3.BitVector.numeral_to_string e) in
              fun _ _ -> n
          | Z3enums.OP_EQ | Z3enums.OP_IFF -> fun _ v -> pairwise Z.equal v
          | Z3enums.OP_DISTINCT ->
              fun _ v ->
                bool
                  (Array.for_alli args ~f:(fun k i ->
                       Array.for_alli args ~f:(fun k' i' ->
                           k' <= k || not (Z.equal v.(i) v.(i')))))
          | Z3enums.OP_ITE ->
              fun _ v -> if Z.equal (a 0 v) Z.one then a 1 v else a 2 v
          | Z3enums.OP_AND -> fun _ v -> bool (Array.for_all args ~f:(fun i -> Z.equal v.(i) Z.one))
          | Z3enums.OP_OR -> fun _ v -> bool (Array.exists args ~f:(fun i -> Z.equal v.(i) Z.one))
          | Z3enums.OP_NOT -> fun _ v -> bool (Z.equal (a 0 v) Z.zero)
          | Z3enums.OP_XOR -> fun _ v -> fold Z.logxor v
          | Z3enums.OP_IMPLIES ->
              fun _ v -> bool (Z.equal (a 0 v) Z.zero || Z.equal (a 1 v) Z.one)
          | Z3enums.OP_BNEG -> fun _ v -> mask (Z.neg (a 0 v))
          | Z3enums.OP_BADD -> fun _ v -> mask (fold Z.add v)
          | Z3enums.OP_BSUB -> fun _ v -> mask (fold Z.sub v)
          | Z3enums.OP_BMUL -> fun _ v -> mask (fold Z.mul v)
          | Z3enums.OP_BAND -> fun _ v -> fold Z.logand v
          | Z3enums.OP_BOR -> fun _ v -> fold Z.logor v
          | Z3enums.OP_BXOR -> fun _ v -> fold Z.logxor v
          | Z3enums.OP_BNOT -> fun _ v -> mask (Z.lognot (a 0 v))
          | Z3enums.OP_BUDIV ->
              fun _ v ->
                if Z.equal (a 1 v) Z.zero then all_ones else Z.div (a 0 v) (a 1 v)
          | Z3enums.OP_BUREM ->
              fun _ v ->
                if Z.equal (a 1 v) Z.zero then a 0 v else Z.rem (a 0 v) (a 1 v)
          | Z3enums.OP_ULEQ -> cmp Z.leq false
          | Z3enums.OP_ULT -> cmp Z.lt false
          | Z3enums.OP_UGEQ -> cmp Z.geq false
          | Z3enums.OP_UGT -> cmp Z.gt false
          | Z3enums.OP_SLEQ -> cmp Z.leq true
          | Z3enums.OP_SLT -> cmp Z.lt true
          | Z3enums.OP_SGEQ -> cmp Z.geq true
          | Z3enums.OP_SGT -> cmp Z.gt true
          | Z3enums.OP_CONCAT ->
              let widths = Array.init (Array.length args) ~f:arg_width in
              fun _ v ->
                Array.foldi args ~init:Z.zero ~f:(fun k acc i ->
                    Z.(logor (shift_left acc widths.(k)) v.(i)))
          | Z3enums.OP_EXTRACT -> (
              match params () with
              | [ hi; lo ] -> fun _ v -> Z.extract (a 0 v) lo (hi - lo + 1)
              | _ -> raise Exit)
          | Z3enums.OP_ZERO_EXT -> fun _ v -> a 0 v
          | Z3enums.OP_SIGN_EXT ->
              let k = arg_width 0 in
              fun _ v -> mask (signed (a 0 v) k)
          | Z3enums.OP_BSHL ->
              fun _ v ->
                let y = a 1 v in
                if Z.(geq y (of_int w)) then Z.zero
                else mask (Z.shift_left (a 0 v) (Z.to_int y))
          | Z3enums.OP_BLSHR ->
              fun _ v ->
                let y = a 1 v in
                if Z.(geq y (of_int w)) then Z.zero
                else Z.shift_right (a 0 v) (Z.to_int y)
          | Z3enums.OP_BASHR ->
              fun _ v ->
                let y = a 1 v and x = signed (a 0 v) w in
                if Z.(geq y (of_int w)) then
                  if Z.(lt x zero) then all_ones else Z.zero
                else mask (Z.shift_right x (Z.to_int y))
          | _ -> raise Exit
        in
        let i = !count in
        incr count;
        steps := step :: !steps;
        Hashtbl.set index ~key:id ~data:i;
        i
  in
  match go e with
  | exception Exit -> None
  | root ->
      let steps = Array.of_list (List.rev !steps) in
      Some
        (fun m ->
          let v = Array.create ~len:(Array.length steps) Z.zero in
          Array.iteri steps ~f:(fun i step -> v.(i) <- step m v);
          v.(root))

(* whether [phi] is true of the words' values [m]; [false] also when it
   cannot be told (a word of [phi] without a value in [m], a conversion
   failing).  A ground bit-vector formula is decided by Z3's simplifier, so
   [true] means that [phi] holds of every assignment extending [m] *)
(* debugging only ([COAR_BITS_SAT_CHECK]): the value of [phi] with each
   free constant that has bits set to its word's value in the last model,
   by Z3's rewriter, or by a Z3 solve when the rewriter leaves a formula
   (a quantifier); "true" or "solved sat" is expected after
   [checker_check] answered [`Sat] with [phi]'s literal among the
   assumed *)
let debug_model_value c phi =
  let ctx = c.cctx in
  match
    Z3Smt.Z3interface.of_formula ~id:None ctx [] [] Map.Poly.empty
      Set.Poly.empty phi
  with
  | exception exn_ when not (Common.Timer.is_async exn_) -> "unconvertible"
  | e ->
      let seen = Hash_set.create (module Int) in
      let froms = ref [] and tos = ref [] and skipped = ref [] in
      let rec go e =
        let id = Z3.AST.get_id (Z3.Expr.ast_of_expr e) in
        if not (Hash_set.mem seen id) then (
          Hash_set.add seen id;
          if
            Z3.Expr.is_numeral e || Z3.Boolean.is_true e
            || Z3.Boolean.is_false e
          then ()
          else if Z3.Expr.is_const e then
            let name =
              Z3.Symbol.to_string (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e))
            in
            let w =
              if Z3.Boolean.is_bool e then 1
              else if Z3.BitVector.is_bv e then
                Z3.BitVector.get_size (Z3.Expr.get_sort e)
              else 0
            in
            if w > 0 && Hashtbl.mem c.cwords (name, w) then (
              let v = word_value c name w in
              froms := e :: !froms;
              tos :=
                (if Z3.Boolean.is_bool e then
                   Z3.Boolean.mk_val ctx (not (Z.equal v Z.zero))
                 else Z3.BitVector.mk_numeral ctx (Z.to_string v) w)
                :: !tos)
            else skipped := name :: !skipped
          else if
            match Z3.AST.get_ast_kind (Z3.Expr.ast_of_expr e) with
            | Z3enums.APP_AST -> true
            | _ -> false
          then List.iter (Z3.Expr.get_args e) ~f:go)
      in
      go e;
      let v = Z3.Expr.simplify (Z3.Expr.substitute e !froms !tos) None in
      if Z3.Boolean.is_true v then "true"
      else if Z3.Boolean.is_false v then "false"
      else
        (* a formula with an existential is left to a solve: the
           quantifier is in a positive position, so Z3 skolemises it *)
        let solver = Z3.Solver.mk_simple_solver ctx in
        let params = Z3.Params.mk_params ctx in
        Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") 10000;
        Z3.Solver.set_parameters solver params;
        let answer =
          match Z3.Solver.check solver [ v ] with
          | Z3.Solver.SATISFIABLE -> "sat"
          | Z3.Solver.UNSATISFIABLE -> "unsat"
          | Z3.Solver.UNKNOWN -> "unknown"
        in
        sprintf "solved %s (no bits for %d constants)" answer
          (List.length !skipped)

let holds c m phi =
  let evaluation =
    Hashtbl.find_or_add c.cevals phi ~default:(fun () ->
        match
          Z3Smt.Z3interface.of_formula ~id:None c.cctx [] [] Map.Poly.empty
            Set.Poly.empty phi
        with
        | exception exn_ when not (Common.Timer.is_async exn_) -> Unevaluable
        | e -> (
            let word e =
              if
                Z3.Expr.is_const e
                && (not (Z3.Expr.is_numeral e))
                && not (Z3.Boolean.is_true e || Z3.Boolean.is_false e)
              then
                let name =
                  Z3.Symbol.to_string
                    (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e))
                in
                if Z3.Boolean.is_bool e then Some (name, 1)
                else if Z3.BitVector.is_bv e then
                  Some (name, Z3.BitVector.get_size (Z3.Expr.get_sort e))
                else None
              else None
            in
            let numeral e =
              if Z3.Boolean.is_true e then Some Z.one
              else if Z3.Boolean.is_false e then Some Z.zero
              else if Z3.BitVector.is_bv_numeral e then
                Some (Z.of_string (Z3.BitVector.numeral_to_string e))
              else None
            in
            let compare positive e =
              match word e with
              | Some x when Z3.Boolean.is_bool e ->
                  Some (Compare (x, Z.one, positive))
              | _ -> (
                  if not (Z3.Boolean.is_eq e) then None
                  else
                    match Z3.Expr.get_args e with
                    | [ a; b ] -> (
                        match (word a, numeral b, word b, numeral a) with
                        | Some x, Some n, _, _ | _, _, Some x, Some n ->
                            Some (Compare (x, n, positive))
                        | _ -> None)
                    | _ -> None)
            in
            let direct =
              if Z3.Boolean.is_not e then
                match Z3.Expr.get_args e with
                | [ a ] -> compare false a
                | _ -> None
              else compare true e
            in
            match direct with
            | Some ev -> ev
            | None -> (
                match compile e with
                | Some f -> Native f
                | None -> (
                match free_consts e with
                | exception exn_ when not (Common.Timer.is_async exn_) ->
                    Unevaluable
                | consts ->
                    let rec find_consts acc seen e =
                      let id = Z3.AST.get_id (Z3.Expr.ast_of_expr e) in
                      if Hashtbl.mem seen id then acc
                      else (
                        Hashtbl.set seen ~key:id ~data:();
                        match word e with
                        | Some (name, w) when Hashtbl.mem consts name ->
                            (e, name, w, Z3.Boolean.is_bool e) :: acc
                        | _ ->
                            List.fold (Z3.Expr.get_args e) ~init:acc
                              ~f:(fun acc a -> find_consts acc seen a))
                    in
                    Ground
                      (e, find_consts [] (Hashtbl.create (module Int)) e)))))
  in
  match evaluation with
  | Unevaluable -> false
  | Compare (x, n, positive) -> (
      Common.PhaseTime.event "blk-bits-eval-compare";
      match Hashtbl.find m x with
      | Some v -> Bool.equal positive (Z.equal v n)
      | None -> false)
  | Native f -> (
      Common.PhaseTime.event "blk-bits-eval-native";
      match f m with
      | v -> Z.equal v Z.one
      | exception Unvalued -> false)
  | Ground (e, consts) -> (
      Common.PhaseTime.event "blk-bits-eval-ground";
      match
        List.map consts ~f:(fun (k, name, w, is_bool) ->
            match Hashtbl.find m (name, w) with
            | None -> None
            | Some v ->
                Some
                  ( k,
                    if is_bool then Z3.Boolean.mk_val c.cctx (not (Z.equal v Z.zero))
                    else Z3.BitVector.mk_numeral c.cctx (Z.to_string v) w ))
        |> Option.all
      with
      | None -> false
      | Some pairs -> (
          let from, into = List.unzip pairs in
          try
            Z3.Boolean.is_true
              (Z3.Expr.simplify (Z3.Expr.substitute e from into) None)
          with exn_ when not (Common.Timer.is_async exn_) -> false))
