(* Simplification of the C frontend's statement graph before it is translated
   into fixpoint logic, so that the translation has fewer statements and
   fewer variables per predicate.

   [optimize spec_fv decls inits stmt] runs three passes: [RemoveAssign]
   substitutes an assignment's value into the statements that read it and
   drops assignments nothing reads, computing reads by a whole-program
   dataflow fixpoint ([ReadGraph]) and repeating until a round changes
   nothing; [RemoveNop] removes no-op statements; and
   [RemoveTrailingNoValueChanged] cuts to the exit every statement after which
   no assumption and no write to a specification variable can follow.

   The graph is mutable and cyclic: [Util.replace_stmt] assigns to successor
   references in place.  Every map over statements is therefore keyed by
   physical equality ([StatementEnv], an association list) or by the
   statement's identity ([LinkedStatementHashtbl]), never by its contents. *)

open Core
open Common.Ext
open CSyntax
open Linked
open Linked.LinkedStatement
open Ast
open Ast.LogicOld

type target = Variables.t * Declare.t list * Init.t list * LinkedStatement.t

module StatementEnv = struct
  type 'a t = ENV of ('a * (LinkedStatement.t * 'a ref) list)

  let mk_empty init = ENV (init, [])

  let init init items =
    ENV (init, List.map ~f:(fun (key, value) -> (key, ref value)) items)

  let exists stmt = function
    | ENV (_, env) ->
        List.exists ~f:(fun (stmt', _) -> phys_equal stmt' stmt) env

  let add stmt = function
    | ENV (init, env) -> ENV (init, (stmt, ref init) :: env)

  let remove stmt = function
    | ENV (init, env) ->
        ENV
          ( init,
            env
            |> List.filter ~f:(fun (stmt', _) -> not @@ phys_equal stmt' stmt)
          )

  let get stmt = function
    | ENV (init, env) -> (
        match List.find ~f:(fun (stmt', _) -> phys_equal stmt' stmt) env with
        | Some (_, item) -> !item
        | None -> init)

  (* let get_exn stmt = function
      ENV (_, env) ->
      match List.find_opt (fun (stmt', _) -> phys_equal stmt' stmt) env with
      | Some (_, item) -> !item
      | None -> assert false *)

  let update stmt newvalue = function
    | ENV (init, env) -> (
        match List.find ~f:(fun (stmt', _) -> phys_equal stmt' stmt) env with
        | Some (_, item) ->
            item := newvalue;
            ENV (init, env)
        | None -> ENV (init, (stmt, ref newvalue) :: env))

  let length = function ENV (_, env) -> List.length env
  let keys = function ENV (_, env) -> List.map ~f:(fun (key, _) -> key) env

  (* A replacer starts with every statement mapped to itself, so this answers
     "did the pass that was handed this replacer actually replace anything?".
     Removals shrink the list, so a caller checks the length as well. *)
  let is_identity = function
    | ENV (_, env) ->
        List.for_all env ~f:(fun (key, value) -> phys_equal key !value)

  let values = function
    | ENV (_, env) -> List.map ~f:(fun (_, value) -> !value) env

  (* The cells, and the list that holds them.  [update] assigns through a cell
     and returns the same list; only [add] and [remove] build a new one.  A
     caller that has derived something from the *values* can therefore keep it
     for as long as the list is physically the same, and see later updates for
     free by reading the cells again. *)
  let cells = function ENV (_, env) -> List.map ~f:snd env
  let spine = function ENV (_, env) -> env

  let entries = function
    | ENV (_, env) -> List.map env ~f:(fun (key, value) -> (key, !value))

  (* Union of two sets of statements, and the hot spot of the read-graph
     fixpoint: a union is taken once per successor of every visited statement,
     about 94,000 times on a loop body of 80 sequential conditionals. Folding
     [update] over [keys env2] allocated a key list per call and rebuilt the
     [ENV] block per key even when the key was already there. The membership
     test is physical identity on a cyclic structure, so hashing the keys costs
     more than scanning for them -- measured, a hash-indexed version of this was
     2.5 times *slower*. Keep the scan and drop the allocation. *)
  let merge env1 env2 : unit t =
    match (env1, env2) with
    | ENV (init, l1), ENV (_, l2) ->
        let absent key =
          not (List.exists l1 ~f:(fun (key', _) -> phys_equal key' key))
        in
        let extra =
          List.filter_map l2 ~f:(fun (key, _) ->
              if absent key then Some (key, ref ()) else None)
        in
        if List.is_empty extra then ENV (init, l1) else ENV (init, extra @ l1)
end

module Util : sig
  val get_prev_env : LinkedStatement.t -> LinkedStatement.t list StatementEnv.t

  val remove_nobranch :
    query:LinkedStatement.t ->
    LinkedStatement.t ->
    LinkedStatement.t list ->
    LinkedStatement.t
  (** remove stmt from stmts and returns new query_stmt *)

  val replace_stmt : query:t -> t StatementEnv.t -> t
  (** returns new query_stmt *)

  val mk_replacer : t list -> t StatementEnv.t
end = struct
  (* get_prev_env *)
  (* The association-list way of recording a predecessor, kept because it says
     plainly what the table-based [get_prev_env] below computes.  It is no
     longer called: both the lookup and the update it performs are linear in
     the graph, which is what made building the relation quadratic. *)
  let add_to_prev_env stmt prev_stmt env =
    StatementEnv.update stmt (prev_stmt :: StatementEnv.get stmt env) env
    [@@warning "-32"]

  (* Which statements can precede each one.  Both halves of this used to be
     association lists scanned linearly -- the visited set and the map being
     built -- so relating the predecessors of an n-statement graph cost O(n^2)
     twice over, 4.6 s of a 24 s run on a 7,892-statement program.  Statement
     identities are dense integers and the tables here are keyed by them, so
     both are constant time.  The traversal order is unchanged, and so is the
     order within each predecessor list: a statement is recorded as the
     predecessor of each successor before the walk descends into it, whether or
     not the successor has been seen. *)
  let get_prev_env stmt =
    let seen = LinkedStatementHashtbl.create 1024 in
    let prev = LinkedStatementHashtbl.create 1024 in
    let order = ref [] in
    let rec visit stmt =
      if not (LinkedStatementHashtbl.mem seen stmt) then (
        LinkedStatementHashtbl.replace seen stmt ();
        List.iter (get_next_statements stmt) ~f:(fun nxt_stmt ->
            if not (LinkedStatementHashtbl.mem prev nxt_stmt) then
              order := nxt_stmt :: !order;
            LinkedStatementHashtbl.replace prev nxt_stmt
              (stmt
              ::
              (match LinkedStatementHashtbl.find_opt prev nxt_stmt with
              | Some l -> l
              | None -> []));
            visit nxt_stmt))
    in
    visit stmt;
    StatementEnv.init []
      (List.map !order ~f:(fun k -> (k, LinkedStatementHashtbl.find prev k)))

  (* TODO: self loop *)
  let remove_nobranch ~query stmt stmts =
    match get_next_statements stmt with
    | [ nxt_stmt ] ->
        List.iter stmts ~f:(fun stmt' ->
            get_next_statements_ref stmt'
            |> List.iter ~f:(fun stmt_ref ->
                if phys_equal !stmt_ref stmt then stmt_ref := nxt_stmt));
        if phys_equal query stmt then nxt_stmt else query
    | _ -> failwith "not a nobranch stmt"

  let mk_replacer stmts =
    let dummy_stmt = mk_exit () in
    stmts
    |> List.map ~f:(fun stmt -> (stmt, stmt))
    |> StatementEnv.init dummy_stmt

  (* Point every next-statement reference at the replacement its target was
     given.

     The guard this replaces was a list of the references already assigned,
     scanned linearly and accumulated across the whole pass -- quadratic, and
     not removable by deduplicating statements, because **different statements
     share reference cells**: counted, every reference the guard skipped had
     been assigned while a *different* statement was being processed (30 of 431
     on one file, 1,056 of 8,822 on another), and no statement occurred twice.

     What makes a cheap guard possible is that a replacement is a statement
     this pass has just built, so it is never a key of the replacer: an
     unchanged statement maps to itself and a changed one maps to something new.
     So a reference whose target is still a key has not been assigned yet, one
     whose target is a value the pass produced has, and one that is neither is
     the error the original reported. *)
  let replace_stmt ~query new_stmts =
    let entries = StatementEnv.entries new_stmts in
    let repl = LinkedStatementHashtbl.create 1024 in
    (* the association list may hold a key twice and answers with the first *)
    List.iter entries ~f:(fun (key, value) ->
        if not (LinkedStatementHashtbl.mem repl key) then
          LinkedStatementHashtbl.replace repl key value);
    let produced = LinkedStatementHashtbl.create 1024 in
    List.iter entries ~f:(fun (_, value) ->
        LinkedStatementHashtbl.replace produced value ());
    List.iter (StatementEnv.values new_stmts) ~f:(fun stmt ->
        List.iter (get_next_statements_ref stmt) ~f:(fun nxt_stmt ->
            match LinkedStatementHashtbl.find_opt repl !nxt_stmt with
            | Some value -> nxt_stmt := value
            | None ->
                if not (LinkedStatementHashtbl.mem produced !nxt_stmt) then
                  failwith
                  @@ sprintf "internal error: replace failed:\n%s\n\n"
                       (string_of stmt)));
    StatementEnv.get query new_stmts
end

module ReadGraph = struct
  (* Which statements read the value that reaches a given one.  The payload is
     a *bitset over statement identities* with its population count.  The
     fixpoint unions these sets once per successor of every visited statement,
     and the sets are large in the programs that cost: on a 2,030-statement
     program a variable's entries hold hundreds to a thousand readers each, the
     unions walked 7.4 billion list elements and were 83 of the 102 seconds the
     five fixpoints took -- a worklist, which only cuts the number of visits,
     changed nothing, because each visit's merge was the cost.  Two earlier
     payloads are recorded here for the same reason: an association list of
     statements (a scan of one side against the other, 46% of the conversion)
     and then a sorted list of identities (one linear merge).  Statement
     identities are dense small integers assigned when the program is linked,
     so a bitset of one word per 62 statements makes the union a few dozen
     word-wise [lor]s, membership a bit test and the length a cached count;
     the set computed is the same, so what the optimiser decides from it is
     unchanged. *)
  module Bits = struct
    type t = { words : int array; count : int }

    let bits_per_word = 62
    let words_for cap = (cap + bits_per_word - 1) / bits_per_word

    let popcount x =
      let rec go x n = if x = 0 then n else go (x land (x - 1)) (n + 1) in
      go x 0

    let singleton ~cap i =
      let words = Array.create ~len:(words_for (max cap (i + 1))) 0 in
      words.(i / bits_per_word) <- 1 lsl (i mod bits_per_word);
      { words; count = 1 }

    let empty = { words = [||]; count = 0 }

    let mem t i =
      let q = i / bits_per_word in
      q < Array.length t.words
      && (t.words.(q) lsr (i mod bits_per_word)) land 1 = 1

    let inter_nonempty a b =
      let n = min (Array.length a.words) (Array.length b.words) in
      let rec go k = k < n && (a.words.(k) land b.words.(k) <> 0 || go (k + 1)) in
      go 0

    let equal a b =
      a.count = b.count
      &&
      let la = Array.length a.words and lb = Array.length b.words in
      let n = max la lb in
      let rec go k =
        k >= n
        || (if k < la then a.words.(k) else 0)
           = (if k < lb then b.words.(k) else 0)
           && go (k + 1)
      in
      go 0

    (* returns one of its arguments when the union adds nothing to it, so
       that an unchanged entry stays physically the same value *)
    let union a b =
      if phys_equal a b || b.count = 0 then a
      else if a.count = 0 then b
      else
        let la = Array.length a.words and lb = Array.length b.words in
        let n = max la lb in
        let words = Array.create ~len:n 0 in
        let count = ref 0 in
        for k = 0 to n - 1 do
          let x =
            (if k < la then a.words.(k) else 0)
            lor if k < lb then b.words.(k) else 0
          in
          words.(k) <- x;
          count := !count + popcount x
        done;
        if !count = a.count then a
        else if !count = b.count then b
        else { words; count = !count }
  end

  (* What the optimiser actually asks about the value of one variable at one
     point, and nothing more.  Two questions:

     - is the value read at all downstream, and can it be read more than once
       along some path?  That is a three-element lattice, so the payload for it
       is a tag and not a set;
     - does *this* statement read the value produced by *that* definition?  The
       query is only ever made at a definition's own program point -- the entry
       of the program, or the statement just after an assignment to the
       variable -- so the value in question is exactly that definition's, and
       the question is answered by which definitions reach the reader.

     Storing the readers instead made this cubic in the number of statements:
     an entry grew one reader at a time towards a size of order n, over n
     entries, at n/62 words a merge -- 4.5 billion words on a 7,892-statement
     program.  A variable has a handful of assignments where it has thousands
     of readers, so reaching definitions is a word per statement and the
     fixpoint is linear per pass. *)
  type rs_t = Never | Once | TwiceOrMore

  type rg_t = {
    rg_idx : int LinkedStatementHashtbl.t;
    rg_tags : rs_t array;  (** how often what reaches here is read, capped at two *)
    rg_rd : Bits.t array;  (** the definitions reaching each statement's entry *)
    rg_reads : bool array;  (** whether the statement itself reads the variable *)
    rg_def : int array;  (** this statement's definition number, or [-1] *)
    rg_ndefs : int;  (** one more than the largest definition number *)
  }

  (** what the consumers hold: the tag at the queried point, together with the
      definitions live there and the graph needed to ask about a reader *)
  type rc_t = { rc_tag : rs_t; rc_defs : Bits.t; rc_rg : rg_t }

  (* Whether the environment carries reaching definitions.  Only the
     substitution pass asks [mem] -- "does this statement read the value that
     definition produced" -- and that is the only question needing them; every
     other consumer asks the tag alone, which the backward pass gives.  The
     flag travels with the environment so that one built without definitions
     cannot be handed to the pass that would ask for them. *)
  type rgenv_t = RGENV of bool * (Ident.tvar * Sort.t, rg_t) List.Assoc.t

  let rgenv_has_defs = function RGENV (d, _) -> d

  let empty = Never

  let rg_empty =
    {
      rg_idx = LinkedStatementHashtbl.create 1;
      rg_tags = [||];
      rg_rd = [||];
      rg_reads = [||];
      rg_def = [||];
      rg_ndefs = 1;
    }

  let rg_index stmt rg = LinkedStatementHashtbl.find_opt rg.rg_idx stmt

  let rg_tag stmt rg =
    match rg_index stmt rg with Some i -> rg.rg_tags.(i) | None -> Never

  let rg_update stmt rs rg =
    (match rg_index stmt rg with Some i -> rg.rg_tags.(i) <- rs | None -> ());
    rg

  (* The tag at a point, with the definitions live there.  Enough for the
     questions that are about the point -- is anything read from here, and how
     often -- but not for a question about one definition's value: where
     several definitions meet, the set is their union and asking [mem] of it
     would answer about all of them. *)
  let rg_get stmt rg =
    match rg_index stmt rg with
    | Some i -> { rc_tag = rg.rg_tags.(i); rc_defs = rg.rg_rd.(i); rc_rg = rg }
    | None -> { rc_tag = Never; rc_defs = Bits.empty; rc_rg = rg }

  (* The value a particular assignment produces, observed at the point just
     after it.  The tag is the point's, the value is the assignment's: the
     statement after an assignment can also be a join, and then the point holds
     more values than the one being asked about. *)
  let rg_get_def ~def stmt rg =
    let tag = rg_tag stmt rg in
    let defs =
      match rg_index def rg with
      | Some i when Array.length rg.rg_def > i && rg.rg_def.(i) >= 0 ->
          Bits.singleton ~cap:rg.rg_ndefs rg.rg_def.(i)
      | _ -> Bits.empty
    in
    { rc_tag = tag; rc_defs = defs; rc_rg = rg }

  (* The value the program starts with, observed at its entry, which a loop
     back to the entry can otherwise join other values into. *)
  let rg_get_initial stmt rg =
    {
      rc_tag = rg_tag stmt rg;
      rc_defs = Bits.singleton ~cap:rg.rg_ndefs 0;
      rc_rg = rg;
    }

  let is_once rc = match rc.rc_tag with Once -> true | _ -> false
  let is_never rc = match rc.rc_tag with Never -> true | _ -> false
  let is_read rc = not (is_never rc)

  (** how often the value at the queried point is read along the worst path,
      counted no further than twice -- 0, 1 or 2 *)
  let read_level rc =
    match rc.rc_tag with Never -> 0 | Once -> 1 | TwiceOrMore -> 2

  (* Does [stmt] read the value the queried point holds?  It does when it reads
     the variable at all and one of the definitions live at that point reaches
     it.  At the points this is asked -- just after a definition, or at the
     entry -- exactly one definition is live, so this is the set of that
     definition's readers and not an approximation of it. *)
  let mem stmt rc =
    match rg_index stmt rc.rc_rg with
    | Some i ->
        rc.rc_rg.rg_reads.(i)
        && Bits.inter_nonempty rc.rc_defs rc.rc_rg.rg_rd.(i)
    | None -> false

  let rgenv_mem tvar = function
    | RGENV (_, rgenv) -> List.Assoc.mem ~equal:Stdlib.( = ) rgenv tvar

  let rgenv_get tvar = function
    | RGENV (d, rgenv) ->
        assert (rgenv_mem tvar (RGENV (d, rgenv)));
        List.Assoc.find_exn ~equal:Stdlib.( = ) rgenv tvar

  let rgenv_entries = function RGENV (_, rgenv) -> rgenv
  let rg_is_empty rg = Array.length rg.rg_tags = 0

  let string_of_rgenv query_stmt = function
    | RGENV (d, rgenv) ->
        string_of
          ~info:(fun stmt ->
            List.map ~f:fst rgenv
            |> String.concat_map_list ~sep:" " ~f:(fun tvar ->
                let r = rgenv_get tvar (RGENV (d, rgenv)) |> rg_get stmt in
                sprintf "%s:%d" (Ident.name_of_tvar (fst tvar)) (read_level r))
            |> sprintf "[%s]")
          query_stmt

  (* max rs1 rs2 *)
  let merge rs1 rs2 =
    match (rs1, rs2) with
    | Never, Never -> Never
    | TwiceOrMore, _ | _, TwiceOrMore -> TwiceOrMore
    | Once, Once | Once, Never | Never, Once -> Once

  (* rs1 + rs2 *)
  let add rs1 rs2 =
    match (rs1, rs2) with
    | Never, Never -> Never
    | TwiceOrMore, _ | _, TwiceOrMore | Once, Once -> TwiceOrMore
    | Once, Never | Never, Once -> Once

  let is_updated old_rs new_rs = Stdlib.(old_rs <> new_rs)

  let rec rc_of_term_rep varname term res =
    if Term.is_var term then
      let (tvar, _), _ = Term.let_var term in
      if String.equal (Ident.name_of_tvar tvar) varname then res + 1 else res
    else if Term.is_app term then
      let _, args, _ = Term.let_app term in
      List.fold
        ~f:(fun res term -> rc_of_term_rep varname term res)
        ~init:res args
    else failwith "rc_of_term_rep: not implemented"

  let rc_of_atom_rep varname atom res =
    if Atom.is_app atom then
      let _, args, _ = Atom.let_app atom in
      List.fold
        ~f:(fun res term -> rc_of_term_rep varname term res)
        ~init:res args
    else if Atom.is_true atom || Atom.is_false atom then res
    else
      failwith
      @@ sprintf "rc_of_atom_rep: not implemented for: %s" (Atom.str_of atom)

  let rec rc_of_formula_rep varname fml res =
    match fml with
    | Formula.Atom (atom, _) -> rc_of_atom_rep varname atom res
    | Formula.UnaryOp (_, phi, _) -> rc_of_formula_rep varname phi res
    | Formula.BinaryOp (_, phi1, phi2, _) ->
        rc_of_formula_rep varname phi1 res |> rc_of_formula_rep varname phi2
    | Formula.Bind (_, bounds, phi', _) ->
        (* <varname> is in <bounds> *)
        if
          List.exists
            ~f:(fun (tvar, _) -> String.equal (Ident.name_of_tvar tvar) varname)
            bounds
        then 0 (* <varname> is not in <bounds> *)
        else rc_of_formula_rep varname phi' res
    | LetRec (_funcs, _phi, _info) ->
        failwith "rc_of_formula_rep: not implemented"
    | LetFormula (_var, _sort, def, body, _info) ->
        rc_of_term_rep varname def res |> rc_of_formula_rep varname body

  let of_rc cnt = if cnt = 0 then Never else if cnt = 1 then Once else TwiceOrMore
  let of_formula varname fml = of_rc @@ rc_of_formula_rep varname fml 0
  let of_term varname term = of_rc @@ rc_of_term_rep varname term 0

  (* What a statement itself reads of the variable: how many times the variable
     occurs in the term it assigns or the condition it tests. This depends only
     on the statement and the variable, not on anything the fixpoint computes,
     yet it was recomputed on every visit -- and a visit happens hundreds of
     thousands of times, each walking a formula. The kind is one of
       [`Kill rs]  the statement assigns the variable, so what follows is cut
       [`Read rs]  what the statement reads, to be added to what follows
       [`Pass]     the statement reads nothing of it
       [`Stop]     nothing to record here (an exit, or a nondeterministic
                   assignment to this very variable)
     and it is computed once per statement per fixpoint. *)
  let own_of varname stmt =
    if is_assign stmt then
      let varname', term, _ = let_assign stmt in
      if String.equal varname' varname then `Kill (of_term varname term)
      else `Read (of_term varname term)
    else if is_nondet_int_assign stmt then
      let varname', _ = let_nondet_int_assign stmt in
      if String.equal varname' varname then `Stop else `Pass
    else if is_nondet_real_assign stmt then
      let varname', _ = let_nondet_real_assign stmt in
      if String.equal varname' varname then `Stop else `Pass
    else if is_if stmt then
      let fml, _, _ = let_if stmt in
      `Read (of_formula varname fml)
    else if is_nondet stmt then `Pass
    else if is_assume stmt then
      let fml, _ = let_assume stmt in
      `Read (of_formula varname fml)
    else if is_nop stmt then `Pass
    else if is_exit stmt then (* Never is the default *) `Stop
    else failwith "not implemented"

  (* A statement defines the variable when it assigns to it, deterministically
     or not; the value the program starts with is a definition too and is
     numbered zero. *)
  let is_def varname stmt =
    (is_assign stmt
    && String.equal (let (v, _, _) = let_assign stmt in v) varname)
    || (is_nondet_int_assign stmt
       && String.equal (fst (let_nondet_int_assign stmt)) varname)
    || (is_nondet_real_assign stmt
       && String.equal (fst (let_nondet_real_assign stmt)) varname)

  let rec get_rg_dfs own_of preds_of stmt res : rg_t =
    match own_of stmt with
    | `Stop -> res
    | (`Kill _ | `Read _ | `Pass) as own -> (
        let rs =
          List.fold ~init:empty (get_next_statements stmt)
            ~f:(fun rs nxt_stmt -> rg_tag nxt_stmt res |> merge rs)
        in
        let update = get_rg_dfs_update own_of preds_of stmt in
        match own with
        | `Kill own -> update res own
        | `Read own -> update res (add own rs)
        | `Pass -> update res rs)

  and get_rg_dfs_update own_of preds_of stmt res rs =
    let rs0 = rg_tag stmt res in
    if is_updated rs0 rs then
      let res = rg_update stmt rs res in
      List.fold ~init:res (preds_of stmt) ~f:(fun res prev_stmt ->
          get_rg_dfs own_of preds_of prev_stmt res)
    else res

  (* Everything a fixpoint needs that does not depend on *which* variable it is
     computing: the set of statements it can reach, their numbering, and each
     statement's predecessors. [get_rgenv] runs one fixpoint per program
     variable over the same graph -- six to eight of them on the C benchmarks --
     and this used to be rebuilt inside every one of them. *)
  type graph_index = {
    gi_all : LinkedStatement.t list;
    gi_size : int;
    gi_idx : int LinkedStatementHashtbl.t;
    gi_preds : LinkedStatement.t -> LinkedStatement.t list;
    gi_cap : int;  (** one more than the largest statement identity *)
    gi_at : LinkedStatement.t option array;  (** the statement at each index *)
    gi_pred_ids : int list array;  (** each statement's predecessors, by index *)
    gi_rpo : int list;
        (** the indices in reverse postorder of the successor graph, which is
            the order a forward dataflow problem converges fastest in: a
            statement is visited after the statements that can precede it,
            except across a back edge, so information crosses the graph in one
            sweep per loop nesting level instead of one edge per sweep *)
  }

  let index_graph prev_env stmts =
    let all =
      let seen = LinkedStatementHashtbl.create (List.length stmts + 1) in
      let acc = ref [] in
      let rec visit stmt =
        if not (LinkedStatementHashtbl.mem seen stmt) then (
          LinkedStatementHashtbl.replace seen stmt ();
          acc := stmt :: !acc;
          List.iter (StatementEnv.get stmt prev_env) ~f:visit;
          List.iter (get_next_statements stmt) ~f:visit)
      in
      List.iter stmts ~f:visit;
      List.rev !acc
    in
    let size = List.length all in
    let idx = LinkedStatementHashtbl.create (size + 1) in
    List.iteri all ~f:(fun i stmt -> LinkedStatementHashtbl.replace idx stmt i);
    let preds = LinkedStatementHashtbl.create (size + 1) in
    List.iter (StatementEnv.entries prev_env) ~f:(fun (key, value) ->
        LinkedStatementHashtbl.replace preds key value);
    let preds_of stmt =
      match LinkedStatementHashtbl.find_opt preds stmt with
      | Some l -> l
      | None -> []
    in
    let cap =
      1
      + List.fold all ~init:0 ~f:(fun m stmt ->
          max m (LinkedStatement.id_of stmt))
    in
    let at = Array.create ~len:size None in
    List.iter all ~f:(fun stmt ->
        match LinkedStatementHashtbl.find_opt idx stmt with
        | Some i -> at.(i) <- Some stmt
        | None -> ());
    let rpo =
      let visited = Array.create ~len:size false in
      let post = ref [] in
      let rec go i =
        if not visited.(i) then (
          visited.(i) <- true;
          (match at.(i) with
          | None -> ()
          | Some stmt ->
              List.iter (get_next_statements stmt) ~f:(fun nxt ->
                  match LinkedStatementHashtbl.find_opt idx nxt with
                  | Some j -> go j
                  | None -> ()));
          post := i :: !post)
      in
      List.iter all ~f:(fun stmt ->
          match LinkedStatementHashtbl.find_opt idx stmt with
          | Some i -> go i
          | None -> ());
      !post
    in
    let pred_ids = Array.create ~len:size [] in
    List.iter all ~f:(fun stmt ->
        match LinkedStatementHashtbl.find_opt idx stmt with
        | None -> ()
        | Some i ->
            pred_ids.(i) <-
              List.filter_map (preds_of stmt) ~f:(fun prev ->
                  LinkedStatementHashtbl.find_opt idx prev));
    {
      gi_all = all;
      gi_size = size;
      gi_idx = idx;
      gi_preds = preds_of;
      gi_cap = cap;
      gi_at = at;
      gi_pred_ids = pred_ids;
      gi_rpo = rpo;
    }

  (* Which definitions of this variable reach the entry of each statement.
     Forward, and the payload is a bitset over the variable's own definitions,
     of which there are a handful -- one word covers 62 of them.  The entry of
     the program holds definition zero, the value the program starts with. *)
  let get_rd gi entry varname =
    let def_of = Array.create ~len:gi.gi_size (-1) in
    let ndefs = ref 1 in
    List.iter gi.gi_all ~f:(fun stmt ->
        if is_def varname stmt then (
          match LinkedStatementHashtbl.find_opt gi.gi_idx stmt with
          | Some i ->
              def_of.(i) <- !ndefs;
              Stdlib.incr ndefs
          | None -> ()));
    let cap = !ndefs in
    let rd_in = Array.create ~len:gi.gi_size Bits.empty in
    (* what flows out of a definition is the same set every time it is asked
       for, and it used to be built afresh on every edge the worklist walked *)
    let out_fixed = Array.create ~len:gi.gi_size Bits.empty in
    Array.iteri def_of ~f:(fun i d ->
        if d >= 0 then out_fixed.(i) <- Bits.singleton ~cap d);
    let out_of i = if def_of.(i) < 0 then rd_in.(i) else out_fixed.(i) in
    (match LinkedStatementHashtbl.find_opt gi.gi_idx entry with
    | Some i -> rd_in.(i) <- Bits.singleton ~cap 0
    | None -> ());
    (* a worklist: a statement is revisited only when something reaching it
       changed, and an entry can change at most as often as there are
       definitions *)
    let queue = Stdlib.Queue.create () in
    let queued = Array.create ~len:gi.gi_size false in
    let push stmt =
      match LinkedStatementHashtbl.find_opt gi.gi_idx stmt with
      | Some i ->
          if not queued.(i) then (
            queued.(i) <- true;
            Stdlib.Queue.add i queue)
      | None -> ()
    in
    List.iter gi.gi_rpo ~f:(fun i ->
        if not queued.(i) then (
          queued.(i) <- true;
          Stdlib.Queue.add i queue));
    while not (Stdlib.Queue.is_empty queue) do
      let i = Stdlib.Queue.pop queue in
      queued.(i) <- false;
      match gi.gi_at.(i) with
      | None -> ()
      | Some stmt ->
          let joined =
            List.fold gi.gi_pred_ids.(i) ~init:rd_in.(i) ~f:(fun acc j ->
                Bits.union acc (out_of j))
          in
          if not (Bits.equal joined rd_in.(i)) then (
            rd_in.(i) <- joined;
            List.iter (get_next_statements stmt) ~f:push)
    done;
    (rd_in, def_of, cap)

  let get_rg ?(defs = true) gi entry varname stmts : rg_t =
    (* one pass to work out what each statement reads of this variable *)
    let own_tbl = LinkedStatementHashtbl.create (gi.gi_size + 1) in
    List.iter gi.gi_all ~f:(fun stmt ->
        LinkedStatementHashtbl.replace own_tbl stmt (own_of varname stmt));
    let own_of stmt =
      match LinkedStatementHashtbl.find_opt own_tbl stmt with
      | Some own -> own
      | None -> own_of varname stmt
    in
    let reads = Array.create ~len:gi.gi_size false in
    List.iter gi.gi_all ~f:(fun stmt ->
        match LinkedStatementHashtbl.find_opt gi.gi_idx stmt with
        | Some i ->
            reads.(i) <-
              (match own_of stmt with
              | `Kill rs | `Read rs -> Stdlib.(rs <> Never)
              | _ -> false)
        | None -> ());
    let rd, def_of, ndefs =
      if defs then get_rd gi entry varname
      else (Array.create ~len:gi.gi_size Bits.empty, [||], 1)
    in
    let rg0 =
      {
        rg_idx = gi.gi_idx;
        rg_tags = Array.create ~len:gi.gi_size Never;
        rg_rd = rd;
        rg_reads = reads;
        rg_def = def_of;
        rg_ndefs = ndefs;
      }
    in
    List.fold ~init:rg0 stmts ~f:(fun rg stmt ->
        get_rg_dfs own_of gi.gi_preds stmt rg)

  let get_rgenv ?(defs = true) spec_fv prev_env stmt : rgenv_t =
    let stmts = get_all_statements stmt in
    let gi = index_graph prev_env stmts in
    let rgdata =
      LinkedStatement.get_used_vars_from stmt
      |> Variables.to_list
      |> List.fold_left ~init:[] ~f:(fun rgdata varname ->
          if Variables.is_mem spec_fv varname then rgdata
          else
            ( (Ident.Tvar (fst varname), snd varname),
              get_rg ~defs gi stmt (fst varname) stmts )
            :: rgdata)
      |> List.rev
    in
    RGENV (defs, rgdata)
end

module RemoveAssign : sig
  val optimize : print:(string lazy_t -> unit) -> target -> target
end = struct
  let remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts) =
    match get_next_statements stmt_key with
    | [ next_stmt_key ] ->
        if not @@ phys_equal stmt_key next_stmt_key then
          let query_stmt_key =
            Util.remove_nobranch ~query:query_stmt_key stmt_key stmt_keys
          in
          let new_stmts = StatementEnv.remove stmt_key new_stmts in
          (query_stmt_key, new_stmts)
        else
          (* case: self loop -> replace with nop loop *)
          let new_stmt = mk_nop (ref stmt_key) in
          (* replace and return *)
          (query_stmt_key, StatementEnv.update stmt_key new_stmt new_stmts)
    | _ -> assert false

  let sub_stmt using_stmt_key tvar term new_stmts =
    if StatementEnv.exists using_stmt_key new_stmts then
      let using_stmt =
        StatementEnv.get using_stmt_key new_stmts |> sub tvar term
      in
      StatementEnv.update using_stmt_key using_stmt new_stmts
    else new_stmts

  let is_nondet_term nondet_tvar term =
    (*ToDo*) Set.mem (Term.tvs_of term) nondet_tvar

  let rec is_nondet_formula nondet_tvar = function
    | Formula.Atom (atom, _) -> (*ToDo*) Set.mem (Atom.tvs_of atom) nondet_tvar
    | UnaryOp (_, phi, _) -> is_nondet_formula nondet_tvar phi
    | BinaryOp (_, phi1, phi2, _) ->
        is_nondet_formula nondet_tvar phi1 && is_nondet_formula nondet_tvar phi2
    | Bind (_, _bounds, _phi, _) -> (* ToDo *) false
    | LetRec (_funcs, _phi, _) -> (* ToDo *) false
    | LetFormula (_tvar, _sort, _def, _body, _info) -> (* ToDo *) false

  let check_nondet_if nondet_tvar stmt =
    if is_if stmt then
      let cond_fml, _, _ = let_if stmt in
      is_nondet_formula nondet_tvar cond_fml
    else false

  let check_nondet_assign nondet_tvar stmt =
    if is_assign stmt then
      let _, term, _ = let_assign stmt in
      is_nondet_term nondet_tvar term
    else false

  (* let rec remove_assign_one rgenv stmt_key stmt_keys (query_stmt_key, new_stmts) =
     if StatementEnv.exists stmt_key new_stmts then
      let stmt = StatementEnv.get stmt_key new_stmts in
      (* remove assign stmt *)
      if is_assign stmt then
        let varname, term, nxt_stmt_key = let_assign stmt in
        let tvar = Ident.Tvar varname in
        if ReadGraph.rgenv_mem tvar rgenv then
          let rs = ReadGraph.rgenv_get tvar rgenv |> ReadGraph.rg_get !nxt_stmt_key in
          match rs with
          | ReadGraph.Never ->
            (* remove *)
            remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts)
          | ReadGraph.Once using_stmt_keys | ReadGraph.TwiceOrMore using_stmt_keys ->
            (*
              substitution
              1. assignment value is const
              2. before execute substituted statement (reading the assigned variable) the assignment statement is always called
                 and other assignment statements for the variable are never callsed
            *)
            (* cond 1 *)
            let can_subst =
              Term.tvs_of term
              |> Set.is_empty
            in
            if can_subst then
              let using_stmt_keys = StatementEnv.keys using_stmt_keys in
              (* sub, cond 2 *)
              let rev_rgenv =
                ReadGraph.rgenv_rev rgenv
                |> Fn.Fn.flip (List.Assoc.find_exn ~equal:Stdlib.(=)) tvar
              in
              let new_stmts, can_remove =
                List.fold
                  (fun (new_stmts, can_remove) using_stmt_key ->
                     let can_subst =
                       StatementEnv.get_exn using_stmt_key rev_rgenv
                       |> List.length
                       |> (fun len -> len = 1)
                     in
                     if can_subst then
                       sub_stmt using_stmt_key tvar term new_stmts, can_remove
                     else
                       new_stmts, false
                  )
                  (new_stmts, true)
                  using_stmt_keys
              in
              (* remove *)
              let query_stmt_key, new_stmts =
                if can_remove then
                  remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts)
                else
                  query_stmt_key, new_stmts
              in
              (* check *)
              List.fold
                (fun (query_stmt_key, new_stmts) using_stmt_key ->
                   remove_assign_one rgenv using_stmt_key stmt_keys (query_stmt_key, new_stmts)
                )
                (query_stmt_key, new_stmts)
                using_stmt_keys
            else
              query_stmt_key, new_stmts
        else
          (* case: <tvar> \in <phi> *)
          query_stmt_key, new_stmts
      else if is_nondet_int_assign stmt then
        let varname, nxt_stmt_key = let_nondet_int_assign stmt in
        let tvar = Ident.Tvar varname in
        if ReadGraph.rgenv_mem tvar rgenv then
          let rs = ReadGraph.rgenv_get tvar rgenv |> ReadGraph.rg_get !nxt_stmt_key in
          match rs with
          | Never ->
            remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts)
          | Once using_stmt_keys ->
            let using_stmt_keys = StatementEnv.keys using_stmt_keys in
            (* TODO: add a LinkedStatement type where we can use a temporary nondet var *)
            (* TODO: truthy / falthy *)
            (* TODO(bug): check whether any path from assign stmt to stmt using the assigned var don't pass an assignment *)
            (* Not reproduced.  The [can_remove] test below demands, besides
               every use being a nondet-if, that the *reverse* read graph give
               the use exactly one reaching assignment ([len = 1]), which is
               what the note above asks for.  Three shapes answer correctly
               under [-p cltl]: an assignment overwriting the nondet before
               the use (valid), two assignments reaching one use with the
               second unbounded (invalid), and a nondet assignment inside a
               branch whose use is also reachable without it (valid).  So
               either the [len = 1] guard covers the case or the input that
               breaks it has another shape; the note stays. *)
            let rev_rgenv =
              ReadGraph.rgenv_rev rgenv
              |> flip (List.Assoc.find_exn ~equal:Stdlib.(=)) tvar
            in
            let can_remove =
              List.for_all
                (fun using_stmt_key ->
                   let using_stmt = StatementEnv.get using_stmt_key new_stmts in
                   is_nondet_if tvar using_stmt
                   &&
                   StatementEnv.get_exn using_stmt_key rev_rgenv
                   |> List.length
                   |> (fun len -> len = 1)
                )
                using_stmt_keys
            in
            if can_remove then
              (* remove *)
              let query_stmt_key, new_stmts = remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts) in
              (* sub *)
              let new_stmts =
                List.fold
                  (fun new_stmts using_stmt_key ->
                     let using_stmt = StatementEnv.get using_stmt_key new_stmts in
                     let _, t_stmt, f_stmt = let_if using_stmt in
                     let using_stmt = mk_nondet t_stmt f_stmt in
                     if StatementEnv.exists using_stmt_key new_stmts then
                       StatementEnv.update using_stmt_key using_stmt new_stmts
                     else
                       new_stmts
                  )
                  new_stmts
                  using_stmt_keys
              in
              query_stmt_key, new_stmts
            else
              query_stmt_key, new_stmts
          | TwiceOrMore _ ->
            query_stmt_key, new_stmts
        else
          (* case: <tvar> \in <phi> *)
          query_stmt_key, new_stmts
      else
        (* case: other stmts *)
        query_stmt_key, new_stmts
     else
      (* already deleted *)
      query_stmt_key, new_stmts *)

  type sub_value_t = T_VALID | T_INVALID | T_NONDET | T_LIT of Term.t

  let check_nondet ~has_init_def rc = ReadGraph.is_once rc && not has_init_def

  (* [assumed] holds the variables an [assume] of the initialisation section
     constrains.  A read of such a variable must never be replaced by a fresh
     nondeterministic value: the assumption stays behind on the old variable
     and the constraint is lost -- a global [int y = nondet_char()] read once
     made [x = y] into [x = nondet_int()] and [[](x < 1000)] came out
     [invalid]. *)
  (* Which surviving statements assign each variable.  The scan below cares
     only about those: everything else leaves the value it is folding
     unchanged, so grouping turns a walk of the whole graph, per variable read
     by a statement, into a walk of that variable's own assignments.

     The grouping holds the environment's *cells* rather than the statements it
     found in them, because a substitution assigns through a cell and does not
     change which variable the statement assigns -- so a later read of the cell
     sees the substituted statement and the grouping stays right. Only adding
     or removing a statement can invalidate it, and both build a new list,
     which is what [spine] lets the caller notice. Built once per statement it
     was 17.4 s of the 19.2 s scan on a 7,892-statement program. *)
  let group_assignments new_stmts =
    let assigns_to = Stdlib.Hashtbl.create 16 in
    List.iter (StatementEnv.cells new_stmts) ~f:(fun cell ->
        let stmt' = !cell in
        let name =
          if is_assign stmt' then
            let varname', _, _ = let_assign stmt' in
            Some varname'
          else if is_nondet_int_assign stmt' then
            Some (fst (let_nondet_int_assign stmt'))
          else if is_nondet_real_assign stmt' then
            Some (fst (let_nondet_real_assign stmt'))
          else None
        in
        match name with
        | None -> ()
        | Some name ->
            Stdlib.Hashtbl.replace assigns_to name
              (cell
              ::
                (try Stdlib.Hashtbl.find assigns_to name
                 with Stdlib.Not_found -> [])));
    fun name ->
      List.map ~f:( ! )
        (try Stdlib.Hashtbl.find assigns_to name with Stdlib.Not_found -> [])

  let sub_assign_one ~assumed ~assigning init_state rgenv stmt_key _stmt_keys
      (query_stmt_key, new_stmts) =
    let may_be_nondet varname = not (Set.mem assumed (fst varname)) in
    if StatementEnv.exists stmt_key new_stmts then (
      let stmt = StatementEnv.get stmt_key new_stmts in
      get_read_vars stmt |> Variables.to_list
      |> List.fold ~init:(query_stmt_key, new_stmts)
           ~f:(fun (query_stmt_key, new_stmts) varname ->
             let tvar = Ident.Tvar (fst varname) in
             if ReadGraph.rgenv_mem (tvar, snd varname) rgenv then
               (* TODO: simplify terms *)
               (* TODO: improve performance *)
               let rg = ReadGraph.rgenv_get (tvar, snd varname) rgenv in
               let rc_init = ReadGraph.rg_get_initial query_stmt_key rg in
               let has_init_def =
                 State.mem (fst varname) init_state
                 && ReadGraph.mem stmt_key rc_init
               in
               let init_value =
                 if ReadGraph.mem stmt_key rc_init then
                   if State.mem (fst varname) init_state then
                     let term = State.get (fst varname) init_state in
                     (* a nondet-initialised variable's "initial value" is
                        the variable itself (State.of_inits): not a literal,
                        so nothing is substituted (this was an assert) *)
                     if Term.tvs_of term |> Set.is_empty then T_LIT term
                     else T_INVALID
                   else if
                     may_be_nondet varname && check_nondet ~has_init_def rc_init
                   then T_NONDET
                   else T_INVALID
                 else T_VALID
               in
               let value =
                 List.fold ~init:init_value
                   (assigning (fst varname))
                   ~f:(fun value stmt' ->
                     if Stdlib.(value = T_INVALID) then T_INVALID
                     else
                       let update new_value =
                         if
                           Stdlib.(value = T_VALID)
                           || Stdlib.(new_value = value)
                         then new_value
                         else T_INVALID
                       in
                       if is_assign stmt' then
                         let varname', term, nxt_stmt_key = let_assign stmt' in
                         if
                           Stdlib.((varname', Term.sort_of term) = varname)
                           && ReadGraph.rg_get_def ~def:stmt' !nxt_stmt_key rg
                              |> ReadGraph.mem stmt_key
                         then
                           if Set.is_empty @@ Term.tvs_of term then
                             update (T_LIT term)
                           else T_INVALID
                         else value
                       else if is_nondet_int_assign stmt' then
                         let varname', nxt_stmt_key =
                           let_nondet_int_assign stmt'
                         in
                         let rc =
                           ReadGraph.rg_get_def ~def:stmt' !nxt_stmt_key rg
                         in
                         if
                           Stdlib.((varname', T_int.SInt) = varname)
                           && ReadGraph.mem stmt_key rc
                         then
                           if
                             may_be_nondet varname
                             && check_nondet ~has_init_def rc
                           then update T_NONDET
                           else T_INVALID
                         else value
                       else if is_nondet_real_assign stmt' then
                         let varname', nxt_stmt_key =
                           let_nondet_real_assign stmt'
                         in
                         let rc =
                           ReadGraph.rg_get_def ~def:stmt' !nxt_stmt_key rg
                         in
                         if
                           Stdlib.((varname', T_real.SReal) = varname)
                           && ReadGraph.mem stmt_key rc
                         then
                           if
                             may_be_nondet varname
                             && check_nondet ~has_init_def rc
                           then update T_NONDET
                           else T_INVALID
                         else value
                       else value)
               in
               match value with
               | T_VALID ->
                   if true (*ToDo*) then (query_stmt_key, new_stmts)
                   else
                     failwith
                     @@ sprintf
                          "internal error: can't reach the statement:\n\
                           %s\n\n\
                           original:\n\
                           %s\n\n\
                           varname: (%s, %s)\n"
                          (string_of stmt) (string_of stmt_key) (fst varname)
                          (Term.str_of_sort (snd varname))
               | T_NONDET ->
                   if check_nondet_if tvar stmt then
                     let _, t_stmt, f_stmt = let_if stmt in
                     let stmt = mk_nondet t_stmt f_stmt in
                     ( query_stmt_key,
                       StatementEnv.update stmt_key stmt new_stmts )
                   else if check_nondet_assign tvar stmt then
                     let varname, t, nxt_stmt = let_assign stmt in
                     let stmt =
                       if T_int.is_sint t then
                         mk_nondet_int_assign varname nxt_stmt
                       else if T_real.is_sreal t then
                         mk_nondet_real_assign varname nxt_stmt
                       else (*ToDo*)
                         mk_nondet_int_assign varname nxt_stmt
                     in
                     ( query_stmt_key,
                       StatementEnv.update stmt_key stmt new_stmts )
                   else (query_stmt_key, new_stmts)
               | T_LIT term ->
                   (query_stmt_key, sub_stmt stmt_key tvar term new_stmts)
               | T_INVALID -> (query_stmt_key, new_stmts)
             else (* case: <tvar> \in <phi> *)
               (query_stmt_key, new_stmts)))
    else (* already deleted *)
      (query_stmt_key, new_stmts)

  let remove_unused_assign_one rgenv stmt_key stmt_keys
      (query_stmt_key, new_stmts) =
    if StatementEnv.exists stmt_key new_stmts then
      let stmt = StatementEnv.get stmt_key new_stmts in
      if
        is_assign stmt || is_nondet_int_assign stmt
        || is_nondet_real_assign stmt
      then
        let varname, nxt_stmt_key =
          if is_assign stmt then
            let varname, t, nxt_stmt_key = let_assign stmt in
            ((varname, Term.sort_of t), nxt_stmt_key)
          else if is_nondet_int_assign stmt then
            let varname, nxt_stmt_key = let_nondet_int_assign stmt in
            ((varname, T_int.SInt), nxt_stmt_key)
          else if is_nondet_real_assign stmt then
            let varname, nxt_stmt_key = let_nondet_real_assign stmt in
            ((varname, T_real.SReal), nxt_stmt_key)
          else failwith "remove_unused_assign_one: not an assign stmt"
        in
        let tvar = Ident.Tvar (fst varname) in
        if
          ReadGraph.rgenv_mem (tvar, snd varname) rgenv
          && (*ToDo*)
          ReadGraph.is_never
            (ReadGraph.rgenv_get (tvar, snd varname) rgenv
            |> ReadGraph.rg_get !nxt_stmt_key)
        then remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts)
        else (* case: <tvar> \in <phi> *)
          (query_stmt_key, new_stmts)
      else (query_stmt_key, new_stmts)
    else (* already deleted *)
      (query_stmt_key, new_stmts)

  (* The read graph is a function of the statement graph, and the graph is
     unchanged by a pass that reports no change: [Util.replace_stmt] assigns
     through the next-statement cells of statements that are themselves mutable
     and cyclic, so an identity replacement leaves every statement the same
     object -- which matters here because the read graph is indexed by physical
     identity. A caller that knows nothing has changed since a graph was built
     may therefore pass it back in, and both passes of a round, and the first
     pass of the next round, can share one. *)
  let rg_of ~reuse build =
    match reuse with Some rgenv -> rgenv | None -> build ()

  let sub_assign ~print ?rgenv is_print_for_debug stmts inits spec_fv query_stmt
      =
    let new_stmts = Util.mk_replacer stmts in
    let prev_env = Util.get_prev_env query_stmt in
    let rgenv =
      rg_of ~reuse:rgenv (fun () ->
          ReadGraph.get_rgenv spec_fv prev_env query_stmt)
    in
    if is_print_for_debug then
      print
      @@ lazy
           (sprintf "rgenv:\n%s\n\n"
              (ReadGraph.string_of_rgenv query_stmt rgenv));
    let init_state = State.of_inits inits in
    let assumed =
      Set.Poly.union_list
      @@ List.filter_map inits ~f:(fun init ->
          if Init.is_assume init then
            Some
              (Set.Poly.map ~f:Ident.name_of_tvar
              @@ Formula.tvs_of @@ Init.let_assume init)
          else None)
    in
    let cache = ref None in
    let assigning_for new_stmts =
      match !cache with
      | Some (spine, f) when phys_equal spine (StatementEnv.spine new_stmts) -> f
      | _ ->
          let f = group_assignments new_stmts in
          cache := Some (StatementEnv.spine new_stmts, f);
          f
    in
    List.fold ~init:(query_stmt, new_stmts) stmts
      ~f:(fun (query_stmt, new_stmts) stmt ->
        sub_assign_one ~assumed
          ~assigning:(assigning_for new_stmts)
          init_state rgenv stmt stmts (query_stmt, new_stmts))
    |> fun (query_stmt, new_stmts) ->
    let changed =
      StatementEnv.length new_stmts <> List.length stmts
      || not (StatementEnv.is_identity new_stmts)
    in
    (Util.replace_stmt ~query:query_stmt new_stmts, changed, rgenv)

  (* This pass asks only whether the value reaching a statement is read at all,
     which the backward pass answers by itself, so the forward pass that
     computes reaching definitions is skipped here. *)
  let remove_unused_assign ?rgenv stmts spec_fv query_stmt =
    let new_stmts = Util.mk_replacer stmts in
    let prev_env = Util.get_prev_env query_stmt in
    let rgenv =
      rg_of ~reuse:rgenv (fun () ->
          ReadGraph.get_rgenv ~defs:false spec_fv prev_env query_stmt)
    in
    let query_stmt, new_stmts =
      List.fold ~init:(query_stmt, new_stmts) stmts
        ~f:(fun (query_stmt, new_stmts) stmt ->
          remove_unused_assign_one rgenv stmt stmts (query_stmt, new_stmts))
    in
    let changed =
      StatementEnv.length new_stmts <> List.length stmts
      || not (StatementEnv.is_identity new_stmts)
    in
    (Util.replace_stmt ~query:query_stmt new_stmts, changed, rgenv)

  let optimize_stmt ~print inits spec_fv stmt =
    (* Each round is a function of the graph it is given, so once a round leaves
       the graph alone every later round would too: stop there rather than
       running out the count. Both passes cost a whole-program dataflow fixpoint
       apiece, and the ten rounds were the bulk of the frontend's time -- on a
       loop body of sequential conditionals every one of the ten was a no-op,
       the graph's printed form unchanged from the first. The count stays as the
       bound it always was, for a graph that keeps shrinking. *)
    let rec rep is_first n reusable stmt =
      if n = 0 then stmt
      else
        let stmts = get_all_statements stmt in
        let stmt, changed1, rgenv =
          sub_assign ~print ?rgenv:reusable is_first stmts inits spec_fv stmt
        in
        let stmts = get_all_statements stmt in
        let stmt, changed2, rgenv =
          remove_unused_assign
            ?rgenv:(if changed1 then None else Some rgenv)
            stmts spec_fv stmt
        in
        if changed1 || changed2 then
          rep false (n - 1)
            (if changed2 || not (ReadGraph.rgenv_has_defs rgenv) then None
             else Some rgenv)
            stmt
        else stmt
    in
    rep false 10 None stmt
  (* rep true 10 stmt *)

  let optimize ~print (spec_fv, decls, inits, stmt) =
    (spec_fv, decls, inits, optimize_stmt ~print inits spec_fv stmt)
end

module RemoveNop : sig
  val optimize : target -> target
end = struct
  let optimize_stmt query_stmt =
    let stmts = get_all_statements query_stmt in
    List.fold ~init:query_stmt stmts ~f:(fun query_stmt stmt ->
        if is_nop stmt then Util.remove_nobranch ~query:query_stmt stmt stmts
        else query_stmt)

  let optimize (spec_fv, decls, inits, stmt) =
    (spec_fv, decls, inits, optimize_stmt stmt)
end

(*
  if there doesn't exists an assign stmt for phivars or an assume stmt after some stmt, remove the stmt
*)
module RemoveTrailingNoValueChanged : sig
  val optimize : target -> target
end = struct
  let rec dfs prev_env stmt used =
    if StatementEnv.exists stmt used then used
    else
      let used = StatementEnv.add stmt used in
      StatementEnv.get stmt prev_env
      |> List.fold ~init:used ~f:(fun used prev_stmt ->
          dfs prev_env prev_stmt used)

  let optimize_stmt spec_fv query_stmt =
    let stmts = get_all_statements query_stmt in
    let prev_env = Util.get_prev_env query_stmt in
    let noreplace_stmts =
      List.fold ~init:(StatementEnv.mk_empty ()) stmts ~f:(fun used stmt ->
          if
            is_assume stmt
            || Fn.non Variables.is_empty
                 (Variables.inter (get_written_vars stmt) spec_fv)
          then dfs prev_env stmt used
          else used)
    in
    let new_stmts = Util.mk_replacer stmts in
    List.fold ~init:new_stmts stmts ~f:(fun new_stmts stmt ->
        if StatementEnv.exists stmt noreplace_stmts then new_stmts
        else StatementEnv.update stmt (mk_exit ()) new_stmts)
    |> Util.replace_stmt ~query:query_stmt

  let optimize (spec_fv, decls, inits, stmt) =
    (spec_fv, decls, inits, optimize_stmt spec_fv stmt)
end

let optimize ~print spec_fv decls inits stmt =
  (spec_fv, decls, inits, stmt)
  |> RemoveAssign.optimize ~print
  |> RemoveNop.optimize |> RemoveTrailingNoValueChanged.optimize
(* TODO: for assumes *)
