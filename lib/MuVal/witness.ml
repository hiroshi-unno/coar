(* The grounds of a MuVal verdict as an in-process value, for a caller that
   builds a verification witness from it (an SV-COMP YAML witness: loop
   invariants, loop transition invariants, a violation path).  The value is
   about the muCLP problem MuVal RECEIVED, in its predicate and parameter
   names, never about the problem MuVal's optimizer made of it.

   Contract (what a consumer may rely on):

   - [side] is the side whose answer decided the verdict; nothing the other
     side produced is in the value.
   - [entries] lists every predicate of the received problem, in the received
     order, exactly once, as an [Invariant] or a [Skipped] with its reason,
     followed by one [Ranking] or [Skipped] per least-fixpoint predicate.  An
     invariant is a formula over the predicate's received parameters (by
     their received names); a parameter the optimizer erased because every
     application passes one constant [c] comes back as the conjunct [x = c]
     (also listed in [erased]); an erased irrelevant parameter is not
     mentioned; a predicate the optimizer removed gets its body with the
     other invariants substituted.  Integers are mathematical integers or
     bit-vector terms, as the received problem has them.
   - status [Inductive]: the invariants AS A WHOLE were checked by Z3 to be
     closed for the received problem (each implies its body under the
     assignment, and the query holds under it), so each holds of every state
     reachable at its predicate.  One member of an assignment that failed the
     check proves nothing, so a failed or undecided check withholds every
     invariant (each becomes [Skipped] with reason [check-failed]).
   - a ranking's [transition] is a relation over [prev] (the parameters at
     an earlier visit, named [<x>__prev]) and [params] (the current visit);
     it is written only when it holds between ANY two visits of the
     predicate along one execution, so it is a loop transition invariant.
     Each piece is a discriminator and a lexicographic tuple of terms; a
     component below zero reads as undefined.
   - [invariants] is the map from each received predicate with an
     [Invariant] entry to its formula: the shape a caller that only wants
     invariants reads.
   - [violation], on an invalid verdict decided by the primal's refutation, is
     a path of the received problem that has been REPLAYED on it by ground
     evaluation (see [Violation]); nothing unreplayed is ever put here.
     On a termination problem it is a LASSO ([cycle_from]): a stem and one
     loop round whose end re-reaches the round's first configuration, also
     replayed; failing that, a problem whose program side has one cut point
     gets the [Cycle_head] entry instead.

   - what a consumer may DROP from a violation path.  Weakening a value
     (writing a waypoint's constraint as [1]) keeps every execution the path
     represents.  Dropping a step's waypoint does not in general: in a witness
     a [follow] waypoint matches the FIRST evaluation of its location after
     the previous waypoint, so once a waypoint inside a loop is dropped, the
     next kept waypoint may match an earlier iteration than the one the path
     took.  A waypoint may be dropped only when the segment it would have
     ended cannot pass the next kept waypoint's location (that location is
     not visited between the two); otherwise the path is cut there (written
     up to the last waypoint that can be kept, followed by the target) or
     the witness falls back to the target alone.

   [lines] prints the value as one S-expression per line (the debug output;
   the format is stable). *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

type side = Primal | Primal_ad | Dual | Ground

let str_of_side = function
  | Primal -> "primal"
  | Primal_ad -> "primal-ad"
  | Dual -> "dual"
  | Ground -> "ground"

type invariant_status =
  | Inductive  (** the whole assignment passed the closedness check *)
  | Unchecked_invariant  (** the configuration declined the check *)

type invariant = {
  name : Ident.pvar;
  params : sort_env_list;  (** the received parameters, in order *)
  kind : Predicate.fixpoint;
  formula : Formula.t;
  erased : (Ident.tvar * Term.t) list;
      (** the parameters the optimizer erased as constant, with the constant;
          already conjoined into [formula] *)
  status : invariant_status;
}

type ranking_status =
  | Direct_returns_checked
      (** Z3 checked the decrease on every return through [fix] predicates *)
  | Ranking_unchecked of string option
      (** not checked; with the reason when the check had nothing to say *)

type ranking = {
  rname : Ident.pvar;
  rparams : sort_env_list;
  pieces : (Formula.t * Term.t list) list;
      (** (discriminator, lexicographic tuple) over [rparams] *)
  prev : sort_env_list;  (** [rparams] renamed [<x>__prev] *)
  transition : Formula.t;  (** over [prev] and [rparams] *)
  rstatus : ranking_status;
}

type skipped = {
  subject : Ident.pvar option;  (** [None]: the answer as a whole *)
  reason : string;
  detail : string;
}

(* -- Violation paths ------------------------------------------------------- *)

type binding = { var : Ident.tvar; sort : Sort.t; value : Term.t }

(* What happens inside one step, in execution order: a universally bound
   variable of the step's body taking its value (a nondeterministic value,
   or the values a called function returns), or the subtree of one child
   step (a configuration the body reaches). *)
type event = Bind of binding | Child of int

type step = {
  index : int;  (** the position in [steps], which is preorder *)
  pred : Ident.pvar;  (** the received predicate *)
  args : binding list;  (** its received parameters with their values *)
  events : event list;
  parent : int option;
}

type error = {
  estep : int;
      (** the step whose body is false by its own atoms at the END of the
          execution: the in-order last leaf, reached from the query through the
          last falsified part of each body (a call's return summary is a subtree
          that ends in a return, never the error) *)
  leaf : int option;
      (** which [false] literal of the step's received body made it false,
          numbered from 0 in the body's left-to-right order; [None] when the
          falsifying atom is not a [false] literal *)
}

type violation = {
  source : string;  (** where the candidate came from, e.g. [refutation] *)
  initial : binding list;  (** the query's universally bound variables *)
  roots : int list;  (** the steps the query reaches, in order *)
  steps : step list;
      (** preorder of the refutation tree = the program's execution order (given
          the frontend's encoding: each binder one nondeterministic value, met
          in execution order) *)
  error : error;
      (** for a lasso ([cycle_from = Some _]): [estep] is the step whose
          falsification reads the back edge, [leaf] is [None] *)
  cycle_from : int option;
      (** [None]: a finite path that ends in an error (safety).  [Some k]: a
          LASSO of a termination problem: the last spine step (the step
          [error.estep]) reads, as false, the application of step [k]'s
          predicate at exactly step [k]'s arguments, so the steps [k] to the
          end (preorder) are one round of a loop that the program can repeat
          forever with the same nondeterministic values; the steps before [k]
          are the stem.  Replayed with the back edge read false, every step
          between [k] and [error.estep] on the spine is a program-side
          predicate (no return summary: no greatest fixpoint) and at least one
          is a cut point (a least fixpoint). *)
}

type entry =
  | Invariant of invariant
  | Ranking of ranking
  | Skipped of skipped
  | Cycle_head of { head : Ident.pvar; hparams : sort_env_list }
      (** on an invalid verdict of a termination problem whose program side
          has exactly one cut point [head] (the problem's only least-fixpoint
          predicate): every infinite execution passes [head] infinitely often,
          given that the frontend's cut points cut every cycle of the program
          side, so a non-termination witness whose only cycle waypoint sits at
          [head]'s loop location (constraint [1]) is valid.  No path and no
          values; checked only syntactically. *)
  | Recurrent of {
      head : Ident.pvar;
      hparams : sort_env_list;
      set : Formula.t;
          (** over [hparams]: a recurrent set of [head], a least fixpoint (a
              program-side cut point): from every state in it, one round of
              [head]'s body with the nondeterministic values chosen by fixed
              terms reaches [head] again in a state in it, checked valid by Z3
              as one quantifier-free formula; so from a state in it the
              program runs forever, passing [head] in a state of [set] at
              every visit *)
      stem : violation;
          (** a replayed path from the query to [head] at [entry]: its
              [error.estep] is the step that applies [head] at [entry];
              [cycle_from] is [None] *)
      entry : binding list;  (** [head]'s parameters at the end of the stem *)
    }

type t = {
  side : side;
  invariants : (Ident.pvar, Formula.t) Map.Poly.t;
  entries : entry list;
  violation : violation option;
}

let empty side =
  { side; invariants = Map.Poly.empty; entries = []; violation = None }

let skipped_whole side reason detail =
  { (empty side) with entries = [ Skipped { subject = None; reason; detail } ] }

(* [bindings_in_order v]: every binding of [v] in execution order (the query's
   first, then each step's events read in preorder) *)
let bindings_in_order (v : violation) =
  let arr = Array.of_list v.steps in
  let rec of_step i =
    List.concat_map arr.(i).events ~f:(function
      | Bind b -> [ b ]
      | Child j -> of_step j)
  in
  v.initial @ List.concat_map v.roots ~f:of_step

(* [binds_by_step v]: [bindings_in_order v] cut where each step begins, as an
   array indexed like [v.steps]: entry [i] holds the bindings from the start
   of step [i] to the start of the next step in preorder (to the end of the
   execution, for the last), in execution order; a binding met after a child's
   subtree returns belongs to the last step that subtree began.  The query's
   bindings ([v.initial]) come first in the first root's entry, and are
   dropped when there is no step.  Concatenated in index order the entries
   are [bindings_in_order v]. *)
let binds_by_step (v : violation) =
  let arr = Array.of_list v.steps in
  (* each entry in reverse; [owner] is the step most recently begun *)
  let out = Array.create ~len:(Array.length arr) [] in
  let owner = ref None in
  let rec visit i =
    owner := Some i;
    List.iter arr.(i).events ~f:(function
      | Bind b -> Option.iter !owner ~f:(fun k -> out.(k) <- b :: out.(k))
      | Child j -> visit j)
  in
  List.iter v.roots ~f:visit;
  (match v.roots with
  | r :: _ -> out.(r) <- out.(r) @ List.rev v.initial
  | [] -> ());
  Array.map out ~f:List.rev

(* -- SMT-LIB printing ---------------------------------------------------- *)

exception Unprintable of string

let unprintable fmt = Printf.ksprintf (fun s -> raise (Unprintable s)) fmt

let is_simple_symbol s =
  (not (String.is_empty s))
  && (not (Char.is_digit s.[0]))
  && String.for_all s ~f:(fun c ->
      Char.is_alphanum c || String.mem "~!@$%^&*_-+=<>.?/" c)

let str_of_name s =
  if is_simple_symbol s then s
  else if String.exists s ~f:(fun c -> Char.equal c '|' || Char.equal c '\\')
  then unprintable "the name %s has no SMT-LIB spelling" s
  else "|" ^ s ^ "|"

let rec str_of_sort = function
  | T_int.SInt -> "Int"
  | T_bool.SBool -> "Bool"
  | T_real.SReal -> "Real"
  | T_bv.SBV (Some n) -> sprintf "(_ BitVec %d)" n
  | T_array.SArray (i, v) ->
      sprintf "(Array %s %s)" (str_of_sort i) (str_of_sort v)
  | s -> unprintable "the sort %s" (Term.str_of_sort s)

let str_of_params params =
  "("
  ^ String.concat_map_list ~sep:" " params ~f:(fun (Ident.Tvar x, s) ->
      sprintf "(%s %s)" (str_of_name x) (str_of_sort s))
  ^ ")"

let rec str_of_formula = function
  | Formula.Atom (atom, _) -> str_of_atom atom
  | Formula.UnaryOp (Not, phi, _) -> sprintf "(not %s)" (str_of_formula phi)
  | Formula.BinaryOp (op, phi1, phi2, _) ->
      let op =
        match op with
        | And -> "and"
        | Or -> "or"
        | Imply -> "=>"
        | Iff -> "="
        | Xor -> "xor"
      in
      sprintf "(%s %s %s)" op (str_of_formula phi1) (str_of_formula phi2)
  | Formula.Bind (Forall, params, phi, _) ->
      sprintf "(forall %s %s)" (str_of_params params) (str_of_formula phi)
  | Formula.Bind (Exists, params, phi, _) ->
      sprintf "(exists %s %s)" (str_of_params params) (str_of_formula phi)
  | Formula.Bind (Random _, _, _, _) -> unprintable "a random binder"
  | Formula.LetRec _ -> unprintable "a recursive definition"
  | Formula.LetFormula _ -> unprintable "a let"

and str_of_atom = function
  | Atom.True _ -> "true"
  | Atom.False _ -> "false"
  | Atom.App (Predicate.Psym sym, [ t1; t2 ], _) -> (
      let bin s = sprintf "(%s %s %s)" s (str_of_term t1) (str_of_term t2) in
      match sym with
      | T_bool.Eq -> bin "="
      | T_bool.Neq -> sprintf "(not %s)" (bin "=")
      | T_int.Leq | T_real.RLeq -> bin "<="
      | T_int.Geq | T_real.RGeq -> bin ">="
      | T_int.Lt | T_real.RLt -> bin "<"
      | T_int.Gt | T_real.RGt -> bin ">"
      | T_bv.BVLeq (Some _, Some true) -> bin "bvsle"
      | T_bv.BVLeq (Some _, Some false) -> bin "bvule"
      | T_bv.BVGeq (Some _, Some true) -> bin "bvsge"
      | T_bv.BVGeq (Some _, Some false) -> bin "bvuge"
      | T_bv.BVLt (Some _, Some true) -> bin "bvslt"
      | T_bv.BVLt (Some _, Some false) -> bin "bvult"
      | T_bv.BVGt (Some _, Some true) -> bin "bvsgt"
      | T_bv.BVGt (Some _, Some false) -> bin "bvugt"
      | sym -> unprintable "the predicate symbol %s" (Predicate.str_of_psym sym)
      )
  | Atom.App (Predicate.Var (Ident.Pvar p, _), _, _) ->
      unprintable "an application of the predicate %s" p
  | Atom.App (pred, _, _) ->
      unprintable "the predicate %s" (Predicate.str_of pred)

and str_of_term t =
  match t with
  | Term.Var (Ident.Tvar x, _, _) -> str_of_name x
  | Term.FunApp (T_bool.Formula phi, [], _) -> str_of_formula phi
  | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _) ->
      sprintf "(ite %s %s %s)" (str_of_term c) (str_of_term a) (str_of_term b)
  | Term.FunApp (T_int.Int n, [], _) ->
      if Z.sign n < 0 then sprintf "(- %s)" (Z.to_string (Z.neg n))
      else Z.to_string n
  | Term.FunApp (T_bv.BVNum (Some n, v), [], _) ->
      (* two's complement, read modulo 2^n *)
      let v = Z.erem v (Z.shift_left Z.one n) in
      sprintf "(_ bv%s %d)" (Z.to_string v) n
  | Term.FunApp (T_int.Neg, [ a ], _) -> sprintf "(- %s)" (str_of_term a)
  | Term.FunApp (T_int.Abs, [ a ], _) -> sprintf "(abs %s)" (str_of_term a)
  | Term.FunApp (sym, [ a; b ], _) -> (
      let bin s = sprintf "(%s %s %s)" s (str_of_term a) (str_of_term b) in
      match sym with
      | T_int.Add | T_real.RAdd -> bin "+"
      | T_int.Sub | T_real.RSub -> bin "-"
      | T_int.Mul | T_real.RMul -> bin "*"
      | T_int.Div Value.Euclidean -> bin "div"
      | T_int.Rem Value.Euclidean -> bin "mod"
      | T_int.Div m | T_int.Rem m ->
          unprintable
            "integer division rounding %s (SMT-LIB has only the Euclidean one)"
            (match m with
            | Value.Euclidean -> "euclidean"
            | Truncated -> "truncated"
            | Flooring -> "flooring"
            | Ceiling -> "ceiling")
      | T_array.ASelect _ -> bin "select"
      | T_bv.BVAdd _ -> bin "bvadd"
      | T_bv.BVSub _ -> bin "bvsub"
      | T_bv.BVMul _ -> bin "bvmul"
      | _ -> unprintable "the function symbol %s" (Term.str_of_funsym sym))
  | Term.FunApp (T_array.AStore _, [ a; i; v ], _) ->
      sprintf "(store %s %s %s)" (str_of_term a) (str_of_term i) (str_of_term v)
  | Term.FunApp (T_bool.Formula _, _, _) -> unprintable "a formula term"
  | Term.FunApp (T_array.AConst (si, se), [ v ], _) ->
      sprintf "((as const %s) %s)"
        (str_of_sort (T_array.SArray (si, se)))
        (str_of_term v)
  | Term.FunApp (sym, _, _) ->
      unprintable "the function symbol %s" (Term.str_of_funsym sym)
  | _ -> unprintable "the term %s" (Term.str_of t)

(* -- The lines ------------------------------------------------------------ *)

let simplify phi =
  try Evaluator.simplify phi
  with exn_ when not (Common.Timer.is_async exn_) -> phi

let skipped_line name reason detail =
  sprintf "(skipped %s %s %S)" (str_of_name name) reason detail

let kind_str = function
  | Predicate.Mu -> "mu"
  | Predicate.Nu -> "nu"
  | Predicate.MuOrNu -> "fix"

let str_of_binding b =
  sprintf "(%s %s %s)"
    (str_of_name (Ident.name_of_tvar b.var))
    (str_of_sort b.sort) (str_of_term b.value)

let str_of_bindings bs =
  "(" ^ String.concat_map_list ~sep:" " bs ~f:str_of_binding ^ ")"

(* the violation lines: the header, the query's bindings, one [step] line per
   step in preorder (with its parent), its bindings and children in
   execution order, then the error (or the back edge of a lasso, or, for the
   stem of a recurrent set, the step that enters it) *)
let violation_lines ?enters (v : violation) =
  try
    [
      sprintf "(violation %s (source %s) (status replayed))"
        (match (v.cycle_from, enters) with
        | _, Some _ -> "nontermination-stem"
        | None, None -> "safety"
        | Some _, None -> "nontermination")
        v.source;
      sprintf "(initial %s)" (str_of_bindings v.initial);
    ]
    @ List.concat_map v.steps ~f:(fun s ->
        sprintf "(step %d %s %s%s)" s.index
          (str_of_name (Ident.name_of_pvar s.pred))
          (str_of_bindings s.args)
          (match s.parent with
          | None -> ""
          | Some p -> sprintf " (parent %d)" p)
        :: List.filter_map s.events ~f:(function
          | Bind b ->
              Some
                (sprintf "(nondet %d %s %s %s)" s.index
                   (str_of_name (Ident.name_of_tvar b.var))
                   (str_of_sort b.sort) (str_of_term b.value))
          | Child j -> Some (sprintf "(child %d %d)" s.index j)))
    @ (match (enters, v.cycle_from) with
      | Some (head, entry), _ ->
          [
            sprintf "(enters %d %s %s)" v.error.estep
              (str_of_name (Ident.name_of_pvar head))
              (str_of_bindings entry);
          ]
      | None, Some k ->
          [ sprintf "(cycle-from %d (back-edge-at %d))" k v.error.estep ]
      | None, None ->
      [
        sprintf "(error %d %s%s)" v.error.estep
          (str_of_name
             (Ident.name_of_pvar (List.nth_exn v.steps v.error.estep).pred))
          (match v.error.leaf with
          | None -> ""
          | Some n -> sprintf " (leaf %d)" n);
      ])
  with Unprintable what ->
    [ skipped_line "*" "unprintable" ("the violation path: " ^ what) ]

let line_of_entry = function
  | Recurrent { head; hparams; set; stem; entry } -> (
      let name = Ident.name_of_pvar head in
      try
        String.concat ~sep:"\n"
          (violation_lines ~enters:(head, entry) stem
          @ [
              sprintf "(recurrent %s %s %s (status checked))" (str_of_name name)
                (str_of_params hparams)
                (str_of_formula (simplify set));
            ])
      with Unprintable what -> skipped_line name "unprintable" what)
  | Cycle_head { head; hparams } -> (
      let name = Ident.name_of_pvar head in
      try
        sprintf "(cycle-head %s %s (status single-cut-point))"
          (str_of_name name) (str_of_params hparams)
      with Unprintable what -> skipped_line name "unprintable" what)
  | Skipped s ->
      skipped_line
        (match s.subject with None -> "*" | Some p -> Ident.name_of_pvar p)
        s.reason s.detail
  | Invariant i -> (
      let name = Ident.name_of_pvar i.name in
      try
        sprintf "(invariant %s %s %s (kind %s)%s (status %s))"
          (str_of_name name) (str_of_params i.params)
          (str_of_formula (simplify i.formula))
          (kind_str i.kind)
          (match i.erased with
          | [] -> ""
          | l ->
              sprintf " (erased %s)"
                (String.concat_map_list ~sep:" " l ~f:(fun (x, c) ->
                     sprintf "(%s %s)"
                       (str_of_name (Ident.name_of_tvar x))
                       (str_of_term c))))
          (match i.status with
          | Inductive -> "inductive"
          | Unchecked_invariant -> "unchecked")
      with Unprintable what -> skipped_line name "unprintable" what)
  | Ranking r -> (
      let name = Ident.name_of_pvar r.rname in
      try
        sprintf "(ranking %s %s (pieces %s) (transition %s %s) (status %s))"
          (str_of_name name) (str_of_params r.rparams)
          (String.concat_map_list ~sep:" " r.pieces ~f:(fun (d, rs) ->
               sprintf "(piece %s (%s))"
                 (str_of_formula (simplify d))
                 (String.concat_map_list ~sep:" " rs ~f:str_of_term)))
          (str_of_params r.prev)
          (str_of_formula (simplify r.transition))
          (match r.rstatus with
          | Direct_returns_checked -> "direct-returns-checked"
          | Ranking_unchecked None -> "unchecked"
          | Ranking_unchecked (Some why) -> sprintf "unchecked %S" why)
      with Unprintable what -> skipped_line name "unprintable" what)

(* [lines w]: the certificate lines of [w], without the verdict line *)
let lines (w : t) =
  [ "(certificate-format 1)"; sprintf "(side %s)" (str_of_side w.side) ]
  @ (match w.violation with None -> [] | Some v -> violation_lines v)
  @ List.map w.entries ~f:line_of_entry
