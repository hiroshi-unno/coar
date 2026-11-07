(* The direct translation of a program to a muCLP problem: the functions
   reachable from [main] with integer
   parameters, structs passed by pointer (byval, sret) and integer or struct
   results, calls and recursion without inlining, integer SSA values and
   struct values as tuples, global and local objects in memory split into
   leaf components, BV and Int mode under both integer readings, for
   unreach-call and termination.

   Each kept program point (a function's entry, the cut points, the heads of
   blocks reached by two or more edges) gets a predicate over the SSA
   values live there and the globals, and in a called function also a return
   summary.  A block reached by one edge is not kept: its
   body is built where that edge is taken.  A body is built forward, in
   continuation-passing style, so that an assumption ([nondet]'s range, a
   guard against UB, [__VERIFIER_assume]) encloses exactly what follows it
   and a condition split ([select] and the signedness conversions)
   copies exactly the rest of the segment.  Values are terms substituted
   into what follows; nothing is written with [let].

   Constructs outside this are refused with their reason, as UNKNOWN. *)

open Ast
open Ast.LogicOld

type mode = Bv | Int
type property = Unreach_call | Termination

let unknown = Scope.unknown
let stop_unknown fmt = Printf.ksprintf (fun r -> Outcome.stop (Unknown r)) fmt

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)
module SMap = Map.Make (String)

(* -- Values and sorts --------------------------------------------------- *)

(* A component of an object in memory: one variable of the
   problem per leaf field, of the leaf's sort, or an array of it when the
   object is allocated more than once or the leaf lies inside an array.  A
   global's component is kept in the environment's globals under its name; a
   local's under its id, beside the SSA values. *)
type cvar = {
  cname : string;
  comp : Memory.comp;
  carray : bool;
  leaf : Sort.t;
  csort : Sort.t;
  key : int option;  (** a local component's id *)
}

type obj = {
  ovalue : Llvm.llvalue;
  elem : Llvm.lltype;
  count : int option;  (** how many values of [elem] it holds; [None]: variable *)
  comps : cvar list;
  vlen : cvar option;  (** a variable-length array's length, set at its [alloca] *)
  memoryk : bool;  (** Ptr2Arr's [memoryK], which gets no bounds condition *)
}

type st = {
  mode : mode;
  property : property;
  config : Config.t;
  index : (Llvm.llvalue, int) Hashtbl.t;  (** SSA value -> its number *)
  values : (int, Llvm.llvalue) Hashtbl.t;  (** its number -> SSA value *)
  mutable fresh : int;
  mutable globals : (string * Sort.t) list;
      (** the components of the global objects the code accesses *)
  layout : Llvm_target.DataLayout.t;
  objects : (Llvm.llvalue, obj) Hashtbl.t;
  comp_ids : (int, cvar) Hashtbl.t;  (** a local component's id -> it *)
  aggs : (int, Term.t list) Hashtbl.t;
      (** the leaves of a struct value (an [*.with.overflow] result, a struct
          loaded, returned or received), read in the same block *)
  mutable loops : MuCLP.Pred.t list;  (** the predicates of the loop form *)
  mutable loop_kind : Predicate.fixpoint;  (** for a loop made while building a body *)
}

let width v = Llvm.integer_bitwidth (Llvm.type_of v)
let is_int_type ty = Llvm.classify_type ty = Llvm.TypeKind.Integer

let sort_of_width st n =
  if n = 1 then T_bool.SBool
  else match st.mode with Int -> T_int.SInt | Bv -> T_bv.SBV (Some n)

(* An SSA value the translation tracks: an integer-typed instruction result
   or argument. *)
let is_tracked v =
  is_int_type (Llvm.type_of v)
  &&
  match Llvm.classify_value v with
  | Instruction _ | Argument -> true
  | _ -> false

let number st v =
  match Hashtbl.find_opt st.index v with
  | Some i -> i
  | None ->
      let i = Hashtbl.length st.index in
      Hashtbl.add st.index v i;
      Hashtbl.add st.values i v;
      i

let var_name i = Printf.sprintf "x%d" i

(* The ids of local components lie above every SSA value's number. *)
let comp_base = 1 lsl 40

let global_name name =
  "g_" ^ String.map (fun c -> match c with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> c | _ -> '_') name

(* The variable name and sort of an id: an SSA value's or a component's. *)
let id_var st x =
  match Hashtbl.find_opt st.comp_ids x with
  | Some cv -> (Ident.Tvar cv.cname, cv.csort)
  | None -> (Ident.Tvar (var_name x), sort_of_width st (Llvm.integer_bitwidth (Llvm.type_of (Hashtbl.find st.values x))))

let fresh_var st sort =
  st.fresh <- st.fresh + 1;
  (Ident.Tvar (Printf.sprintf "n%d" st.fresh), sort)

(* -- Integer constants and helpers -------------------------------------- *)

let pow2 n = Z.shift_left Z.one n

(* The signed value of an integer constant of width at most 64. *)
let constant_z at c =
  match Llvm.int64_of_const c with
  | Some x -> Z.of_int64 x
  | None -> unknown at "an integer constant wider than 64 bits (%s)" (Llvm.string_of_llvalue c)

let int_num z = T_int.mk_int z

(* A bit-vector numeral of width [n] for the pattern of [z] (taken modulo 2^n). *)
let bv_num n z = T_bv.mk_bvnum ~size:(Some n) (Z.erem z (pow2 n))

let fmla_true = Formula.mk_true ()
let fmla_false = Formula.mk_false ()
let atom a = Formula.mk_atom a
let bool_of_fmla f = T_bool.of_formula f

(* [a ⇔ b] written with [∧], [∨] and [¬]: MuVal's check of a problem's
   quantifier shape (MuCLP.Problem.has_only_forall) fails with "not
   implemented" on an [⇔] in a body. *)
let iff a b = Formula.mk_or (Formula.mk_and a b) (Formula.mk_and (Formula.mk_neg a) (Formula.mk_neg b))
let fmla_of_bool t = Formula.of_bool_term t
let forall_vars vars body = if vars = [] then body else Formula.mk_forall vars body

(* -- Static ranges ------------------------------------------------- *)

(* Whether a value's holder is known to lie in the signed range, in the
   unsigned range of its width.  Only used in Int mode, to omit a
   conversion. *)
type range = { signed : bool; unsigned : bool }

let no_range = { signed = false; unsigned = false }

let nondet_signedness = Scope.nondet_signedness

(* The constant operand of a binary instruction, as its unsigned value. *)
let constant_operand v =
  let n = width v in
  let un c =
    match (Llvm.classify_value c, Llvm.int64_of_const c) with
    | ConstantInt, Some x -> Some (Z.erem (Z.of_int64 x) (pow2 n))
    | _ -> None
  in
  match (un (Llvm.operand v 0), un (Llvm.operand v 1)) with
  | _, Some c -> Some (Llvm.operand v 0, c)
  | Some c, None -> Some (Llvm.operand v 1, c)
  | None, None -> None

let is_pow2 z = Z.gt z Z.zero && Z.equal (Z.logand z (Z.pred z)) Z.zero

(* [and a, 2^k - 1] with 0 < k < width: [Some (a, 2^k)]. *)
let low_mask v =
  match constant_operand v with
  | Some (a, c) when Z.lt (Z.succ c) (pow2 (width v)) && is_pow2 (Z.succ c) -> Some (a, Z.succ c)
  | _ -> None

(* [xor a, -1] (C's [~]): [Some a]. *)
let not_operand v =
  match constant_operand v with
  | Some (a, c) when Z.equal c (Z.pred (pow2 (width v))) -> Some a
  | _ -> None

(* [~wrap]: the reading is a wrapping one, which reduces every [add], [sub]
   and [mul] result into the unsigned range whatever its flags. *)
let rec range_of ?(wrap = false) seen v =
  match Llvm.classify_value v with
  | ConstantInt -> (
      match Llvm.int64_of_const v with
      | Some x ->
          let n = width v in
          let z = Z.of_int64 x in
          {
            signed = true;
            unsigned = Z.geq z Z.zero && (n >= 64 || Z.lt z (pow2 (n - 1)));
          }
      | None -> no_range)
  | Instruction op -> (
      (* Only [phi] and [select], which copy one of their operands, recurse,
         so a value met again lies on a cycle of copies: every value on it
         is a copy of one entering it from outside, whose ranges the meet
         already takes.  It is the neutral element of the meet, not
         [no_range], which would lose the range of every loop counter. *)
      if List.memq v seen then { signed = true; unsigned = true }
      else
        let seen = v :: seen in
        match op with
        | Add | Sub | Mul | Load when wrap -> { signed = false; unsigned = true }
        | Add | Sub | Mul ->
            {
              signed = Ir.has_nsw v;
              unsigned = Ir.has_nuw v;
            }
        | SDiv | SRem | SExt | AShr -> { signed = true; unsigned = false }
        | UDiv | URem | ZExt | LShr -> { signed = false; unsigned = true }
        | And when low_mask v <> None -> { signed = false; unsigned = true }
        | Xor when width v > 1 && not_operand v <> None -> { signed = true; unsigned = false }
        | PHI ->
            List.fold_left
              (fun acc (x, _) ->
                let r = range_of ~wrap seen x in
                { signed = acc.signed && r.signed; unsigned = acc.unsigned && r.unsigned })
              { signed = true; unsigned = true }
              (Llvm.incoming v)
        | Select ->
            let a = range_of ~wrap seen (Llvm.operand v 1)
            and b = range_of ~wrap seen (Llvm.operand v 2) in
            { signed = a.signed && b.signed; unsigned = a.unsigned && b.unsigned }
        | Call -> (
            match Llvm.classify_value (Ir.callee v) with
            | Function ->
                let name = Llvm.value_name (Ir.callee v) in
                (* a nondet the module defines returns what its body does *)
                if String.starts_with ~prefix:"__VERIFIER_nondet_" name && Llvm.is_declaration (Ir.callee v) then
                  match nondet_signedness name with
                  | Some true -> { signed = true; unsigned = false }
                  | Some false -> { signed = false; unsigned = true }
                  | None -> no_range
                else if String.starts_with ~prefix:Scope.uninit_marker_prefix name
                then { signed = true; unsigned = false }
                else (
                  match Scope.modelled_of_name name with
                  | Some (Scope.Wrap (signed, _)) -> { signed; unsigned = not signed }
                  | _ -> no_range)
            | _ -> no_range)
        | _ -> no_range)
  | _ -> no_range

(* An interval known to contain the holder of a value (Int mode), for the
   modulo reading's omission of a reduction.  The
   holder of [sext] is the operand's signed value and of [zext] its unsigned
   one whatever the operand's holder; [add]/[sub] add the holders, which an
   [nsw] ([nuw]) operation reads through [to_S] ([to_U]), so it is used only
   when the operands' intervals lie in that range.  A [phi] met again gives
   no interval.  [~havoc]: an [nsw] result that leaves the signed range is
   an arbitrary signed value (the [Arbitrary_value] reading), so an [nsw]
   interval that is not inside the signed range is widened to contain it.
   Contract: the interval contains every holder the reading gives [v]. *)
let rec interval_of ?(wrap = false) ?(havoc = false) seen v =
  let signed_range n = (Z.neg (pow2 (n - 1)), Z.pred (pow2 (n - 1))) in
  let unsigned_range n = (Z.zero, Z.pred (pow2 n)) in
  let within (lo, hi) (a, b) = Z.geq a lo && Z.leq b hi in
  let join a b = match (a, b) with Some (a, b), Some (c, d) -> Some (Z.min a c, Z.max b d) | _ -> None in
  match Llvm.classify_value v with
  | ConstantInt -> (
      match Llvm.int64_of_const v with Some x -> Some (Z.of_int64 x, Z.of_int64 x) | None -> None)
  | Instruction op -> (
      if List.memq v seen then None
      else
        let seen = v :: seen in
        let n = width v in
        match op with
        | SExt -> Some (if width (Llvm.operand v 0) = 1 then (Z.minus_one, Z.zero) else signed_range (width (Llvm.operand v 0)))
        | ZExt -> Some (unsigned_range (width (Llvm.operand v 0)))
        | Add | Sub | Mul | Load when wrap -> Some (unsigned_range n)
        | Add | Sub -> (
            match (interval_of ~wrap ~havoc seen (Llvm.operand v 0), interval_of ~wrap ~havoc seen (Llvm.operand v 1)) with
            | Some x, Some y
              when (not (Ir.has_nsw v) || (within (signed_range n) x && within (signed_range n) y))
                   && (Ir.has_nsw v || not (Ir.has_nuw v) || (within (unsigned_range n) x && within (unsigned_range n) y)) ->
                let (a, b), (c, d) = (x, y) in
                let iv = if op = Add then (Z.add a c, Z.add b d) else (Z.sub a d, Z.sub b c) in
                if havoc && Ir.has_nsw v && not (within (signed_range n) iv) then join (Some iv) (Some (signed_range n))
                else Some iv
            | _ -> None)
        | PHI -> (
            match Llvm.incoming v with
            | [] -> None
            | (x, _) :: rest -> List.fold_left (fun acc (y, _) -> join acc (interval_of ~wrap ~havoc seen y)) (interval_of ~wrap ~havoc seen x) rest)
        | Select -> join (interval_of ~wrap ~havoc seen (Llvm.operand v 1)) (interval_of ~wrap ~havoc seen (Llvm.operand v 2))
        | And when low_mask v <> None -> Option.map (fun (_, m) -> (Z.zero, Z.pred m)) (low_mask v)
        | Call -> (
            match Llvm.classify_value (Ir.callee v) with
            | Function -> (
                let name = Llvm.value_name (Ir.callee v) in
                if not (Llvm.is_declaration (Ir.callee v)) && String.starts_with ~prefix:"__VERIFIER_nondet_" name then None
                else if name = "__VERIFIER_nondet_bool" || name = "__VERIFIER_nondet__Bool" then Some (Z.zero, Z.one)
                else if String.starts_with ~prefix:"__VERIFIER_nondet_" name then
                  match nondet_signedness name with
                  | Some true -> Some (signed_range n)
                  | Some false -> Some (unsigned_range n)
                  | None -> None
                else
                  match Scope.modelled_of_name name with
                  | Some (Scope.Wrap (true, _)) -> Some (signed_range n)
                  | Some (Scope.Wrap (false, _)) -> Some (unsigned_range n)
                  | _ -> None)
            | _ -> None)
        | _ -> None)
  | _ -> None

(* Whether a holder in [iv] already lies in the dual range of width [n]. *)
let in_dual_range n iv =
  match iv with Some (lo, hi) -> Z.geq lo (Z.neg (pow2 (n - 1))) && Z.lt hi (pow2 n) | None -> false

(* -- Choices ---------------------------------------------------- *)

(* The rest [k] for the value [ite(c, a, b)]: a conditional term, or the
   condition split. *)
let choose encoding c a b k =
  match (encoding : Config.choice_encoding) with
  | Ite -> k (T_bool.ifte c a b)
  | Split ->
      Formula.mk_and (Formula.mk_imply c (k a))
        (Formula.mk_imply (Formula.mk_neg c) (k b))

(* to_S / to_U of the holder [a] of width [n] (Int mode), constants folded
   and conversions omitted where [range] says so; to_S is the identity in the
   unbounded reading, where a signed value has no range to be brought into. *)
let half n = int_num (pow2 (n - 1))
let full n = int_num (pow2 n)

(* Whether the reading reduces a result that may leave its type's range:
   the modulo reading at [trunc], [shl] and the overflow builtins, the
   wrapping readings at every arithmetic result too. *)
let reduces st = match st.config.Config.int_reading with Modulo | Wrap_unsigned | Wrap_all -> true | Mathematical | Unbounded -> false
let wraps st = match st.config.Config.int_reading with Wrap_unsigned | Wrap_all -> true | _ -> false

let to_s st ~range n a k =
  if range.signed || st.config.Config.int_reading = Config.Unbounded then k a
  else
    match T_int.let_int a with
    | z -> k (int_num (if Z.geq z (pow2 (n - 1)) then Z.sub z (pow2 n) else z))
    | exception _ ->
        choose st.config.Config.signedness_conversion
          (atom (T_int.mk_geq a (half n)))
          (T_int.mk_sub a (full n)) a k

let to_u st ~range n a k =
  if range.unsigned then k a
  else
    match T_int.let_int a with
    | z -> k (int_num (if Z.lt z Z.zero then Z.add z (pow2 n) else z))
    | exception _ ->
        choose st.config.Config.signedness_conversion
          (atom (T_int.mk_lt a (T_int.zero ())))
          (T_int.mk_add a (full n)) a k

(* -- Environments -------------------------------------------------------- *)

type env = { vals : Term.t IntMap.t; globs : Term.t SMap.t }

(* The term of an operand, through [k] (a [poison] constant is an arbitrary
   value). *)
let operand st env at v k =
  match Llvm.classify_value v with
  | ConstantInt ->
      let n = width v in
      if n = 1 then
        k (if Llvm.int64_of_const v = Some 0L then T_bool.mk_false () else T_bool.mk_true ())
      else (
        let z = constant_z at v in
        match st.mode with Int -> k (int_num z) | Bv -> k (bv_num n z))
  (* a poison constant (never used in an execution) and an undef
     operand (a fresh value at each use) are arbitrary values *)
  | PoisonValue | UndefValue ->
      if not (is_int_type (Llvm.type_of v)) then unknown at "an undef or poison value that is not an integer";
      let x = fresh_var st (sort_of_width st (width v)) in
      Formula.mk_forall [ x ] (k (Term.mk_var (fst x) (snd x)))
  | Instruction _ | Argument when is_tracked v -> (
      match IntMap.find_opt (number st v) env.vals with
      | Some t -> k t
      | None ->
          Outcome.stop
            (Internal_error
               (Printf.sprintf "%s: an operand with no value on this path"
                  (Scope.location at))))
  | ConstantExpr -> unknown at "a constant expression operand"
  | _ -> unknown at "an operand %s" (Llvm.string_of_llvalue v)

let operands st env at vs k =
  let rec go acc = function
    | [] -> k (List.rev acc)
    | v :: vs -> operand st env at v (fun t -> go (t :: acc) vs)
  in
  go [] vs

let bind st env v t = { env with vals = IntMap.add (number st v) t env.vals }

(* A guard against UB: the path stops where it fails, or, under the
   literal C reading, the property fails there. *)
let guarded st g rest =
  if Formula.is_true g then rest
  else
    match st.config.Config.ub_reading with
    | Stop_path -> Formula.mk_imply g rest
    | Literal_c -> Formula.mk_and g rest

(* Dropping the guard atoms that an enclosing branch test implies (switch
   [drop_implied_guards], off by default).

   Contract: for every formula [phi], [drop_implied_guards_in phi] is
   equivalent to [phi].  Only the conjuncts of an implication's premise are
   dropped, and only when the conjunction of the enclosing implications'
   premises implies them; (A => (g /\ h => B)) and (A => (h => B)) agree
   whenever A implies g.  The implication is decided on single-variable
   bounds alone: an atom counts when it compares an integer term of the form
   [x + c] or [-x + c] with a numeral (after moving everything to one side),
   possibly negated.  The traversal enters conjunctions and implications only,
   never a binder, so every variable it reads a bound of is the same variable
   wherever it occurs.

   Why: an overflow guard such as [n + 11 < 2^31] written beside the branch
   [n <= 100] adds nothing to the path condition, yet MuVal's template
   synthesis takes its constant into the candidates' pieces and was seen to
   lose a ranking function it found without the guard (a McCarthy-91 loop:
   0 of 5 runs with the guards, 4 of 5 without the implied ones). *)
module Implied_guards = struct
  (* [Some (x, a, c)] for the term [a * x + c] with [x] an integer variable
     (or [None] for a numeral, [a = 0]) *)
  let rec affine (t : Term.t) : (Ident.tvar option * Z.t * Z.t) option =
    let combine f (x, a, c) (y, b, d) =
      match (x, y) with
      | None, _ -> Some (y, f Z.zero b, f c d)
      | _, None -> Some (x, a, f c d)
      | Some x', Some y' when Ident.tvar_equal x' y' -> Some (x, f a b, f c d)
      | _ -> None
    in
    match t with
    | Term.Var (x, T_int.SInt, _) -> Some (Some x, Z.one, Z.zero)
    | Term.FunApp (T_int.Int z, [], _) -> Some (None, Z.zero, z)
    | Term.FunApp (T_int.Neg, [ u ], _) -> Option.map (fun (x, a, c) -> (x, Z.neg a, Z.neg c)) (affine u)
    | Term.FunApp (T_int.Add, [ u; v ], _) -> (
        match (affine u, affine v) with Some p, Some q -> combine Z.add p q | _ -> None)
    | Term.FunApp (T_int.Sub, [ u; v ], _) -> (
        match (affine u, affine v) with Some p, Some q -> combine Z.sub p q | _ -> None)
    | _ -> None

  (* the bound [x >= lo] ([`Lo lo]) or [x <= hi] ([`Hi hi]) an atom states,
     when it states one on a single variable with coefficient 1 or -1 *)
  let bound (phi : Formula.t) =
    let of_atom neg = function
      | Atom.App (Predicate.Psym op, [ t1; t2 ], _) -> (
          (* t1 op t2  <=>  d op' 0 with d = t1 - t2; under [neg] the strict
             complement *)
          let op =
            match (op, neg) with
            | T_int.Leq, false | T_int.Gt, true -> Some `Le
            | T_int.Lt, false | T_int.Geq, true -> Some `Lt
            | T_int.Geq, false | T_int.Lt, true -> Some `Ge
            | T_int.Gt, false | T_int.Leq, true -> Some `Gt
            | _ -> None
          in
          match (op, affine t1, affine t2) with
          | Some op, Some p, Some q -> (
                  let d =
                    match (p, q) with
                    | (x, a, c), (None, _, d) -> Some (x, a, Z.sub c d)
                    | (None, _, c), (y, b, d) -> Some (y, Z.neg b, Z.sub c d)
                    | (Some x, a, c), (Some y, b, d) when Ident.tvar_equal x y -> Some (Some x, Z.sub a b, Z.sub c d)
                    | _ -> None
                  in
                  match d with
                  | Some (Some x, a, c) when Z.equal a Z.one || Z.equal a Z.minus_one -> (
                      (* a*x + c op 0, i.e. a*x op -c *)
                      let k = Z.neg c in
                      (* strict to non-strict on integers *)
                      let le, ge = match op with `Le -> (Some k, None) | `Lt -> (Some (Z.pred k), None) | `Ge -> (None, Some k) | `Gt -> (None, Some (Z.succ k)) in
                      (* a = -1 flips: -x <= k is x >= -k *)
                      match (Z.equal a Z.one, le, ge) with
                      | true, Some h, _ -> Some (x, `Hi h)
                      | true, _, Some l -> Some (x, `Lo l)
                      | false, Some h, _ -> Some (x, `Lo (Z.neg h))
                      | false, _, Some l -> Some (x, `Hi (Z.neg l))
                      | _ -> None)
                  | _ -> None)
          | _ -> None)
      | _ -> None
    in
    match phi with
    | Formula.Atom (a, _) -> of_atom false a
    | Formula.UnaryOp (Formula.Not, Formula.Atom (a, _), _) -> of_atom true a
    | _ -> None

  let rec conjuncts = function Formula.BinaryOp (Formula.And, a, b, _) -> conjuncts a @ conjuncts b | phi -> [ phi ]

  (* the context: per variable, the greatest lower and least upper bound known *)
  let add ctx phi =
    match bound phi with
    | Some (x, `Lo l) ->
        let lo, hi = Option.value (List.assoc_opt x ctx) ~default:(None, None) in
        (x, ((match lo with Some l' when Z.geq l' l -> lo | _ -> Some l), hi)) :: List.remove_assoc x ctx
    | Some (x, `Hi h) ->
        let lo, hi = Option.value (List.assoc_opt x ctx) ~default:(None, None) in
        (x, (lo, match hi with Some h' when Z.leq h' h -> hi | _ -> Some h)) :: List.remove_assoc x ctx
    | None -> ctx

  let implied ctx phi =
    match bound phi with
    | Some (x, `Lo l) -> (
        match List.assoc_opt x ctx with Some (Some l', _) -> Z.geq l' l | _ -> false)
    | Some (x, `Hi h) -> (
        match List.assoc_opt x ctx with Some (_, Some h') -> Z.leq h' h | _ -> false)
    | None -> false

  let rec drop ctx (phi : Formula.t) =
    match phi with
    | Formula.BinaryOp (Formula.Imply, p, q, info) ->
        let ps = conjuncts p in
        let ctx' = List.fold_left add ctx ps in
        let q' = drop ctx' q in
        (match List.filter (fun a -> not (implied ctx a)) ps with
         | [] -> q'
         | kept when List.length kept = List.length ps -> Formula.mk_imply ~info p q'
         | kept -> Formula.mk_imply ~info (Formula.and_of kept) q')
    | Formula.BinaryOp (Formula.And, a, b, info) -> Formula.mk_and ~info (drop ctx a) (drop ctx b)
    | _ -> phi
end

let drop_implied_guards_in st phi = if st.config.Config.drop_implied_guards then Implied_guards.drop [] phi else phi

(* -- Bit-vector overflow conditions (BV mode) --------------------------- *)

let bv_eq a b = atom (T_bool.mk_eq a b)
let sz n = Some n

(* The add and sub conditions stay at width [n], with no wider or narrower
   vector beside the operands: an overflow test through an (n+1)-bit sum
   compared on its top two bits made MuVal hand Z3 an equality between a
   32-bit and a 2-bit vector on a recursive input (a solver defect; these
   forms avoid it).  Signed: the operands' signs agree (add) or differ (sub)
   and the result's sign differs from [a]'s.  Unsigned: the sum is below an
   operand, or [a] is below [b]. *)
let bv_negative n x = atom (T_bv.mk_bvlt ~size:(sz n) ~signed:(Some true) x (bv_num n Z.zero))

let bv_no_signed_overflow n ~sub a b =
  let size = sz n in
  let r = if sub then T_bv.mk_bvsub ~size a b else T_bv.mk_bvadd ~size a b in
  let same_sign = iff (bv_negative n a) (bv_negative n b) in
  let operands = if sub then Formula.mk_neg same_sign else same_sign in
  Formula.mk_neg
    (Formula.mk_and operands (Formula.mk_neg (iff (bv_negative n r) (bv_negative n a))))

let bv_no_unsigned_overflow n ~sub a b =
  let size = sz n and u = Some false in
  if sub then Formula.mk_neg (atom (T_bv.mk_bvlt ~size ~signed:u a b))
  else Formula.mk_neg (atom (T_bv.mk_bvlt ~size ~signed:u (T_bv.mk_bvadd ~size a b) a))

let bv_no_signed_mul_overflow n a b =
  let ext x = T_bv.mk_bvsext ~size:(sz n) n x in
  let wide = T_bv.mk_bvmul ~size:(sz (2 * n)) (ext a) (ext b) in
  let top = T_bv.mk_bvextract ~size:(sz (2 * n)) ((2 * n) - 1) (n - 1) wide in
  Formula.mk_or (bv_eq top (bv_num (n + 1) Z.zero)) (bv_eq top (bv_num (n + 1) Z.minus_one))

let bv_no_unsigned_mul_overflow n a b =
  let ext x = T_bv.mk_bvzext ~size:(sz n) n x in
  let wide = T_bv.mk_bvmul ~size:(sz (2 * n)) (ext a) (ext b) in
  bv_eq (T_bv.mk_bvextract ~size:(sz (2 * n)) ((2 * n) - 1) n wide) (bv_num n Z.zero)

(* -- Instructions ------------------------------------------------------- *)

let bool_binop instr a b =
  let fa = fmla_of_bool a and fb = fmla_of_bool b in
  match Llvm.instr_opcode instr with
  | And -> Formula.mk_and fa fb
  | Or -> Formula.mk_or fa fb
  | Xor -> Formula.mk_neg (iff fa fb)
  | _ -> unknown instr "the instruction %s on i1" (Ir.opcode_name (Llvm.instr_opcode instr))

(* A bitwise operation or shift in Int mode: the forms with an exact
   linear value; any other is refused.  [a] and [b] are the operands'
   holders. *)
let erem a m = T_int.mk_rem Value.Euclidean a (int_num m)
let ediv a m = T_int.mk_div Value.Euclidean a (int_num m)

(* [a & c] for a constant [c] read as N-bit unsigned: for each run of 1 bits
   [lo, hi) of [c], [erem(a, 2^hi) - erem(a, 2^lo)], summed.  The low N bits of a holder do not depend on which
   of its two holders a value has, so this is exact in the dual range, and
   the result lies in [0, 2^N). *)
let and_const a c n =
  let rec runs i acc =
    if i >= n then List.rev acc
    else if not (Z.testbit c i) then runs (i + 1) acc
    else
      let rec top j = if j < n && Z.testbit c j then top (j + 1) else j in
      let j = top i in
      runs j ((i, j) :: acc)
  in
  let low k = if k = 0 then None else Some (erem a (pow2 k)) in
  let run (i, j) = match low i with None -> erem a (pow2 j) | Some l -> T_int.mk_sub (erem a (pow2 j)) l in
  match runs 0 [] with
  | [] -> T_int.zero ()
  | r :: rs -> List.fold_left (fun acc r -> T_int.mk_add acc (run r)) (run r) rs

(* In the unbounded reading a holder is the value itself, of any size, and a
   bitwise operation with a constant is the one on integers in infinite
   two's complement, the constant read as signed: [x & c] for [c >= 0] by
   its runs of 1 bits, [x - (x & ~c)] for [c < 0]; [x | c = x + c - (x & c)]
   and [x ^ c = x + c - 2 (x & c)], identities of every integer. *)
let bitwise_const_unbounded op a c n =
  let c = if Z.geq c (pow2 (n - 1)) then Z.sub c (pow2 n) else c in
  let and_c =
    if Z.geq c Z.zero then and_const a c n else T_int.mk_sub a (and_const a (Z.lognot c) n)
  in
  match (op : Llvm.Opcode.t) with
  | And -> and_c
  | Or -> T_int.mk_sub (T_int.mk_add a (int_num c)) and_c
  | _ -> T_int.mk_sub (T_int.mk_add a (int_num c)) (T_int.mk_mul (int_num (Z.of_int 2)) and_c)

(* The UB conditions of an instruction's [nsw] and [nuw] flags, through [k]:
   with [nsw] the result computed on the operands read as signed ([signed])
   lies in the signed range, with [nuw] the one on them read as unsigned
   ([unsigned]) in the unsigned range.  A breach makes the result poison, and
   these readings take it as UB, stopping the path under the stop-path
   reading:
   - Wrap_unsigned reads both flags, Wrap_all [nuw] only (gcc's -fwrapv);
   - Mathematical and Modulo read both.  They rely on them: neither writes
     a wrap-around for signed arithmetic (the modulo route's C-to-C stage
     makes only unsigned wrap-around explicit, so a signed operation keeps
     C's semantics, where overflow is undefined), so the result of an [nsw]
     operation that leaves the signed range is held as the out-of-range
     integer, while the static ranges take an [nsw] result to lie in the
     signed range and an [nuw] one in the unsigned range and omit its
     conversion.  Without the condition one execution read that value in two
     ways: [-INT_MIN] held as 2^31 was positive where the static range
     omitted [to_S] (a loop test on the negated variable) and negative where
     it did not (the same test on a recursive call's parameter, whose range
     is unknown), so a terminating recursion through [f(-m)] was answered
     non-terminating.  With it every [nsw]/[nuw] result lies in its range,
     so the omission is exact;
   - Unbounded reads neither: it has no range.
   Under the [Arbitrary_value] reading of signed overflow an [nsw] breach
   is not UB but yields an arbitrary value of the type ([on_signed_overflow]);
   a [nuw] breach stays UB. *)
let reads_nsw st = match st.config.Config.int_reading with Wrap_unsigned | Mathematical | Modulo -> true | Wrap_all | Unbounded -> false
let reads_nuw st = match st.config.Config.int_reading with Wrap_unsigned | Wrap_all | Mathematical | Modulo -> true | Unbounded -> false

(* [lo <= r < hi], folded when [r] is a numeral. *)
let in_range lo hi r =
  match T_int.let_int r with
  | z -> if Z.geq z lo && Z.lt z hi then fmla_true else Formula.mk_false ()
  | exception Assert_failure _ (* [let_int] of a non-numeral *) ->
      Formula.mk_and (atom (T_int.mk_geq r (int_num lo))) (atom (T_int.mk_lt r (int_num hi)))

(* Under [drop_implied_guards], the interval of an [nsw] [add]/[sub] result
   computed on its operands read as signed, when each operand is a constant
   or a value the static ranges place in the signed range (the operands
   already read without [to_S]); [None] otherwise.  A side of the guard that
   this interval implies is not written: [n + 11 >= INT_MIN] for a signed [n]
   says nothing.  Only the non-wrapping readings, where the operand term is
   the holder itself. *)
let nsw_result_interval st instr =
  if not (st.config.Config.drop_implied_guards && not (wraps st)) then None
  else
    let n = width instr in
    let iv v =
      match interval_of [] v with
      | Some iv -> Some iv
      | None -> if (range_of [] v).signed then Some (Z.neg (pow2 (n - 1)), Z.pred (pow2 (n - 1))) else None
    in
    match (Llvm.instr_opcode instr, iv (Llvm.operand instr 0), iv (Llvm.operand instr 1)) with
    | Llvm.Opcode.Add, Some (a, b), Some (c, d) -> Some (Z.add a c, Z.add b d)
    | Llvm.Opcode.Sub, Some (a, b), Some (c, d) -> Some (Z.sub a d, Z.sub b c)
    | _ -> None

(* [lo <= r < hi] less the sides the interval [iv] of [r] implies *)
let in_range_given iv lo hi r =
  match iv with
  | None -> in_range lo hi r
  | Some (a, b) ->
      let low = if Z.geq a lo then fmla_true else atom (T_int.mk_geq r (int_num lo)) in
      let high = if Z.lt b hi then fmla_true else atom (T_int.mk_lt r (int_num hi)) in
      if Formula.is_true low then high else if Formula.is_true high then low else Formula.mk_and low high

(* [k gs gu]: [gs] the [nsw] condition (true when the flag is absent or the
   reading does not read it), [gu] the [nuw] one, each folded to a constant
   when its result is a numeral. *)
let wrap_flags st instr ~signed ~unsigned k =
  let n = width instr in
  let nsw k =
    if reads_nsw st && Ir.has_nsw instr then
      let iv = nsw_result_interval st instr in
      signed (fun r -> k (in_range_given iv (Z.neg (pow2 (n - 1))) (pow2 (n - 1)) r))
    else k fmla_true
  in
  let nuw k = if reads_nuw st && Ir.has_nuw instr then unsigned (fun r -> k (in_range Z.zero (pow2 n) r)) else k fmla_true in
  nsw (fun gs -> nuw (fun gu -> k gs gu))

(* The two flags' conditions as one guard, as the stop-path and literal C
   readings check them. *)
let both_flags gs gu = if Formula.is_true gs then gu else if Formula.is_true gu then gs else Formula.mk_and gs gu

(* Whether an overflowing signed operation yields an arbitrary value of its
   type (the [Arbitrary_value] reading) rather than undefined behaviour. *)
let havocs st = st.config.Config.signed_overflow = Config.Arbitrary_value

(* BV mode reads [nsw] unless signed arithmetic wraps ([Wrap_all], gcc's
   -fwrapv); [nuw] always. *)
let bv_reads_nsw st = st.config.Config.int_reading <> Config.Wrap_all

(* The holders an arbitrary value of an [n]-bit signed result is drawn from
   (Int mode): the signed range, or in the wrapping readings, whose ring
   results are held reduced, the unsigned range. *)
let signed_holder n v = in_range (Z.neg (pow2 (n - 1))) (pow2 (n - 1)) v
let wrapped_holder n v = in_range Z.zero (pow2 n) v

(* [(ok => normal ()) /\ (not ok => forall v. holder v => rest v)], [v]
   fresh of [sort]: where [ok] fails, the operation yields any value
   [holder] admits, each choice covered.  [ok] is not [true]. *)
let overflow_choice st ~ok ~holder ~sort normal rest =
  let x = fresh_var st sort in
  let v = Term.mk_var (fst x) (snd x) in
  let h = holder v in
  let chosen = Formula.mk_forall [ x ] (if Formula.is_true h then rest v else Formula.mk_imply h (rest v)) in
  if Formula.is_false ok then chosen
  else Formula.mk_and (Formula.mk_imply ok (normal ())) (Formula.mk_imply (Formula.mk_neg ok) chosen)

(* The rest [k] of an operation with the value [r] when [ok] holds, [ok]
   being "no signed overflow".  Under [Undefined], [k guard r]: [guard] is
   the operation's whole UB guard (which includes [ok]), read as
   [ub_reading] says.  Under [Arbitrary_value],
     (ok => k rest r) /\ (not ok => forall v. holder v => k rest v)
   with [v] fresh of [sort] and [rest] the operation's other UB guards: an
   overflow yields any value [holder] admits, each choice covered.
   Contract: [guard] is equivalent to [ok /\ rest]; [holder] admits exactly
   the holders of the type's values, so a value chosen is one the static
   ranges allow for the result. *)
let on_signed_overflow st ~ok ~rest ~guard ~holder ~sort k r =
  if Formula.is_true ok || not (havocs st) then k guard r
  else overflow_choice st ~ok ~holder ~sort (fun () -> k rest r) (k rest)

let bitwise_int st instr a b (k : Formula.t -> Term.t -> Formula.t) =
  let at = instr in
  let n = width instr in
  let op = Llvm.instr_opcode instr in
  let x = Llvm.operand instr 0 and y = Llvm.operand instr 1 in
  let holder_of v = if v == x then a else b in
  let shift_amount () =
    match (Llvm.classify_value y, Llvm.int64_of_const y) with
    | ConstantInt, Some c -> Int64.to_int c
    | _ -> unknown at "a shift by a variable amount in Int mode"
  in
  let exact_guard a' c =
    if Ir.is_exact instr then atom (T_bool.mk_eq (erem a' (pow2 c)) (T_int.zero ())) else fmla_true
  in
  match op with
  | (And | Or | Xor)
    when st.config.Config.int_reading = Config.Unbounded && constant_operand instr <> None ->
      let v, c = Option.get (constant_operand instr) in
      k fmla_true (bitwise_const_unbounded op (holder_of v) c n)
  | Xor -> (
      match not_operand instr with
      | Some v -> to_s st ~range:(range_of ~wrap:(wraps st) [] v) n (holder_of v) (fun a' -> k fmla_true (T_int.mk_sub (T_int.mk_neg a') (T_int.one ())))
      | None -> (
          (* a ^ c = (a & ~c) + (c - (a & c)), in [0, 2^N) *)
          match constant_operand instr with
          | Some (v, c) ->
              let t = holder_of v in
              let not_c = Z.logxor c (Z.pred (pow2 n)) in
              k fmla_true (T_int.mk_add (and_const t not_c n) (T_int.mk_sub (int_num c) (and_const t c n)))
          | None -> unknown at "an xor of two variables in Int mode"))
  | And -> (
      match (low_mask instr, constant_operand instr) with
      | Some (v, m), _ -> k fmla_true (erem (holder_of v) m)
      | None, Some (v, c) when Z.equal c (Z.pred (pow2 n)) -> k fmla_true (holder_of v)
      | None, Some (_, c) when Z.equal c Z.zero -> k fmla_true (T_int.zero ())
      | None, Some (v, c) when is_pow2 (Z.sub (pow2 n) c) ->
          let t = holder_of v in
          k fmla_true (T_int.mk_sub t (erem t (Z.sub (pow2 n) c)))
      | None, Some (v, c) -> k fmla_true (and_const (holder_of v) c n)
      | None, None -> unknown at "an and of two variables in Int mode")
  | Or -> (
      match constant_operand instr with
      | Some (v, c) when Z.equal c Z.zero -> k fmla_true (holder_of v)
      | Some (v, c) ->
          (* a | c = (a & ~c) + c, in [0, 2^N) *)
          let not_c = Z.logxor c (Z.pred (pow2 n)) in
          k fmla_true (T_int.mk_add (and_const (holder_of v) not_c n) (int_num c))
      | None -> unknown at "an or of two variables in Int mode")
  | Shl | LShr | AShr ->
      let c = shift_amount () in
      (* a shift by the width or more is poison, which stops the path *)
      if c < 0 || c >= n then k fmla_false a
      else (
        match op with
        | Shl -> (
            let t = T_int.mk_mul a (int_num (pow2 c)) in
            let times v = T_int.mk_mul v (int_num (pow2 c)) in
            (* an [nsw] breach: under [Arbitrary_value] any value of the
               type, held as the reading holds a ring result *)
            let overflow gs gu r =
              on_signed_overflow st ~ok:gs ~rest:gu ~guard:(both_flags gs gu)
                ~holder:(if wraps st then wrapped_holder n else signed_holder n)
                ~sort:(sort_of_width st n) k r
            in
            if not (reduces st) then
              (* the flags' conditions, as for [mul] (none under Unbounded) *)
              wrap_flags st instr
                ~signed:(fun k -> to_s st ~range:(range_of [] x) n a (fun a' -> k (times a')))
                ~unsigned:(fun k -> to_u st ~range:(range_of [] x) n a (fun a' -> k (times a')))
                (fun gs gu -> overflow gs gu t)
            else
              let iv = Option.map (fun (lo, hi) -> (Z.mul lo (pow2 c), Z.mul hi (pow2 c))) (interval_of ~wrap:(wraps st) ~havoc:(havocs st) [] x) in
              wrap_flags st instr
                ~signed:(fun k -> to_s st ~range:(range_of ~wrap:(wraps st) [] x) n a (fun a' -> k (times a')))
                ~unsigned:(fun k -> to_u st ~range:(range_of ~wrap:(wraps st) [] x) n a (fun a' -> k (times a')))
                (fun gs gu -> overflow gs gu (if in_dual_range n iv && not (wraps st) then t else erem t (pow2 n))))
        | LShr -> to_u st ~range:(range_of ~wrap:(wraps st) [] x) n a (fun a' -> k (exact_guard a' c) (ediv a' (pow2 c)))
        | _ -> to_s st ~range:(range_of ~wrap:(wraps st) [] x) n a (fun a' -> k (exact_guard a' c) (ediv a' (pow2 c))))
  | _ -> assert false

(* The value of an arithmetic instruction, through [k] with its UB guard. *)
let arith st env instr (k : Formula.t -> Term.t -> Formula.t) =
  let at = instr in
  let n = width instr in
  let op = Llvm.instr_opcode instr in
  let x = Llvm.operand instr 0 and y = Llvm.operand instr 1 in
  operands st env at [ x; y ] @@ function
  | [ a; b ] when n = 1 -> k fmla_true (bool_of_fmla (bool_binop instr a b))
  | [ a; b ] -> (
      match st.mode with
      | Bv -> (
          let size = sz n in
          (* [nsw] is not read when signed arithmetic wraps (Wrap_all) *)
          let nsw = Ir.has_nsw instr && bv_reads_nsw st and nuw = Ir.has_nuw instr in
          let nonzero = Formula.mk_neg (bv_eq b (bv_num n Z.zero)) in
          let conj = List.fold_left Formula.mk_and fmla_true in
          (* the rest after a result [r] with the signed condition [gs] and
             the other guards [gu]: under [Arbitrary_value] a signed
             overflow yields any vector of the width *)
          let flagged gs gu r =
            on_signed_overflow st ~ok:gs ~rest:(conj [ gu ]) ~guard:(conj [ gs; gu ])
              ~holder:(fun _ -> fmla_true) ~sort:(sort_of_width st n) k r
          in
          match op with
          | Add ->
              flagged
                (if nsw then bv_no_signed_overflow n ~sub:false a b else fmla_true)
                (if nuw then bv_no_unsigned_overflow n ~sub:false a b else fmla_true)
                (T_bv.mk_bvadd ~size a b)
          | Sub ->
              flagged
                (if nsw then bv_no_signed_overflow n ~sub:true a b else fmla_true)
                (if nuw then bv_no_unsigned_overflow n ~sub:true a b else fmla_true)
                (T_bv.mk_bvsub ~size a b)
          | Mul ->
              flagged
                (if nsw then bv_no_signed_mul_overflow n a b else fmla_true)
                (if nuw then bv_no_unsigned_mul_overflow n a b else fmla_true)
                (T_bv.mk_bvmul ~size a b)
          | UDiv | SDiv | URem | SRem ->
              let signed = Some (op = SDiv || op = SRem) in
              let min = bv_num n (Z.neg (pow2 (n - 1))) in
              let no_min_by_minus_one =
                if op = SDiv || op = SRem then
                  Formula.mk_neg
                    (Formula.mk_and (bv_eq a min) (bv_eq b (bv_num n Z.minus_one)))
                else fmla_true
              in
              let value =
                if op = UDiv || op = SDiv then T_bv.mk_bvdiv ~size ~signed a b
                else T_bv.mk_bvrem ~size ~signed a b
              in
              let exact =
                if Ir.is_exact instr then
                  bv_eq (T_bv.mk_bvrem ~size ~signed a b) (bv_num n Z.zero)
                else fmla_true
              in
              on_signed_overflow st ~ok:no_min_by_minus_one ~rest:(conj [ nonzero; exact ])
                ~guard:(conj [ nonzero; no_min_by_minus_one; exact ])
                ~holder:(fun _ -> fmla_true) ~sort:(sort_of_width st n) k value
          | Shl | LShr | AShr ->
              let in_range =
                atom (T_bv.mk_bvlt ~size ~signed:(Some false) b (bv_num n (Z.of_int n)))
              in
              let r =
                match op with
                | Shl -> T_bv.mk_bvshl ~size a b
                | LShr -> T_bv.mk_bvlshr ~size a b
                | _ -> T_bv.mk_bvashr ~size a b
              in
              (match op with
              | Shl ->
                  let gs = if nsw then bv_eq (T_bv.mk_bvashr ~size r b) a else fmla_true in
                  let gu = if nuw then bv_eq (T_bv.mk_bvlshr ~size r b) a else fmla_true in
                  on_signed_overflow st ~ok:gs ~rest:(Formula.mk_and in_range (conj [ gu ]))
                    ~guard:(Formula.mk_and in_range (conj [ gs; gu ]))
                    ~holder:(fun _ -> fmla_true) ~sort:(sort_of_width st n) k r
              | _ ->
                  let back = if Ir.is_exact instr then bv_eq (T_bv.mk_bvshl ~size r b) a else fmla_true in
                  k (Formula.mk_and in_range back) r)
          | And -> k fmla_true (T_bv.mk_bvand ~size a b)
          | Or -> k fmla_true (T_bv.mk_bvor ~size a b)
          | Xor -> k fmla_true (T_bv.mk_bvxor ~size a b)
          | op -> unknown at "the instruction %s" (Ir.opcode_name op))
      | Int -> (
          let rx = range_of ~wrap:(wraps st) [] x and ry = range_of ~wrap:(wraps st) [] y in
          let signed_pair k' = to_s st ~range:rx n a (fun a' -> to_s st ~range:ry n b (fun b' -> k' a' b')) in
          let unsigned_pair k' = to_u st ~range:rx n a (fun a' -> to_u st ~range:ry n b (fun b' -> k' a' b')) in
          (* an [nsw] breach: under [Arbitrary_value] any value of the
             type, held as the reading holds the result *)
          let overflow ~holder gs gu r =
            on_signed_overflow st ~ok:gs ~rest:gu ~guard:(both_flags gs gu) ~holder ~sort:(sort_of_width st n) k r
          in
          let ring mk =
            if wraps st then
              (* the holders' result is congruent to C's modulo 2^N, and is
                 always reduced, so that the result's range is known to be
                 the unsigned one *)
              let t = mk a b in
              wrap_flags st instr
                ~signed:(fun k' -> signed_pair (fun a b -> k' (mk a b)))
                ~unsigned:(fun k' -> unsigned_pair (fun a b -> k' (mk a b)))
                (fun gs gu -> overflow ~holder:(wrapped_holder n) gs gu (erem t (pow2 n)))
            else if Ir.has_nsw instr then
              signed_pair (fun a' b' ->
                  let r = mk a' b' in
                  wrap_flags st instr ~signed:(fun k' -> k' r)
                    ~unsigned:(fun k' -> unsigned_pair (fun a b -> k' (mk a b)))
                    (fun gs gu -> overflow ~holder:(signed_holder n) gs gu r))
            else if Ir.has_nuw instr then
              unsigned_pair (fun a' b' ->
                  let r = mk a' b' in
                  wrap_flags st instr ~signed:(fun k' -> k' r) ~unsigned:(fun k' -> k' r) (fun gs gu -> k (both_flags gs gu) r))
            else k fmla_true (mk a b)
          in
          let division pair mk =
            pair (fun a b ->
                let nonzero = Formula.mk_neg (atom (T_bool.mk_eq b (T_int.zero ()))) in
                let exact =
                  if Ir.is_exact instr then
                    atom (T_bool.mk_eq (T_int.mk_rem Value.Truncated a b) (T_int.zero ()))
                  else fmla_true
                in
                (* INT_MIN / -1 overflows, UB that the wrapping readings
                   write as BV mode does, and the mathematical and modulo
                   readings too, whose static range takes an [sdiv] result
                   to be signed *)
                let no_min_by_minus_one =
                  if st.config.Config.int_reading <> Config.Unbounded && (op = SDiv || op = SRem) then
                    Formula.mk_neg
                      (Formula.mk_and
                         (atom (T_bool.mk_eq a (int_num (Z.neg (pow2 (n - 1))))))
                         (atom (T_bool.mk_eq b (T_int.minus_one ()))))
                  else fmla_true
                in
                let g = Formula.mk_and nonzero exact in
                (* the quotient and remainder are signed values, whatever
                   the reading holds a ring result as *)
                on_signed_overflow st ~ok:no_min_by_minus_one ~rest:g
                  ~guard:(if Formula.is_true no_min_by_minus_one then g else Formula.mk_and g no_min_by_minus_one)
                  ~holder:(signed_holder n) ~sort:(sort_of_width st n) k (mk a b))
          in
          match op with
          | Add -> ring T_int.mk_add
          | Sub -> ring T_int.mk_sub
          | Mul -> ring T_int.mk_mul
          | SDiv -> division signed_pair (T_int.mk_div Value.Truncated)
          | SRem -> division signed_pair (T_int.mk_rem Value.Truncated)
          | UDiv -> division unsigned_pair (T_int.mk_div Value.Truncated)
          | URem -> division unsigned_pair (T_int.mk_rem Value.Truncated)
          | Shl | LShr | AShr | And | Or | Xor -> bitwise_int st instr a b k
          | op -> unknown at "the instruction %s" (Ir.opcode_name op)))
  | _ -> assert false

(* The conversion [icmp eq]/[ne] and a [switch] case compare under, given the
   operands' ranges.  In the dual range a bit pattern has two holders, which
   to_U makes one.  In the unbounded reading a holder outside the dual range
   is a value of its own, and to_U would make 2^N - 1 equal to -1; the
   holders are compared as they are, unless an operand is known to hold an
   unsigned value, against which the other (an unsigned constant spelled by
   its signed pattern, such as [UINT_MAX] as -1) is read unsigned. *)
let eq_conv st rx ry =
  if rx.signed && ry.signed then to_s
  else if st.config.Config.int_reading <> Config.Unbounded then to_u
  else if (rx.unsigned && not rx.signed) || (ry.unsigned && not ry.signed) then to_u
  else to_s

let icmp st env instr k =
  let at = instr in
  let x = Llvm.operand instr 0 and y = Llvm.operand instr 1 in
  let n = width x in
  let pred =
    match Llvm.icmp_predicate instr with
    | Some p -> p
    | None -> unknown at "a comparison without a predicate"
  in
  operands st env at [ x; y ] @@ function
  | [ a; b ] when n = 1 -> (
      let fa = fmla_of_bool a and fb = fmla_of_bool b in
      match pred with
      | Eq -> k (iff fa fb)
      | Ne -> k (Formula.mk_neg (iff fa fb))
      | _ -> unknown at "an ordered comparison of i1 values")
  | [ a; b ] -> (
      match st.mode with
      | Bv -> (
          let size = sz n in
          let s = Some true and u = Some false in
          match pred with
          | Eq -> k (bv_eq a b)
          | Ne -> k (Formula.mk_neg (bv_eq a b))
          | Slt -> k (atom (T_bv.mk_bvlt ~size ~signed:s a b))
          | Sle -> k (atom (T_bv.mk_bvleq ~size ~signed:s a b))
          | Sgt -> k (atom (T_bv.mk_bvgt ~size ~signed:s a b))
          | Sge -> k (atom (T_bv.mk_bvgeq ~size ~signed:s a b))
          | Ult -> k (atom (T_bv.mk_bvlt ~size ~signed:u a b))
          | Ule -> k (atom (T_bv.mk_bvleq ~size ~signed:u a b))
          | Ugt -> k (atom (T_bv.mk_bvgt ~size ~signed:u a b))
          | Uge -> k (atom (T_bv.mk_bvgeq ~size ~signed:u a b)))
      | Int -> (
          let rx = range_of ~wrap:(wraps st) [] x and ry = range_of ~wrap:(wraps st) [] y in
          let cmp conv mk =
            conv st ~range:rx n a (fun a' -> conv st ~range:ry n b (fun b' -> k (mk a' b')))
          in
          let eq_conv = eq_conv st rx ry in
          match pred with
          | Eq -> cmp eq_conv (fun a b -> atom (T_bool.mk_eq a b))
          | Ne -> cmp eq_conv (fun a b -> Formula.mk_neg (atom (T_bool.mk_eq a b)))
          | Slt -> cmp to_s (fun a b -> atom (T_int.mk_lt a b))
          | Sle -> cmp to_s (fun a b -> atom (T_int.mk_leq a b))
          | Sgt -> cmp to_s (fun a b -> atom (T_int.mk_gt a b))
          | Sge -> cmp to_s (fun a b -> atom (T_int.mk_geq a b))
          | Ult -> cmp to_u (fun a b -> atom (T_int.mk_lt a b))
          | Ule -> cmp to_u (fun a b -> atom (T_int.mk_leq a b))
          | Ugt -> cmp to_u (fun a b -> atom (T_int.mk_gt a b))
          | Uge -> cmp to_u (fun a b -> atom (T_int.mk_geq a b))))
  | _ -> assert false

let cast st env instr k =
  let at = instr in
  let x = Llvm.operand instr 0 in
  let m = width x and n = width instr in
  operand st env at x @@ fun a ->
  match (Llvm.instr_opcode instr, st.mode) with
  | Trunc, _ when n = 1 -> (
      match st.mode with
      | Bv -> k (bool_of_fmla (bv_eq (T_bv.mk_bvextract ~size:(sz m) 0 0 a) (bv_num 1 Z.one)))
      | Int -> (
          match interval_of ~wrap:(wraps st) ~havoc:(havocs st) [] x with
          | Some (lo, hi) when Z.geq lo Z.minus_one && Z.leq hi Z.one ->
              k (bool_of_fmla (Formula.mk_neg (atom (T_bool.mk_eq a (T_int.zero ())))))
          | _ -> k (bool_of_fmla (atom (T_bool.mk_eq (erem a (Z.of_int 2)) (T_int.one ()))))))
  | (ZExt | SExt), _ when m = 1 ->
      let one, ones =
        match st.mode with
        | Int -> (T_int.one (), T_int.minus_one ())
        | Bv -> (bv_num n Z.one, bv_num n Z.minus_one)
      in
      let zero = match st.mode with Int -> T_int.zero () | Bv -> bv_num n Z.zero in
      choose st.config.Config.conditional_value (fmla_of_bool a)
        (if Llvm.instr_opcode instr = ZExt then one else ones)
        zero k
  | Trunc, Bv -> k (T_bv.mk_bvextract ~size:(sz m) (n - 1) 0 a)
  | ZExt, Bv -> k (T_bv.mk_bvzext ~size:(sz m) (n - m) a)
  | SExt, Bv -> k (T_bv.mk_bvsext ~size:(sz m) (n - m) a)
  | Trunc, Int -> (
      if not (reduces st) then k a
      else if in_dual_range n (interval_of ~wrap:(wraps st) ~havoc:(havocs st) [] x) then k a
      else k (erem a (pow2 n)))
  | ZExt, Int -> to_u st ~range:(range_of ~wrap:(wraps st) [] x) m a k
  | SExt, Int -> to_s st ~range:(range_of ~wrap:(wraps st) [] x) m a k
  | op, _ -> unknown at "the cast %s" (Ir.opcode_name op)

(* -- Calls and memory --------------------------------------------------- *)

let nondet_range st at name n x =
  match st.mode with
  | Bv -> (
      (* As in Int mode, the range is the C type's, which the name gives,
         where the IR result is wider than that type (a [char] nondet
         declared as returning [int], or a [_Bool] one as returning [i8]):
         read at the IR width alone, the value could leave the type's range,
         and a check of that range would be reached by an execution the
         program does not have. *)
      let pointer_bits = 8 * Llvm_target.DataLayout.pointer_size st.layout in
      let size = sz n in
      let c_type =
        if String.starts_with ~prefix:Scope.nondet_prefix name then
          (Scope.nondet_signedness name, Scope.nondet_bits ~pointer_bits name)
        else (None, None)
      in
      match c_type with
      | _, Some 1 when n > 1 -> atom (T_bv.mk_bvleq ~size ~signed:(Some false) x (bv_num n Z.one))
      | Some true, Some b when b > 1 && b < n ->
          Formula.mk_and
            (atom (T_bv.mk_bvgeq ~size ~signed:(Some true) x (bv_num n (Z.neg (pow2 (b - 1))))))
            (atom (T_bv.mk_bvleq ~size ~signed:(Some true) x (bv_num n (Z.pred (pow2 (b - 1))))))
      | Some false, Some b when b > 1 && b < n ->
          atom (T_bv.mk_bvleq ~size ~signed:(Some false) x (bv_num n (Z.pred (pow2 b))))
      | _ -> fmla_true)
  | Int -> (
      let signed =
        if String.starts_with ~prefix:Scope.uninit_marker_prefix name then Some true
        else nondet_signedness name
      in
      match signed with
      | None -> unknown at "%s: its range is not known in Int mode" name
      | Some s ->
          (* The range is the C type's, which the name gives: the result may
             be wider in the IR than that type (SemanticAugmentor declares
             __VERIFIER_nondet_int as returning long long), and a range from
             the IR type would let it leave int's. *)
          let pointer_bits = 8 * Llvm_target.DataLayout.pointer_size st.layout in
          let bits =
            if not (String.starts_with ~prefix:Scope.nondet_prefix name) then n
            else
              match Scope.nondet_bits ~pointer_bits name with
              | Some b when b < n || b = 1 -> b
              | _ -> n
          in
          let lo, hi =
            if bits = 1 then (Z.zero, Z.one)
            else if s then (Z.neg (pow2 (bits - 1)), Z.pred (pow2 (bits - 1)))
            else (Z.zero, Z.pred (pow2 bits))
          in
          let geq_lo = atom (T_int.mk_geq x (int_num lo)) and leq_hi = atom (T_int.mk_leq x (int_num hi)) in
          (* the unbounded reading bounds only the narrow types, as CoAR's C
             frontend does by default *)
          if st.config.Config.int_reading = Config.Unbounded && bits > 16 then
            if s then fmla_true else geq_lo
          else Formula.mk_and geq_lo leq_hi)

(* -- Memory ---------------------------------------------------- *)

(* Indices into a component: [Int] in Int mode, 64-bit vectors in BV mode
   (getelementptr's indices are sign-extended to the index width). *)
let index_width = 64
let index_sort st = match st.mode with Int -> T_int.SInt | Bv -> T_bv.SBV (Some index_width)
let idx_num st z = match st.mode with Int -> int_num z | Bv -> bv_num index_width z

let idx_add st a b =
  match st.mode with Int -> T_int.mk_add a b | Bv -> T_bv.mk_bvadd ~size:(sz index_width) a b

let idx_sub st a b =
  match st.mode with Int -> T_int.mk_sub a b | Bv -> T_bv.mk_bvsub ~size:(sz index_width) a b

let idx_scale st a k =
  if Z.equal k Z.one then a
  else match st.mode with Int -> T_int.mk_mul a (int_num k) | Bv -> T_bv.mk_bvmul ~size:(sz index_width) a (bv_num index_width k)

let idx_lt st a b =
  match st.mode with
  | Int -> atom (T_int.mk_lt a b)
  | Bv -> atom (T_bv.mk_bvlt ~size:(sz index_width) ~signed:(Some true) a b)

let idx_le st a b = Formula.mk_neg (idx_lt st b a)

(* A position along one array dimension, in elements: a constant plus a
   sum of index terms. *)
type index = { off : Z.t; terms : Term.t list }

let const_index z = { off = z; terms = [] }
let is_zero_index i = Z.equal i.off Z.zero && i.terms = []
let add_index a b = { off = Z.add a.off b.off; terms = a.terms @ b.terms }

let scale_index st i k =
  if Z.equal k Z.one then i else { off = Z.mul i.off k; terms = List.map (fun t -> idx_scale st t k) i.terms }

let index_term st i =
  match i.terms with
  | [] -> idx_num st i.off
  | t :: rest ->
      let sum = List.fold_left (idx_add st) t rest in
      if Z.equal i.off Z.zero then sum else idx_add st sum (idx_num st i.off)

(* The arrays a Ptr2Arr keeps the heap and address-taken objects in, whose
   declared length only gives the C program room: the old Ptr2Arr's
   [memoryK] (or [memory<N>]) and the new one's region arrays [p2a_mem<N>],
   possibly followed by [_<M>] where the input already used the name.  They
   are read as unbounded arrays, with no bounds condition: the bounds of a
   block inside them are the C level's to check, which the new Ptr2Arr does
   in its safety modes. *)
let is_memoryk name =
  let digits s = s <> "" && String.for_all (fun c -> c >= '0' && c <= '9') s in
  let after prefix = String.sub name (String.length prefix) (String.length name - String.length prefix) in
  (String.starts_with ~prefix:"memory" name
  && let rest = after "memory" in
     rest = "K" || digits rest)
  || String.starts_with ~prefix:"p2a_mem" name
     &&
     match String.split_on_char '_' (after "p2a_mem") with
     | [ k ] -> digits k
     | [ k; m ] -> digits k && digits m
     | _ -> false

let describe_type ty =
  match (Llvm.classify_type ty, Llvm.struct_name ty) with
  | Struct, Some name when Ir.is_union ty -> Printf.sprintf "the union %s" name
  | Struct, Some name -> Printf.sprintf "the struct %s" name
  | _ -> Printf.sprintf "a value of type %s" (Llvm.string_of_lltype ty)

(* The object a pointer is rooted at: an [alloca] or a global, through
   getelementptr chains. *)
let rec root_of p =
  match Llvm.classify_value p with
  | Instruction Alloca | GlobalVariable -> Some p
  | Argument when Ir.struct_param_of_arg p <> None -> Some p
  | Instruction GetElementPtr -> root_of (Llvm.operand p 0)
  | ConstantExpr when Llvm.constexpr_opcode p = GetElementPtr -> root_of (Llvm.operand p 0)
  | _ -> None

let object_of st at p =
  match Hashtbl.find_opt st.objects p with
  | Some o -> o
  | None ->
      let local = Llvm.classify_value p <> GlobalVariable in
      let name = Printf.sprintf "m%d" (Hashtbl.length st.objects) in
      let elem, count, name =
        match Llvm.classify_value p with
        | GlobalVariable -> (Ir.global_value_type p, Some 1, global_name (Llvm.value_name p))
        | Argument -> (
            (* a struct passed by value or a result slot: the
               callee's own object, started from the caller's values *)
            match Ir.struct_param_of_arg p with
            | Some (Byval ty | Sret ty) -> (ty, Some 1, name)
            | None -> unknown at "a pointer parameter")
        | _ -> (
            match Llvm.int64_of_const (Llvm.operand p 0) with
            | Some n -> (Ir.allocated_type p, Some (Int64.to_int n), name)
            | None -> (Ir.allocated_type p, None, name))
      in
      let comps =
        match Memory.components elem with
        | comps -> comps
        | exception Memory.Unsupported ty -> unknown at "%s in memory" (describe_type ty)
      in
      let comps =
        List.map
          (fun (c : Memory.comp) ->
            let cname = String.concat "_" (name :: List.map string_of_int c.path) in
            let carray = count <> Some 1 || c.dims <> [] in
            let leaf = sort_of_width st c.width in
            let csort = if carray then T_array.mk_array_sort (index_sort st) leaf else leaf in
            let key =
              if local then (
                let id = comp_base + Hashtbl.length st.comp_ids in
                Some id)
              else None
            in
            let cv = { cname; comp = c; carray; leaf; csort; key } in
            Option.iter (fun id -> Hashtbl.add st.comp_ids id cv) key;
            cv)
          comps
      in
      let vlen =
        if count <> None then None
        else
          let id = comp_base + Hashtbl.length st.comp_ids in
          let cv =
            { cname = name ^ "_len"; comp = { Memory.path = []; width = index_width; dims = [] }; carray = false;
              leaf = index_sort st; csort = index_sort st; key = Some id }
          in
          Hashtbl.add st.comp_ids id cv;
          Some cv
      in
      let o = { ovalue = p; elem; count; comps; vlen; memoryk = (not local) && is_memoryk (Llvm.value_name p) } in
      Hashtbl.add st.objects p o;
      o

let comp_ids o = List.filter_map (fun cv -> cv.key) (o.comps @ Option.to_list o.vlen)

let comp_get env cv =
  match cv.key with
  | Some id -> (
      match IntMap.find_opt id env.vals with
      | Some t -> t
      | None -> Outcome.stop (Internal_error (Printf.sprintf "the component %s has no value on this path" cv.cname)))
  | None -> SMap.find cv.cname env.globs

let comp_set env cv t =
  match cv.key with
  | Some id -> { env with vals = IntMap.add id t env.vals }
  | None -> { env with globs = SMap.add cv.cname t env.globs }

let component at o path =
  match List.find_opt (fun cv -> cv.comp.path = path) o.comps with
  | Some cv -> cv
  | None -> unknown at "an access to part of a value"

(* The position of a leaf in its component: the outer index (which of the
   [count] values), then one index per array on its path, missing inner
   ones being 0, combined row-major. *)
let linear st cv levels =
  let dims = cv.comp.dims in
  let missing = 1 + List.length dims - List.length levels in
  match levels @ List.init missing (fun _ -> const_index Z.zero) with
  | outer :: inner ->
      List.fold_left2 (fun acc d i -> add_index (scale_index st acc (Z.of_int d)) i) outer dims inner
  | [] -> assert false

(* The number of leaves of a component in the whole object. *)
let total o cv = Option.map (fun n -> n * Memory.count cv.comp) o.count

(* The bounds condition of an access to leaves [lo, lo + n) of a component
   (over the whole object, on arrays other than memoryK). *)
let bounds st env o cv lo n =
  if (not cv.carray) || o.memoryk || not st.config.Config.bounds_conditions then fmla_true
  else
    let t =
      match (total o cv, o.vlen) with
      | Some k, _ -> idx_num st (Z.of_int k)
      | None, Some len -> idx_scale st (comp_get env len) (Z.of_int (Memory.count cv.comp))
      | None, None -> assert false
    in
    Formula.mk_and (idx_le st (idx_num st Z.zero) lo) (idx_le st (idx_add st lo n) t)

let read st env at o cv idx =
  if cv.carray then
    let i = index_term st idx in
    (T_array.mk_select (index_sort st) cv.leaf (comp_get env cv) i, bounds st env o cv i (idx_num st Z.one))
  else (
    if not (is_zero_index idx) then unknown at "an access beyond the variable %s" cv.cname;
    (comp_get env cv, fmla_true))

let write st env at o cv idx value =
  if cv.carray then
    let i = index_term st idx in
    (comp_set env cv (T_array.mk_store (index_sort st) cv.leaf (comp_get env cv) i value), bounds st env o cv i (idx_num st Z.one))
  else (
    if not (is_zero_index idx) then unknown at "an access beyond the variable %s" cv.cname;
    (comp_set env cv value, fmla_true))

(* -- Addresses as byte offsets -- *)

(* A byte offset into an object: a constant plus terms, each an index
   times its stride in bytes. *)
type bytes = { bc : int64; bterms : (Term.t * int64) list }

let as_index st env at v k =
  operand st env at v @@ fun t ->
  let n = width v in
  match st.mode with
  | Int -> to_s st ~range:(range_of ~wrap:(wraps st) [] v) n t k
  | Bv when n < index_width -> k (T_bv.mk_bvsext ~size:(sz n) (index_width - n) t)
  | Bv when n = index_width -> k t
  | Bv -> unknown at "an index wider than %d bits" index_width

let add_stride st env at b v stride k =
  match (Llvm.classify_value v, Llvm.int64_of_const v) with
  | ConstantInt, Some c -> k { b with bc = Int64.add b.bc (Int64.mul c stride) }
  | _ -> as_index st env at v (fun t -> k { b with bterms = b.bterms @ [ (t, stride) ] })

let gep_bytes st env at gep b k =
  let n = Llvm.num_operands gep in
  let rec go i ty b =
    if i >= n then k b
    else
      let v = Llvm.operand gep i in
      match Llvm.classify_type ty with
      | Struct -> (
          match Llvm.int64_of_const v with
          | Some f ->
              let f = Int64.to_int f in
              go (i + 1) (Ir.struct_element_types ty).(f)
                { b with bc = Int64.add b.bc (Memory.field_offset st.layout ty f) }
          | None -> unknown at "a variable struct field")
      | Array ->
          let e = Llvm.element_type ty in
          add_stride st env at b v (Memory.size st.layout e) (go (i + 1) e)
      | _ -> unknown at "a getelementptr into %s" (describe_type ty)
  in
  let source = Ir.gep_source_element_type gep in
  add_stride st env at b (Llvm.operand gep 1) (Memory.size st.layout source) (go 2 source)

(* The object an address points into, and the byte offset. *)
let rec address st env at p k =
  let through_gep () = address st env at (Llvm.operand p 0) (fun (o, b) -> gep_bytes st env at p b (fun b -> k (o, b))) in
  match Llvm.classify_value p with
  | Instruction Alloca | GlobalVariable -> k (object_of st at p, { bc = 0L; bterms = [] })
  | Argument when Ir.struct_param_of_arg p <> None -> k (object_of st at p, { bc = 0L; bterms = [] })
  | Instruction GetElementPtr -> through_gep ()
  | ConstantExpr when Llvm.constexpr_opcode p = GetElementPtr -> through_gep ()
  | _ -> unknown at "an access through a pointer whose target is not tracked"

(* -- From byte offsets back to leaves -- *)

type cursor = { ty : Llvm.lltype; path : int list; levels : index list; cbc : int64; cterms : (Term.t * int64) list }

let floor_div a b =
  let q = Int64.div a b in
  if Int64.rem a b < 0L then Int64.pred q else q

(* Selects an element of an array of [elem]: the terms whose stride is the
   element size or a multiple of it choose it, the others are left for the
   arrays inside (an index stays within its array: out of bounds is UB). *)
let enter_element st at cur elem =
  let s = Memory.size st.layout elem in
  if s = 0L then unknown at "an access into a value of size 0";
  let mine, rest = List.partition (fun (_, k) -> k >= s) cur.cterms in
  let q = floor_div cur.cbc s in
  let idx =
    List.fold_left
      (fun acc (e, k) ->
        if Int64.rem k s <> 0L then unknown at "an index whose stride is not a whole number of elements";
        add_index acc (scale_index st { off = Z.zero; terms = [ e ] } (Z.of_int64 (Int64.div k s))))
      (const_index (Z.of_int64 q)) mine
  in
  { ty = elem; path = cur.path; levels = cur.levels @ [ idx ]; cbc = Int64.sub cur.cbc (Int64.mul q s); cterms = rest }

let enter_field st cur =
  let fields = Ir.struct_element_types cur.ty in
  let rec find i =
    if i >= Array.length fields then None
    else
      let off = Memory.field_offset st.layout cur.ty i in
      if off <= cur.cbc && cur.cbc < Int64.add off (Memory.size st.layout fields.(i)) then
        Some { cur with ty = fields.(i); path = cur.path @ [ i ]; cbc = Int64.sub cur.cbc off }
      else find (i + 1)
  in
  find 0

let outer_cursor st at o (b : bytes) =
  enter_element st at { ty = o.elem; path = []; levels = []; cbc = b.bc; cterms = b.bterms } o.elem

(* The leaves an access of [w] bytes covers: component, index, bit position
   in the accessed value, width. *)
let pieces st at o (b : bytes) ~w =
  let fits c = Int64.add c.cbc w <= Memory.size st.layout c.ty in
  let rec descend cur =
    match Llvm.classify_type cur.ty with
    | Array ->
        let c = enter_element st at cur (Llvm.element_type cur.ty) in
        if fits c then descend c else (c, true)
    | Struct -> ( match enter_field st cur with Some c when fits c -> descend c | _ -> (cur, false))
    | _ -> (cur, false)
  in
  let start = outer_cursor st at o b in
  let cur, span = if fits start then descend start else (start, true) in
  if cur.cterms <> [] then unknown at "an access at a position that is not a field";
  let s = Memory.size st.layout cur.ty in
  let lo = cur.cbc and hi = Int64.add cur.cbc w in
  let leaves j =
    let shift = Int64.mul (Int64.of_int j) s in
    match Memory.leaves_in st.layout cur.ty ~lo:(Int64.sub lo shift) ~hi:(Int64.sub hi shift) with
    | leaves -> List.map (fun l -> (j, l)) leaves
    | exception Memory.Partial -> unknown at "an access to part of an integer"
    | exception Memory.Unsupported ty -> unknown at "%s in memory" (describe_type ty)
  in
  let elements = if span then Int64.to_int (floor_div (Int64.pred hi) s) + 1 else 1 in
  List.concat_map
    (fun (j, (suffix, inner, off, bits)) ->
      let cv = component at o (cur.path @ suffix) in
      let levels =
        match List.rev cur.levels with
        | last :: before when span -> List.rev before @ [ add_index last (const_index (Z.of_int j)) ]
        | _ -> cur.levels
      in
      let idx = linear st cv (levels @ List.map (fun i -> const_index (Z.of_int64 i)) inner) in
      let pos = Int64.sub (Int64.add off (Int64.mul (Int64.of_int j) s)) lo in
      [ (cv, idx, 8 * Int64.to_int pos, bits) ])
    (List.concat (List.init elements leaves))

(* The unsigned values of terms, through [k]. *)
let to_u_all st parts k =
  let rec go acc = function
    | [] -> k (List.rev acc)
    | (n, t) :: rest -> to_u st ~range:no_range n t (fun t' -> go (t' :: acc) rest)
  in
  go [] parts

(* A value of [n] bits made of the leaves [parts] (bit position, width,
   term).  Bits no part covers (padding) are arbitrary: each gap is
   a fresh value.  Int mode writes the value arithmetically, exact in the
   dual range. *)
let compose st at n parts k =
  if List.exists (fun (_, w, _) -> w = 1) parts then unknown at "an i1 inside a wider access";
  let parts = List.sort (fun (a, _, _) (b, _, _) -> compare a b) parts in
  let gaps =
    let rec go pos acc = function
      | [] -> List.rev (if pos < n then (pos, n - pos) :: acc else acc)
      | (p, w, _) :: rest -> go (p + w) (if p > pos then (pos, p - pos) :: acc else acc) rest
    in
    go 0 [] parts
  in
  let fresh = List.map (fun (pos, w) -> (pos, w, fresh_var st (sort_of_width st w))) gaps in
  let in_range =
    match st.mode with
    | Bv -> fmla_true
    | Int ->
        Formula.and_of
          (List.map
             (fun (_, w, (x, s)) ->
               let t = Term.mk_var x s in
               Formula.mk_and (atom (T_int.mk_geq t (T_int.zero ()))) (atom (T_int.mk_lt t (int_num (pow2 w)))))
             fresh)
  in
  let unsigned_gaps = List.map (fun (pos, w, (x, s)) -> (pos, w, Term.mk_var x s, true)) fresh in
  let all = List.sort (fun (a, _, _, _) (b, _, _, _) -> compare a b) (List.map (fun (p, w, t) -> (p, w, t, false)) parts @ unsigned_gaps) in
  let value =
    match st.mode with
    | Int ->
        let rec go acc = function
          | [] -> k acc
          | (pos, w, t, known_unsigned) :: rest ->
              let add u = go (T_int.mk_add acc (if pos = 0 then u else T_int.mk_mul u (int_num (pow2 pos)))) rest in
              if known_unsigned then add t else to_u st ~range:no_range w t add
        in
        go (T_int.zero ()) all
    | Bv ->
        k
          (List.fold_left
             (fun acc (pos, w, t, _) ->
               let t = if w = n then t else T_bv.mk_bvzext ~size:(sz w) (n - w) t in
               let t = if pos = 0 then t else T_bv.mk_bvshl ~size:(sz n) t (bv_num n (Z.of_int pos)) in
               T_bv.mk_bvor ~size:(sz n) acc t)
             (bv_num n Z.zero) all)
  in
  forall_vars (List.map (fun (_, _, v) -> v) fresh) (Formula.mk_imply in_range value)

(* The bits [pos, pos + w) of an [n]-bit value. *)
let bits_of st n x ~pos ~w k =
  match st.mode with
  | Int -> to_u st ~range:no_range n x (fun u -> k (erem (if pos = 0 then u else ediv u (pow2 pos)) (pow2 w)))
  | Bv -> k (T_bv.mk_bvextract ~size:(sz n) (pos + w - 1) pos x)

let rec load st env at ptr n k = address st env at ptr @@ fun (o, b) -> load_at st env at o b n k

and load_at st env at o b n k =
  match pieces st at o b ~w:(Int64.of_int ((n + 7) / 8)) with
  | [ (cv, idx, 0, bits) ] when bits = n ->
      let t, g = read st env at o cv idx in
      guarded st g (k t)
  | ps ->
      let reads = List.map (fun (cv, idx, pos, bits) -> (pos, bits, read st env at o cv idx)) ps in
      let g = Formula.and_of (List.map (fun (_, _, (_, g)) -> g) reads) in
      guarded st g (compose st at n (List.map (fun (pos, bits, (t, _)) -> (pos, bits, t)) reads) k)

let rec store st env at ptr n value k = address st env at ptr @@ fun (o, b) -> store_at st env at o b n value k

and store_at st env at o b n value k =
  match pieces st at o b ~w:(Int64.of_int ((n + 7) / 8)) with
  | [ (cv, idx, 0, bits) ] when bits = n ->
      let env, g = write st env at o cv idx value in
      guarded st g (k env)
  | ps ->
      if List.exists (fun (_, _, pos, bits) -> pos + bits > n) ps then unknown at "a store that covers part of a field";
      let rec go env gs = function
        | [] -> guarded st (Formula.and_of gs) (k env)
        | (cv, idx, pos, bits) :: rest ->
            bits_of st n value ~pos ~w:bits (fun part ->
                let env, g = write st env at o cv idx part in
                go env (g :: gs) rest)
      in
      go env [] ps

(* The leaves of a struct type: path, array indices, byte offset, width. *)
let struct_leaves st ty =
  match Memory.leaves_in st.layout ty ~lo:0L ~hi:(Memory.size st.layout ty) with
  | leaves -> leaves
  | exception Memory.Unsupported t -> stop_unknown "%s in a struct value" (describe_type t)

let leaf_sorts st ty = List.map (fun (_, _, _, w) -> sort_of_width st w) (struct_leaves st ty)

(* The index path of each leaf of an aggregate type as [extractvalue] and
   [insertvalue] write it: a struct field's number and an array element's
   index, interleaved from the outside in, one list per leaf in the order of
   [struct_leaves].  [struct_leaves] keeps the field numbers and the array
   indices in two lists, so a prefix test on the field numbers alone takes
   element [j] of an array of structs for field [j] of the struct around it,
   and finds no leaf at all under an index into an array of integers, where
   an [insertvalue] would then change nothing. *)
let leaf_index_paths st at ty =
  let rec go ty =
    match Llvm.classify_type ty with
    | Integer -> [ [] ]
    | Array ->
        let inner = go (Llvm.element_type ty) in
        List.concat (List.init (Llvm.array_length ty) (fun j -> List.map (fun p -> j :: p) inner))
    | Struct ->
        List.concat (List.mapi (fun i f -> List.map (fun p -> i :: p) (go f)) (Array.to_list (Ir.struct_element_types ty)))
    | _ -> unknown at "%s in a struct value" (describe_type ty)
  in
  let paths = go ty in
  if List.length paths <> List.length (struct_leaves st ty) then unknown at "%s with a leaf of size 0" (describe_type ty);
  paths

(* Whether the index path [path] leads to the leaf at [p] or to a part
   containing it. *)
let under path p = List.length p >= List.length path && List.filteri (fun i _ -> i < List.length path) p = path

(* A struct value is the tuple of its leaves, loaded and stored
   leaf by leaf. *)
let load_struct st env at ptr ty k =
  address st env at ptr @@ fun (o, b) ->
  let rec go acc = function
    | [] -> k (List.rev acc)
    | (_, _, off, w) :: rest -> load_at st env at o { b with bc = Int64.add b.bc off } w (fun t -> go (t :: acc) rest)
  in
  go [] (struct_leaves st ty)

let store_struct st env at ptr ty terms k =
  address st env at ptr @@ fun (o, b) ->
  let rec go env = function
    | [] -> k env
    | ((_, _, off, w), t) :: rest -> store_at st env at o { b with bc = Int64.add b.bc off } w t (fun env -> go env rest)
  in
  go env (List.combine (struct_leaves st ty) terms)

(* The leaves of a struct value made in the same block. *)
let agg_of st at v =
  (match Llvm.classify_value v with
  | Instruction (Call | Load | InsertValue | ExtractValue) -> ()
  | _ -> unknown at "a struct value other than one loaded, returned or built");
  if Llvm.instr_parent v != Llvm.instr_parent at then unknown at "a struct value used in another block";
  match Hashtbl.find_opt st.aggs (number st v) with
  | Some ts -> ts
  | None -> Outcome.stop (Internal_error "a struct value with no leaves on this path")

(* New, arbitrary contents for an object. *)
let havoc st env o k =
  let xs = List.map (fun cv -> (cv, fresh_var st cv.csort)) o.comps in
  forall_vars (List.map snd xs)
    (k (List.fold_left (fun env (cv, (x, s)) -> comp_set env cv (Term.mk_var x s)) env xs))

(* Whether the passes give this object its arbitrary contents: an integer
   local variable gets them from the marker stored into it. *)
let marked o = Ir.is_integer o.elem && o.count = Some 1

(* -- Whole regions: memset, memcpy, memmove -- *)

type count = Known of int | Variable of Term.t

(* A length of [k * unit_bytes] bytes, [k] read unsigned. *)
let length st env at len k =
  let const v = match (Llvm.classify_value v, Llvm.int64_of_const v) with ConstantInt, Some c -> Some c | _ -> None in
  let as_count v k =
    operand st env at v @@ fun t ->
    match st.mode with
    | Int -> to_u st ~range:(range_of ~wrap:(wraps st) [] v) (width v) t k
    | Bv when width v < index_width -> k (T_bv.mk_bvzext ~size:(sz (width v)) (index_width - width v) t)
    | Bv -> k t
  in
  match const len with
  | Some n -> k (None, n)
  | None -> (
      match Llvm.classify_value len with
      | Instruction Mul when const (Llvm.operand len 1) <> None ->
          as_count (Llvm.operand len 0) (fun t -> k (Some t, Option.get (const (Llvm.operand len 1))))
      | Instruction Mul when const (Llvm.operand len 0) <> None ->
          as_count (Llvm.operand len 1) (fun t -> k (Some t, Option.get (const (Llvm.operand len 0))))
      | Instruction Shl when const (Llvm.operand len 1) <> None ->
          as_count (Llvm.operand len 0) (fun t ->
              k (Some t, Int64.shift_left 1L (Int64.to_int (Option.get (const (Llvm.operand len 1))))))
      | _ -> as_count len (fun t -> k (Some t, 1L)))

(* The values of type [ty] a region covers: [m] consecutive elements of the
   array whose element the cursor is at, or one value. *)
let region st at o (b : bytes) (k_len, unit_bytes) =
  let size = Memory.size st.layout in
  let count_of factor =
    match k_len with None -> Known (Int64.to_int factor) | Some e -> Variable (idx_scale st e (Z.of_int64 factor))
  in
  let starts c = c.cterms = [] && c.cbc = 0L in
  let rec element cur =
    let s = size cur.ty in
    if starts cur && Int64.rem unit_bytes s = 0L then Some (cur, count_of (Int64.div unit_bytes s)) else inside cur
  and inside cur =
    match Llvm.classify_type cur.ty with
    | Array -> element (enter_element st at cur (Llvm.element_type cur.ty))
    | Struct -> (
        match enter_field st cur with
        | Some c when starts c && k_len = None && unit_bytes = size c.ty -> Some (c, Known 1)
        | Some c -> inside c
        | None -> None)
    | _ -> None
  in
  element (outer_cursor st at o b)

(* Per component of the region's type: the component, its first leaf and
   the number of leaves. *)
let region_components st at o (cur, m) =
  List.map
    (fun (c : Memory.comp) ->
      let cv = component at o (cur.path @ c.path) in
      let n = Memory.count c in
      let cnt = match m with Known k -> Known (k * n) | Variable e -> Variable (idx_scale st e (Z.of_int n)) in
      (cv, linear st cv cur.levels, cnt))
    (Memory.components cur.ty)

let covers_whole o cv start cnt =
  (not cv.carray) || (is_zero_index start && match (cnt, total o cv) with Known k, Some n -> k = n | _ -> false)

let unrolled_limit = 16

(* [a := λj. ite(lo ≤ j < hi, value j, a[j])], the default form of a
   variable-length region. *)
let lambda_region st cv old lo cnt value =
  let j, si = fresh_var st (index_sort st) in
  let jt = Term.mk_var j si in
  let hi = idx_add st lo cnt in
  let inside = Formula.mk_and (idx_le st lo jt) (idx_lt st jt hi) in
  T_array.mk_lambda (j, si) cv.leaf (T_bool.ifte inside (value jt) (T_array.mk_select si cv.leaf old jt))

let count_term st = function Known k -> idx_num st (Z.of_int k) | Variable e -> e

(* Writes [value j] (j the offset from the region's start) into the leaves
   of a region. *)
let fill st env at o cv start cnt value (k : env -> Formula.t -> Formula.t) =
  match cnt with
  | Known n when n <= unrolled_limit || not cv.carray ->
      let rec go env gs j =
        if j >= n then k env (Formula.and_of gs)
        else
          let env, g =
            write st env at o cv (add_index start (const_index (Z.of_int j))) (value (Some j) (idx_num st (Z.of_int j)))
          in
          go env (g :: gs) (j + 1)
      in
      go env [] 0
  | _ when st.config.Config.variable_length_copy = Loop ->
      (* the loop form: L(j, a, v̄) = (j < n ⇒ L(j + 1, a[lo + j := value j], v̄)) ∧ (j ≥ n ⇒ rest(a)),
         with v̄ the free variables of the rest and of the step, entered at
         L(0, a, v̄); a predicate of its own, a cut point of the body's kind *)
      if not cv.carray then unknown at "a region of variable length over a variable";
      let lo = index_term st start in
      let n = count_term st cnt in
      let old = comp_get env cv in
      let name = Ident.Pvar (Printf.sprintf "L%d" (List.length st.loops)) in
      st.loops <- MuCLP.Pred.make st.loop_kind name [] fmla_true :: st.loops;
      let j, si = fresh_var st (index_sort st) in
      let a, sa = fresh_var st cv.csort in
      let jt = Term.mk_var j si and av = Term.mk_var a sa in
      let step = T_array.mk_store si cv.leaf av (idx_add st lo jt) (value None jt) in
      let rest = k (comp_set env cv av) fmla_true in
      let free =
        Core.Set.to_list
          (Core.Set.union (Formula.term_sort_env_of rest)
             (Core.Set.union (Term.term_sort_env_of step) (Term.term_sort_env_of n)))
        |> List.filter (fun (x, _) -> not (Stdlib.( = ) x j || Stdlib.( = ) x a))
      in
      let params = ((j, si) :: (a, sa) :: free) in
      let app j' a' =
        atom (Atom.mk_pvar_app name (List.map snd params) (j' :: a' :: List.map (fun (x, s) -> Term.mk_var x s) free))
      in
      let more = idx_lt st jt n in
      let body =
        Formula.mk_and
          (Formula.mk_imply more (app (idx_add st jt (idx_num st Z.one)) step))
          (Formula.mk_imply (Formula.mk_neg more) rest)
      in
      st.loops <-
        List.map
          (fun (pred : MuCLP.Pred.t) -> if Stdlib.( = ) pred.name name then MuCLP.Pred.make st.loop_kind name params body else pred)
          st.loops;
      guarded st (bounds st env o cv lo n) (app (idx_num st Z.zero) old)
  | _ ->
      if not cv.carray then unknown at "a region of variable length over a variable";
      let lo = index_term st start in
      let n = count_term st cnt in
      let old = comp_get env cv in
      k (comp_set env cv (lambda_region st cv old lo n (fun j -> value None (idx_sub st j lo)))) (bounds st env o cv lo n)

(* The value a memset writes into a leaf of [w] bits. *)
let memset_value st env at byte w k =
  if w = 1 then unknown at "a memset of i1 values";
  if w = 8 then operand st env at byte k
  else (
    if w mod 8 <> 0 || w > 64 then unknown at "a memset of i%d values" w;
    let ones = List.fold_left (fun acc _ -> Z.add (Z.shift_left acc 8) Z.one) Z.zero (List.init (w / 8) Fun.id) in
    match (Llvm.classify_value byte, Llvm.int64_of_const byte) with
    | ConstantInt, Some v ->
        let pattern = Z.mul (Z.of_int64 (Int64.logand v 0xFFL)) ones in
        k (match st.mode with Int -> int_num pattern | Bv -> bv_num w pattern)
    | _ -> (
        operand st env at byte @@ fun c ->
        match st.mode with
        | Int -> to_u st ~range:(range_of ~wrap:(wraps st) [] byte) 8 c (fun u -> k (T_int.mk_mul u (int_num ones)))
        | Bv -> k (T_bv.mk_bvmul ~size:(sz w) (T_bv.mk_bvzext ~size:(sz 8) (w - 8) c) (bv_num w ones))))

let memset st env at instr k =
  address st env at (Llvm.operand instr 0) @@ fun (o, b) ->
  length st env at (Llvm.operand instr 2) @@ fun len ->
  match region st at o b len with
  | None -> unknown at "a memset that does not cover whole values"
  | Some r ->
      let rec go env gs = function
        | [] -> guarded st (Formula.and_of gs) (k env)
        | (cv, start, cnt) :: rest ->
            memset_value st env at (Llvm.operand instr 1) cv.comp.width @@ fun v ->
            if covers_whole o cv start cnt then
              go (comp_set env cv (if cv.carray then T_array.mk_const_array (index_sort st) cv.leaf v else v)) gs rest
            else
              fill st env at o cv start cnt (fun _ _ -> v) (fun env g -> go env (g :: gs) rest)
      in
      go env [] (region_components st at o r)

let shape st ty =
  (Memory.size st.layout ty, List.map (fun (c : Memory.comp) -> (c.width, Memory.count c)) (Memory.components ty))

(* memcpy and memmove: component by component between values of one shape;
   the source is read from the contents before the copy, which is
   memmove's result.  For memcpy the overlap of a copy within one component
   is UB (LangRef 19.1.7), whose condition is written. *)
let memcpy st env at instr ~overlap_ub k =
  address st env at (Llvm.operand instr 0) @@ fun (od, bd) ->
  address st env at (Llvm.operand instr 1) @@ fun (os, bs) ->
  length st env at (Llvm.operand instr 2) @@ fun len ->
  match (region st at od bd len, region st at os bs len) with
  | Some ((cd, md) as rd), Some ((cs, ms) as rs)
    when shape st cd.ty = shape st cs.ty
         && (match (md, ms) with Known a, Known b -> a = b | Variable _, Variable _ -> true | _ -> false) ->
      let pairs = List.combine (region_components st at od rd) (region_components st at os rs) in
      let rec go env gs = function
        | [] -> guarded st (Formula.and_of gs) (k env)
        | ((dv, dstart, cnt), (sv, sstart, _)) :: rest ->
            if covers_whole od dv dstart cnt && covers_whole os sv sstart cnt && dv.carray = sv.carray then
              go (comp_set env dv (comp_get env sv)) gs rest
            else
              let src = comp_get env sv in
              let source = { env with vals = env.vals } in
              let value j jt =
                match j with
                | Some j ->
                    fst (read st source at os sv (add_index sstart (const_index (Z.of_int j))))
                | None ->
                    T_array.mk_select (index_sort st) sv.leaf src (idx_add st (index_term st sstart) jt)
              in
              let src_bounds =
                if sv.carray then bounds st env os sv (index_term st sstart) (count_term st cnt) else fmla_true
              in
              let overlap =
                if overlap_ub && dv.cname = sv.cname && dv.carray then
                  let d = index_term st dstart and s = index_term st sstart and n = count_term st cnt in
                  Formula.or_of
                    [ atom (T_bool.mk_eq d s); idx_le st (idx_add st d n) s; idx_le st (idx_add st s n) d ]
                else fmla_true
              in
              fill st env at od dv dstart cnt value (fun env g -> go env (g :: src_bounds :: overlap :: gs) rest)
      in
      go env [] pairs
  | _ -> (
      (* between values of different shapes (a 12-byte struct and the
         { i64, i32 } clang returns it in): leaf by leaf, each destination
         leaf assembled from the source bits it covers *)
      match len with
      | Some _, _ -> unknown at "a copy of a variable length between values of different shapes"
      | None, w ->
          let src = pieces st at os bs ~w and dst = pieces st at od bd ~w in
          let reads = List.map (fun (cv, idx, pos, bits) -> (pos, bits, read st env at os cv idx)) src in
          let g = Formula.and_of (List.map (fun (_, _, (_, g)) -> g) reads) in
          let parts = List.map (fun (pos, bits, (t, _)) -> (pos, bits, t)) reads in
          let rec go env gs = function
            | [] -> guarded st (Formula.and_of (g :: gs)) (k env)
            | (cv, idx, lo, width) :: rest ->
                let overlapping =
                  List.filter_map
                    (fun (bp, bw, t) ->
                      let a = max lo bp and z = min (lo + width) (bp + bw) in
                      if a >= z then None else Some (a - lo, z - a, bw, a - bp, t))
                    parts
                in
                let rec slices acc = function
                  | [] -> compose st at width (List.rev acc) (fun v -> let env, g = write st env at od cv idx v in go env (g :: gs) rest)
                  | (pos, n, bw, from, t) :: more ->
                      if n = bw then slices ((pos, n, t) :: acc) more
                      else bits_of st bw t ~pos:from ~w:n (fun piece -> slices ((pos, n, piece) :: acc) more)
                in
                slices [] overlapping
          in
          go env [] dst)

(* llvm.lifetime.start/end on a whole local variable of constant size. *)
let alloca_bytes st a =
  match Llvm.int64_of_const (Llvm.operand a 0) with
  | Some n -> Some (Int64.mul n (Memory.size st.layout (Ir.allocated_type a)))
  | None -> None


(* -- Blocks and functions ------------------------------------------------ *)

type cfg = {
  blocks : Llvm.llbasicblock array;
  block_index : (Llvm.llbasicblock, int) Hashtbl.t;
  succs : int list array;  (** with repetition: one per edge *)
  incoming : int array;  (** number of incoming edges from reachable blocks *)
  on_cycle : bool array;  (** the block reaches itself by one or more edges *)
  live : IntSet.t array;  (** live at the block head, after its phis *)
  phis : Llvm.llvalue list array;
}

let successors_of block =
  match Llvm.block_terminator block with
  | None -> []
  | Some t -> Array.to_list (Llvm.successors t)

let build_cfg st fn =
  let blocks = Ir.basic_blocks fn in
  let nb = Array.length blocks in
  let block_index = Hashtbl.create nb in
  Array.iteri (fun i b -> Hashtbl.add block_index b i) blocks;
  let succs = Array.map (fun b -> List.map (Hashtbl.find block_index) (successors_of b)) blocks in
  let reachable = Array.make nb false in
  let rec visit i =
    if not reachable.(i) then (
      reachable.(i) <- true;
      List.iter visit succs.(i))
  in
  if nb > 0 then visit 0;
  let on_cycle =
    Array.init nb (fun i ->
        let seen = Array.make nb false in
        let rec reaches = function
          | [] -> false
          | j :: rest ->
              j = i
              || (if seen.(j) then reaches rest
                  else (
                    seen.(j) <- true;
                    reaches (succs.(j) @ rest)))
        in
        reaches succs.(i))
  in
  let incoming = Array.make nb 0 in
  Array.iteri (fun i ss -> if reachable.(i) then List.iter (fun j -> incoming.(j) <- incoming.(j) + 1) ss) succs;
  let phis =
    Array.map
      (fun b ->
        Llvm.fold_right_instrs (fun i acc -> if Llvm.instr_opcode i = PHI then i :: acc else acc) b [])
      blocks
  in
  (* liveness of tracked SSA values *)
  let tracked_set vs = List.fold_left (fun s v -> if is_tracked v then IntSet.add (number st v) s else s) IntSet.empty vs in
  let uses = Array.make nb IntSet.empty and defs = Array.make nb IntSet.empty in
  (* A local object's components are treated as one variable: an access to
     it uses all of them, and only a point that gives it arbitrary contents
     defines them (coarser than per component, which only keeps more
     arguments). *)
  let local_ids_at at p =
    match root_of p with
    | Some r when Llvm.classify_value r <> GlobalVariable -> IntSet.of_list (comp_ids (object_of st at r))
    | _ -> IntSet.empty
  in
  let sret_param =
    List.find_opt (fun p -> match Ir.struct_param_of_arg p with Some (Sret _) -> true | _ -> false) (Array.to_list (Ir.params fn))
  in
  let object_effect instr =
    let local_ids = local_ids_at instr in
    let callee_name () = Llvm.value_name (Ir.callee instr) in
    match Llvm.instr_opcode instr with
    | Ret -> ((match sret_param with Some p -> local_ids p | None -> IntSet.empty), IntSet.empty)
    | Load -> (local_ids (Llvm.operand instr 0), IntSet.empty)
    | Store -> (local_ids (Llvm.operand instr 1), IntSet.empty)
    | Alloca when Llvm.use_begin instr <> None -> (IntSet.empty, local_ids instr)
    | Call when Llvm.classify_value (Ir.callee instr) = Function -> (
        let name = callee_name () in
        let has prefix = String.starts_with ~prefix name in
        if has "llvm.memset." then (local_ids (Llvm.operand instr 0), IntSet.empty)
        else if has "llvm.memcpy." || has "llvm.memmove." then
          (IntSet.union (local_ids (Llvm.operand instr 0)) (local_ids (Llvm.operand instr 1)), IntSet.empty)
        else if has "llvm.lifetime.start." then (IntSet.empty, local_ids (Llvm.operand instr 1))
        else if has "llvm.dbg.declare" then
          match Ir.declared_slot instr with
          | Some slot when Ir.declared_arg instr = 0 -> (IntSet.empty, local_ids slot)
          | _ -> (IntSet.empty, IntSet.empty)
        else if Llvm.is_declaration (Ir.callee instr) then (IntSet.empty, IntSet.empty)
        else
          (* a struct passed by pointer: the caller's object is read (and an
             [sret] slot written, which is also a use when partial) *)
          let args = List.init (Llvm.num_arg_operands instr) (Llvm.operand instr) in
          ( List.fold_left
              (fun acc a -> if Ir.is_pointer (Llvm.type_of a) then IntSet.union acc (local_ids a) else acc)
              IntSet.empty args,
            IntSet.empty ))
    | _ -> (IntSet.empty, IntSet.empty)
  in
  Array.iteri
    (fun i b ->
      Llvm.iter_instrs
        (fun instr ->
          if Llvm.instr_opcode instr <> PHI then (
            (* a debug intrinsic's operands are metadata, which may be an
               argument list the bindings cannot classify (licm and
               simplifycfg leave one where they salvage a deleted value);
               its effect on a local object is object_effect's *)
            let ops =
              if Passes.is_debug_call instr then []
              else List.init (Llvm.num_operands instr) (Llvm.operand instr)
            in
            let ops = List.filter (fun v -> match Llvm.classify_value v with BasicBlock -> false | _ -> true) ops in
            let obj_uses, obj_defs = object_effect instr in
            uses.(i) <- IntSet.union uses.(i) (IntSet.diff (IntSet.union (tracked_set ops) obj_uses) defs.(i));
            defs.(i) <- IntSet.union defs.(i) obj_defs;
            if is_tracked instr then defs.(i) <- IntSet.add (number st instr) defs.(i)))
        b)
    blocks;
  let live = Array.make nb IntSet.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    for i = nb - 1 downto 0 do
      let out =
        List.fold_left
          (fun acc j ->
            let phi_results = tracked_set phis.(j) in
            let from_edge =
              List.fold_left
                (fun s phi ->
                  match List.find_opt (fun (_, b) -> b == blocks.(i)) (Llvm.incoming phi) with
                  | Some (v, _) when is_tracked v -> IntSet.add (number st v) s
                  | _ -> s)
                IntSet.empty phis.(j)
            in
            IntSet.union acc (IntSet.union (IntSet.diff live.(j) phi_results) from_edge))
          IntSet.empty succs.(i)
      in
      let l = IntSet.diff (IntSet.union uses.(i) out) defs.(i) in
      if not (IntSet.equal l live.(i)) then (
        live.(i) <- l;
        changed := true)
    done
  done;
  { blocks; block_index; succs; incoming; on_cycle; live; phis }

(* The two kinds of predicates: the property's ([W] for
   termination, [S] for unreach-call), and the return summary [T¬], which
   also takes the return value and the globals at the return.  [Ret] carries
   the terms that stand for those in the body being built. *)
type role = Prop | Ret of { re : Term.t list; ge : Term.t SMap.t }

type role_kind = P | R

let kind_of_role = function Prop -> P | Ret _ -> R

type fn = {
  llfn : Llvm.llvalue;
  fname : string;
  cfg : cfg;
  rets : Sort.t list;
      (** what a return gives the caller: the [sret] slot's components, then
          the value's leaves (none for [void]) *)
  sret : Llvm.llvalue option;  (** the [sret] parameter *)
  cut : (role_kind * int, unit) Hashtbl.t;
  visited : (role_kind * int, unit) Hashtbl.t;
}

let fn_of st_fns at llfn =
  match Hashtbl.find_opt st_fns llfn with
  | Some f -> f
  | None -> Outcome.stop (Internal_error (Printf.sprintf "%s: a callee outside the scope" (Scope.location at)))


(* The program points that get a predicate.  A join (a block reached by two
   or more edges) that lies on no cycle may instead be built at each edge
   into it, as a block reached by one edge is: every cycle passes a cut
   point, so the building stops, and the predicate it replaces is a
   non-recursive definition, so substituting its body changes no fixpoint.
   The part from the join to the next kept point is then copied once per
   edge into it. *)
let kept st f rk i =
  Hashtbl.mem f.visited (rk, i)
  && (i = 0
     || Hashtbl.mem f.cut (rk, i)
     || (f.cfg.incoming.(i) >= 2 && not (st.config.Config.inline_acyclic_joins && not f.cfg.on_cycle.(i)))
     || st.config.Config.every_point)

let pred_name st f rk i =
  let prefix =
    match (rk, st.property) with
    | R, _ -> "T"
    | P, Unreach_call -> "S"
    | P, Termination -> "W"
  in
  Ident.Pvar (Printf.sprintf "%s_%s_%d" prefix f.fname i)

let re_var i = Printf.sprintf "r_e%d" i
let ge_var name = "e_" ^ name

let pred_args st f rk i =
  let locals = List.map (id_var st) (IntSet.elements f.cfg.live.(i)) in
  let globs = List.map (fun (name, sort) -> (Ident.Tvar name, sort)) st.globals in
  let ret =
    match rk with
    | P -> []
    | R ->
        List.mapi (fun i s -> (Ident.Tvar (re_var i), s)) f.rets
        @ List.map (fun (name, sort) -> (Ident.Tvar (ge_var name), sort)) st.globals
  in
  locals @ globs @ ret

let pred_app st f role i env =
  let locals =
    List.map
      (fun x ->
        match IntMap.find_opt x env.vals with
        | Some t -> t
        | None -> Outcome.stop (Internal_error (Printf.sprintf "%s: no value for x%d at block %d" f.fname x i)))
      (IntSet.elements f.cfg.live.(i))
  in
  let globs = List.map (fun (name, _) -> SMap.find name env.globs) st.globals in
  let ret =
    match role with
    | Prop -> []
    | Ret { re; ge } -> re @ List.map (fun (name, _) -> SMap.find name ge) st.globals
  in
  let rk = kind_of_role role in
  let args = pred_args st f rk i in
  atom (Atom.mk_pvar_app (pred_name st f rk i) (List.map snd args) (locals @ globs @ ret))

(* Equality of two values of one sort ([i1] values are Boolean terms). *)
let eq_value sort a b =
  if Stdlib.( = ) sort T_bool.SBool then iff (fmla_of_bool a) (fmla_of_bool b)
  else atom (T_bool.mk_eq a b)

let forall = forall_vars

(* The absolute value of a call's first argument ([llvm.abs], [imaxabs]),
   bound to the call.  With [poison_at_min] the minimum, whose absolute value
   does not fit, is UB in BV mode; Int mode writes no condition for it, as it
   writes none for an overflow. *)
(* [llvm.abs]; with [poison_at_min] its result at the minimum is poison
   (C's [abs(INT_MIN)] overflows): undefined behaviour guarded by [g] under
   [Undefined], an arbitrary value of the type (signed in Int mode, any
   vector in BV mode) under [Arbitrary_value].  The mathematical and modulo
   readings write no guard here. *)
let absolute st env instr ~poison_at_min continue =
  let at = instr in
  let x = Llvm.operand instr 0 in
  let n = width x in
  let rest v = continue (bind st env instr v) in
  operand st env at x @@ fun a ->
  match st.mode with
  | Int ->
      to_s st ~range:(range_of ~wrap:(wraps st) [] x) n a (fun a' ->
          (* the wrapping readings write the minimum's UB, as BV mode does *)
          let g =
            if wraps st && poison_at_min then Formula.mk_neg (atom (T_bool.mk_eq a' (int_num (Z.neg (pow2 (n - 1))))))
            else fmla_true
          in
          let normal () =
            choose st.config.Config.conditional_value
              (atom (T_int.mk_lt a' (T_int.zero ())))
              (T_int.mk_neg a') a' rest
          in
          if Formula.is_true g || not (havocs st) then guarded st g (normal ())
          else overflow_choice st ~ok:g ~holder:(signed_holder n) ~sort:(sort_of_width st n) normal rest)
  | Bv ->
      let size = sz n in
      let g = if poison_at_min then Formula.mk_neg (bv_eq a (bv_num n (Z.neg (pow2 (n - 1))))) else fmla_true in
      let normal () = choose st.config.Config.conditional_value (bv_negative n a) (T_bv.mk_bvneg ~size a) a rest in
      if Formula.is_true g || not (havocs st) then guarded st g (normal ())
      else overflow_choice st ~ok:g ~holder:(fun _ -> fmla_true) ~sort:(sort_of_width st n) normal rest

(* The n-bit value [a] with its bytes reversed, read as unsigned: byte k of
   the unsigned value moves to byte n/8 - 1 - k.  In Int mode the unsigned
   value is [erem(a, 2^n)], which depends only on the bit pattern, so every
   reading gives the same result, in [0, 2^n). *)
let byte_swap st n a =
  let bytes = n / 8 in
  match st.mode with
  | Int ->
      let u = erem a (pow2 n) in
      let byte k =
        let shifted = if k = 0 then u else ediv u (pow2 (8 * k)) in
        let b = if k = bytes - 1 then shifted else erem shifted (pow2 8) in
        let target = bytes - 1 - k in
        if target = 0 then b else T_int.mk_mul b (int_num (pow2 (8 * target)))
      in
      List.fold_left T_int.mk_add (byte 0) (List.init (bytes - 1) (fun k -> byte (k + 1)))
  | Bv ->
      let size = sz n in
      let byte k =
        let b = T_bv.mk_bvzext ~size:(sz 8) (n - 8) (T_bv.mk_bvextract ~size (8 * k + 7) (8 * k) a) in
        let target = bytes - 1 - k in
        if target = 0 then b else T_bv.mk_bvshl ~size b (bv_num n (Z.of_int (8 * target)))
      in
      List.fold_left (T_bv.mk_bvor ~size) (byte 0) (List.init (bytes - 1) (fun k -> byte (k + 1)))

let rec edge st fns f role env ~from j =
  let cfg = f.cfg in
  let source = cfg.blocks.(from) in
  let incoming phi =
    match List.find_opt (fun (_, b) -> b == source) (Llvm.incoming phi) with
    | Some (v, _) -> v
    | None -> unknown phi "a phi without a value for this edge"
  in
  let tracked_phis = List.filter is_tracked cfg.phis.(j) in
  (* the phis of the target are assigned simultaneously: every incoming
     value is read in [env] *)
  operands st env (List.hd (cfg.phis.(j) @ [ Option.get (Llvm.block_terminator source) ]))
    (List.map incoming tracked_phis)
  @@ fun ts ->
  let env' = List.fold_left2 (fun e phi t -> bind st e phi t) env tracked_phis ts in
  if kept st f (kind_of_role role) j then pred_app st f role j env' else block_body st fns f role env' j

and block_body st fns f role env i =
  let instrs = Llvm.fold_right_instrs (fun x acc -> x :: acc) f.cfg.blocks.(i) [] in
  instructions st fns f role env i instrs

and instructions st fns f role env i = function
  | [] -> Outcome.stop (Internal_error "a block without a terminator")
  | instr :: rest -> (
      let continue env = instructions st fns f role env i rest in
      let edge_to target = edge st fns f role env ~from:i (Hashtbl.find f.cfg.block_index target) in
      let at = instr in
      match Llvm.instr_opcode instr with
      | PHI -> continue env
      (* An unused result of an instruction that has no UB of its own adds
         nothing, and a choice ([zext] of an [i1], [select]) would copy the
         rest of the segment for it; clang leaves such values at -O0 (the
         [i64] [zext] of a condition it does not use). *)
      | (ICmp | Select | Trunc | ZExt | SExt) when Llvm.use_begin instr = None -> continue env
      | Add | Sub | Mul | UDiv | SDiv | URem | SRem | Shl | LShr | AShr | And | Or | Xor ->
          arith st env instr (fun g v -> guarded st g (continue (bind st env instr v)))
      | ICmp -> icmp st env instr (fun c -> continue (bind st env instr (bool_of_fmla c)))
      | Trunc | ZExt | SExt -> cast st env instr (fun v -> continue (bind st env instr v))
      | Select ->
          operands st env at [ Llvm.operand instr 0; Llvm.operand instr 1; Llvm.operand instr 2 ]
          @@ (function
          | [ c; a; b ] ->
              if width instr = 1 then
                continue
                  (bind st env instr
                     (bool_of_fmla
                        (Formula.mk_or
                           (Formula.mk_and (fmla_of_bool c) (fmla_of_bool a))
                           (Formula.mk_and (Formula.mk_neg (fmla_of_bool c)) (fmla_of_bool b)))))
              else
                choose st.config.Config.conditional_value (fmla_of_bool c) a b (fun v ->
                    continue (bind st env instr v))
          | _ -> assert false)
      | Load ->
          let ty = Llvm.type_of instr in
          if Llvm.classify_type ty = Struct then
            load_struct st env at (Llvm.operand instr 0) ty (fun ts ->
                Hashtbl.replace st.aggs (number st instr) ts;
                continue env)
          else (
            if not (is_int_type ty) then unknown at "a load of a non-integer";
            (* the wrapping readings hold every value of a type as one in its
               unsigned range, an object's arbitrary contents included *)
            let n = width instr in
            let reduce t = if st.mode = Int && wraps st && n > 1 then erem t (pow2 n) else t in
            load st env at (Llvm.operand instr 0) n (fun t -> continue (bind st env instr (reduce t))))
      | Store ->
          let value = Llvm.operand instr 0 in
          let ty = Llvm.type_of value in
          if Llvm.classify_type ty = Struct then store_struct st env at (Llvm.operand instr 1) ty (agg_of st at value) continue
          else operand st env at value @@ fun t -> store st env at (Llvm.operand instr 1) (width value) t continue
      | Alloca ->
          (* arbitrary contents where the object is allocated, for paths
             that bypass its declaration *)
          if Llvm.use_begin instr = None then continue env
          else
            let o = object_of st at instr in
            if marked o then continue env
            else (
              match o.vlen with
              | None -> havoc st env o continue
              | Some len ->
                  (* a variable-length array: its length, read unsigned, is
                     kept for the bounds condition; fresh contents each time *)
                  length st env at (Llvm.operand instr 0) @@ fun (k, unit) ->
                  let t = match k with Some t -> idx_scale st t (Z.of_int64 unit) | None -> idx_num st (Z.of_int64 unit) in
                  havoc st (comp_set env len t) o continue)
      | GetElementPtr -> continue env
      (* a block's index converted for [free], which uses it only there
         (Allowlist) and does nothing *)
      | IntToPtr -> continue env
      | Call -> call st fns f role env i instr rest
      | Ret when Ir.is_noreturn f.llfn ->
          (* a return from a function declared noreturn is UB *)
          guarded st fmla_false fmla_true
      | Ret -> (
          (* a return ends [W] and [S] (the caller continues); [T¬] says
             that this return is not the one with [r_e], [ḡ_e] *)
          match role with
          | Prop -> fmla_true
          | Ret { re; ge } ->
              let globals_equal =
                List.map (fun (name, sort) -> eq_value sort (SMap.find name ge) (SMap.find name env.globs)) st.globals
              in
              let finish values =
                if List.length values <> List.length re then Outcome.stop (Internal_error "a return that does not match its function");
                Formula.mk_neg
                  (Formula.and_of (List.map2 (fun (r, v) sort -> eq_value sort r v) (List.combine re values) f.rets @ globals_equal))
              in
              let slot = match f.sret with Some p -> List.map (comp_get env) (object_of st at p).comps | None -> [] in
              if Llvm.num_operands instr = 0 then finish slot
              else
                let v = Llvm.operand instr 0 in
                if Llvm.classify_type (Llvm.type_of v) = Struct then finish (slot @ agg_of st at v)
                else operand st env at v @@ fun t -> finish (slot @ [ t ]))
      | Unreachable -> (
          match st.config.Config.ub_reading with Stop_path -> fmla_true | Literal_c -> fmla_false)
      | Br -> (
          match Llvm.get_branch instr with
          | Some (`Unconditional target) -> edge_to target
          | Some (`Conditional (c, _, _)) when (match Llvm.classify_value c with UndefValue | PoisonValue -> true | _ -> false) ->
              (* a branch on undef or poison is UB *)
              guarded st fmla_false fmla_true
          | Some (`Conditional (c, t, e)) ->
              operand st env at c @@ fun c ->
              let c = fmla_of_bool c in
              Formula.mk_and (Formula.mk_imply c (edge_to t)) (Formula.mk_imply (Formula.mk_neg c) (edge_to e))
          | None -> unknown at "a branch")
      | Switch ->
          let cond = Llvm.operand instr 0 in
          let n = width cond in
          let cases =
            List.init ((Llvm.num_operands instr - 2) / 2) (fun k ->
                (Llvm.operand instr (2 + (2 * k)), Llvm.block_of_value (Llvm.operand instr (3 + (2 * k)))))
          in
          let default = Llvm.block_of_value (Llvm.operand instr 1) in
          operand st env at cond @@ fun x ->
          let eq_case k_val k =
            operand st env at k_val @@ fun kt ->
            (* an [i1] condition and its cases are Boolean terms in both
               modes, which no integer conversion applies to *)
            if n = 1 then k (iff (fmla_of_bool x) (fmla_of_bool kt))
            else
              match st.mode with
              | Bv -> k (bv_eq x kt)
              | Int ->
                  let r = range_of ~wrap:(wraps st) [] cond in
                  let conv, rk =
                    if st.config.Config.int_reading = Config.Unbounded then
                      let rk = range_of ~wrap:(wraps st) [] k_val in
                      (eq_conv st r rk, rk)
                    else (to_u, no_range)
                  in
                  conv st ~range:r n x (fun x' -> conv st ~range:rk n kt (fun k' -> k (atom (T_bool.mk_eq x' k'))))
          in
          let rec go acc_not = function
            | [] -> Formula.mk_imply (Formula.and_of acc_not) (edge_to default)
            | (kv, target) :: cs ->
                eq_case kv (fun e ->
                    Formula.mk_and (Formula.mk_imply e (edge_to target)) (go (Formula.mk_neg e :: acc_not) cs))
          in
          go [] cases
      | ExtractValue -> (
          (* the element's leaves of the struct value *)
          let agg = Llvm.operand instr 0 in
          let terms = agg_of st at agg in
          let path = Array.to_list (Ir.indices instr) in
          let paths = leaf_index_paths st at (Llvm.type_of agg) in
          if List.length paths <> List.length terms then Outcome.stop (Internal_error "a struct value with a wrong number of leaves");
          let mine = List.filter_map (fun (p, t) -> if under path p then Some t else None) (List.combine paths terms) in
          match mine with
          | [ t ] when is_int_type (Llvm.type_of instr) -> continue (bind st env instr t)
          | ts when Llvm.classify_type (Llvm.type_of instr) = Struct ->
              Hashtbl.replace st.aggs (number st instr) ts;
              continue env
          | _ -> unknown at "an extractvalue of an element that is not a field")
      | Freeze ->
          (* the value itself; on a poison or undef constant one arbitrary
             value, the same at every use *)
          if not (is_int_type (Llvm.type_of instr)) then unknown at "a freeze of a value that is not an integer";
          operand st env at (Llvm.operand instr 0) (fun t -> continue (bind st env instr t))
      | InsertValue ->
          let agg = Llvm.operand instr 0 and elem = Llvm.operand instr 1 in
          let ty = Llvm.type_of instr in
          let leaves = struct_leaves st ty in
          let base k =
            match Llvm.classify_value agg with
            | UndefValue | PoisonValue ->
                let xs = List.map (fun (_, _, _, w) -> fresh_var st (sort_of_width st w)) leaves in
                forall_vars xs (k (List.map (fun (x, s) -> Term.mk_var x s) xs))
            | _ -> k (agg_of st at agg)
          in
          let path = Array.to_list (Ir.indices instr) in
          let paths = leaf_index_paths st at ty in
          base @@ fun old ->
          (* the leaves under [path], in order, are replaced by the element's,
             one for one *)
          let put news =
            if List.length (List.filter (under path) paths) <> List.length news then
              unknown at "an insertvalue whose element does not match the leaves it replaces";
            let rec go olds news acc = function
              | [] -> List.rev acc
              | p :: rest ->
                  if under path p then go (List.tl olds) (List.tl news) (List.hd news :: acc) rest
                  else go (List.tl olds) news (List.hd olds :: acc) rest
            in
            Hashtbl.replace st.aggs (number st instr) (go old news [] paths);
            continue env
          in
          if Llvm.classify_type (Llvm.type_of elem) = Struct then put (agg_of st at elem)
          else operand st env at elem (fun t -> put [ t ])
      | op -> unknown at "the instruction %s" (Ir.opcode_name op))

and call st fns f role env i instr rest =
  let at = instr in
  let continue env = instructions st fns f role env i rest in
  match Scope.classify_callee instr with
  | Intrinsic fn -> intrinsic st env instr (Llvm.value_name fn) continue
  | Defined callee -> defined_call st fns f role env at callee continue
  | Modelled (kind, fn) -> (
      let name = Llvm.value_name fn in
      match kind with
      | Nondet | Uninit_marker ->
          let n = width instr in
          let x = fresh_var st (sort_of_width st n) in
          let xt = Term.mk_var (fst x) (snd x) in
          let range = if n = 1 then fmla_true else nondet_range st at name n xt in
          Formula.mk_forall [ x ] (Formula.mk_imply range (continue (bind st env instr xt)))
      | Assume ->
          operand st env at (Llvm.operand instr 0) @@ fun c ->
          let holds =
            if width (Llvm.operand instr 0) = 1 then fmla_of_bool c
            else
              match st.mode with
              | Int -> Formula.mk_neg (atom (T_bool.mk_eq c (T_int.zero ())))
              | Bv -> Formula.mk_neg (bv_eq c (bv_num (width (Llvm.operand instr 0)) Z.zero))
          in
          (* assume(0) loops forever: it never returns, and it
             does not terminate *)
          (match (role, st.property) with
          | Prop, Termination -> Formula.mk_and holds (continue env)
          | _ -> Formula.mk_imply holds (continue env))
      | Cut ->
          (* an execution where the argument is 0 ends there: it terminates,
             is safe, and does not return *)
          operand st env at (Llvm.operand instr 0) @@ fun c ->
          let holds =
            match st.mode with
            | Int -> Formula.mk_neg (atom (T_bool.mk_eq c (T_int.zero ())))
            | Bv -> Formula.mk_neg (bv_eq c (bv_num (width (Llvm.operand instr 0)) Z.zero))
          in
          Formula.mk_imply holds (continue env)
      | Wrap (signed, n) ->
          (* In C the call converts its argument to the N-bit type, which the
             BV mode's value already is.  In Int mode no reading reduces the
             result of an arithmetic operation, so the value is reduced here
             into the type's range modulo 2^N, unless its holder is known to
             lie there already; the name is the only place the signedness is
             written. *)
          let x = Llvm.operand instr 0 in
          operand st env at x @@ fun a ->
          let value =
            match st.mode with
            | Bv -> a
            | Int ->
                let lo, hi = if signed then (Z.neg (pow2 (n - 1)), pow2 (n - 1)) else (Z.zero, pow2 n) in
                let within = match interval_of ~wrap:(wraps st) ~havoc:(havocs st) [] x with Some (l, h) -> Z.geq l lo && Z.lt h hi | None -> false in
                if within then a
                else if signed then T_int.mk_sub (erem (T_int.mk_add a (half n)) (pow2 n)) (half n)
                else erem a (pow2 n)
          in
          continue (bind st env instr value)
      | Reach_error -> (
          match (role, st.property) with
          | Prop, Unreach_call -> fmla_false
          | _ -> fmla_true)
      | Program_end -> fmla_true
      | Free -> continue env
      | Region_arbitrary global -> (
          (* The new Ptr2Arr's region arrays (and the scalars it keeps a
             region's one cell in) are C globals, which start at 0, but they
             stand for heap and local objects whose contents are
             indeterminate; Ptr2Arr calls this at the head of main, before it
             writes the static objects, and where a scalar cell's block is
             allocated.  A global the translated code never accesses has no
             components, and its contents do not matter. *)
          match Llvm.lookup_global global (Llvm.global_parent fn) with
          | Some g -> (
              match Hashtbl.find_opt st.objects g with
              | Some o -> havoc st env o continue
              | None -> continue env)
          | None -> unknown at "%s names no global variable" name)
      | No_effect -> continue env
      | Rand | Time | Descriptor | Status ->
          (* a fresh value: rand's in [0, RAND_MAX], time's of its type,
             a descriptor >= -1 and a status 0 or -1, both read as signed *)
          if Llvm.use_begin instr = None then continue env
          else
            let n = width instr in
            let x = fresh_var st (sort_of_width st n) in
            let xt = Term.mk_var (fst x) (snd x) in
            let int_num_of z = match st.mode with Int -> int_num z | Bv -> bv_num n z in
            let geq lo = match st.mode with Int -> atom (T_int.mk_geq xt (int_num lo)) | Bv -> atom (T_bv.mk_bvgeq ~size:(sz n) ~signed:(Some true) xt (bv_num n lo)) in
            let eq z = atom (T_bool.mk_eq xt (int_num_of z)) in
            let range =
              match kind with
              | Rand -> (
                  let max = Z.pred (pow2 31) in
                  match st.mode with
                  | Int -> Formula.mk_and (geq Z.zero) (atom (T_int.mk_leq xt (int_num max)))
                  | Bv -> atom (T_bv.mk_bvleq ~size:(sz n) ~signed:(Some false) xt (bv_num n max)))
              | Descriptor ->
                  (* in Int mode a value of int also lies below 2^31 *)
                  Formula.mk_and (geq Z.minus_one)
                    (match st.mode with Int -> atom (T_int.mk_lt xt (int_num (pow2 31))) | Bv -> fmla_true)
              | Status -> Formula.mk_or (eq Z.zero) (eq Z.minus_one)
              | _ -> (
                  (* time_t is signed; the unbounded reading bounds no wide type *)
                  match st.mode with
                  | Int when st.config.Config.int_reading <> Config.Unbounded ->
                      Formula.mk_and (geq (Z.neg (pow2 (n - 1)))) (atom (T_int.mk_lt xt (half n)))
                  | _ -> fmla_true)
            in
            Formula.mk_forall [ x ] (Formula.mk_imply range (continue (bind st env instr xt)))
      | Byte_swap n ->
          operand st env at (Llvm.operand instr 0) @@ fun a -> continue (bind st env instr (byte_swap st n a))
      | Inet_addr -> (
          match Scope.inet_addr_value instr with
          | Some v ->
              let z = Z.of_int64 v in
              continue (bind st env instr (match st.mode with Int -> int_num z | Bv -> bv_num 32 z))
          | None -> unknown at "%s of anything but a constant decimal dotted quad" name)
      | Imaxabs -> absolute st env instr ~poison_at_min:true continue
      | Output ->
          (* no effect on the state; any int, also negative on error *)
          if Llvm.use_begin instr = None then continue env
          else
            let x = fresh_var st (sort_of_width st 32) in
            Formula.mk_forall [ x ] (continue (bind st env instr (Term.mk_var (fst x) (snd x)))))

(* The intrinsics.  [llvm.abs] and the overflow builtins are read
   in both modes; an [*.with.overflow] result is a pair kept for the
   [extractvalue]s that follow it in its block. *)
and intrinsic st env instr name continue =
  let at = instr in
  let has prefix = String.starts_with ~prefix name in
  if has "llvm.dbg.declare" then
    (* a local array or struct gets arbitrary contents where it is declared,
       so one declared in a loop is fresh on every iteration; a parameter's
       declaration (a struct passed by value) changes nothing *)
    match Ir.declared_slot instr with
    | Some slot when Llvm.classify_value slot = Instruction Alloca && Llvm.use_begin slot <> None && Ir.declared_arg instr = 0 ->
        let o = object_of st at slot in
        if marked o then continue env else havoc st env o continue
    | _ -> continue env
  else if
    has "llvm.dbg." || has "llvm.stacksave" || has "llvm.stackrestore" || has "llvm.lifetime.end."
    (* a scope of noalias metadata, which the translation does not read *)
    || has "llvm.experimental.noalias.scope.decl"
  then continue env
  else if has "llvm.lifetime.start." then (
    let size = Llvm.int64_of_const (Llvm.operand instr 0) in
    let p = Llvm.operand instr 1 in
    match Llvm.classify_value p with
    | Instruction Alloca when size <> None && size = alloca_bytes st p ->
        if Llvm.use_begin p = None then continue env else havoc st env (object_of st at p) continue
    | _ -> unknown at "a lifetime marker other than on a whole local variable")
  else if has "llvm.memset." then memset st env at instr continue
  else if has "llvm.memcpy." then memcpy st env at instr ~overlap_ub:true continue
  else if has "llvm.memmove." then memcpy st env at instr ~overlap_ub:false continue
  else if name = "llvm.trap" then fmla_true
  else if name = "llvm.ubsantrap" then
    (* a check clang inserted found UB (-fsanitize-trap): the path stops by
       default, a violation under the literal C reading *)
    guarded st fmla_false fmla_true
  else if name = "llvm.assume" then
    operand st env at (Llvm.operand instr 0) @@ fun c -> guarded st (fmla_of_bool c) (continue env)
  else if has "llvm.abs." then
    absolute st env instr ~poison_at_min:(Llvm.int64_of_const (Llvm.operand instr 1) <> Some 0L) continue
  else if has "llvm.ctpop." || has "llvm.ctlz." || has "llvm.cttz." || has "llvm.bswap." then (
    let x = Llvm.operand instr 0 in
    let n = width instr in
    match st.mode with
    | Int -> unknown at "the intrinsic %s in Int mode" name
    | Bv when n = 1 -> unknown at "the intrinsic %s on i1" name
    | Bv when has "llvm.bswap." && n mod 16 <> 0 -> unknown at "the intrinsic %s on i%d" name n
    | Bv ->
        let size = sz n in
        operand st env at x @@ fun a ->
        (* a step's value is named by a variable, so that no term repeats a
           growing one: the smearing doubles its operand at every step *)
        let named e k =
          let t, sort = fresh_var st (T_bv.SBV size) in
          let tt = Term.mk_var t sort in
          Formula.mk_forall [ (t, sort) ] (Formula.mk_imply (bv_eq tt e) (k tt))
        in
        let bit_count e =
          let bits = List.init n (fun i -> T_bv.mk_bvzext ~size:(sz 1) (n - 1) (T_bv.mk_bvextract ~size i i e)) in
          List.fold_left (T_bv.mk_bvadd ~size) (List.hd bits) (List.tl bits)
        in
        (* every bit below the highest set bit (lshr), or above the lowest
           (shl), set too *)
        let smear shift e k =
          let rec go step e = if step >= n then k e else named (T_bv.mk_bvor ~size e (shift ~size e (bv_num n (Z.of_int step)))) (go (2 * step)) in
          go 1 e
        in
        let finish v = continue (bind st env instr v) in
        if has "llvm.ctpop." then finish (bit_count a)
        else if has "llvm.bswap." then finish (byte_swap st n a)
        else
          (* with the flag true, a zero argument gives poison, which stops
             the path *)
          let zero_is_poison = Llvm.int64_of_const (Llvm.operand instr 1) <> Some 0L in
          let g = if zero_is_poison then Formula.mk_neg (bv_eq a (bv_num n Z.zero)) else fmla_true in
          guarded st g
            (smear (fun ~size e k -> if has "llvm.ctlz." then T_bv.mk_bvlshr ~size e k else T_bv.mk_bvshl ~size e k) a (fun s ->
                 finish (T_bv.mk_bvsub ~size (bv_num n (Z.of_int n)) (bit_count s)))))
  else
    let overflow =
      List.find_opt (fun op -> has ("llvm." ^ op ^ ".with.overflow.")) [ "sadd"; "uadd"; "ssub"; "usub"; "smul"; "umul" ]
    in
    match overflow with
    | None -> unknown at "the intrinsic %s" name
    | Some op ->
        let signed = op.[0] = 's' in
        let kind = String.sub op 1 3 in
        let x = Llvm.operand instr 0 and y = Llvm.operand instr 1 in
        let n = width x in
        operands st env at [ x; y ] @@ (function
        | [ a; b ] ->
            let finish value flag =
              Hashtbl.replace st.aggs (number st instr) [ value; bool_of_fmla flag ];
              continue env
            in
            (match st.mode with
            | Bv ->
                let size = sz n in
                let value, no_overflow =
                  match kind with
                  | "add" -> (T_bv.mk_bvadd ~size a b, (if signed then bv_no_signed_overflow else bv_no_unsigned_overflow) n ~sub:false a b)
                  | "sub" -> (T_bv.mk_bvsub ~size a b, (if signed then bv_no_signed_overflow else bv_no_unsigned_overflow) n ~sub:true a b)
                  | _ -> (T_bv.mk_bvmul ~size a b, (if signed then bv_no_signed_mul_overflow else bv_no_unsigned_mul_overflow) n a b)
                in
                finish value (Formula.mk_neg no_overflow)
            | Int ->
                let conv = if signed then to_s else to_u in
                conv st ~range:(range_of ~wrap:(wraps st) [] x) n a @@ fun a' ->
                conv st ~range:(range_of ~wrap:(wraps st) [] y) n b @@ fun b' ->
                let r =
                  match kind with
                  | "add" -> T_int.mk_add a' b'
                  | "sub" -> T_int.mk_sub a' b'
                  | _ -> T_int.mk_mul a' b'
                in
                let lo, hi = if signed then (Z.neg (pow2 (n - 1)), Z.pred (pow2 (n - 1))) else (Z.zero, Z.pred (pow2 n)) in
                (* the flag is whether the mathematical result leaves the
                   type's range, in both readings; only the modulo reading
                   reduces the value *)
                let flag = Formula.mk_or (atom (T_int.mk_lt r (int_num lo))) (atom (T_int.mk_gt r (int_num hi))) in
                let value = if reduces st then erem r (pow2 n) else r in
                finish value flag)
        | _ -> assert false)

(* A call to a defined function:
     W:   W_g_entry(ā, ḡ) ∧ ∀r, ḡ'. ( T¬_g_entry(ā, ḡ, r, ḡ') ∨ rest[r/%r, ḡ'/ḡ] )
     T¬:  ∀r, ḡ'. ( T¬_g_entry(ā, ḡ, r, ḡ') ∨ rest[r/%r, ḡ'/ḡ] )
   [S] is written as [W].  The point after the call is referred to once, so
   its body is the rest itself. *)
and defined_call st fns f role env at callee continue =
  let g = fn_of fns at callee in
  ignore f;
  let indexed = List.mapi (fun i p -> (i, p)) (Array.to_list (Ir.params callee)) in
  let int_params = List.filter (fun (_, p) -> is_tracked p) indexed in
  let struct_params = List.filter_map (fun (i, p) -> Option.map (fun sp -> (i, p, sp)) (Ir.struct_param callee i)) indexed in
  List.iter
    (fun (i, p) ->
      if not (is_tracked p || Ir.struct_param callee i <> None) then
        unknown at "a call with an argument that is neither an integer nor a struct passed by pointer")
    indexed;
  operands st env at (List.map (fun (i, _) -> Llvm.operand at i) int_params) @@ fun ts ->
  let vals = List.fold_left2 (fun m (_, p) t -> IntMap.add (number st p) t m) IntMap.empty int_params ts in
  (* a struct parameter starts from the components of the caller's object,
     which must be a whole object of the parameter's type; the
     [sret] slot also receives the callee's at the return *)
  let rec pass vals dest = function
    | [] -> after_call vals dest
    | (i, p, sp) :: rest ->
        address st env at (Llvm.operand at i) @@ fun (o, b) ->
        let ty = match sp with Ir.Byval t | Ir.Sret t -> t in
        if b.bc <> 0L || b.bterms <> [] || o.count <> Some 1 || not (o.elem == ty) then
          unknown at "a struct passed from a place other than a whole object of its type";
        let po = object_of st at p in
        let vals = List.fold_left2 (fun m pc oc -> IntMap.add (Option.get pc.key) (comp_get env oc) m) vals po.comps o.comps in
        pass vals (match sp with Ir.Sret _ -> Some o | Ir.Byval _ -> dest) rest
  and after_call vals dest =
    let callee_env = { vals; globs = env.globs } in
    let rs = List.map (fresh_var st) g.rets in
    let rts = List.map (fun (x, s) -> Term.mk_var x s) rs in
    let g' = List.map (fun (name, sort) -> (name, fresh_var st sort)) st.globals in
    let ge = List.fold_left (fun m (name, (x, s)) -> SMap.add name (Term.mk_var x s) m) SMap.empty g' in
    let summary = pred_app st g (Ret { re = rts; ge }) 0 callee_env in
    let env' =
      let env = { env with globs = ge } in
      let slot_n = match dest with Some o -> List.length o.comps | None -> 0 in
      let slot = List.filteri (fun i _ -> i < slot_n) rts and value = List.filteri (fun i _ -> i >= slot_n) rts in
      let env = match dest with Some o -> List.fold_left2 comp_set env o.comps slot | None -> env in
      match value with
      | [] -> env
      | [ t ] when is_tracked at -> bind st env at t
      | ts ->
          Hashtbl.replace st.aggs (number st at) ts;
          env
    in
    let after = forall (rs @ List.map snd g') (Formula.mk_or summary (continue env')) in
    match role with
    | Prop -> Formula.mk_and (pred_app st g Prop 0 callee_env) after
    | Ret _ -> after
  in
  pass vals None struct_params

(* -- Cut points -------------------------------------------------- *)

(* A depth-first search over the predicate reference graph, at the
   granularity of blocks: a block refers to its successors and, for each call
   to a defined function in it, to that function's entry.  A point after a
   call has one incoming reference, so it is never the target of a back edge
   and merging it into its block changes no cut point.  [P] is searched from
   [main]'s entry, [R] from the entry of every called function; the targets
   of back edges are the cut points. *)
let search fns rk roots =
  let colour = Hashtbl.create 64 in
  let rec dfs f i =
    Hashtbl.replace colour (f.fname, i) 1;
    Hashtbl.replace f.visited (rk, i) ();
    let callees =
      Llvm.fold_right_instrs
        (fun instr acc ->
          if Llvm.instr_opcode instr = Call then
            match Scope.classify_callee instr with
            | Defined callee -> fn_of fns instr callee :: acc
            | _ -> acc
          else acc)
        f.cfg.blocks.(i) []
    in
    let step g j =
      match Hashtbl.find_opt colour (g.fname, j) with
      | None -> dfs g j
      | Some 1 -> Hashtbl.replace g.cut (rk, j) ()
      | Some _ -> ()
    in
    List.iter (fun g -> step g 0) callees;
    List.iter (fun j -> step f j) f.cfg.succs.(i);
    Hashtbl.replace colour (f.fname, i) 2
  in
  List.iter (fun f -> if not (Hashtbl.mem colour (f.fname, 0)) then dfs f 0) roots

(* -- The problem -------------------------------------------------------- *)

(* The global objects the translated code reads or writes, each once. *)
let accessed_globals st fns =
  let seen = Hashtbl.create 16 and order = ref [] in
  let note p =
    match root_of p with
    | Some g when Llvm.classify_value g = GlobalVariable && not (Hashtbl.mem seen g) ->
        Hashtbl.add seen g ();
        order := g :: !order
    | _ -> ()
  in
  List.iter
    (fun llfn ->
      Llvm.iter_blocks
        (Llvm.iter_instrs (fun instr ->
             match Llvm.instr_opcode instr with
             | Load -> note (Llvm.operand instr 0)
             | Store -> note (Llvm.operand instr 1)
             | Call when Llvm.classify_value (Ir.callee instr) = Function ->
                 let name = Llvm.value_name (Ir.callee instr) in
                 if List.exists (fun prefix -> String.starts_with ~prefix name) [ "llvm.memset."; "llvm.memcpy."; "llvm.memmove." ]
                 then (
                   note (Llvm.operand instr 0);
                   if not (String.starts_with ~prefix:"llvm.memset." name) then note (Llvm.operand instr 1))
             | _ -> ()))
        llfn)
    fns;
  List.rev_map
    (fun g ->
      if Llvm.is_declaration g then stop_unknown "the global %s is declared but not defined" (Llvm.value_name g);
      object_of st g g)
    !order

(* A global's components at the start: its initial value, an array
   as [const_array(0)] with its nonzero leaves stored. *)
let global_initial st ~undef o =
  let at = o.ovalue in
  let constant w c =
    match Llvm.int64_of_const c with
    | _ when Llvm.classify_value c = UndefValue -> undef w
    | Some x when w = 1 -> if x = 0L then T_bool.mk_false () else T_bool.mk_true ()
    | Some x -> ( match st.mode with Int -> int_num (Z.of_int64 x) | Bv -> bv_num w (Z.of_int64 x))
    | None -> unknown at "the initial value of %s cannot be read" (Llvm.value_name o.ovalue)
  in
  let zero w = if w = 1 then T_bool.mk_false () else match st.mode with Int -> T_int.zero () | Bv -> bv_num w Z.zero in
  let leaves =
    match Option.map Memory.nonzero_leaves (Llvm.global_initializer o.ovalue) with
    | Some (Ok leaves) -> leaves
    | _ -> stop_unknown "the initial value of %s is not made of integers" (Llvm.value_name o.ovalue)
  in
  List.map
    (fun cv ->
      let w = cv.comp.width in
      let mine = List.filter (fun (p, _, _) -> p = cv.comp.path) leaves in
      if cv.carray then
        ( cv.cname,
          List.fold_left
            (fun a (_, idx, c) ->
              let i = linear st cv (List.map (fun j -> const_index (Z.of_int j)) (0 :: idx)) in
              T_array.mk_store (index_sort st) cv.leaf a (index_term st i) (constant w c))
            (T_array.mk_const_array (index_sort st) cv.leaf (zero w))
            mine )
      else (cv.cname, match mine with [ (_, _, c) ] -> constant w c | _ -> zero w))
    o.comps

(* -- The map for witnesses ----------------------------------------------- *)

(* What a correctness witness needs to turn the solution of a loop head's
   predicate into an invariant of the C program the IR was compiled from:
   where the loop is, and which C variable each parameter holds.

   A parameter holds a C variable [v] at a loop head when, on every path from
   the function's entry to the head, the last [llvm.dbg.value] for [v] names
   that parameter's SSA value with an empty expression: that call says [v]
   has that value from there on, until the next call for [v].  This is a
   forward must-analysis with an optimistic start; a call that names
   anything else (a constant, undef, a computed location) leaves [v] unknown
   from there on.  The calls at the head itself, after its phis and before
   its first other instruction, are where mem2reg describes the phis.

   A global holds a C variable when it is a scalar integer object of one
   component whose debug information names exactly one variable, described
   by an empty expression. *)

module VMap = Map.Make (String)

let is_dbg_call instr =
  Llvm.instr_opcode instr = Call
  && Llvm.classify_value (Ir.callee instr) = Function
  && String.starts_with ~prefix:"llvm.dbg." (Llvm.value_name (Ir.callee instr))

(* The effect of an instruction on what each C variable holds: a variable ->
   the id of the SSA value it holds, with its debug description. *)
let dbg_transfer st m instr =
  if is_dbg_call instr && Llvm.value_name (Ir.callee instr) = "llvm.dbg.value" then
    match Ir.dbg_variable instr with
    | None -> m
    | Some dv -> (
        let id =
          match Ir.dbg_value_operand instr with
          | Some v when dv.Ir.dv_plain && is_tracked v -> Hashtbl.find_opt st.index v
          | _ -> None
        in
        match id with Some id -> VMap.add dv.dv_name (id, dv) m | None -> VMap.remove dv.dv_name m)
  else m

(* What each C variable holds at the head of each block of [f], once the
   head's phis are described: [None] for a block no path reaches. *)
let dbg_heads st f =
  let cfg = f.cfg in
  let nb = Array.length cfg.blocks in
  let preds = Array.make nb [] in
  Array.iteri (fun i ss -> List.iter (fun j -> preds.(j) <- i :: preds.(j)) ss) cfg.succs;
  let meet a b = VMap.merge (fun _ x y -> match (x, y) with Some (i, d), Some (j, _) when i = j -> Some (i, d) | _ -> None) a b in
  let same a b = VMap.equal (fun (i, _) (j, _) -> i = j) a b in
  let out = Array.make nb None in
  let input i =
    if i = 0 then Some VMap.empty
    else
      List.fold_left
        (fun acc p -> match (out.(p), acc) with None, _ -> acc | Some m, None -> Some m | Some m, Some a -> Some (meet a m))
        None preds.(i)
  in
  let changed = ref true in
  while !changed do
    changed := false;
    for i = 0 to nb - 1 do
      match input i with
      | None -> ()
      | Some m ->
          let m' = Llvm.fold_left_instrs (dbg_transfer st) m cfg.blocks.(i) in
          if not (match out.(i) with Some o -> same o m' | None -> false) then (
            out.(i) <- Some m';
            changed := true)
    done
  done;
  let rec lead m = function
    | Llvm.Before instr when Llvm.instr_opcode instr = PHI || is_dbg_call instr ->
        lead (dbg_transfer st m instr) (Llvm.instr_succ instr)
    | _ -> m
  in
  Array.init nb (fun i -> Option.map (fun m -> lead m (Llvm.instr_begin cfg.blocks.(i))) (input i))

let cvar_of (dv : Ir.dbg_variable) ~width ~global =
  match dv.dv_kind with
  | (Ir.Signed | Ir.Unsigned) when dv.dv_bits = width && dv.dv_plain ->
      Some
        {
          LLVMWitness.Cmap.name = dv.dv_name;
          ctype = { LLVMWitness.Cmap.signed = dv.dv_kind = Ir.Signed; width };
          global;
        }
  | _ -> None

(* The C globals: a global component's name in the problem -> the C variable. *)
let witness_globals global_objects =
  List.filter_map
    (fun o ->
      match o.comps with
      | [ cv ] when (not cv.carray) && o.count = Some 1 && is_int_type o.elem ->
          Option.bind (Ir.global_dbg_variable o.ovalue) (fun dv ->
              Option.map (fun v -> (cv.cname, v)) (cvar_of dv ~width:(Llvm.integer_bitwidth o.elem) ~global:true))
      | _ -> None)
    global_objects

(* The map of every cut point of the property's predicates. *)
let witness_map st order global_objects =
  let globals = witness_globals global_objects in
  let points =
    List.concat_map
      (fun f ->
        let heads = lazy (dbg_heads st f) in
        List.filter_map
          (fun i ->
            if not (Hashtbl.mem f.cut (P, i)) then None
            else
              let cfg = f.cfg in
              let loc =
                List.find_map
                  (fun j ->
                    if List.mem i cfg.succs.(j) then Option.bind (Llvm.block_terminator cfg.blocks.(j)) Ir.loop_start
                    else None)
                  (List.init (Array.length cfg.blocks) Fun.id)
              in
              let locals =
                match (Lazy.force heads).(i) with
                | None -> []
                | Some m ->
                    (* a value two C variables hold is left out: which of
                       them the input's loop can name is not known here *)
                    let holders id = VMap.fold (fun _ (j, _) n -> if j = id then n + 1 else n) m 0 in
                    VMap.fold
                      (fun _ (id, dv) acc ->
                        let x = var_name id in
                        if (not (IntSet.mem id cfg.live.(i))) || holders id > 1 then acc
                        else
                          let width = Llvm.integer_bitwidth (Llvm.type_of (Hashtbl.find st.values id)) in
                          match cvar_of dv ~width ~global:false with Some v -> (x, v) :: acc | None -> acc)
                      m []
                    |> List.rev
              in
              Some
                {
                  LLVMWitness.Cmap.pred = (match pred_name st f P i with Ident.Pvar n -> n);
                  func = Llvm.value_name f.llfn;
                  loc;
                  params = locals @ globals;
                })
          (List.init (Array.length f.cfg.blocks) Fun.id))
      order
  in
  { LLVMWitness.Cmap.mode = (match st.mode with Int -> LLVMWitness.Cmap.Int | Bv -> LLVMWitness.Cmap.Bv); points }

let sanitize name = String.map (fun c -> match c with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> c | _ -> '_') name

let translate ~mode ~property ~(config : Config.t) llmodule =
  let main = Scope.main_function llmodule in
  let st =
    {
      mode;
      property;
      config;
      index = Hashtbl.create 64;
      values = Hashtbl.create 64;
      fresh = 0;
      globals = [];
      layout = Llvm_target.DataLayout.of_string (Llvm.data_layout llmodule);
      objects = Hashtbl.create 16;
      comp_ids = Hashtbl.create 16;
      aggs = Hashtbl.create 8;
      loops = [];
      loop_kind = Predicate.Nu;
    }
  in
  let global_objects = accessed_globals st (Scope.reachable llmodule) in
  st.globals <- List.concat_map (fun o -> List.map (fun cv -> (cv.cname, cv.csort)) o.comps) global_objects;
  let fns = Hashtbl.create 16 in
  let used_names = Hashtbl.create 16 in
  let order =
    List.map
      (fun llfn ->
        let base = sanitize (Llvm.value_name llfn) in
        let fname = if Hashtbl.mem used_names base then Printf.sprintf "%s_%d" base (Hashtbl.length used_names) else base in
        Hashtbl.add used_names fname ();
        let name = Llvm.value_name llfn in
        let ret = Llvm.return_type (Ir.global_value_type llfn) in
        let value_sorts =
          match Llvm.classify_type ret with
          | Void -> []
          | Integer -> [ sort_of_width st (Llvm.integer_bitwidth ret) ]
          | Struct -> leaf_sorts st ret
          | _ -> stop_unknown "%s: it returns a value that is neither an integer nor a struct" name
        in
        let struct_params = List.filter (fun p -> Ir.struct_param_of_arg p <> None) (Array.to_list (Ir.params llfn)) in
        Array.iter
          (fun p ->
            if not (is_int_type (Llvm.type_of p)) && llfn != main && Ir.struct_param_of_arg p = None then
              stop_unknown "%s: a parameter that is neither an integer nor a struct passed by pointer" name;
            if is_tracked p then ignore (number st p))
          (Ir.params llfn);
        let sret = List.find_opt (fun p -> match Ir.struct_param_of_arg p with Some (Sret _) -> true | _ -> false) struct_params in
        let entry_at = match Llvm.instr_begin (Llvm.entry_block llfn) with Llvm.Before i -> i | Llvm.At_end _ -> stop_unknown "%s: an empty function" name in
        let slot_sorts = match sret with Some p -> List.map (fun cv -> cv.csort) (object_of st entry_at p).comps | None -> [] in
        let cfg = build_cfg st llfn in
        let params =
          (Array.to_list (Ir.params llfn) |> List.filter is_tracked |> List.map (number st))
          @ List.concat_map (fun p -> comp_ids (object_of st entry_at p)) struct_params
          |> IntSet.of_list
        in
        if Array.length cfg.blocks > 0 && not (IntSet.subset cfg.live.(0) params) then
          stop_unknown "%s: a value is used before it is defined" name;
        let f = { llfn; fname; cfg; rets = slot_sorts @ value_sorts; sret; cut = Hashtbl.create 8; visited = Hashtbl.create 32 } in
        Hashtbl.add fns llfn f;
        f)
      (Scope.reachable llmodule)
  in
  let main_fn = Hashtbl.find fns main in
  (* argc, when main reads it; argv is refused by Scope *)
  let argc =
    match Ir.params main with
    | [||] -> None
    | ps -> if is_tracked ps.(0) && IntSet.mem (number st ps.(0)) main_fn.cfg.live.(0) then Some ps.(0) else None
  in
  let argc_ids = match argc with Some p -> IntSet.singleton (number st p) | None -> IntSet.empty in
  if not (IntSet.subset main_fn.cfg.live.(0) argc_ids) then stop_unknown "main: a value is used before it is defined";
  search fns P [ main_fn ];
  let called =
    List.filter
      (fun f ->
        List.exists
          (fun caller ->
            Scope.fold_calls
              (fun acc call ->
                acc
                || (Hashtbl.mem caller.visited (P, Hashtbl.find caller.cfg.block_index (Llvm.instr_parent call))
                   && match Scope.classify_callee call with Defined c -> c == f.llfn | _ -> false))
              false caller.llfn)
          order)
      order
  in
  search fns R called;
  let kind rk f i =
    if Hashtbl.mem f.cut (rk, i) then
      match (rk, property) with
      | P, Termination -> Predicate.Mu
      | P, Unreach_call | R, _ -> Predicate.Nu
    else Predicate.MuOrNu
  in
  let var_env st f i extra_globs =
    {
      vals =
        List.fold_left
          (fun m x -> IntMap.add x (let v, sort = id_var st x in Term.mk_var v sort) m)
          IntMap.empty (IntSet.elements f.cfg.live.(i));
      globs =
        List.fold_left
          (fun m (name, sort) -> SMap.add name (Term.mk_var (Ident.Tvar (extra_globs name)) sort) m)
          SMap.empty st.globals;
    }
  in
  let make rk f i =
    let args = pred_args st f rk i in
    let env = var_env st f i Fun.id in
    let role =
      match rk with
      | P -> Prop
      | R ->
          Ret
            {
              re = List.mapi (fun i s -> Term.mk_var (Ident.Tvar (re_var i)) s) f.rets;
              ge = (var_env st f i ge_var).globs;
            }
    in
    st.loop_kind <- (match (rk, property) with P, Termination -> Predicate.Mu | _ -> Predicate.Nu);
    MuCLP.Pred.make (kind rk f i) (pred_name st f rk i) args (drop_implied_guards_in st (block_body st fns f role env i))
  in
  (* The cut points come first and the [MuOrNu] predicates after them.  A lower
     index is an outer equation, and MuVal reads [MuOrNu] as a greatest
     fixpoint, also in the dual problem it solves for a refutation (the dual
     keeps [MuOrNu]).  The [MuOrNu] predicates form no cycle among themselves
     (every cycle passes a cut point), so as the innermost equations each has
     one solution given the cut points, and reading it as greatest or least
     changes nothing.  Placed before a cut point of its cycle, a join inside
     a loop read as greatest would make a loop that never ends terminate. *)
  let points =
    List.concat_map
      (fun f -> List.concat_map (fun rk -> List.init (Array.length f.cfg.blocks) (fun i -> (rk, f, i))) [ P; R ])
      order
    |> List.filter (fun (rk, f, i) -> kept st f rk i)
  in
  let is_cut (rk, f, i) = Hashtbl.mem f.cut (rk, i) in
  let preds =
    let cut = List.map (fun (rk, f, i) -> make rk f i) (List.filter is_cut points) in
    let fix = List.map (fun (rk, f, i) -> make rk f i) (List.filter (fun p -> not (is_cut p)) points) in
    (* the loop form's predicates are cut points of their own *)
    cut @ List.rev st.loops @ fix
  in
  let query =
    (* padding in a global's initial value is arbitrary, as is
       argc, which C requires to be nonnegative *)
    let undefs = ref [] in
    let undef w =
      let x, sort = fresh_var st (sort_of_width st w) in
      undefs := (x, sort) :: !undefs;
      Term.mk_var x sort
    in
    let globs =
      List.fold_left (fun m (name, t) -> SMap.add name t m) SMap.empty (List.concat_map (global_initial st ~undef) global_objects)
    in
    let vals, argc_vars, argc_fact =
      match argc with
      | None -> (IntMap.empty, [], fmla_true)
      | Some p ->
          let n = width p in
          let x, sort = fresh_var st (sort_of_width st n) in
          let t = Term.mk_var x sort in
          let nonneg =
            match mode with
            | Int -> Formula.mk_and (atom (T_int.mk_geq t (T_int.zero ()))) (atom (T_int.mk_lt t (int_num (pow2 (n - 1)))))
            | Bv -> Formula.mk_neg (bv_negative n t)
          in
          (IntMap.singleton (number st p) t, [ (x, sort) ], nonneg)
    in
    forall_vars (argc_vars @ !undefs) (Formula.mk_imply argc_fact (pred_app st main_fn Prop 0 { vals; globs }))
  in
  let map = if config.witness then Some (witness_map st order global_objects) else None in
  (MuCLP.Problem.make preds query, map)
