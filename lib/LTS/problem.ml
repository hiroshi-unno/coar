(* Labelled transition systems (control-flow automata whose edges carry guarded
   commands: assumptions, assignments, sequencing and nondeterministic choice),
   the common form of the T2 and integer-transition-system frontends, with the
   property to verify (safety, termination, their negations, mu-calculus or
   relational).  Beside the syntax and the type inference of its variables, this
   provides a weakest-precondition transformer over commands ([wp]), the
   bounding of sized nondeterministic values to their machine range
   ([bind_nondet]), and [analyze], which simplifies the automaton by contracting
   edges and pass-through locations and returns its live variables and a set of
   cut points covering every cycle.  Nondeterministic values are fresh variables
   whose names begin with [#nondet], and a sized one carries its width and
   signedness in its name, which [range_of_nondet] reads back. *)
open Core
open Graph
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld

let bv_mode = ref false
let nondet_count = ref 0
let nondet_prefix = "#nondet"

let mk_nondet = function
  | None ->
      incr nondet_count;
      Ident.Tvar (nondet_prefix ^ string_of_int !nondet_count)
  | Some (bits, signed) ->
      incr nondet_count;
      Ident.Tvar
        (nondet_prefix
        ^ string_of_int !nondet_count
        ^ "_" ^ string_of_int bits
        ^ if signed then "_s" else "_u")

(* an input the grammar accepts but that states no transition system *)
exception Malformed of string

type lts =
  string option (* start *)
  * sort_env_list (* types *)
  * string option (* error *)
  * string option (* cutpoint *)
  * transition list
  * string list option
(* the Buechi locations of a [BUCHI] line, if one is given: the acceptance
   condition of the Buechi modes, which visit them infinitely often; every
   other mode ignores it, since it states a property, not the program *)

and transition = string * command * string

and command =
  | Skip
  | Assume of LogicOld.Formula.t
  | Subst of (Ident.tvar * LogicOld.Sort.t) * LogicOld.Term.t
  | Seq of command * command
  | Choice of command * command

(* [Buchi]: every run visits the [BUCHI] locations infinitely often (UB-PA of
   Chatterjee et al., FM 2024).  [ExBuchi]: some run does (their EB-PA).  A
   run is infinite; a state without a successor ends no run. *)
type mode = Safe | NonSafe | Term | NonTerm | MuCal | Rel | Buchi | ExBuchi
type t = lts * mode

let seq = function
  | [] -> Skip
  | c :: cs -> List.fold_left ~init:c cs ~f:(fun c1 c2 -> Seq (c1, c2))

let seq = List.filter ~f:(Stdlib.( <> ) Skip) >> seq

let choice = function
  | [] -> assert false
  | c :: cs -> List.fold_left ~init:c cs ~f:(fun c1 c2 -> Choice (c1, c2))

let subst = List.map2_exn ~f:(fun arg term -> Subst (arg, term))

let commands_of_formula ~print args rel =
  let rel =
    let rel =
      Typeinf.typeinf_formula ~print ~default:(Some T_int.SInt (*ToDo*)) rel
    in
    if Formula.is_quantifier_free rel then rel
    else Z3Smt.Z3interface.qelim ~id:None ~fenv:(LogicOld.get_fenv ()) rel
  in
  let args_set = Set.Poly.of_list @@ List.map ~f:fst args in
  let phis_cond, phis_rest =
    Set.partition_tf (Formula.conjuncts_of rel) ~f:(fun phi ->
        Set.are_disjoint (Formula.fvs_of phi) args_set)
  in
  let sub, phis_rest, phis_cond =
    let rec loop (sub, phis_rest, phis_cond) =
      let sub', phis_rest' =
        Set.partition_map phis_rest ~f:(fun phi ->
            try
              let t1, t2, _ = Formula.let_eq phi in
              (*ToDo: the following code is ad hoc*)
              if
                Term.is_var t1
                && Set.mem args_set (Term.tvar_of t1)
                && Set.are_disjoint (Term.fvs_of t2) args_set
              then First (fst @@ Term.let_var t1, t2)
              else if
                Term.is_var t2
                && Set.mem args_set (Term.tvar_of t2)
                && Set.are_disjoint (Term.fvs_of t1) args_set
              then First (fst @@ Term.let_var t2, t1)
              else Second phi
            with exn_ when not (Common.Timer.is_async exn_) -> Second phi)
      in
      if Set.is_empty sub' then (sub, phis_rest, phis_cond)
      else
        let sub', phiss_rest =
          List.unzip
          @@ List.map ~f:(fun res ->
              let arg = fst @@ List.hd_exn res in
              match List.map ~f:snd res with
              | [] -> assert false
              | t :: ts ->
                  ( (arg, t),
                    Set.Poly.of_list
                    @@ List.map ts
                         ~f:(Formula.eq (Tuple2.uncurry Term.mk_var arg)) ))
          @@ List.classify (fun x y -> Stdlib.(fst x = fst y))
          @@ Set.to_list sub'
        in
        let subst =
          Map.Poly.of_alist_exn @@ List.map sub' ~f:(fun ((x, _), t) -> (x, t))
        in
        loop
          ( Set.union sub @@ Set.Poly.of_list sub',
            Set.Poly.map phis_rest' ~f:(Formula.subst subst),
            Set.union phis_cond
            @@ Set.Poly.map ~f:(Formula.subst subst)
            @@ Set.Poly.union_list phiss_rest )
    in
    loop (Set.Poly.empty, phis_rest, phis_cond)
  in
  let sub = Map.of_set_exn sub in
  let phi_rest = Formula.and_of @@ Set.to_list phis_rest in
  Assume (Formula.and_of @@ Set.to_list phis_cond)
  :: List.map args ~f:(fun arg ->
      if Map.Poly.mem sub arg then Subst (arg, Map.Poly.find_exn sub arg)
      else Subst (arg, Term.mk_var (mk_nondet None (*ToDo*)) (snd arg)))
  @ [ Assume phi_rest ]

let rec term_sort_env_of_command = function
  | Skip -> Set.Poly.empty
  | Assume atm -> Formula.term_sort_env_of atm
  | Subst ((x, s), t) -> Set.add (Term.term_sort_env_of t) (x, s)
  | Seq (c1, c2) | Choice (c1, c2) ->
      Set.union (term_sort_env_of_command c1) (term_sort_env_of_command c2)

let term_sort_env_of_transition (_, c, _) = term_sort_env_of_command c

let term_sort_env_of (_, _, _, _, trs, _) =
  Set.Poly.union_list @@ List.map ~f:term_sort_env_of_transition trs

let rec tvs_of_command = function
  | Skip -> Set.Poly.empty
  | Assume atm -> Formula.tvs_of atm
  | Subst ((x, _s), t) -> Set.add (Term.tvs_of t) x
  | Seq (c1, c2) | Choice (c1, c2) ->
      Set.union (tvs_of_command c1) (tvs_of_command c2)

let tvs_of_transition (_, c, _) = tvs_of_command c

let tvs_of (_, _, _, _, trs, _) =
  Set.Poly.union_list @@ List.map ~f:tvs_of_transition trs

(* whether a command divides: [/] and its signed and unsigned forms, read as
   the numeric division the parser builds before typing *)
let rec divides = function
  | Skip -> false
  | Assume phi -> Set.exists (Formula.funsyms_of phi) ~f:is_division
  | Subst (_, t) -> Set.exists (Term.funsyms_of t) ~f:is_division
  | Seq (c1, c2) | Choice (c1, c2) -> divides c1 || divides c2

and is_division = function
  | T_num.NDiv _ | T_int.Div _ | T_bv.BVDiv _ -> true
  | _ -> false

(* How [/] is read in a file with a [BUCHI] line, the dialect of LTL-VerP
   (Chatterjee et al., FM 2024), whose reader divides exactly by a constant (a
   rational coefficient), where T2's [/] truncates.  A file without a [BUCHI]
   line is T2's and is always read with truncation.
   - [Exact]: the rational reading, over integer variables ([exact_division]).
   - [Truncate]: T2's integer division, truncating towards zero.
   - [Refuse]: such a file is refused when it divides. *)
type division = Exact | Truncate | Refuse [@@deriving yojson]

(* Set by the reader for the file it reads, as [bv_mode] is. *)
let division = ref Exact

(* [Inexact why]: a division the exact reading cannot state over integer
   variables, which the reader reports as a malformed input. *)
exception Inexact of string

(* The integer value of a closed, division-free constant term built from
   numerals by [-], [+], [*]; [None] for anything else. *)
let rec const_of = function
  | Term.FunApp (T_num.Value (n, _), [], _) -> (
      (* a rational numeral is not an integer constant *)
      try Some (Z.of_string n)
      with exn_ when not (Common.Timer.is_async exn_) -> None)
  | Term.FunApp (T_num.NNeg _, [ a ], _) -> Option.map (const_of a) ~f:Z.neg
  | Term.FunApp (T_num.NAdd _, [ a; b ], _) ->
      Option.map2 (const_of a) (const_of b) ~f:Z.add
  | Term.FunApp (T_num.NSub _, [ a; b ], _) ->
      Option.map2 (const_of a) (const_of b) ~f:Z.sub
  | Term.FunApp (T_num.NMul _, [ a; b ], _) ->
      Option.map2 (const_of a) (const_of b) ~f:Z.mul
  | _ -> None

(* [den t]: a positive integer d such that d * t, with [/] read as exact
   division, is a polynomial with integer coefficients in the variables of
   [t] (for d = 1, [t] has no division).  Raises [Inexact] for a division by
   anything but a nonzero integer constant, and for a division under an
   operator other than [-], [+], [*], whose exact value a scaling cannot
   reach. *)
let rec den t =
  match t with
  | Term.FunApp (T_num.NNeg _, [ a ], _) -> den a
  | Term.FunApp ((T_num.NAdd _ | T_num.NSub _), [ a; b ], _) ->
      Z.lcm (den a) (den b)
  | Term.FunApp (T_num.NMul _, [ a; b ], _) -> Z.mul (den a) (den b)
  | Term.FunApp (T_num.NDiv _, [ a; c ], _) -> (
      match const_of c with
      | Some c when not (Z.equal c Z.zero) -> Z.mul (den a) (Z.abs c)
      | _ ->
          raise
            (Inexact
               "a division whose divisor is not a nonzero integer constant"))
  | t ->
      if Set.exists (Term.funsyms_of t) ~f:is_division then
        raise (Inexact "a division under an operator other than -, +, *")
      else Z.one

let mul_const k t =
  if Z.equal k Z.one then t
  else if Z.equal k Z.minus_one then T_num.mk_nneg t
  else T_num.mk_nmul (T_num.mk_value (Z.to_string k)) t

(* [scale k t] assumes [den t] divides [k] (either sign) and returns a term
   without division equal to k * t for every integer (indeed rational)
   valuation, [/] in [t] read as exact division: by induction on [t], since
   den(a + b) and den(a - b) divide k, den(a * b) = den a * den b, and
   den(a / c) = den a * |c|. *)
let rec scale k t =
  if Z.equal (den t) Z.one then mul_const k t
  else
    match t with
    | Term.FunApp (T_num.NNeg _, [ a ], _) -> T_num.mk_nneg (scale k a)
    | Term.FunApp (T_num.NAdd _, [ a; b ], _) ->
        T_num.mk_nadd (scale k a) (scale k b)
    | Term.FunApp (T_num.NSub _, [ a; b ], _) ->
        T_num.mk_nsub (scale k a) (scale k b)
    | Term.FunApp (T_num.NMul _, [ a; b ], _) ->
        let da = den a in
        T_num.mk_nmul (scale da a) (scale (Z.divexact k da) b)
    | Term.FunApp (T_num.NDiv _, [ a; c ], _) ->
        scale (Z.divexact k (Option.value_exn (const_of c))) a
    | _ -> assert false (* [den] is 1 on every other shape, or raised *)

(* A comparison or an equation with a division, multiplied on both sides by
   the positive lcm of the sides' denominators, which preserves its truth
   value over the rationals, hence over integer valuations.  Any other atom
   must not divide. *)
let exact_atom atom =
  match atom with
  | Atom.App
      ( (Predicate.Psym
           ( T_bool.Eq | T_bool.Neq | T_num.NGeq _ | T_num.NLeq _
           | T_num.NGt _ | T_num.NLt _ ) as p),
        [ t1; t2 ],
        info ) ->
      let l = Z.lcm (den t1) (den t2) in
      if Z.equal l Z.one then atom
      else Atom.mk_app ~info p [ scale l t1; scale l t2 ]
  | atom ->
      if Set.exists (Formula.funsyms_of (Formula.mk_atom atom)) ~f:is_division
      then raise (Inexact "a division in an atom that is not a comparison")
      else atom

(* [exact_division ~tmp c]: [c] with [/] read as exact division by a
   constant over integer variables, stated without division.
   - In a guard, every comparison is scaled by [exact_atom].
   - An assignment [x := t] whose [den t] is d > 1 becomes
     [tmp := nondet; assume(d * tmp = d * t); x := tmp]: its successors are
     exactly those where [x] is the integer equal to [t], and there is none
     when [t] is not an integer.  The intermediate [tmp] is needed because
     the weakest precondition binds a nondet variable at the command it
     occurs in, so a nondet in the guard and the same nondet in the
     assignment would be bound separately.
   Assumes [tmp] is an integer variable that no command of the input
   mentions; then every read of [tmp] follows a write of it in the same
   sequence, so one such variable serves every rewritten assignment and is
   dead at every location.  Preserves: the integer successor states of every
   state, [tmp] projected away.  Raises [Inexact] (see [den]). *)
let rec exact_division ~tmp = function
  | Skip -> Skip
  | Assume phi -> Assume (Formula.map_atom phi ~f:(exact_atom >> Formula.mk_atom))
  | Subst ((x, s), t) as c ->
      let d = den t in
      if Z.equal d Z.one then c
      else
        let v = (tmp, T_int.SInt) in
        let nd = Term.mk_var (mk_nondet None) T_int.SInt in
        Seq
          ( Seq
              ( Subst (v, nd),
                Assume
                  (Formula.eq
                     (mul_const d (Term.mk_var (fst v) T_int.SInt))
                     (scale d t)) ),
            Subst ((x, s), Term.mk_var (fst v) T_int.SInt) )
  | Seq (c1, c2) -> Seq (exact_division ~tmp c1, exact_division ~tmp c2)
  | Choice (c1, c2) ->
      Choice (exact_division ~tmp c1, exact_division ~tmp c2)

let print_log = false

let rec cgen_command senv = function
  | Skip -> (senv, Set.Poly.empty)
  | Assume atm ->
      Typeinf.cgen_formula
        ~print:(fun s -> if print_log then print_endline (force s) else ())
        senv atm
  | Subst ((x, s), t) -> (
      let senv, s', constrs =
        Typeinf.cgen_term
          ~print:(fun s -> if print_log then print_endline (force s) else ())
          senv t
      in
      ( senv,
        match Map.Poly.find senv x with
        | None -> Set.add constrs (Typeinf.CEq (s, s'))
        | Some s'' ->
            Set.add
              (Set.add constrs (Typeinf.CEq (s'', s)))
              (Typeinf.CEq (s'', s')) ))
  | Seq (c1, c2) | Choice (c1, c2) ->
      let senv, cs1 = cgen_command senv c1 in
      let senv, cs2 = cgen_command senv c2 in
      (senv, Set.union cs1 cs2)

let cgen_transition senv (_, c, _) = cgen_command senv c

let rec subst_sorts_command senv map = function
  | Skip -> Skip
  | Assume atm -> Assume (Formula.subst_sorts map atm)
  | Subst ((x, s), t) ->
      Subst
        ( ( x,
            match Map.find senv x with
            | Some s -> s
            | None -> Term.subst_sorts_sort map s ),
          Term.subst_sorts map t )
  | Seq (c1, c2) ->
      Seq (subst_sorts_command senv map c1, subst_sorts_command senv map c2)
  | Choice (c1, c2) ->
      Choice (subst_sorts_command senv map c1, subst_sorts_command senv map c2)

let subst_sorts_trans senv map (f, c, t) = (f, subst_sorts_command senv map c, t)

let rec str_of_command = function
  | Skip -> "skip;\n"
  | Assume atom ->
      sprintf "assume(%s);\n" (LogicOld.Formula.str_of ~priority:20 atom)
  | Subst ((x, sort), t) ->
      if false then
        sprintf "%s := %s;\n" (Ident.name_of_tvar x) (LogicOld.Term.str_of t)
      else
        sprintf "%s : %s := %s;\n" (Ident.name_of_tvar x)
          (Term.str_of_sort sort) (LogicOld.Term.str_of t)
  | Seq (c1, c2) -> str_of_command c1 ^ str_of_command c2
  | Choice (c1, c2) ->
      "(\n" ^ str_of_command c1 ^ ") || (\n" ^ str_of_command c2 ^ ");\n"

let str_of_transition (from, c, to_) =
  sprintf "FROM: %s;\n%sTO: %s;\n\n" from (str_of_command c) to_

let str_of_lts (s, _ (*ToDo*), e, c, trans, b) =
  (match s with None -> "" | Some s -> sprintf "START: %s;\n" s)
  ^ (match e with None -> "" | Some e -> sprintf "ERROR: %s;\n" e)
  ^ (match b with
    | None -> ""
    | Some b -> sprintf "BUCHI: {%s};\n" (String.concat ~sep:", " b))
  ^ (match c with None -> "" | Some c -> sprintf "CUTPOINT: %s;\n" c)
  ^ String.concat_map_list ~f:str_of_transition trans

let typeinf ?(bv_mode = false) (s, types, e, c, trans, b) =
  let types =
    if bv_mode then types
    else
      List.map types ~f:(function
        | _, T_bv.SBV _ -> failwith "not supported"
        | bind -> bind (*ToDo*))
  in
  let senv =
    Map.of_set_exn
    @@ Set.Poly.map
         (tvs_of (s, types, e, c, trans, b))
         ~f:(fun x ->
           match List.Assoc.find ~equal:Stdlib.( = ) types x with
           | None -> (x, Sort.mk_fresh_svar ())
           | Some s -> (x, s))
  in
  let _, constrs =
    List.fold trans ~init:(senv, Set.Poly.empty) ~f:(fun (senv, cs) tr ->
        let senv, cs' = cgen_transition senv tr in
        (senv, Set.union cs cs'))
  in
  let nums, map =
    (* The constraints are generated from the file alone, so when they have no
       solution the file is ill-sorted -- an array stored once with arrays as
       its elements and once with integers, as C-to-T2 converters write some
       two-dimensional C arrays -- and that is a refusal of the input, not a
       crash.  [Typeinf] reports it as a [Failure] (a unification clash, an
       occurs check, or a numeric sort variable bound to an array); no other
       exception is caught, so a timeout passes through. *)
    try
      Typeinf.solve constrs ~print:(fun s ->
          if print_log then print_endline (force s) else ())
    with Failure msg ->
      raise
        (Malformed
           ("the variables of this transition system cannot be given \
             consistent sorts: " ^ msg))
  in
  let default_size =
    Some !T_bv.default_bits
    (* --bv-default *)
  in
  let map =
    Typeinf.elim_nums ~to_sus:false
      ~default:(Some (if bv_mode then T_bv.SBV default_size else T_int.SInt))
      nums map
  in
  (*let map =
    Map.Poly.map map ~f:(function
      | T_bv.SBV None -> T_bv.SBV default_size
      | s (*ToDo*) -> s)
  in*)
  let svs = Set.diff (Typeinf.svs_of_constrs constrs) (Map.Poly.key_set map) in
  if false then
    print_endline
    @@ sprintf "unsolved vars: %s"
         (String.concat_map_set ~sep:", " ~f:Ident.name_of_svar svs);
  let map' =
    Map.of_set_exn
    @@ Set.Poly.map svs ~f:(fun svar ->
        (*print_endline @@ sprintf "adding svar %s" (Ident.name_of_svar svar);*)
        (svar, if bv_mode then T_bv.SBV default_size else T_int.SInt))
  in
  let map =
    Map.force_merge (Map.Poly.map map ~f:(Term.subst_sorts_sort map')) map'
  in
  let types =
    (*List.map ~f:(fun (x, s) -> (x, Term.subst_sorts_sort map s))*) types
  in
  let senv = Map.Poly.map senv ~f:(Term.subst_sorts_sort map) in
  if false then
    print_endline
    @@ sprintf "senv: %s"
         (String.concat_map_list ~sep:", "
            ~f:(fun (x, s) ->
              sprintf "%s: %s" (Ident.name_of_tvar x) (Term.str_of_sort s))
            (Map.to_alist senv));
  let trans = List.map trans ~f:(subst_sorts_trans senv map) in
  (s, types, e, c, trans, b)

let rec is_effect_free = function
  | Skip | Assume _ -> true
  | Subst ((_, _), t) ->
      Set.for_all (Term.tvs_of t) ~f:(fun x ->
          not @@ String.is_prefix (Ident.name_of_tvar x) ~prefix:nondet_prefix)
  | Seq (c1, c2) | Choice (c1, c2) -> is_effect_free c1 && is_effect_free c2

let qelim_records = Hashtbl.PolyDeep.create ()
let clean () = Hashtbl.Poly.clear qelim_records

let qelim phi =
  match Hashtbl.Poly.find qelim_records phi with
  | Some rcd -> rcd
  | None ->
      let ret =
        Z3Smt.Z3interface.qelim ~id:None ~fenv:(LogicOld.get_fenv ()) phi
      in
      Hashtbl.Poly.set qelim_records ~key:phi ~data:ret;
      ret

(* the value range of a sized nondet variable [#nondetN_<bits>_<s|u>], if any *)
let range_of_nondet (x, s) =
  match (String.split ~on:'_' (Ident.name_of_tvar x), s) with
  | [ _; bits; signed ], T_int.SInt ->
      let bits = int_of_string bits in
      let is_signed = String.(signed = "s") in
      Some
        (Formula.and_of
        @@ Formula.mk_range (Term.mk_var x s) (min_num bits is_signed)
             (max_num bits is_signed))
  | [ _; bits; signed ], T_bv.SBV (Some width) ->
      (* BV mode: the variable is a [width]-bit vector.  A narrower nondet
         is extended to it (sign-extended if signed, zero-extended if not),
         so its values are exactly the C type's range, stated with signed
         bit-vector comparisons (the unsigned range [0, 2^bits - 1] lies
         below 2^(width-1), so the signed reading of it is the same set).  A
         nondet at least as wide as the variable, of either signedness, can
         leave every bit pattern of the variable, so it needs no constraint:
         the unsigned values [2^(width-1), 2^width) are the patterns with the
         sign bit set, which a signed comparison reads as negative and an
         unsigned one ([ult], ...) as large.  Requiring [x >=s 0] of an
         unsigned one dropped those states, and a path that only they reach
         was taken for unreachable. *)
      let bits = int_of_string bits in
      let is_signed = String.(signed = "s") in
      let size = Some width in
      let const n = T_bv.mk_bvnum ~size n in
      let v = Term.mk_var x s in
      let geq lo =
        Formula.mk_atom (T_bv.mk_bvgeq ~size ~signed:(Some true) v (const lo))
      in
      let leq hi =
        Formula.mk_atom (T_bv.mk_bvleq ~size ~signed:(Some true) v (const hi))
      in
      if bits < width then
        Some
          (Formula.mk_and
             (geq (min_num bits is_signed))
             (leq (max_num bits is_signed)))
      else None
  | _ (*ToDo*) -> None

let bind_nondet nondet_senv phi =
  let nondet_senv =
    let tvs = Formula.tvs_of phi in
    List.filter nondet_senv ~f:(fst >> Set.mem tvs)
  in
  let range = List.filter_map nondet_senv ~f:range_of_nondet in
  Formula.mk_forall_if_bounded nondet_senv
  @@
  if List.is_empty range then phi
  else Formula.mk_imply (Formula.and_of range) phi

(* Whether [wp] collects only the nondet variables of a weakest precondition
   (on) or all of its variables and then keeps the nondet ones (off).  The two
   give the same set; off, the whole environment is rebuilt by set unions at
   every step of a sequence, which is most of the conversion's time on a long
   transition system (47 s of a 50 s conversion on one 2.5 MB T2 input).  Off only for
   checking that equality ([COAR_WP_COLLECT_ALL] set). *)
let wp_collect_nondets_only =
  Atomic.make (Option.is_none (Sys.getenv "COAR_WP_COLLECT_ALL"))

let wp_skip_composite =
  Atomic.make (Option.is_none (Sys.getenv "COAR_WP_CHECK_COMPOSITE"))

(* Whether [wp] applies a run of consecutive substitutions of a sequence as one
   composed simultaneous substitution (on) or one substitution per command, each
   walking the whole precondition (off: [COAR_WP_SEQUENTIAL_SUBST] set, for
   checking that the two give the same precondition). *)
let wp_compose_substs =
  Atomic.make (Option.is_none (Sys.getenv "COAR_WP_SEQUENTIAL_SUBST"))

(* Whether [wp] of a choice keeps the continuation's precondition shared
   between the branches (on) or copies it into each branch (off).  It comes from
   the backend's configuration ([set_wp_share_choice], called before the
   conversion: MuVal's [wp_share_choice] and MuStrat's, both on by
   default, MuStrat's above a larger size); a backend that sets nothing (MuCyc, Mu2CHC, whose answers on shared
   conversions have not been measured) gets the copying form.  [COAR_WP_SHARE_CHOICE] overrides it, as
   a debugging override only: [0] forces it off, any other value on.  The size
   threshold below is [wp_share_choice_min_size].

   Off, [wp (c1 [] c2) phi] is [wp c1 phi /\ wp c2 phi] with the implications
   merged by right-hand side, so [phi] is copied once per branch, and once more
   with different substitutions where the branches assign differently
   ([if b then t := 1 else t := 0]): a sequence of n choices gives a
   precondition of size 2^n |phi| (T2 inputs with 88 choices in one transition
   never finished their conversion).

   On, when [phi] has more than the threshold's formula nodes, no free nondet
   variable and no nullary predicate application named after a Boolean
   variable the choice substitutes, the branches are computed against a placeholder atom K(y) for
   [phi] (y the free variables of [phi]), which only collects the arguments
   each path passes, and [phi] is put back once:
     /\_i forall w_i. (L_i => K(t_i))
       <=> forall w v. (\/_i (L_i /\ v = t_i|D)) => phi[y := t[D := v]]
   where i ranges over the implications with a K-atom right-hand side, w_i are
   the universally bound variables lifted from above it (renamed fresh), D the
   argument positions on which the t_i disagree and v fresh variables, one per
   position in D.  Each step is a logical equivalence: [wp] commutes with
   substituting a formula for a predicate variable that occurs only positively
   in the postcondition (it substitutes terms for variables, adds hypotheses and
   binds fresh nondet variables, none of which looks inside the predicate), a
   universal quantifier over a fresh variable moves out of an implication's
   conclusion and over a conjunction, and the one-point rule gives the
   equality form.  The conjuncts the L_i share are factored out of the
   disjunction (distributivity).  So the precondition is equivalent to the
   copying one, with [phi] once per choice, and every other case of [wp] maps
   equivalent postconditions to equivalent preconditions; the converted problem
   differs in form only, never in meaning.  At or below the threshold, the old
   merge runs unchanged. *)
let wp_share_choice = Atomic.make false

let wp_share_choice_override =
  Option.map (Sys.getenv "COAR_WP_SHARE_CHOICE") ~f:(fun v ->
      not (String.equal (String.strip v) "0"))

let set_wp_share_choice on =
  Atomic.set wp_share_choice (Option.value wp_share_choice_override ~default:on)

let () = set_wp_share_choice false

(* The threshold of [wp_share_choice]: a choice is shared only when its
   postcondition has more than this many formula nodes.  Read only when the
   switch is on.  It comes from the backend's configuration
   ([set_wp_share_choice_min_size], called before the conversion; 256 for a
   backend that sets nothing); a numeric value greater than 1 of
   [COAR_WP_SHARE_CHOICE] overrides it, as a debugging override only.
   Why 256: the inputs whose conversion is exponential without sharing share
   choices whose postconditions are far larger, and still convert in seconds
   at 256; at 64, one small input (a postcondition of 128 to 256 nodes) got a
   shared form whose recursive calls take fresh universally bound arguments
   tied to the state by a disjunction of equalities, which the fixpoint solver
   answered in half of the runs where the copied form answered in nine of ten. *)
let wp_share_choice_min_size = Atomic.make 256

let wp_share_choice_min_size_override =
  match Option.bind (Sys.getenv "COAR_WP_SHARE_CHOICE") ~f:Int.of_string_opt with
  | Some n when n > 1 -> Some n
  | _ -> None

let set_wp_share_choice_min_size n =
  Atomic.set wp_share_choice_min_size
    (Option.value wp_share_choice_min_size_override ~default:n)

let () = set_wp_share_choice_min_size 256

(* Whether [phi] has more than [n] formula nodes (atoms and connectives),
   counted only up to [n + 1]. *)
let formula_size_exceeds n phi =
  let count = ref 0 in
  let exception Exceeded in
  let rec go phi =
    incr count;
    if !count > n then raise Exceeded;
    match phi with
    | Formula.UnaryOp (_, phi, _) | Formula.Bind (_, _, phi, _) -> go phi
    | Formula.BinaryOp (_, phi1, phi2, _) -> go phi1; go phi2
    | Formula.LetFormula (_, _, _, phi, _) -> go phi
    | Formula.LetRec (_, phi, _) -> go phi
    | Formula.Atom _ -> ()
  in
  try go phi; false with Exceeded -> true

(* The left-hand side merged for one right-hand side from the left-hand sides
   [lhss_list] (each a conjunction given as a set) of the implications with that
   right-hand side: their disjunction, with the conjuncts all of them share
   factored out (see [wp_share_choice]).  With nothing shared it is the plain
   merge's disjunction of [Evaluator.simplify_and]s. *)
let merge_choice_lhss lhss_list =
  let plain () =
    List.map lhss_list ~f:Evaluator.simplify_and
    |> Set.Poly.of_list |> Set.to_list |> Formula.or_of
  in
  match lhss_list with
  | [] | [ _ ] -> plain ()
  | _ -> (
      let flat =
        List.map lhss_list ~f:(fun lhss ->
            Set.Poly.union_list
            @@ List.map (Set.to_list lhss) ~f:Formula.conjuncts_of)
      in
      match flat with
      | [] -> assert false
      | f :: fs ->
          let common = List.fold fs ~init:f ~f:Set.inter in
          if Set.is_empty common then plain ()
          else
            let rests =
              List.map flat ~f:(fun cs ->
                  Evaluator.simplify_and (Set.diff cs common))
            in
            if List.exists rests ~f:Formula.is_true then
              Evaluator.simplify_and common
            else
              let rests = List.filter rests ~f:(Fn.non Formula.is_false) in
              if List.is_empty rests then Formula.mk_false ()
              else
                Evaluator.simplify_and
                  (Set.add common
                     (Formula.or_of
                        (Set.to_list (Set.Poly.of_list rests)))))

(* Raised by the composed substitution when it reaches a binder (see
   [compose_rfvs]); the run is then replayed one command at a time. *)
exception Compose_abort

(* The range-free-variable argument of [Formula.subst_rfvs] and
   [Term.subst_rfvs] is forced exactly when a binder is reached while some
   substitution key is still unbound under it, which is the only place a
   substitution may rename a binder.  Forcing this one aborts instead, so a
   substitution that returns has renamed nothing and is plain first-order
   replacement. *)
let compose_rfvs () = lazy (raise Compose_abort)

(* A term made of variables and function symbols other than a function
   variable, a formula or an array lambda: substituting into it touches only
   its [Term.tvs_of] variables and reaches no binder, so a substitution whose
   key is not among them returns the same term. *)
let rec plain_term = function
  | Term.Var _ -> true
  | Term.FunApp ((FVar _ | T_bool.Formula _ | T_array.ALambda _), _, _) -> false
  | Term.FunApp (_, ts, _) -> List.for_all ts ~f:plain_term
  | Term.LetTerm _ -> false

(* A composed substitution [theta] with an index of which entries a later
   substitution must rewrite: [users] maps a variable to the keys whose (plain)
   value mentions it, and [opaque] holds the keys whose value is not plain and
   is rewritten at every step.  Invariant: for every key [k] of [theta], either
   [k] is in [opaque], or [theta(k)] is plain and [k] is in [users(v)] exactly
   for the [v] in [Term.tvs_of (theta(k))]. *)
type composed = {
  theta : (Ident.tvar, Term.t) Map.Poly.t;
  users : (Ident.tvar, Ident.tvar Set.Poly.t) Map.Poly.t;
  opaque : Ident.tvar Set.Poly.t;
}

let composed_empty =
  { theta = Map.Poly.empty; users = Map.Poly.empty; opaque = Set.Poly.empty }

let composed_remove k cm =
  match Map.Poly.find cm.theta k with
  | None -> cm
  | Some u ->
      if Set.mem cm.opaque k then
        { cm with theta = Map.Poly.remove cm.theta k; opaque = Set.remove cm.opaque k }
      else
        {
          cm with
          theta = Map.Poly.remove cm.theta k;
          users =
            Set.fold (Term.tvs_of u) ~init:cm.users ~f:(fun users v ->
                Map.Poly.change users v ~f:(function
                  | None -> None
                  | Some ks ->
                      let ks = Set.remove ks k in
                      if Set.is_empty ks then None else Some ks));
        }

let composed_set k u cm =
  let cm = composed_remove k cm in
  let theta = Map.Poly.set cm.theta ~key:k ~data:u in
  if plain_term u then
    {
      cm with
      theta;
      users =
        Set.fold (Term.tvs_of u) ~init:cm.users ~f:(fun users v ->
            Map.Poly.update users v ~f:(function
              | None -> Set.Poly.singleton k
              | Some ks -> Set.add ks k));
    }
  else { cm with theta; opaque = Set.add cm.opaque k }

(* theta followed by [x := t]: theta'(y) = theta(y)[x := t] for y in
   dom theta, theta'(x) = t when x is not in dom theta.  Only the entries
   whose value mentions [x] (or is not plain) are rewritten; the others are
   the same terms.  Raises [Compose_abort] where a substitution reaches a
   binder. *)
let composed_then cm x t =
  let sigma = Map.Poly.singleton x t in
  let affected =
    Set.union cm.opaque
      (Option.value ~default:Set.Poly.empty (Map.Poly.find cm.users x))
  in
  let cm =
    Set.fold affected ~init:cm ~f:(fun cm k ->
        composed_set k
          (Term.subst_rfvs (compose_rfvs ()) sigma (Map.Poly.find_exn cm.theta k))
          cm)
  in
  if Map.Poly.mem cm.theta x then cm else composed_set x t cm

(* The names of the Boolean variables [c] substitutes. *)
let bool_substituted c =
  let rec go acc = function
    | Skip | Assume _ -> acc
    | Subst ((Ident.Tvar x, s), _) ->
        if Term.is_bool_sort s then Set.add acc x else acc
    | Seq (c1, c2) | Choice (c1, c2) -> go (go acc c1) c2
  in
  go Set.Poly.empty c

let rec seq_list c acc =
  match c with Seq (c1, c2) -> seq_list c1 (seq_list c2 acc) | c -> c :: acc

let rec wp ?(post_clean = false) c phi =
  if print_log then
    print_endline
    @@ sprintf "command:\n%spost: %s\n" (str_of_command c) (Formula.str_of phi);
  let phi =
    match c with
    | Skip -> phi
    | Assume phi' -> Formula.mk_imply phi' phi
    | Subst ((x, _s), t) ->
        (if false then Evaluator.simplify_keep_imply else Fn.id)
        @@ Formula.apply_pred (x, phi) t
    | Seq _ when Atomic.get wp_compose_substs && Atomic.get wp_skip_composite
      ->
        wp_seq ~post_clean (seq_list c []) phi
    | Seq (c1, c2) -> wp ~post_clean:true c1 (wp ~post_clean c2 phi)
    | Choice (c1, c2)
      when Atomic.get wp_share_choice
           && formula_size_exceeds (Atomic.get wp_share_choice_min_size) phi
           && Set.is_empty
                (Formula.term_sort_env_of
                   ~keep:
                     (Ident.name_of_tvar
                     >> String.is_prefix ~prefix:nondet_prefix)
                   phi)
           &&
           let bools = bool_substituted c in
           Set.is_empty bools
           || Set.for_all (Formula.pred_sort_env_of phi)
                ~f:(fun (Ident.Pvar name, sorts) ->
                  not (List.is_empty sorts && Set.mem bools name)) ->
        wp_choice_shared ~post_clean c1 c2 phi
    | Choice (c1, c2) ->
        Set.union
          (Formula.implies_of (wp ~post_clean c1 phi))
          (Formula.implies_of (wp ~post_clean c2 phi))
        |> Set.fold ~init:Map.Poly.empty ~f:(fun map (lhss, rhs) ->
            let lhs = Evaluator.simplify_and lhss in
            Map.Poly.update map rhs ~f:(function
              | None -> Set.Poly.singleton lhs
              | Some lhss -> Set.add lhss lhs))
        |> Map.Poly.map ~f:(Set.to_list >> Formula.or_of)
        |> Map.Poly.to_alist
        |> List.filter_map ~f:(fun (rhs, lhs) ->
            if Formula.is_false lhs || Formula.is_true rhs then None
            else if Formula.is_true lhs then Some rhs
            else Some (Formula.mk_imply lhs rhs))
        |> Formula.and_of
  in
  if print_log then
    print_endline @@ sprintf "wp: %s" (LogicOld.Formula.str_of phi);
  let is_nondet = Ident.name_of_tvar >> String.is_prefix ~prefix:nondet_prefix in
  let nondet_senv_of phi =
    if Atomic.get wp_collect_nondets_only then
      (* the same set: the restriction is applied while collecting *)
      Formula.term_sort_env_of ~keep:is_nondet phi
    else Set.filter (Formula.term_sort_env_of phi) ~f:(fst >> is_nondet)
  in
  (* Invariant: [wp c phi] never has a free nondet variable, whatever [phi].
     Where the precondition built below has one, every free one is bound
     ([bind_nondet]: the elimination keeps subformulas of the precondition
     and quantifier eliminations of them, which introduce no variable);
     where it has none, it is returned as it is.  Hence the search below can
     only find nothing, and is skipped, in two cases: at a sequence or a
     choice, whose precondition only combines results of [wp] on its parts
     (a choice through [implies_of] and [simplify_and], which introduce no
     variable); and at a leaf whose postcondition is itself a result of [wp]
     ([post_clean]: the first command of a sequence) when the leaf's own
     assumed formula or substituted term has no nondet variable (a
     substitution renames binders to fresh names, never to nondet ones).
     The search walks the whole precondition, at every step of a sequence,
     and was most of the conversion's time on long sequences.
     [COAR_WP_CHECK_COMPOSITE] searches at every step; with
     COAR_EXACT_CROSSCHECK a skipped search is made anyway and a found
     variable reported. *)
  let known_clean =
    Atomic.get wp_skip_composite
    &&
    match c with
    | Seq _ | Choice _ -> true
    | Skip -> post_clean
    | Assume phi' ->
        post_clean && Set.is_empty (Formula.term_sort_env_of ~keep:is_nondet phi')
    | Subst (_, t) ->
        post_clean && Set.is_empty (Term.term_sort_env_of ~keep:is_nondet t)
  in
  let nondet_senv =
    if known_clean then (
      if PropLogic.Formula.crosscheck then (
        PropLogic.Formula.crosscheck_tick ();
        if not (Set.is_empty (nondet_senv_of phi)) then
          prerr_endline "exact-crosscheck: LTS wp skipped search FINDS nondets");
      Set.Poly.empty)
    else nondet_senv_of phi
  in
  if Set.is_empty nondet_senv then phi
  else
    let res =
      let nondet_senv_int =
        (* integer and bit-vector nondets: both carry a width range *)
        Set.filter nondet_senv ~f:(fun (_, s) ->
            LogicOld.Term.is_int_sort s || LogicOld.Term.is_bv_sort s)
      in
      if Set.is_empty nondet_senv_int then phi
      else (
        clean ();
        Formula.and_of @@ Set.to_list
        @@ Set.Poly.filter_map ~f:(fun (lhss, rhs) ->
            if Formula.is_true rhs then None
            else if Set.is_empty lhss then Some rhs
            else
              let lhs =
                (if true then Set.to_list >> Formula.and_of
                 else Evaluator.simplify_and)
                  lhss
              in
              if Formula.is_false lhs then None
              else
                let nondet_senv_int_lhs =
                  let tvs = Formula.tvs_of rhs in
                  Set.filter nondet_senv_int ~f:(fst >> Set.mem tvs >> not)
                in
                let lhs =
                  (* the eliminated nondet variables keep their value range:
                     [bind_nondet] only sees the variables that survive, so
                     without this a sized nondet was unbounded exactly when
                     it was eliminated here *)
                  let ranges =
                    List.filter_map
                      (Set.to_list nondet_senv_int_lhs)
                      ~f:range_of_nondet
                  in
                  qelim
                  @@ Formula.mk_exists_if_bounded
                       (Set.to_list nondet_senv_int_lhs)
                       (Formula.and_of (lhs :: ranges))
                in
                if Formula.is_false lhs then None
                else if Formula.is_true lhs then Some rhs
                else Some (Formula.mk_imply lhs rhs))
        @@ Formula.implies_of phi)
    in
    if print_log then
      print_endline @@ sprintf "simplified wp: %s" (LogicOld.Formula.str_of res);
    bind_nondet (Set.to_list nondet_senv) res

(* [wp_choice_shared ~post_clean c1 c2 phi] is a formula equivalent to
   [wp ~post_clean (Choice (c1, c2)) phi] with [phi] occurring once (see
   [wp_share_choice] for the construction and the equivalence argument).
   Assumes [phi] has no free nondet variable, so the placeholder atom has none
   either and the branches bind exactly the nondet variables they bind
   against [phi]; and no nullary predicate application named after a Boolean
   variable the choice substitutes, since such a substitution also replaces a
   nullary application of the same name, which the placeholder's arguments
   (the free term variables) would not carry (a location with no live
   variable is a nullary application too, and is kept). *)
and wp_choice_shared ~post_clean c1 c2 phi =
  let senv = Set.to_list (Formula.term_sort_env_of phi) in
  let pvar = Ident.mk_fresh_pvar ~prefix:(Some "#wpk") () in
  let k = Formula.mk_atom (Atom.pvar_app_of_senv pvar senv) in
  let k_args = function
    | Formula.Atom (Atom.App (Predicate.Var (p, _), args, _), _)
      when Stdlib.( = ) p pvar ->
        Some args
    | _ -> None
  in
  (* Implications [lhss => rhs] of the branches, with every universal
     quantifier above a K-atom lifted (its variables renamed fresh, so that it
     captures nothing in the hypotheses it moves over or in the other
     branch). *)
  let rec collect (bound, items, others) (lhss, rhs) =
    match k_args rhs with
    | Some args -> (bound, (lhss, args) :: items, others)
    | None -> (
        match rhs with
        | Formula.Bind (Formula.Forall, params, body, _) ->
            let ren =
              List.map params ~f:(fun (x, s) -> (x, Ident.mk_fresh_tvar (), s))
            in
            let body =
              Formula.subst
                (Map.Poly.of_alist_exn
                   (List.map ren ~f:(fun (x, y, s) -> (x, Term.mk_var y s))))
                body
            in
            let bound = List.map ren ~f:(fun (_, y, s) -> (y, s)) @ bound in
            Set.fold (Formula.implies_of body) ~init:(bound, items, others)
              ~f:(fun acc (l, r) -> collect acc (Set.union lhss l, r))
        | _ -> (bound, items, (lhss, rhs) :: others))
  in
  let bound, items, others =
    Set.fold
      (Set.union
         (Formula.implies_of (wp ~post_clean c1 k))
         (Formula.implies_of (wp ~post_clean c2 k)))
      ~init:([], [], []) ~f:collect
  in
  let instantiate =
    Formula.subst_preds (Map.Poly.singleton pvar (senv, phi))
  in
  let others =
    List.filter_map others ~f:(fun (lhss, rhs) ->
        if Formula.is_true rhs then None
        else
          let rhs = instantiate rhs in
          if Set.is_empty lhss then Some rhs
          else Some (Formula.mk_imply (Formula.and_of (Set.to_list lhss)) rhs))
  in
  let term_equal t1 t2 =
    try Stdlib.( = ) t1 t2 with Invalid_argument _ -> false
  in
  let merged, fresh =
    match items with
    | [] -> ([], [])
    | (_, args0) :: _ ->
        (* per argument position: [None] where every item passes the same
           term, [Some v] (a fresh variable) where they disagree *)
        let positions =
          List.mapi senv ~f:(fun j (_, s) ->
              let t0 = List.nth_exn args0 j in
              if
                List.for_all items ~f:(fun (_, args) ->
                    term_equal (List.nth_exn args j) t0)
              then (t0, None)
              else (t0, Some (Ident.mk_fresh_tvar (), s)))
        in
        let fresh = List.filter_map positions ~f:snd in
        let lhss_list =
          List.map items ~f:(fun (lhss, args) ->
              List.fold2_exn positions args ~init:lhss
                ~f:(fun lhss (_, v) t ->
                  match v with
                  | None -> lhss
                  | Some (v, s) -> Set.add lhss (Formula.eq (Term.mk_var v s) t)))
        in
        let lhs = merge_choice_lhss lhss_list in
        let rhs =
          Formula.subst
            (Map.Poly.of_alist_exn
               (List.map2_exn senv positions ~f:(fun (y, _) (t0, v) ->
                    ( y,
                      match v with
                      | None -> t0
                      | Some (v, s) -> Term.mk_var v s ))))
            phi
        in
        if Formula.is_false lhs then ([], fresh)
        else if Formula.is_true lhs then ([ rhs ], fresh)
        else ([ Formula.mk_imply lhs rhs ], fresh)
  in
  Formula.mk_forall_if_bounded (bound @ fresh)
    (Formula.and_of (others @ merged))

(* [wp_seq ~post_clean cs phi] is [wp ~post_clean (Seq (c1, Seq (c2, ...))) phi]
   for [cs = [c1; c2; ...]], the same formula, computed with fewer walks of the
   precondition.  [wp] of a sequence applies its commands from the last to the
   first, and a substitution walks the whole precondition built so far, so a
   sequence of n substitutions in front of a large postcondition cost n walks of
   it (a T2 input whose blocks rename two dozen variables twice per transition
   spent its whole conversion there).  Here a run of commands that [wp] would
   not search for nondet variables -- a substitution [x := t] with [t] free of
   nondet variables and [x] not Boolean, an assumption free of nondet variables,
   [Skip], each with a postcondition that is itself a result of [wp] -- is kept
   as a pair (psi, theta) standing for psi theta:
   - [x := t]: (psi theta)[x := t] = psi theta' with theta'(y) = theta(y)[x := t]
     for y in dom theta, and theta'(x) = t when x is not in dom theta;
   - [assume g] where g theta = g (checked on the terms):
     g => psi theta = (g => psi) theta.
   theta is applied once, when a command outside the run (or the start of the
   sequence) needs the formula.  Both identities are identities of terms, not
   only of meanings, provided no substitution renames a binder: every
   substitution here runs with [compose_rfvs], which aborts at the first binder
   that could be renamed, and the run is then replayed through [wp] one command
   at a time, as before.  Every binder at which one of the one-at-a-time
   substitutions would have looked for a clash is also reached by the
   composition with a key still unbound (every key of those substitutions is a
   key of theta, and every term they insert is substituted into while theta is
   built), so a composition that does not abort stands for a sequence that
   renamed nothing.  A Boolean [x] is excluded because a
   nullary predicate application is replaced by [Formula.of_bool_term] of the
   value, which need not commute with the later substitutions. *)
and wp_seq ~post_clean cs phi =
  let is_nondet = Ident.name_of_tvar >> String.is_prefix ~prefix:nondet_prefix in
  (* the same tests as [wp]'s, so that a command is absorbed exactly when [wp]
     would skip the nondet search after it *)
  let clean_formula g =
    Set.is_empty (Formula.term_sort_env_of ~keep:is_nondet g)
  in
  let clean_term t = Set.is_empty (Term.term_sort_env_of ~keep:is_nondet t) in
  (* the run being composed: [base] is the formula at its start, [cmds] its
     commands from the last applied to the first, and [psi] and [theta] the
     composed form of [cmds] applied to [base] *)
  let replay base cmds =
    List.fold_right cmds ~init:base ~f:(fun c phi -> wp ~post_clean:true c phi)
  in
  let materialize (base, cmds, psi, cm) =
    let theta = cm.theta in
    if Map.Poly.is_empty theta then psi
    else
      let composed =
        try Some (Formula.subst_rfvs (compose_rfvs ()) theta psi)
        with Compose_abort -> None
      in
      match composed with
      | None when Atomic.get wp_share_choice ->
          (* The composed substitution reached a binder.  Replaying the run
             gives the same formula as the term-identical path; with the
             shared choices on, only equivalence is required, and one
             capture-avoiding simultaneous substitution of the composed theta
             is, up to the names of renamed binders, the run of substitutions
             it composes: psi theta1 ... thetan =alpha psi (theta1; ...;
             thetan).  The shared choices put fresh universal binders into
             the precondition, so without this every later run of
             substitutions over it was replayed one command at a time, each
             walking the whole precondition. *)
          Formula.subst theta psi
      | None -> replay base cmds
      | Some res ->
          (if PropLogic.Formula.crosscheck then (
             PropLogic.Formula.crosscheck_tick ();
             let seq = replay base cmds in
             if
               not
                 (try Stdlib.(seq = res)
                  with Invalid_argument _ -> false)
             then prerr_endline "exact-crosscheck: LTS wp_seq composed DIFFERS"));
          res
  in
  let start phi = (phi, [], phi, composed_empty) in
  let step ((base, cmds, psi, cm) as run) ~post_clean c =
    match c with
    | (Skip | Assume _ | Subst _) when not post_clean ->
        start (wp ~post_clean c (materialize run))
    | Skip -> (base, c :: cmds, psi, cm)
    | Assume g when clean_formula g ->
        let unchanged =
          (* g theta = g, checked on the terms themselves *)
          Map.Poly.is_empty cm.theta
          ||
          try Stdlib.(Formula.subst_rfvs (compose_rfvs ()) cm.theta g = g)
          with Compose_abort | Invalid_argument _ -> false
        in
        if unchanged then (base, c :: cmds, Formula.mk_imply g psi, cm)
        else
          let phi = materialize run in
          (phi, [ c ], Formula.mk_imply g phi, composed_empty)
    | Subst ((x, s), t)
      when (not (Term.is_bool_sort s))
           && (not (Term.is_bool_sort (Term.sort_of t)))
           && clean_term t -> (
        match
          try Some (composed_then cm x t) with Compose_abort -> None
        with
        | Some cm' -> (base, c :: cmds, psi, cm')
        | None ->
            let phi = materialize run in
            (phi, [ c ], phi, composed_set x t composed_empty))
    | _ -> start (wp ~post_clean c (materialize run))
  in
  List.foldi (List.rev cs) ~init:(start phi) ~f:(fun i run c ->
      (* the last command keeps the caller's flag, as in [wp] of a [Seq] *)
      step run ~post_clean:(if i = 0 then post_clean else true) c)
  |> materialize

let used_vars c =
  let rec aux env = function
    | Skip -> env
    | Assume phi ->
        let env' =
          Set.filter
            (Formula.term_sort_env_of phi)
            ~f:
              (fst >> Ident.name_of_tvar
              >> String.is_prefix ~prefix:nondet_prefix
              >> not)
        in
        Set.union env' env
    | Subst ((x, _), t) ->
        let env' =
          Set.filter (Term.term_sort_env_of t)
            ~f:
              (fst >> Ident.name_of_tvar
              >> String.is_prefix ~prefix:nondet_prefix
              >> not)
        in
        Set.union env' (Set.filter env ~f:(fun (y, _) -> Stdlib.(x <> y)))
    | Seq (c1, c2) -> aux (aux env c2) c1
    | Choice (c1, c2) -> Set.union (aux env c1) (aux env c2)
  in
  aux Set.Poly.empty c

let defined_vars c =
  let rec aux env = function
    | Skip -> env
    | Assume _ -> env
    | Subst ((x, _), _) -> Set.add env x
    | Seq (c1, c2) -> aux (aux env c2) c1
    | Choice (c1, c2) -> Set.inter (aux env c1) (aux env c2)
  in
  aux Set.Poly.empty c

module V (*: Sig.COMPARABLE*) = struct
  type t = string

  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
end

module E (*: Sig.ORDERED_TYPE_DFT*) = struct
  type t = command

  let compare = Stdlib.compare
  let default = Skip
end

module G = Imperative.Digraph.ConcreteBidirectionalLabeled (V) (E)
module DFS = Traverse.Dfs (G)

let graph_of (trans : transition list) =
  let g = G.create () in
  List.iter trans ~f:(fun (f, c, t) ->
      let v1 = G.V.create f in
      let v2 = G.V.create t in
      G.add_vertex g v1;
      G.add_vertex g v2;
      G.add_edge_e g (G.E.create v1 c v2));
  g

let of_graph cfa : transition list =
  G.fold_edges_e (fun tr trans -> tr :: trans) cfa []

exception Found_Edges of G.edge list

let contract_edges ~print cfa =
  try
    G.iter_edges
      (fun s d ->
        let edges = G.find_all_edges cfa s d in
        if List.length edges > 1 then raise (Found_Edges edges) else ())
      cfa;
    false
  with
  | Found_Edges [] -> assert false
  | Found_Edges ((s, _, d) :: _ as es) ->
      print @@ lazy (sprintf "eliminating edge (%s, %s)" s d);
      let c = choice @@ List.map es ~f:snd3 in
      G.remove_edge cfa s d;
      G.add_edge_e cfa (s, c, d);
      true

exception Found_Vertex_1_1 of G.edge * G.vertex * G.edge

let contract_vertex_1_1 ~print keep cfa =
  try
    G.iter_vertex
      (fun v ->
        if
          keep v
          (* ignore the start node and the Buechi locations *)
          || Fn.non List.is_empty
             @@ G.find_all_edges cfa v v (* ignore vertex with a self-loop *)
        then ()
        else
          match (G.pred_e cfa v, G.succ_e cfa v) with
          | [ e1 ], [ e2 ] -> raise (Found_Vertex_1_1 (e1, v, e2))
          | _ -> ())
      cfa;
    false
  with Found_Vertex_1_1 ((s, c1, _d), v, (_s, c2, d)) ->
    print @@ lazy (sprintf "eliminating vertex %s" v);
    G.remove_vertex cfa v;
    G.add_edge_e cfa (s, seq [ c1; c2 ], d);
    true

exception Found_Vertex_1_n of G.edge * G.vertex * G.edge list

let contract_vertex_1_n ~print keep cfa =
  try
    G.iter_vertex
      (fun v ->
        if
          keep v
          (* ignore the start node and the Buechi locations *)
          || Fn.non List.is_empty
             @@ G.find_all_edges cfa v v (* ignore vertex with a self-loop *)
        then ()
        else
          match (G.pred_e cfa v, G.succ_e cfa v) with
          | [ ((_, c, _) as e) ], es when is_effect_free c ->
              raise (Found_Vertex_1_n (e, v, es))
          | _ -> ())
      cfa;
    false
  with Found_Vertex_1_n ((s, c1, _d), v, es) ->
    print @@ lazy (sprintf "eliminating vertex %s" v);
    G.remove_vertex cfa v;
    List.iter es ~f:(fun (_s, c2, d) -> G.add_edge_e cfa (s, seq [ c1; c2 ], d));
    true

exception Found_Vertex_n_1 of G.edge list * G.vertex * G.edge

let contract_vertex_n_1 ~print keep cfa =
  try
    G.iter_vertex
      (fun v ->
        if
          keep v
          (* ignore the start node and the Buechi locations *)
          || Fn.non List.is_empty
             @@ G.find_all_edges cfa v v (*ignore vertex with a self-loop*)
        then ()
        else
          match (G.pred_e cfa v, G.succ_e cfa v) with
          | es, [ ((_, c, _) as e) ] when is_effect_free c ->
              raise (Found_Vertex_n_1 (es, v, e))
          | _ -> ())
      cfa;
    false
  with Found_Vertex_n_1 (es, v, (_s, c2, d)) ->
    print @@ lazy (sprintf "eliminating vertex %s" v);
    G.remove_vertex cfa v;
    List.iter es ~f:(fun (s, c1, _d) -> G.add_edge_e cfa (s, seq [ c1; c2 ], d));
    true

(* [keep v] holds of the vertices that must survive: the start location, and
   the Buechi locations, whose visits are what a Buechi mode counts (merging a
   path through one into an edge would hide them).  Every other contraction
   preserves the infinite runs and which kept vertices each visits. *)
let rec simplify ~print keep cfa =
  if
    contract_edges ~print cfa
    || contract_vertex_1_1 ~print keep cfa
    || contract_vertex_1_n ~print keep cfa
    || contract_vertex_n_1 ~print keep cfa
  then simplify ~print keep cfa
  else cfa

(* commands keyed by physical identity (see [LiveVariables.def_use]) *)
module PhysCmd = Stdlib.Hashtbl.Make (struct
  type t = command

  let equal = phys_equal
  let hash = Stdlib.Hashtbl.hash_param 100 1000
end)

let live_vars_recompute =
  Option.is_some (Sys.getenv "COAR_LIVE_VARS_RECOMPUTE")

module LiveVariables =
  Graph.Fixpoint.Make
    (G)
    (struct
      type vertex = G.E.vertex
      type edge = G.E.t
      type g = G.t
      type data = sort_env_set

      let direction = Graph.Fixpoint.Backward
      let equal = Set.equal
      let join = Set.union

      (* the defined and used variables of an edge's command, computed once
         per command object: the fixpoint asks them of every edge at every
         pass, and on a large transition system recomputing them was most of
         the analysis (a pure function of the command, so the result is the
         same).  Keyed by physical identity, hashed deeply so that commands
         alike in their first nodes do not share a bucket.  The conversion
         runs on one domain, before any solver domain exists.
         [COAR_LIVE_VARS_RECOMPUTE] recomputes at every visit. *)
      let def_use_memo : (Ident.tvar Set.Poly.t * sort_env_set) PhysCmd.t =
        PhysCmd.create 1024

      let def_use c =
        if live_vars_recompute then (defined_vars c, used_vars c)
        else
          match PhysCmd.find_opt def_use_memo c with
          | Some r -> r
          | None ->
              let r = (defined_vars c, used_vars c) in
              PhysCmd.add def_use_memo c r;
              r

      let analyze (_, c, _) env =
        let def, use = def_use c in
        Set.union use (Set.filter env ~f:(fst >> Set.mem def >> not))
    end)

(* How [cut_points_of] breaks its ties, i.e. which of the many sets that
   meet every cycle it returns.

   - [Graph_order]: the order in which the graph's hash table lists its
     vertices.  It depends on the location names, so renaming the locations
     of a file can change the set.
   - [Loop_heads]: by the program's loop structure, independently of the hash
     table.  The loop heads are the targets of the back edges of a depth-first
     search from the start location (restarted at any vertex it does not
     reach), whose successors are visited in the order the locations first
     occur in the transitions; every cycle contains a back edge of such a
     search, so the heads alone meet every cycle.  A bypass then removes the
     vertices that are not heads before the heads, so that a head rather than
     a body vertex keeps the self-loop that makes it a cut point, and the
     largest-degree pick prefers a head; every remaining tie goes to the
     vertex that occurs first in the transitions.

   Both return a set that meets every cycle, and the termination encoding of
   a transition system has the same solution for every such set: a location
   outside the set can be read as a greatest fixpoint because every infinite
   run visits some cut point infinitely often.  So the choice never changes
   a verdict; it changes which locations carry a ranking obligation, and with
   it what the constraint solver has to find, and so its time.  On one
   termination input the hash order picked a body vertex where the loop head
   was available and MuVal stopped answering within 300 s, while MuStrat
   answered on that set and not on the loop heads: no rule is better for
   every engine. *)
type cut_point_choice = Graph_order | Loop_heads [@@deriving yojson]

(* [loop_heads g ~start ~rank]: the targets of the back edges of a
   depth-first search of [g] from [start] and then from every vertex not yet
   reached, both in increasing [rank], with each vertex's successors visited
   in increasing [rank].  Every cycle of [g] contains a back edge of the
   search, so the result meets every cycle.  Iterative: a simplified graph can
   have tens of thousands of vertices.  The result depends on [g]'s edges and
   on [rank] only, never on the hash table's order. *)
let loop_heads g ~start ~rank =
  let by_rank = List.sort ~compare:(fun a b -> Int.compare (rank a) (rank b)) in
  (* 0 white, 1 on the current path, 2 finished *)
  let color = Hashtbl.create (module String) in
  let get v = Option.value (Hashtbl.find color v) ~default:0 in
  let heads = ref Set.Poly.empty in
  let visit root =
    if get root = 0 then (
      Hashtbl.set color ~key:root ~data:1;
      let stack = Stack.create () in
      Stack.push stack (root, by_rank (G.succ g root));
      while not (Stack.is_empty stack) do
        match Stack.pop_exn stack with
        | v, [] -> Hashtbl.set color ~key:v ~data:2
        | v, w :: ws ->
            Stack.push stack (v, ws);
            let c = get w in
            if c = 1 then heads := Set.add !heads w
            else if c = 0 then (
              Hashtbl.set color ~key:w ~data:1;
              Stack.push stack (w, by_rank (G.succ g w)))
      done)
  in
  if G.mem_vertex g start then visit start;
  List.iter (by_rank (G.fold_vertex List.cons g [])) ~f:visit;
  !heads

(* [cut_points_of ?choice ?start ?rank g res]: [res] united with a set of
   vertices of [g] that meets every cycle of [g] (destroying [g]).  The Term
   encoding makes exactly these locations least fixpoints and reads every
   other one as a greatest fixpoint, so a cycle missed here is a loop taken to
   terminate.  Each step keeps the invariant that every cycle of the original
   graph either passes through a vertex already in [res] or maps to a cycle of
   the current graph: a vertex with a self-loop is moved to [res]; a vertex
   with at most one edge lies on no cycle; and a vertex [s] with one
   predecessor [p] and one successor [q], neither of them [s], is bypassed by
   an edge [p -> q], which turns every cycle through [s] into one through that
   edge.  The bypass is decided on the graph as it is when [s] is reached:
   deciding every bypass of a round up front and then applying them all
   removed the whole of a cycle whose vertices all had one predecessor and one
   successor (bypassing [b] in [a -> b -> c -> a] leaves [a -> c -> a], where
   [c]'s predecessor is no longer [b]), and the encoding answered that a loop
   that never exits terminates.

   The invariant holds whatever order the steps visit the vertices in, so
   [choice] (see [cut_point_choice]) changes which set is returned and never
   its property.  [start] and [rank] are read only by [Loop_heads]: the
   search's start and the order of first occurrence in the transitions; a
   vertex without a rank sorts after every ranked one, by name. *)
let cut_points_of ?(choice = Graph_order) ?start ?(rank = fun _ -> 0) g res =
  let heads, order =
    match choice with
    | Graph_order -> (Set.Poly.empty, None)
    | Loop_heads ->
        let heads =
          match start with
          | Some start -> loop_heads g ~start ~rank
          | None -> loop_heads g ~start:"" ~rank
        in
        (* heads last, then by rank, then by name: a total order *)
        let compare a b =
          match Bool.compare (Set.mem heads a) (Set.mem heads b) with
          | 0 -> (
              match Int.compare (rank a) (rank b) with
              | 0 -> String.compare a b
              | c -> c)
          | c -> c
        in
        (heads, Some compare)
  in
  let rec go g res =
    if DFS.has_cycle g then (
      let vertices_self_loop =
        G.fold_vertex
          (fun s vs -> if G.mem_edge g s s then Set.add vs s else vs)
          g Set.Poly.empty
      in
      Set.iter vertices_self_loop ~f:(G.remove_vertex g);
      let res = Set.union res vertices_self_loop in
      let vertices_deg_leq_1 =
        G.fold_vertex
          (fun s vs ->
            if G.in_degree g s + G.out_degree g s <= 1 then Set.add vs s
            else vs)
          g Set.Poly.empty
      in
      Set.iter vertices_deg_leq_1 ~f:(G.remove_vertex g);
      let visit_order =
        let vs = G.fold_vertex (fun s vs -> s :: vs) g [] in
        match order with None -> vs | Some compare -> List.sort vs ~compare
      in
      let bypassed =
        List.fold visit_order ~init:false ~f:(fun bypassed s ->
            if not (G.mem_vertex g s) then bypassed
            else
              match (G.pred g s, G.succ g s) with
              | [ pred ], [ succ ] when String.(pred <> s && succ <> s) ->
                  if not @@ G.mem_edge g pred succ then G.add_edge g pred succ;
                  G.remove_vertex g s;
                  true
              | _ -> bypassed)
      in
      if
        Set.is_empty vertices_self_loop
        && Set.is_empty vertices_deg_leq_1
        && not bypassed
      then (
        let v =
          match order with
          | None ->
              snd
              @@ G.fold_vertex
                   (fun s (deg0, s0) ->
                     let deg = G.in_degree g s + G.out_degree g s in
                     if deg > deg0 then (deg, s) else (deg0, s0))
                   g (-1, "")
          | Some _ ->
              (* the largest degree; among those a head; then by rank and
                 name *)
              let better (d1, h1, r1, n1) (d2, h2, r2, n2) =
                if d1 <> d2 then d1 > d2
                else if Bool.(h1 <> h2) then h1
                else if r1 <> r2 then r1 < r2
                else String.(n1 < n2)
              in
              let _, _, _, v =
                G.fold_vertex
                  (fun s best ->
                    let c =
                      ( G.in_degree g s + G.out_degree g s,
                        Set.mem heads s,
                        rank s,
                        s )
                    in
                    match best with
                    | Some b when not (better c b) -> best
                    | _ -> Some c)
                  g None
                |> Option.value_exn
              in
              v
        in
        G.remove_vertex g v;
        go g @@ Set.add res v)
      else go g res)
    else res
  in
  go g res

(* [rank_of trans start]: the position of each location's first occurrence
   in [start :: trans] (source before target), and [max_int] for any other
   name: the order [Loop_heads] breaks its ties by. *)
let rank_of trans start =
  let tbl = Hashtbl.create (module String) in
  let add v =
    if not (Hashtbl.mem tbl v) then
      Hashtbl.set tbl ~key:v ~data:(Hashtbl.length tbl)
  in
  add start;
  List.iter trans ~f:(fun (f, _, t) ->
      add f;
      add t);
  fun v -> Option.value (Hashtbl.find tbl v) ~default:Int.max_value

let analyze ~print ?(cut_point_choice = Graph_order)
    ((s, types, e, c, trans, b) as lts) =
  print @@ lazy "************* simplifying LTS ***************";
  print @@ lazy (sprintf "input LTS:\n%s" @@ str_of_lts lts);
  let trans_with_error =
    match e with
    | Some error_state -> (error_state, Skip, error_state) :: trans
    | None -> trans
  in
  match s with
  | None ->
      ((fun _ -> Set.Poly.empty), Set.Poly.empty, (s, types, e, c, trans, b))
  | Some s ->
      let graph = graph_of trans_with_error in
      (* a start location no transition mentions is a vertex too: a run from
         it ends at once, and the encoding asks for its live variables *)
      G.add_vertex graph s;
      let cfa =
        Common.PhaseTime.with_phase "lts-simplify" @@ fun () ->
        let buchi = Set.Poly.of_list (Option.value b ~default:[]) in
        simplify ~print (fun v -> String.(s = v) || Set.mem buchi v) graph
      in
      let live_vars =
        Common.PhaseTime.with_phase "live-vars" @@ fun () ->
        LiveVariables.analyze (fun _ -> Set.Poly.empty) cfa
      in
      let cut_points =
        Common.PhaseTime.with_phase "cut-points" @@ fun () ->
        match cut_point_choice with
        | Graph_order -> cut_points_of (G.copy cfa) Set.Poly.empty
        | Loop_heads ->
            cut_points_of ~choice:Loop_heads ~start:s
              ~rank:(rank_of trans_with_error s) (G.copy cfa) Set.Poly.empty
      in
      let lts' = (Some s, types, e, c, of_graph cfa, b) in
      print @@ lazy (sprintf "simplified LTS:\n%s" @@ str_of_lts lts');
      print
      @@ lazy
           (sprintf "cut points%s: %s"
              (match cut_point_choice with
              | Graph_order -> ""
              | Loop_heads -> " (loop heads)")
           @@ String.concat_set ~sep:", " cut_points);
      (live_vars, cut_points, lts')
