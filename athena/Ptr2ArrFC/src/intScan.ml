(* The scan behind --integers=auto: before the reductions of --wrap-integers
   are placed, look once at the whole program and decide
   - whether a consumer reading integers as mathematical integers can take it
     (every bitwise operation of a form that reading writes exactly), or it
     must be read at fixed width;
   - for each integer expression, an interval of its exact (mathematical)
     value, from which the reduction pass leaves out a reduction that cannot
     change the value.

   The ranges come from Frama-C's value analysis (Eva), a sound
   over-approximation of the program's C executions without undefined
   behaviour. An expression's interval is computed here over the integers
   from its leaves' ranges, never from Eva's value of the whole expression,
   which is the wrapped C value. A leaf counts only when every value Eva gives
   it lies in [0, 2^(w-1)) for its width w: a consumer that holds a width-w
   value as any integer congruent to it in [-2^(w-1), 2^w), as the direct
   LLVM translation's integer mode does, then holds exactly the C value, so
   a sum or product of such leaves is the same integer in C's mathematical
   reading and in the consumer. Eva's own unsigned-overflow alarms are not
   used: after an alarm Eva keeps only the executions that did not overflow,
   and later ranges would miss the ones that did.

   Eva is not used, and no interval is given, when its results are not a
   sound cover of the program: a recursive call (Eva reads a recursive
   function past its unrolling through an incomplete generated specification
   and loses the globals it writes), an error Eva reports, an analysis that
   does not finish, or no main function.

   Contract: [run ~eva ()] reads the current project, which must be the
   program the reduction pass will rewrite, and changes nothing in it; the
   intervals are keyed by the expressions' ids, which the reduction pass sees
   on the original expressions it visits. *)

open Cil_types

type reading = Int | Bv

type t = {
  reading : reading;
  eva : string;  (** [used], [off], or [fallback:<reason>] *)
  intervals : (int, Z.t * Z.t) Hashtbl.t;
      (** expression id -> interval of its exact value, when known *)
  rescued : (int, Z.t) Hashtbl.t;
      (** operand id -> the one value Eva gives it, where a bitwise operation
          is writable only with that operand constant *)
  bv_sites : (string * string * string) list;
      (** location, operation, why a mathematical reading cannot write it *)
  mutable kept : int;  (** reductions placed as __p2a_wrap_ *)
  mutable nonneg : int;  (** reductions placed as __p2a_wrapnn_ *)
  mutable elided : (string * string) list;  (** location and rule, reversed *)
  mutable ext_elided : int;  (** nondet results not reduced *)
}

let pow2 n = Z.shift_left Z.one n

let width_signed t =
  match Ast_types.unroll_node t with
  | TInt ik -> Some (Cil.bitsSizeOfInt ik, Cil.isSigned ik)
  | TEnum ei -> Some (Cil.bitsSizeOfInt ei.ekind, Cil.isSigned ei.ekind)
  | _ -> None

let loc_string loc = Format.asprintf "%a" Fileloc.pretty loc

(* Every statement of a function, including those the passes before this one
   added after the front end computed [sallstmts]. *)
let statements fd =
  let out = ref [] in
  let v =
    object
      inherit Visitor.frama_c_inplace
      method! vstmt s = out := s :: !out; Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacFunction v fd);
  List.rev !out

(* -- When Eva's results are not a sound cover ------------------------- *)

(* A cycle in the graph of direct calls among defined functions. Calls
   through function pointers are gone by the time this runs (they became
   direct calls of the address-taken functions). *)
let has_recursion () =
  let calls = Hashtbl.create 16 in
  Globals.Functions.iter (fun kf ->
      if Kernel_function.is_definition kf then begin
        let fd = Kernel_function.get_definition kf in
        let out = ref [] in
        let v =
          object
            inherit Visitor.frama_c_inplace
            method! vinst = function
              | Call (_, Var f, _, _)
              | Local_init (_, ConsInit (f, _, _), _) ->
                  out := f.vname :: !out;
                  Cil.SkipChildren
              | _ -> Cil.SkipChildren
          end
        in
        ignore (Visitor.visitFramacFunction v fd);
        Hashtbl.replace calls fd.svar.vname !out
      end);
  let state = Hashtbl.create 16 in
  let rec visit f =
    match Hashtbl.find_opt state f with
    | Some `Active -> true
    | Some `Done -> false
    | None ->
        Hashtbl.replace state f `Active;
        let r = List.exists visit (Option.value ~default:[] (Hashtbl.find_opt calls f)) in
        Hashtbl.replace state f `Done;
        r
  in
  Hashtbl.fold (fun f _ acc -> acc || visit f) calls false

let eva_errors = ref 0

let () =
  Log.add_listener ~plugin:"eva" ~kind:[ Log.Error; Log.Failure ] (fun _ -> incr eva_errors)

(* Run Eva, or say why its results cannot be used. *)
let compute_eva () =
  if not (Globals.Functions.mem_name "main") then Error "no-main"
  else if has_recursion () then Error "recursion"
  else begin
    (* the passes before this one rewrote function bodies in place without
       recomputing their control-flow graphs, which Eva follows *)
    Globals.Functions.iter (fun kf ->
        if Kernel_function.is_definition kf then begin
          let fd = Kernel_function.get_definition kf in
          Cfg.clearCFGinfo ~clear_id:false fd;
          Cfg.cfgFun fd
        end);
    Eva.Parameters.Precision.set 5;
    eva_errors := 0;
    (* An error Eva reports is deferred by Frama-C to the end of the run,
       which it would then fail; raising it here, where it is caught, takes
       it off the run's record: such an input is transformed without Eva. *)
    let deferred () =
      match Log.treat_deferred_error () with
      | () -> false
      | exception (Log.AbortError _ | Log.AbortFatal _) -> true
    in
    match Eva.Analysis.compute () with
    | exception (Sys.Break | Out_of_memory | Stack_overflow as e) -> raise e
    | exception _ -> ignore (deferred ()); Error "eva-crash"
    | () -> (
        let deferred = deferred () in
        match Eva.Analysis.current_computation_state () with
        | Computed when !eva_errors = 0 && not deferred -> Ok ()
        | Computed -> Error "eva-error"
        | _ -> Error "eva-unfinished")
  end

(* The code annotations present now, to tell apart afterwards those Eva adds
   (its alarms, as assertions), which must not reach the output. *)
let annotations () =
  let l = ref [] in
  Annotations.iter_all_code_annot (fun stmt e ca -> l := (stmt, e, ca) :: !l);
  !l

let remove_added before =
  let old = Hashtbl.create 16 in
  List.iter (fun (_, _, (ca : code_annotation)) -> Hashtbl.replace old ca.annot_id ()) before;
  List.iter
    (fun (stmt, e, (ca : code_annotation)) ->
      if not (Hashtbl.mem old ca.annot_id) then Annotations.remove_code_annot e stmt ca)
    (annotations ())

(* -- Intervals ------------------------------------------------------- *)

let ival_at stmt e =
  match Eva.Results.(before stmt |> eval_exp e |> as_ival) with
  | Ok iv when not (Ival.is_bottom iv) -> (
      match Ival.min_and_max iv with Some lo, Some hi -> Some (lo, hi) | _ -> None)
  | _ -> None
  | exception _ -> None

(* The one value Eva gives [e] before [stmt], if there is one. *)
let singleton stmt e =
  match ival_at stmt e with Some (lo, hi) when Z.equal lo hi -> Some lo | _ -> None

(* A leaf's interval, when its C values all lie in [0, 2^(w-1)). *)
let leaf stmt e =
  match width_signed (Cil.typeOf e) with
  | None -> None
  | Some (w, _) -> (
      let iv =
        match Cil.constFoldToInt e with Some z -> Some (z, z) | None -> ival_at stmt e
      in
      match iv with
      | Some (lo, hi) when Z.geq lo Z.zero && Z.lt hi (pow2 (w - 1)) -> Some (lo, hi)
      | _ -> None)

let add (a, b) (c, d) = (Z.add a c, Z.add b d)
let sub (a, b) (c, d) = (Z.sub a d, Z.sub b c)

let mul (a, b) (c, d) =
  let ps = [ Z.mul a c; Z.mul a d; Z.mul b c; Z.mul b d ] in
  (List.fold_left Z.min (List.hd ps) ps, List.fold_left Z.max (List.hd ps) ps)

let both f x y = match (x, y) with Some x, Some y -> Some (f x y) | _ -> None

(* The interval of [e]'s exact value before [stmt], recording every
   subexpression's in [tbl]. A ring operation (+, -, *, unary -, << by one
   count) combines its operands'; anything else is a leaf. *)
let rec interval tbl stmt e =
  let r =
    match e.enode with
    | BinOp (PlusA, a, b, _) -> both add (interval tbl stmt a) (interval tbl stmt b)
    | BinOp (MinusA, a, b, _) -> both sub (interval tbl stmt a) (interval tbl stmt b)
    | BinOp (Mult, a, b, _) -> both mul (interval tbl stmt a) (interval tbl stmt b)
    | UnOp (Neg, a, _) -> Option.map (fun (lo, hi) -> (Z.neg hi, Z.neg lo)) (interval tbl stmt a)
    | BinOp (Shiftlt, a, b, _) -> (
        let x = interval tbl stmt a in
        match singleton stmt b with
        | Some k when Z.geq k Z.zero && Z.lt k (Z.of_int 64) -> Option.map (mul (pow2 (Z.to_int k), pow2 (Z.to_int k))) x
        | _ -> None)
    | _ -> leaf stmt e
  in
  (match r with Some iv -> Hashtbl.replace tbl e.eid iv | None -> ());
  r

(* -- Bitwise operations ---------------------------------------------- *)

(* The forms of the direct LLVM translation's integer mode: ~x, & with 0,
   with all bits set, or with a mask of the low or the high bits, | with 0,
   ^ with all bits set (that is ~), and a shift by a constant count.
   [const] gives an operand's constant, written or rescued. *)
let classify_bitwise ~const e =
  let w = match width_signed (Cil.typeOf e) with Some (w, _) -> w | None -> 64 in
  let norm z = Z.erem z (pow2 w) in
  let low_or_high c =
    let c = norm c in
    Z.equal c Z.zero || Z.equal c (Z.pred (pow2 w))
    || Z.equal (Z.logand c (Z.succ c)) Z.zero
    || Z.equal (Z.logand (Z.sub (pow2 w) c) (Z.pred (Z.sub (pow2 w) c))) Z.zero
  in
  let either a b f = match (const a, const b) with Some c, _ | _, Some c -> f c | None, None -> false in
  match e.enode with
  | UnOp (BNot, _, _) -> `Ok
  | BinOp (BAnd, a, b, _) -> if either a b low_or_high then `Ok else `Bv "an & other than with 0 or a mask of low or high bits"
  | BinOp (BOr, a, b, _) -> if either a b (fun c -> Z.equal (norm c) Z.zero) then `Ok else `Bv "a | other than with 0"
  | BinOp (BXor, a, b, _) ->
      if either a b (fun c -> Z.equal (norm c) (Z.pred (pow2 w))) then `Ok else `Bv "a ^ other than with all bits set"
  | BinOp ((Shiftlt | Shiftrt), _, b, _) -> if const b <> None then `Ok else `Bv "a shift by a variable count"
  | _ -> `Not_bitwise

(* -- The scan -------------------------------------------------------- *)

(* The last scan's result, for the record. *)
let last : t option ref = ref None

let run ~eva () =
  let before = annotations () in
  let eva_status = if not eva then Error "off" else compute_eva () in
  let use_eva = Result.is_ok eva_status in
  let intervals = Hashtbl.create 64 and rescued = Hashtbl.create 8 in
  let bv = ref [] in
  let scan_exp stmt e =
    let reachable = use_eva && Eva.Results.is_reachable stmt in
    let v =
      object
        inherit Visitor.frama_c_inplace

        method! vexpr e =
          (if reachable && width_signed (Cil.typeOf e) <> None then ignore (interval intervals stmt e));
          let const a =
            match Cil.constFoldToInt a with
            | Some z -> Some z
            | None when reachable -> (
                match singleton stmt a with
                | Some z ->
                    Hashtbl.replace rescued a.eid z;
                    Some z
                | None -> None)
            | None -> None
          in
          (match classify_bitwise ~const e with
          | `Bv why ->
              let op = match e.enode with UnOp _ -> "~" | BinOp (op, _, _, _) -> Format.asprintf "%a" Printer.pp_binop op | _ -> "?" in
              bv := (loc_string e.eloc, op, why) :: !bv
          | `Ok | `Not_bitwise -> ());
          Cil.DoChildren

        (* a bit-field read or written through a typed object: clang masks
           it with constants that are not masks of low or high bits *)
        method! voffs = function
          | Field ({ fbitfield = Some _; _ }, _) ->
              bv := (loc_string (Cil_datatype.Stmt.loc stmt), "bit-field", "a bit-field access") :: !bv;
              Cil.DoChildren
          | _ -> Cil.DoChildren
      end
    in
    ignore (Visitor.visitFramacExpr v e)
  in
  let scan_lval stmt lv =
    let v =
      object
        inherit Visitor.frama_c_inplace
        method! vexpr e = scan_exp stmt e; Cil.SkipChildren
        method! voffs = function
          | Field ({ fbitfield = Some _; _ }, _) ->
              bv := (loc_string (Cil_datatype.Stmt.loc stmt), "bit-field", "a bit-field access") :: !bv;
              Cil.DoChildren
          | _ -> Cil.DoChildren
      end
    in
    ignore (Visitor.visitFramacLval v lv)
  in
  Globals.Functions.iter (fun kf ->
      if Kernel_function.is_definition kf then
        List.iter
          (fun stmt ->
            match stmt.skind with
            | Instr (Set (lv, e, _)) -> scan_lval stmt lv; scan_exp stmt e
            | Instr (Call (lv, _, args, _)) ->
                Option.iter (scan_lval stmt) lv;
                List.iter (scan_exp stmt) args
            | Instr (Local_init (_, AssignInit i, _)) ->
                let rec init = function
                  | SingleInit e -> scan_exp stmt e
                  | CompoundInit (_, l) -> List.iter (fun (_, i) -> init i) l
                in
                init i
            | Instr (Local_init (_, ConsInit (_, args, _), _)) -> List.iter (scan_exp stmt) args
            | Return (Some e, _) | If (e, _, _, _) | Switch (e, _, _, _) -> scan_exp stmt e
            | _ -> ())
          (statements (Kernel_function.get_definition kf)));
  remove_added before;
  let bv_sites = List.rev !bv in
  {
    reading = (if bv_sites = [] then Int else Bv);
    eva = (match eva_status with Ok () -> "used" | Error "off" -> "off" | Error r -> "fallback:" ^ r);
    intervals = (if use_eva then intervals else Hashtbl.create 1);
    rescued = (if use_eva then rescued else Hashtbl.create 1);
    bv_sites;
    kept = 0;
    nonneg = 0;
    elided = [];
    ext_elided = 0;
  }

let to_json t =
  `Assoc
    [ ("reading", `String (match t.reading with Int -> "int" | Bv -> "bv"));
      ("eva", `String t.eva);
      ( "bv_sites",
        `List
          (List.map
             (fun (loc, op, why) ->
               `Assoc [ ("location", `String loc); ("operation", `String op); ("reason", `String why) ])
             t.bv_sites) );
      ( "wraps",
        `Assoc
          [ ("kept", `Int t.kept);
            ("nonneg", `Int t.nonneg);
            ( "elided",
              `List
                (List.rev_map
                   (fun (loc, rule) -> `Assoc [ ("location", `String loc); ("rule", `String rule) ])
                   t.elided) );
            ("ext_elided", `Int t.ext_elided) ] );
      ("rescued", `Int (Hashtbl.length t.rescued)) ]
