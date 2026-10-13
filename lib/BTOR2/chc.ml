open Core
open Ast
open Ast.LogicOld
open Problem

(* The translation of a BTOR2 safety question into constrained Horn clauses over one predicate
   [INV] on the state variables:

     (1)  Init(s)                          => INV(s)
     (2)  INV(s) /\ Cons(s,i) /\ T(s,i,s')  => INV(s')
     (3)  INV(s) /\ Cons(s,i) /\ Bad(s,i)   => false

   The system is unsatisfiable iff some trace reaches a bad state while every constraint holds at
   every time up to and including that of the bad state. [Cons] is left out of (1) and of the
   successor in (2): a state at which no input satisfies the constraints may enter [INV], but no
   clause continues from it, since (2) and (3) require [Cons] of the state they start from; so the
   answer, and every refutation read back as a trace, are those of the clauses that do require it.

   Bit-vectors keep their width, a value of width 1 stays a bit-vector, and arrays become SMT
   arrays. The operators follow SMT-LIB's FixedSizeBitVectors where SMT-LIB defines them; the
   overflow predicates are written with operators [T_bv] has, each computing the exact result in a
   wider bit-vector, where it cannot wrap, and asking whether it fits; rotation by a value, which
   SMT-LIB's indexed rotation cannot express, is the reference simulator's definition. *)

exception Unsupported of string

let rec sort_of_btor = function
  | Bitvec w -> T_bv.SBV (Some w)
  | Array (i, e) -> T_array.SArray (sort_of_btor i, sort_of_btor e)

let width = function Bitvec w -> w | Array _ -> assert false
let bv w z = T_bv.mk_bvnum ~size:(Some w) Z.(erem z (shift_left one w))
let bit1 = bv 1 Z.one
let bit0 = bv 1 Z.zero

(* a formula as a value of width 1, and back; the two compositions are identities, so the pair is
   cancelled where it meets, which keeps a comparison used as a condition a formula *)
let b2bv phi =
  match phi with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t; one ], _), _)
    when Stdlib.(one = bit1) ->
      (* an equation with [#b1] is between two terms of width 1; asking [t] its sort instead
         would walk the term as a tree, which a circuit's shared subterms make exponential *)
      t
  | _ -> T_bool.mk_if_then_else (T_bool.of_formula phi) bit1 bit0

let is1 t =
  match t with
  | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _)
    when Stdlib.(a = bit1) && Stdlib.(b = bit0) -> (
      match c with
      | Term.FunApp (T_bool.Formula phi, [], _) -> phi
      | _ -> Formula.eq c (T_bool.mk_true ()))
  | _ -> Formula.eq t bit1

let state_var id = Ident.Tvar (sprintf "s%d" id)
let next_var id = Ident.Tvar (sprintf "sn%d" id)
let input_var id = Ident.Tvar (sprintf "i%d" id)
let inv = Ident.Pvar "INV"

(* the exact result of [op] on [m]-bit [x] and [y], computed in [m + k] bits after extending both
   operands by [k] with [ext] *)
let wide ~m ~k ext op x y =
  let e t =
    match ext with
    | `Z -> T_bv.mk_bvzext ~size:(Some m) k t
    | `S -> T_bv.mk_bvsext ~size:(Some m) k t
  in
  op (Some (m + k)) (e x) (e y)

let add size a b = T_bv.mk_bvadd ~size a b
let sub size a b = T_bv.mk_bvsub ~size a b
let mul size a b = T_bv.mk_bvmul ~size a b

(* a value [v] of the signed range of [n] bits is in the signed range of [m < n] bits iff bits
   [n-1] down to [m-1] of its encoding are all equal *)
let fits_signed ~n ~m v =
  let hi = T_bv.mk_bvextract ~size:(Some n) (n - 1) (m - 1) v in
  let k = n - m + 1 in
  Formula.or_of [ Formula.eq hi (bv k Z.zero); Formula.eq hi (bv k Z.(pred (shift_left one k))) ]

let overflow tag m x y =
  match tag with
  | Uaddo ->
      T_bv.mk_bvextract ~size:(Some (m + 1)) m m (wide ~m ~k:1 `Z add x y)
  | Saddo ->
      b2bv @@ Formula.mk_neg
      @@ fits_signed ~n:(m + 1) ~m (wide ~m ~k:1 `S add x y)
  | Usubo -> b2bv @@ Formula.mk_atom @@ T_bv.mk_bvlt ~size:(Some m) ~signed:(Some false) x y
  | Ssubo ->
      b2bv @@ Formula.mk_neg
      @@ fits_signed ~n:(m + 1) ~m (wide ~m ~k:1 `S sub x y)
  | Umulo ->
      let p = wide ~m ~k:m `Z mul x y in
      b2bv @@ Formula.mk_neg
      @@ Formula.eq (T_bv.mk_bvextract ~size:(Some (2 * m)) ((2 * m) - 1) m p) (bv m Z.zero)
  | Smulo ->
      b2bv @@ Formula.mk_neg
      @@ fits_signed ~n:(2 * m) ~m (wide ~m ~k:m `S mul x y)
  | Sdivo ->
      b2bv
      @@ Formula.and_of
           [
             Formula.eq x (bv m (Z.shift_left Z.one (m - 1)));
             Formula.eq y (bv m Z.(pred (shift_left one m)));
           ]
  | _ -> assert false

(* rotation by the value of [y], as the reference simulator defines it: with r = y mod m,
   (x << r) | (x >> (m - r)); the second shift is by m, hence 0, when r = 0 *)
let rotate ~left m x y =
  let size = Some m in
  let wv = bv m (Z.of_int m) in
  let r = T_bv.mk_bvrem ~size ~signed:(Some false) y wv in
  let r' = T_bv.mk_bvsub ~size wv r in
  let sh1, sh2 = if left then (T_bv.mk_bvshl, T_bv.mk_bvlshr) else (T_bv.mk_bvlshr, T_bv.mk_bvshl) in
  T_bv.mk_bvor ~size (sh1 ~size x r) (sh2 ~size x r')

let literal (n : node) =
  let c = Option.value_exn n.cst in
  match n.tag with
  | Const -> Z.of_string_base 2 c
  | Constd -> Z.of_string c
  | Consth -> Z.of_string_base 16 c
  | _ -> assert false

let let_var id = Ident.Tvar (sprintf "l%d" id)

let is_leaf = function
  | Input | State | Const | Constd | Consth | Zero | One | Ones -> true
  | _ -> false

(* The value of a node over constant operands, as the reference simulator computes it, for the
   operators whose definition is a line of arithmetic; [None] leaves the node to the solver. Values
   are the unsigned residues modulo [2^w]. *)
let fold_const (n : node) ~w ~aw (vs : Z.t list) =
  let open Z in
  let mask k = pred (shift_left one k) in
  let md k v = erem v (shift_left one k) in
  let signed k v = if testbit v (Int.pred k) then v - shift_left one k else v in
  let bool b = Some (if b then one else zero) in
  let shift f = function
    | [ x; s ] -> Some (if geq s (of_int w) then zero else md w (f x (to_int s)))
    | _ -> None
  in
  match (n.tag, vs) with
  | Not, [ x ] -> Some (logxor x (mask w))
  | Neg, [ x ] -> Some (md w (neg x))
  | Inc, [ x ] -> Some (md w (succ x))
  | Dec, [ x ] -> Some (md w (pred x))
  | Redand, [ x ] -> bool (equal x (mask (aw 0)))
  | Redor, [ x ] -> bool (not (equal x zero))
  | Redxor, [ x ] -> Some (logand (of_int (popcount x)) one)
  | Slice, [ x ] -> (
      match n.imm with [ _; l ] -> Some (md w (shift_right x l)) | _ -> None)
  | Uext, [ x ] -> Some x
  | Sext, [ x ] -> Some (md w (signed (aw 0) x))
  | Add, [ x; y ] -> Some (md w (x + y))
  | Sub, [ x; y ] -> Some (md w (x - y))
  | Mul, [ x; y ] -> Some (md w (x * y))
  | And, [ x; y ] -> Some (logand x y)
  | Or, [ x; y ] -> Some (logor x y)
  | Xor, [ x; y ] -> Some (logxor x y)
  | Nand, [ x; y ] -> Some (logxor (logand x y) (mask w))
  | Nor, [ x; y ] -> Some (logxor (logor x y) (mask w))
  | Xnor, [ x; y ] -> Some (logxor (logxor x y) (mask w))
  | Sll, _ -> shift shift_left vs
  | Srl, _ -> shift shift_right vs
  | Concat, [ x; y ] -> Some (logor (shift_left x (aw 1)) y)
  | Eq, [ x; y ] -> bool (equal x y)
  | Neq, [ x; y ] -> bool (not (equal x y))
  | Ult, [ x; y ] -> bool (lt x y)
  | Ulte, [ x; y ] -> bool (leq x y)
  | Ugt, [ x; y ] -> bool (gt x y)
  | Ugte, [ x; y ] -> bool (geq x y)
  | Slt, [ x; y ] -> bool (lt (signed (aw 0) x) (signed (aw 0) y))
  | Slte, [ x; y ] -> bool (leq (signed (aw 0) x) (signed (aw 0) y))
  | Sgt, [ x; y ] -> bool (gt (signed (aw 0) x) (signed (aw 0) y))
  | Sgte, [ x; y ] -> bool (geq (signed (aw 0) x) (signed (aw 0) y))
  | Implies, [ x; y ] -> bool (equal x zero || equal y one)
  | Iff, [ x; y ] -> bool (equal x y)
  | _ -> None

(* Each node of [cone] mapped to a representative of its value. Two nodes whose value is the same
   function of the same operands are one node: an operator's value is determined by its tag, its
   sort, its indices and its operands' values, so a node with the same four as an earlier one is
   replaced by that one, operands first represented themselves. A node whose operands are all
   constants is folded to its value ([fold_const]), so constants of one width and value are one
   node too; [not] of a node is that node negated, and an [ite] whose condition is a constant, or
   whose branches are one node, is the branch it selects. Inputs and states are never merged: two
   of them are two variables. Returns the signed representative of a signed id, and the value of
   a representative that is a constant. *)
let canon_of (ts : ts) cone =
  let rep = Hashtbl.create (module Int) in
  let value = Hashtbl.create (module Int) in
  let by_value = Hashtbl.Poly.create () and by_shape = Hashtbl.Poly.create () in
  let canon id =
    let r = Option.value (Hashtbl.find rep (Int.abs id)) ~default:(Int.abs id) in
    if id < 0 then -r else r
  in
  let width_of id = match sort_of ts.model id with Bitvec w -> Some w | Array _ -> None in
  (* the value of a signed representative, if it is a constant *)
  let value_of sid =
    Option.bind (Hashtbl.find value (Int.abs sid)) ~f:(fun v ->
        if sid >= 0 then Some v
        else
          Option.map (width_of sid) ~f:(fun w -> Z.(logxor v (pred (shift_left one w)))))
  in
  let constant id w v =
    match Hashtbl.find by_value (w, Z.to_string v) with
    | Some r -> Hashtbl.set rep ~key:id ~data:r
    | None ->
        Hashtbl.set by_value ~key:(w, Z.to_string v) ~data:id;
        Hashtbl.set value ~key:id ~data:v
  in
  List.iter ts.model.order ~f:(fun id ->
      if Hash_set.mem cone id then
        let n = find ts.model id in
        match n.tag with
        | Init | Next | Bad | Constraint | Fair | Justice | Output | Sort_decl | Input | State
          ->
            ()
        | Const | Constd | Consth | Zero | One | Ones -> (
            match n.nsort with
            | Some (Bitvec w) ->
                let v =
                  match n.tag with
                  | Zero -> Z.zero
                  | One -> Z.one
                  | Ones -> Z.(pred (shift_left one w))
                  | _ -> literal n
                in
                constant id w Z.(erem v (shift_left one w))
            | _ -> ())
        | _ -> (
            let args = List.map n.args ~f:canon in
            let alias r = Hashtbl.set rep ~key:id ~data:r in
            let vs = List.map args ~f:value_of in
            let w = width_of id in
            let folded =
              match w with
              | Some w when List.for_all vs ~f:Option.is_some ->
                  let aw i = Option.value_exn (width_of (List.nth_exn n.args i)) in
                  fold_const n ~w ~aw (List.filter_opt vs)
              | _ -> None
            in
            match (folded, n.tag, args, vs) with
            | Some v, _, _, _ -> constant id (Option.value_exn w) v
            | None, Not, [ a ], _ -> alias (-a)
            | None, Ite, [ _; a; b ], Some c :: _ -> alias (if Z.equal c Z.zero then b else a)
            | None, Ite, [ _; a; b ], _ when a = b -> alias a
            | None, _, _, _ -> (
                let key = (n.tag, n.nsort, args, n.imm) in
                match Hashtbl.find by_shape key with
                | Some r -> alias r
                | None -> Hashtbl.set by_shape ~key ~data:id)));
  (canon, Hashtbl.find value)

(* The term of every node in [cone], at the current time. A circuit shares subterms, and every
   traversal in this code base walks a term as a tree, so a node read more than once is bound by a
   [let] and referred to by its variable; the rest are inlined, each in the one place that reads
   it. [roots] are the nodes the clauses read directly. Returns the term of a (signed) node, and
   for a list of nodes the [let] bindings their terms need, outermost first. *)
let terms_of (ts : ts) cone ~roots =
  let canon, value = canon_of ts cone in
  (* a representative that is not a constant has a term built from its operands *)
  let built id = canon id = id && Option.is_none (value id) in
  let reads = Hashtbl.create (module Int) in
  let read id =
    Hashtbl.update reads (Int.abs (canon id)) ~f:(fun c -> 1 + Option.value c ~default:0)
  in
  List.iter roots ~f:read;
  Hash_set.iter cone ~f:(fun id -> if built id then List.iter (find ts.model id).args ~f:read);
  let shared id =
    built id
    && (not (is_leaf (find ts.model id).tag))
    && Option.value (Hashtbl.find reads id) ~default:0 >= 2
  in
  let env = Hashtbl.create (module Int) in
  (* the shared nodes a node's term mentions, through the nodes inlined in it *)
  let uses = Hashtbl.create (module Int) in
  let ref_of id =
    if shared id then Term.mk_var (let_var id) (sort_of_btor (sort_of ts.model id))
    else Hashtbl.find_exn env id
  in
  let get id =
    let id = canon id in
    let t = ref_of (Int.abs id) in
    if id < 0 then T_bv.mk_bvnot ~size:(Some (width (sort_of ts.model id))) t else t
  in
  let uses_of id =
    let id = Int.abs (canon id) in
    if shared id then [ id ] else Option.value (Hashtbl.find uses id) ~default:[]
  in
  List.iter ts.model.order ~f:(fun id ->
      if Hash_set.mem cone id && canon id = id then
        let n = find ts.model id in
        Hashtbl.set uses ~key:id ~data:(if built id then List.concat_map n.args ~f:uses_of else []);
        let a i = get (List.nth_exn n.args i) in
        let aw i = width (sort_of ts.model (List.nth_exn n.args i)) in
        let self () = Option.value_exn n.nsort in
        let w () = width (self ()) in
        let size () = Some (w ()) in
        let bin f = f (size ()) (a 0) (a 1) in
        let cmp f signed = b2bv @@ Formula.mk_atom @@ f (Some (aw 0)) (Some signed) (a 0) (a 1) in
        let t =
          match (value id, n.tag) with
          | Some v, _ -> Some (bv (w ()) v)
          | None, tag -> (
              match tag with
              | Init | Next | Bad | Constraint | Fair | Justice | Output | Sort_decl -> None
              | Input -> Some (Term.mk_var (input_var id) (sort_of_btor (self ())))
              | State -> Some (Term.mk_var (state_var id) (sort_of_btor (self ())))
              | Const | Constd | Consth -> Some (bv (w ()) (literal n))
              | Zero -> Some (bv (w ()) Z.zero)
              | One -> Some (bv (w ()) Z.one)
              | Ones -> Some (bv (w ()) Z.(pred (shift_left one (w ()))))
              | Not -> Some (T_bv.mk_bvnot ~size:(size ()) (a 0))
              | Neg -> Some (T_bv.mk_bvneg ~size:(size ()) (a 0))
              | Inc -> Some (T_bv.mk_bvadd ~size:(size ()) (a 0) (bv (w ()) Z.one))
              | Dec -> Some (T_bv.mk_bvsub ~size:(size ()) (a 0) (bv (w ()) Z.one))
              | Redand ->
                  Some (b2bv @@ Formula.eq (a 0) (bv (aw 0) Z.(pred (shift_left one (aw 0)))))
              | Redor -> Some (b2bv @@ Formula.mk_neg @@ Formula.eq (a 0) (bv (aw 0) Z.zero))
              | Redxor ->
                  let m = aw 0 in
                  let bit i = T_bv.mk_bvextract ~size:(Some m) i i (a 0) in
                  Some
                    (List.fold (List.range 1 m) ~init:(bit 0) ~f:(fun acc i ->
                         T_bv.mk_bvxor ~size:(Some 1) acc (bit i)))
              | Slice -> (
                  match n.imm with
                  | [ u; l ] -> Some (T_bv.mk_bvextract ~size:(Some (aw 0)) u l (a 0))
                  | _ -> assert false)
              | Uext | Sext -> (
                  match n.imm with
                  | [ 0 ] -> Some (a 0)
                  | [ k ] ->
                      let ext = if equal_tag n.tag Uext then T_bv.mk_bvzext else T_bv.mk_bvsext in
                      Some (ext ~size:(Some (aw 0)) k (a 0))
                  | _ -> assert false)
              | Add -> Some (bin (fun size a b -> T_bv.mk_bvadd ~size a b))
              | Sub -> Some (bin (fun size a b -> T_bv.mk_bvsub ~size a b))
              | Mul -> Some (bin (fun size a b -> T_bv.mk_bvmul ~size a b))
              | And -> Some (bin (fun size a b -> T_bv.mk_bvand ~size a b))
              | Or -> Some (bin (fun size a b -> T_bv.mk_bvor ~size a b))
              | Xor -> Some (bin (fun size a b -> T_bv.mk_bvxor ~size a b))
              | Nand -> Some (bin (fun size a b -> T_bv.mk_bvnand ~size a b))
              | Nor -> Some (bin (fun size a b -> T_bv.mk_bvnor ~size a b))
              | Xnor -> Some (bin (fun size a b -> T_bv.mk_bvxnor ~size a b))
              | Udiv -> Some (T_bv.mk_bvdiv ~size:(size ()) ~signed:(Some false) (a 0) (a 1))
              | Sdiv -> Some (T_bv.mk_bvdiv ~size:(size ()) ~signed:(Some true) (a 0) (a 1))
              | Urem -> Some (T_bv.mk_bvrem ~size:(size ()) ~signed:(Some false) (a 0) (a 1))
              | Srem -> Some (T_bv.mk_bvrem ~size:(size ()) ~signed:(Some true) (a 0) (a 1))
              | Smod -> Some (bin (fun size a b -> T_bv.mk_bvsmod ~size a b))
              | Sll -> Some (bin (fun size a b -> T_bv.mk_bvshl ~size a b))
              | Srl -> Some (bin (fun size a b -> T_bv.mk_bvlshr ~size a b))
              | Sra -> Some (bin (fun size a b -> T_bv.mk_bvashr ~size a b))
              | Rol -> Some (rotate ~left:true (w ()) (a 0) (a 1))
              | Ror -> Some (rotate ~left:false (w ()) (a 0) (a 1))
              | Concat ->
                  Some (T_bv.mk_bvconcat ~size1:(Some (aw 0)) ~size2:(Some (aw 1)) (a 0) (a 1))
              | Ult -> Some (cmp (fun size signed a b -> T_bv.mk_bvlt ~size ~signed a b) false)
              | Ulte -> Some (cmp (fun size signed a b -> T_bv.mk_bvleq ~size ~signed a b) false)
              | Ugt -> Some (cmp (fun size signed a b -> T_bv.mk_bvgt ~size ~signed a b) false)
              | Ugte -> Some (cmp (fun size signed a b -> T_bv.mk_bvgeq ~size ~signed a b) false)
              | Slt -> Some (cmp (fun size signed a b -> T_bv.mk_bvlt ~size ~signed a b) true)
              | Slte -> Some (cmp (fun size signed a b -> T_bv.mk_bvleq ~size ~signed a b) true)
              | Sgt -> Some (cmp (fun size signed a b -> T_bv.mk_bvgt ~size ~signed a b) true)
              | Sgte -> Some (cmp (fun size signed a b -> T_bv.mk_bvgeq ~size ~signed a b) true)
              | Eq -> Some (b2bv @@ Formula.eq (a 0) (a 1))
              | Neq -> Some (b2bv @@ Formula.mk_neg @@ Formula.eq (a 0) (a 1))
              | Implies ->
                  Some (T_bv.mk_bvor ~size:(Some 1) (T_bv.mk_bvnot ~size:(Some 1) (a 0)) (a 1))
              | Iff -> Some (T_bv.mk_bvxnor ~size:(Some 1) (a 0) (a 1))
              | Uaddo | Saddo | Usubo | Ssubo | Umulo | Smulo | Sdivo ->
                  Some (overflow n.tag (aw 0) (a 0) (a 1))
              | Ite -> Some (T_bool.mk_if_then_else (T_bool.of_formula (is1 (a 0))) (a 1) (a 2))
              | Read -> (
                  match sort_of ts.model (List.hd_exn n.args) with
                  | Array (i, e) ->
                      Some (T_array.mk_select (sort_of_btor i) (sort_of_btor e) (a 0) (a 1))
                  | Bitvec _ -> assert false)
              | Write -> (
                  match self () with
                  | Array (i, e) ->
                      Some (T_array.mk_store (sort_of_btor i) (sort_of_btor e) (a 0) (a 1) (a 2))
                  | Bitvec _ -> assert false))
        in
        Option.iter t ~f:(fun t -> Hashtbl.set env ~key:id ~data:t));
  let lets_for ids =
    let need = Hash_set.create (module Int) in
    let rec close = function
      | [] -> ()
      | id :: rest ->
          if Hash_set.mem need id then close rest
          else (
            Hash_set.add need id;
            close (Option.value (Hashtbl.find uses id) ~default:[] @ rest))
    in
    close (List.concat_map ids ~f:uses_of);
    List.filter_map ts.model.order ~f:(fun id ->
        if Hash_set.mem need id then
          Some (let_var id, sort_of_btor (sort_of ts.model id), Hashtbl.find_exn env id)
        else None)
  in
  (get, lets_for)

(** The transition system of the properties [bads] as formulas over the variables [s<id>] (a
    state now), [sn<id>] (the same state next) and [i<id>] (an input now), each formula carrying
    the [let]s its terms need. Only the cone of the properties and the constraints is translated,
    so [states] and [inputs] are the cone's, in file order. *)
type system = {
  cone_states : int list;
  cone_inputs : int list;
  init_f : Formula.t;  (** the registered states' initial values *)
  step_f : Formula.t;  (** the constraints now and every registered state's next value *)
  bad_now : (int * Formula.t) list;
      (** per property, its signed id and the constraints now with that property *)
  bad_any : Formula.t;  (** the constraints now with some property *)
}

let system_of (ts : ts) bads =
  let cone = cone ts (bads @ ts.constraints) in
  let states = List.filter ts.states ~f:(Hash_set.mem cone) in
  let inputs = List.filter ts.inputs ~f:(Hash_set.mem cone) in
  let init_roots =
    List.filter_map states ~f:(fun id ->
        if is_registered ts id then Hashtbl.find ts.init id else None)
  in
  let next_roots = List.filter_map states ~f:(Hashtbl.find ts.next) in
  let term, lets_for =
    terms_of ts cone ~roots:(init_roots @ next_roots @ ts.constraints @ bads)
  in
  let with_lets roots phi =
    List.fold_right (lets_for roots) ~init:phi ~f:(fun (x, s, d) acc ->
        Formula.mk_let_formula x s d acc)
  in
  let ssort id = sort_of_btor (sort_of ts.model id) in
  let senv var ids = List.map ids ~f:(fun id -> (var id, ssort id)) in
  let s_env = senv state_var states and sn_env = senv next_var states in
  let i_env = senv input_var inputs in
  let inv_app env =
    Formula.mk_atom
    @@ Atom.mk_pvar_app inv (List.map env ~f:snd) (List.map env ~f:(fun (x, s) -> Term.mk_var x s))
  in
  let init =
    (* a state without [next] is an input at every time, so its [init] constrains nothing *)
    Formula.and_of
    @@ List.filter_map states ~f:(fun id ->
        if not (is_registered ts id) then None
        else
          Option.map (Hashtbl.find ts.init id) ~f:(fun v ->
              let lhs = Term.mk_var (state_var id) (ssort id) in
              let rhs =
                match (sort_of ts.model id, sort_of ts.model v) with
                | Array (i, e), Bitvec _ ->
                    T_array.mk_const_array (sort_of_btor i) (sort_of_btor e) (term v)
                | _ -> term v
              in
              Formula.eq lhs rhs))
  in
  let trans =
    Formula.and_of
    @@ List.filter_map states ~f:(fun id ->
        Option.map (Hashtbl.find ts.next id) ~f:(fun v ->
            Formula.eq (Term.mk_var (next_var id) (ssort id)) (term v)))
  in
  let cons = Formula.and_of @@ List.map ts.constraints ~f:(fun c -> is1 (term c)) in
  let bad = Formula.or_of @@ List.map bads ~f:(fun b -> is1 (term b)) in
  let clause env body head = Formula.forall env (Formula.mk_imply body head) in
  let clauses =
    [
      clause s_env (with_lets init_roots init) (inv_app s_env);
      clause (s_env @ i_env @ sn_env)
        (with_lets (ts.constraints @ next_roots) (Formula.and_of [ inv_app s_env; cons; trans ]))
        (inv_app sn_env);
      clause (s_env @ i_env)
        (with_lets (ts.constraints @ bads) (Formula.and_of [ inv_app s_env; cons; bad ]))
        (Formula.mk_false ());
    ]
  in
  let system =
    {
      cone_states = states;
      cone_inputs = inputs;
      init_f = with_lets init_roots init;
      step_f = with_lets (ts.constraints @ next_roots) (Formula.and_of [ cons; trans ]);
      bad_now =
        List.map bads ~f:(fun b ->
            (b, with_lets (ts.constraints @ [ b ]) (Formula.and_of [ cons; is1 (term b) ])));
      bad_any = with_lets (ts.constraints @ bads) (Formula.and_of [ cons; bad ]);
    }
  in
  (clauses, List.map s_env ~f:snd, system)

(* The clauses for the properties [bads], read as one: the system is unsatisfiable iff some trace
   reaches one of them. *)
let clauses_of (ts : ts) bads =
  let clauses, sorts, _ = system_of ts bads in
  (clauses, sorts)

(* The size of a clause as a solver that names subterms sees it: the [let] bindings, and the
   compound subterm occurrences with a [let]-bound variable read as a leaf. Each definition is
   walked once, so this is linear in the clause as built. A diagnostic only. *)
let size_up_to_lets phi =
  let lets = ref 0 and apps = ref 0 in
  let rec term = function
    | Term.Var _ -> ()
    | Term.FunApp (T_bool.Formula phi, [], _) -> formula phi
    | Term.FunApp (_, args, _) ->
        if not (List.is_empty args) then incr apps;
        List.iter args ~f:term
    | Term.LetTerm (_, _, def, body, _) ->
        incr lets;
        term def;
        term body
  and atom = function
    | Atom.True _ | Atom.False _ -> ()
    | Atom.App (_, args, _) ->
        incr apps;
        List.iter args ~f:term
  and formula = function
    | Formula.Atom (a, _) -> atom a
    | Formula.UnaryOp (_, phi, _) | Formula.Bind (_, _, phi, _) -> formula phi
    | Formula.BinaryOp (_, phi, psi, _) ->
        formula phi;
        formula psi
    | Formula.LetRec (_, phi, _) -> formula phi
    | Formula.LetFormula (_, _, def, body, _) ->
        incr lets;
        term def;
        formula body
  in
  formula phi;
  (!lets, !apps)

(** The constraint problem of the properties [bads] of a model, by default all of them at once.
    A model without a property asks nothing, and is refused rather than answered. *)
let pcsp_of ?(print = fun _ -> ()) ?bads (ts : ts) =
  let bads = Option.value bads ~default:ts.bads in
  if not (List.is_empty ts.justices) then
    raise
      (Unsupported
         "the model has a justice property, which asks for an infinite trace; reachability \
          cannot express it");
  if List.is_empty bads then raise (Unsupported "the model has no bad property");
  if List.is_empty ts.justices && not (List.is_empty ts.fairs) then
    print @@ lazy "BTOR2: fairness constraints without a justice property are ignored";
  let phis, sorts = clauses_of ts bads in
  (* the treatment the SMT-LIB reader gives a CHC file's assertions, so that a model reaches the
     solvers in the same shape as its printed CHC read back; no [let] here mentions an unknown,
     so every one is kept *)
  let phis =
    List.map phis ~f:(fun phi ->
        Normalizer.normalize
        @@ Formula.elim_let_with_unknowns (Set.Poly.singleton (Ident.pvar_to_tvar inv))
        @@ Normalizer.normalize_let ~rename:true phi)
  in
  print
  @@ lazy
       (String.concat ~sep:"\n"
       @@ List.mapi phis ~f:(fun i phi ->
           let lets, apps = size_up_to_lets phi in
           sprintf "BTOR2: clause %d: %d lets, %d compound occurrences" i lets apps));
  let envs =
    {
      SMT.Problem.decl_reading = SMT.Problem.Synthesize;
      uni_sort = Set.Poly.empty;
      uni_senv = Map.Poly.empty;
      exi_senv =
        Map.Poly.singleton (Ident.pvar_to_tvar inv) (Sort.mk_fun (sorts @ [ T_bool.SBool ]));
      dep_map = Map.Poly.empty;
      kind_map = Map.Poly.singleton (Ident.pvar_to_tvar inv) Kind.Ord;
      fenv = Map.Poly.empty;
      dtenv = Map.Poly.empty;
      candidates = Map.Poly.empty;
    }
  in
  PCSP.Problem.make ~skolem_pred:true phis envs
