open Core
open Common.Ext

type t =
  | Bool of bool
  | Int of Z.t
  | Real of Q.t
  | BV of int option * Z.t
  | Arr of t (*dummy index*) * t * (t, t) Map.Poly.t
  | TupleCons of t list
  | DTCons of string * t list (*dummy params*) * t list
  | Seq of t (*dummy element*) * t list
      (** A finite sequence, listed from index 0. The dummy element is carried
          for the same reason an array value carries a dummy index: an empty
          sequence has no element to read its element sort off, and turning the
          value back into a term needs that sort. A read at an index that is
          negative or not below the length is NOT a value of this type: the
          theory leaves such a read open, fixed within one model and different
          across models, so nothing here answers it. *)

let rec str_of = function
  | Bool b -> string_of_bool b
  | Int n -> Z.to_string n
  | Real r -> Q.to_string r
  | BV (_, bv) -> Z.format "0b%b" bv
  | Arr (_, v, m) ->
      let entries =
        List.map (Map.Poly.to_alist m) ~f:(fun (k, v) ->
            str_of k ^ " |-> " ^ str_of v)
        @ [ "_ |-> " ^ str_of v ]
      in
      "{" ^ String.concat ~sep:", " entries ^ "}"
  | TupleCons vs -> "(" ^ String.concat ~sep:", " (List.map vs ~f:str_of) ^ ")"
  | DTCons (name, _pvs, vs) ->
      name ^ "(" ^ String.concat ~sep:", " (List.map vs ~f:str_of) ^ ")"
  | Seq (_, vs) -> "[" ^ String.concat ~sep:"; " (List.map vs ~f:str_of) ^ "]"

let is_true = function Bool b -> b | _ -> false
let is_false = function Bool b -> not b | _ -> false

let ite cond_ then_ else_ =
  match cond_ with
  | Bool true -> then_
  | Bool false -> else_
  | _ -> failwith "[Value.ite] type error"

let bool_of = function
  | Bool b -> b
  | _ -> failwith "[Value.bool_of] type error"

let int_of = function Int i -> i | _ -> failwith "[Value.int_of] type error"

let real_of = function
  | Real r -> r
  | _ -> failwith "[Value.real_of] type error"

let bv_of = function
  | BV (size, bits) -> (size, bits)
  | _ -> failwith "[Value.real_of] type error"

let cast_real_of = function
  | Int i -> Q.of_bigint i
  | Real r -> r
  | _ -> failwith "[Value.cast_real_of] type error"

let rec compare pos opi opr ?(opb = fun _ _ -> assert false) t1 t2 =
  match (t1, t2) with
  | Bool b1, Bool b2 -> opb b1 b2
  | Int i1, Int i2 -> opi i1 i2
  | Real r1, Real r2 -> opr r1 r2
  | Int i, Real r -> opr (Q.of_bigint i) r
  | Real r, Int i -> opr r (Q.of_bigint i)
  | BV (Some s1, bits1), BV (Some s2, bits2) when s1 = s2 -> opi bits1 bits2
  | Arr (_, default1, m1), Arr (_, default2, m2) ->
      (if pos then ( && ) else ( || ))
        (compare pos opi opr ~opb default1 default2)
        (let keys = Set.union (Map.Poly.key_set m1) (Map.Poly.key_set m2) in
         let f k =
           (* An index that only one of the two stores mentions still HAS a
              value in the other one -- its default -- so the pair to compare is
              the stored value against that default.  Reporting [false] for such
              an index is right for equality by accident and wrong for
              disequality: it says the two arrays agree at exactly the indices
              where one of them was written, which is how two arrays differing
              at one index were reported equal. *)
           match (Map.Poly.find m1 k, Map.Poly.find m2 k) with
           | Some x1, Some x2 -> compare pos opi opr ~opb x1 x2
           | Some x1, None -> compare pos opi opr ~opb x1 default2
           | None, Some x2 -> compare pos opi opr ~opb default1 x2
           | None, None -> compare pos opi opr ~opb default1 default2
         in
         if pos then Set.for_all keys ~f else Set.exists keys ~f)
  | TupleCons vs1, TupleCons vs2 ->
      if List.length vs1 <> List.length vs2 then
        failwith "[Value.compare] type error: tuple lengths differ"
      else
        (if pos then List.for_all2_exn else List.exists2_exn)
          vs1 vs2 ~f:(compare pos opi opr ~opb)
  | DTCons (name1, _pvs1, vs1), DTCons (name2, _pvs2, vs2) ->
      if String.(name1 = name2) then
        if List.length vs1 <> List.length vs2 then
          failwith "[Value.compare] type error: datatype lengths differ"
        else
          (if pos then List.for_all2_exn else List.exists2_exn)
            vs1 vs2 ~f:(compare pos opi opr ~opb)
        (* Two values built by DIFFERENT constructors are never equal and always
           distinct, so the answer depends on which of the two this call is
           computing.  Returning [false] outright answers equality correctly and
           disequality backwards -- it reports that [A] and [B] are not
           distinct, which is the wrong direction for a refutation. *)
      else not pos
  | _ ->
      failwith @@ "[Value.compare] type error: " ^ str_of t1 ^ " vs "
      ^ str_of t2

(* The answer a comparison of two VALUES can give.  [Unknown] is not an error
   and not a third truth value: it says these two values do not settle the
   question, so whoever asked must leave the term alone rather than pick.  Two
   arrays force it -- a value carries a dummy index and a map, not the index
   SORT, so when the defaults differ there is nothing here to say whether any
   index is left over to observe them at, and neither answer is safe: [false]
   for equality is a wrong unsat and [true] a wrong sat. *)
type cmp = Same | Diff | Unknown

(* How much of the index sort the stored indices leave.  It is read off the
   dummy index VALUE, which is all an array value carries, so it is exact for
   the sorts whose values name their sort and [`Unknown] for the rest -- a
   datatype value carries its constructor's name and not its datatype, so the
   constructors cannot be counted here. *)
let index_room dummy n_stored =
  match dummy with
  | Int _ | Real _ -> `Room
  | Bool _ -> if n_stored >= 2 then `Covered else `Room
  | BV (Some w, _) ->
      (* [2^w] is not computed: a width that large cannot be covered by a map *)
      if w >= 62 then `Room
      else if n_stored >= Int.pow 2 w then `Covered
      else `Room
  | _ -> `Unknown

let both a b =
  match (a, b) with
  | Diff, _ | _, Diff -> Diff
  | Unknown, _ | _, Unknown -> Unknown
  | Same, Same -> Same

let rec equal_status v1 v2 =
  match (v1, v2) with
  | Bool b1, Bool b2 -> if Stdlib.(b1 = b2) then Same else Diff
  | Int i1, Int i2 -> if Z.Compare.(i1 = i2) then Same else Diff
  | Real r1, Real r2 -> if Q.(r1 = r2) then Same else Diff
  | Int i, Real r -> if Q.(Q.of_bigint i = r) then Same else Diff
  | Real r, Int i -> if Q.(r = Q.of_bigint i) then Same else Diff
  | BV (Some s1, b1), BV (Some s2, b2) when s1 = s2 ->
      if Z.Compare.(b1 = b2) then Same else Diff
  | Arr (dummy, default1, m1), Arr (_, default2, m2) -> (
      let keys = Set.union (Map.Poly.key_set m1) (Map.Poly.key_set m2) in
      let at k =
        (* An index only one of the two stores mentions still has a value in the
           other one: its default. *)
        match (Map.Poly.find m1 k, Map.Poly.find m2 k) with
        | Some x1, Some x2 -> equal_status x1 x2
        | Some x1, None -> equal_status x1 default2
        | None, Some x2 -> equal_status default1 x2
        | None, None -> equal_status default1 default2
      in
      let stored =
        Set.fold keys ~init:Same ~f:(fun acc k -> both acc (at k))
      in
      if Stdlib.(stored <> Same) then stored
      else
        (* Every stored index agrees, so the answer now rests on the indices
           that are left, where the defaults decide.  Equal defaults settle it
           either way, which is why that case does not consult the sort. *)
        let by_default = equal_status default1 default2 in
        if Stdlib.(by_default = Same) then Same
        else
          match index_room dummy (Set.length keys) with
          | `Room -> by_default
          | `Covered -> Same
          | `Unknown -> Unknown)
  | TupleCons vs1, TupleCons vs2 ->
      if List.length vs1 <> List.length vs2 then
        failwith "[Value.equal_status] type error: tuple lengths differ"
      else
        List.fold2_exn vs1 vs2 ~init:Same ~f:(fun acc x1 x2 ->
            both acc (equal_status x1 x2))
  | DTCons (name1, _pvs1, vs1), DTCons (name2, _pvs2, vs2) ->
      (* Values built by different constructors are never equal, whichever of
         the two questions is being asked. *)
      if String.(name1 <> name2) then Diff
      else if List.length vs1 <> List.length vs2 then
        failwith "[Value.equal_status] type error: datatype lengths differ"
      else
        List.fold2_exn vs1 vs2 ~init:Same ~f:(fun acc x1 x2 ->
            both acc (equal_status x1 x2))
  | Seq (_, vs1), Seq (_, vs2) ->
      (* Extensional: two sequences are equal exactly when they have the same
         length and agree at every index inside it.  A length mismatch settles
         it whatever the elements are, even ones whose own equality these
         values cannot decide. *)
      if List.length vs1 <> List.length vs2 then Diff
      else
        List.fold2_exn vs1 vs2 ~init:Same ~f:(fun acc x1 x2 ->
            both acc (equal_status x1 x2))
  | _ ->
      failwith @@ "[Value.equal_status] type error: " ^ str_of v1 ^ " vs "
      ^ str_of v2

(* [eq] and [neq] are complements by construction, which is the point of routing
   both through one three-way walk: the earlier shape computed them from one
   body parameterised by a flag, and two of its arms answered with a constant
   instead of consulting the flag -- right for equality and backwards for
   disequality both times.  [Unknown] is raised rather than guessed, and the
   simplifier already reads an exception from evaluation as "leave this atom
   alone". *)
let eq v1 v2 =
  match equal_status v1 v2 with
  | Same -> true
  | Diff -> false
  | Unknown ->
      failwith
        "[Value.eq] the two values do not decide equality: the arrays' defaults \
         differ and the index sort is not one these values name, so whether any \
         index is left to observe them at is not known here"

let neq v1 v2 =
  match equal_status v1 v2 with
  | Same -> false
  | Diff -> true
  | Unknown ->
      failwith
        "[Value.neq] the two values do not decide disequality: see [Value.eq]"
let leq = compare true (*ToDo*) Z.Compare.( <= ) Q.( <= )
let geq = compare true (*ToDo*) Z.Compare.( >= ) Q.( >= )
let lt = compare true (*ToDo*) Z.Compare.( < ) Q.( < )
let gt = compare true (*ToDo*) Z.Compare.( > ) Q.( > )

let neg = function
  | Bool _ -> failwith "[Value.neg] not supported for booleans"
  | Int i -> Int (Z.neg i)
  | Real r -> Real (Q.neg r)
  | BV (_size, _bits) -> failwith "[Value.neg] not supported for bit-vectors"
  | Arr (_, _v, _m) -> failwith "[Value.neg] not supported for arrays"
  | TupleCons _vs -> failwith "[Value.neg] not supported for tuples"
  | DTCons (_name, _pvs, _vs) ->
      failwith "[Value.neg] not supported for datatypes"
  | Seq _ -> failwith "[Value.neg] not supported for sequences"

let abs = function
  | Bool _ -> failwith "[Value.abs] not supported for booleans"
  | Int i -> Int (Z.abs i)
  | Real r -> Real (Q.abs r)
  | BV (_size, _bits) -> failwith "[Value.abs] not supported for bit-vectors"
  | Arr (_, _v, _m) -> failwith "[Value.abs] not supported for arrays"
  | TupleCons _vs -> failwith "[Value.abs] not supported for tuples"
  | DTCons (_name, _pvs, _vs) ->
      failwith "[Value.abs] not supported for datatypes"
  | Seq _ -> failwith "[Value.abs] not supported for sequences"

type modulo = Euclidean | Truncated | Flooring | Ceiling

let div_of = function
  | Euclidean -> Z.ediv
  | Truncated -> Z.div
  | Flooring -> Z.fdiv
  | Ceiling -> Z.cdiv

let rem_of = function
  | Euclidean -> Z.erem
  | Truncated -> Z.rem
  | Flooring -> failwith "not implemented"
  | Ceiling -> failwith "not implemented"

let add t1 t2 = Int Z.(int_of t1 + int_of t2)
let radd t1 t2 = Real Q.(cast_real_of t1 + cast_real_of t2)
let sub t1 t2 = Int Z.(int_of t1 - int_of t2)
let rsub t1 t2 = Real Q.(cast_real_of t1 - cast_real_of t2)
let mul t1 t2 = Int Z.(int_of t1 * int_of t2)
let rmul t1 t2 = Real Q.(cast_real_of t1 * cast_real_of t2)
let div m t1 t2 = Int ((div_of m) (int_of t1) (int_of t2))
let rdiv t1 t2 = Real Q.(cast_real_of t1 / cast_real_of t2)
let rem m t1 t2 = Int ((rem_of m) (int_of t1) (int_of t2))

let rrem t1 t2 =
  Real (Q.of_float @@ Float.mod_float (Q.to_float t1) (Q.to_float t2))

(** [pow_of x y] is [x ^ y] for [y >= 0], computed without narrowing [y] when
    [x] is 0, 1 or -1 (whose powers are known for any exponent), and [None]
    when [y] is negative or when [x] is any other integer and [y] exceeds a
    native int (a result of more than 2^62 bits).  The exponent is a term's
    value, so it can be any integer; where it fits, the result is [Z.pow]'s. *)
let pow_of x y =
  if Z.sign y < 0 then None
  else if Z.equal x Z.zero then Some (if Z.equal y Z.zero then Z.one else Z.zero)
  else if Z.equal x Z.one then Some Z.one
  else if Z.equal x Z.minus_one then
    Some (if Z.is_even y then Z.one else Z.minus_one)
  else if Z.fits_int y then Some (Z.pow x (Z.to_int y))
  else None

let pow t1 t2 =
  match pow_of (int_of t1) (int_of t2) with
  | Some z -> Int z
  | None ->
      failwith
        (sprintf "[Value.pow] %s ^ %s: negative exponent or result too large"
           (Z.to_string (int_of t1)) (Z.to_string (int_of t2)))
