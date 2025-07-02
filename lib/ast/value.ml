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

let rec compare opi opr ?(opb = fun _ _ -> assert false) t1 t2 =
  match (t1, t2) with
  | Bool b1, Bool b2 -> opb b1 b2
  | Int i1, Int i2 -> opi i1 i2
  | Real r1, Real r2 -> opr r1 r2
  | Int i, Real r -> opr (Q.of_bigint i) r
  | Real r, Int i -> opr r (Q.of_bigint i)
  | BV (Some s1, bits1), BV (Some s2, bits2) when s1 = s2 -> opi bits1 bits2
  | Arr (_, v1, m1), Arr (_, v2, m2) ->
      compare opi opr ~opb v1 v2 && Map.Poly.equal (compare opi opr ~opb) m1 m2
  | TupleCons vs1, TupleCons vs2 ->
      if List.length vs1 <> List.length vs2 then
        failwith "[Value.compare] type error: tuple lengths differ"
      else List.for_all2_exn vs1 vs2 ~f:(compare opi opr ~opb)
  | DTCons (name1, _pvs1, vs1), DTCons (name2, _pvs2, vs2)
    when String.(name1 = name2) ->
      if List.length vs1 <> List.length vs2 then
        failwith "[Value.compare] type error: datatype lengths differ"
      else List.for_all2_exn vs1 vs2 ~f:(compare opi opr ~opb)
  | _ -> failwith "[Value.compare] type error"

let equal = compare Z.Compare.( = ) Q.( = ) ~opb:Stdlib.( = )

let neg = function
  | Bool _ -> failwith "[Value.neg] not supported for booleans"
  | Int i -> Int (Z.neg i)
  | Real r -> Real (Q.neg r)
  | BV (_size, _bits) -> failwith "[Value.neg] not supported for bit-vectors"
  | Arr (_, _v, _m) -> failwith "[Value.neg] not supported for arrays"
  | TupleCons _vs -> failwith "[Value.neg] not supported for tuples"
  | DTCons (_name, _pvs, _vs) ->
      failwith "[Value.neg] not supported for datatypes"

let abs = function
  | Bool _ -> failwith "[Value.abs] not supported for booleans"
  | Int i -> Int (Z.abs i)
  | Real r -> Real (Q.abs r)
  | BV (_size, _bits) -> failwith "[Value.abs] not supported for bit-vectors"
  | Arr (_, _v, _m) -> failwith "[Value.abs] not supported for arrays"
  | TupleCons _vs -> failwith "[Value.abs] not supported for tuples"
  | DTCons (_name, _pvs, _vs) ->
      failwith "[Value.abs] not supported for datatypes"

type modulo = Euclidean | Truncated | Flooring | Ceiling

let div_of = function
  | Euclidean -> Z.ediv
  | Truncated -> Z.div
  | Flooring -> Z.fdiv
  | Ceiling -> Z.cdiv

let rem_of = function
  | Euclidean -> Z.erem
  | Truncated -> Z.rem
  | Flooring -> failwith "not implmented"
  | Ceiling -> failwith "not implmented"

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

let pow t1 t2 = Int (Z.pow (int_of t1) (Z.to_int (*ToDo*) (int_of t2)))
