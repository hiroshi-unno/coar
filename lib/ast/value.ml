open Core
open Common.Ext

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

type t = Bool of bool | Int of Z.t | Real of Q.t

let neg = function
  | Int i -> Int (Z.neg i)
  | Real r -> Real (Q.neg r)
  | Bool _ -> failwith "[Value.neg] type error"

let abs = function
  | Int i -> Int (Z.abs i)
  | Real r -> Real (Q.abs r)
  | Bool _ -> failwith "[Value.abs] type error"

let compare opi opr ?(opb = fun _ _ -> assert false) t1 t2 =
  match (t1, t2) with
  | Int i1, Int i2 -> opi i1 i2
  | Real r1, Real r2 -> opr r1 r2
  | Bool b1, Bool b2 -> opb b1 b2
  | Int i, Real r -> opr (Q.of_bigint i) r
  | Real r, Int i -> opr r (Q.of_bigint i)
  | _ -> failwith "[Value.compare] type error"

let bool_of = function Bool b -> b | _ -> assert false
let int_of = function Int i -> i | _ -> failwith "[Value.int_of] type error"
let real_of = function Real r -> r | _ -> assert false

let cast_real_of = function
  | Int i -> Q.of_bigint i
  | Real r -> r
  | _ -> failwith "[Value.cast_real_of] type error"

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

let ite cond_ then_ else_ =
  match cond_ with
  | Bool true -> then_
  | Bool false -> else_
  | _ -> failwith "[Value.ite] type error"

let str_of = function
  | Bool b -> string_of_bool b
  | Int n -> Z.to_string n
  | Real r -> Q.to_string r

let is_true = function Bool b -> b | _ -> false
let is_false = function Bool b -> not b | _ -> false
