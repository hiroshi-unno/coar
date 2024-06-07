(* parents, heights, data, merge *)
type 'a t = UF of int array * int array * 'a array * ('a -> 'a -> 'a)

val mk_uf : initial_data:'a array -> merge:('a -> 'a -> 'a) -> 'a t
val mk_unit_uf : size:int -> unit t
val mk_size_uf : size:int -> int t
val unite : int -> int -> 'a t -> unit
val find : int -> 'a t -> int
val is_united : int -> int -> 'a t -> bool
val get_data : int -> 'a t -> 'a
val get_groups : 'a t -> int list list
