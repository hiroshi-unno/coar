open Core
open Common
open Util
open Logic

type t = (Ident.tvar option, Z.t) Map.Poly.t
let of_z n = Map.Poly.singleton None n
let of_var v = Map.Poly.of_alist_exn [(None, Z.zero); (Some v, Z.one)]
let (+) a b =
  Map.Poly.merge a b ~f:(fun ~key:_ -> function
      | `Left c | `Right c -> Some c
      | `Both (c1, c2) -> Some Z.(c1 + c2))
let (~-) a = Map.Poly.map a ~f:Z.neg
let (-) a b = a + (~-b)
let mult n a = Map.Poly.map a ~f:(fun data -> Z.(n * data))
let to_string a = Map.Poly.to_alist a |> List.map ~f:(fun (key, data) -> 
    match key with
    | None -> Z.to_string data
    | Some tvar -> Z.to_string data ^ "*" ^ Ident.name_of_tvar tvar) |> String.concat ~sep:" + "
let (=) : t -> t -> bool = Map.Poly.equal Z.Compare.(=)
let term_of a =
  Map.Poly.to_alist a |> List.map ~f:(fun (key, data) -> match key with
      | None -> IntTerm.mk_int data
      | Some tvar -> Term.mk_apps (IntTerm.mk_mult ()) [IntTerm.mk_int data; Term.mk_var tvar]) |> IntTerm.sum
let rec of_term = function
  | Con(IntTerm.Int n, _) -> Some (of_z n)
  | Var(var, _) -> Some (of_var var)
  | App(App(Con(IntTerm.Add, _), t1, _), t2, _) ->
    Option.(of_term t1 >>= fun a1 ->
            of_term t2 >>= fun a2 ->
            return (a1 + a2))
  | App(App(Con(IntTerm.Sub, _), t1, _), t2, _) ->
    Option.(of_term t1 >>= fun a1 ->
            of_term t2 >>= fun a2 ->
            return (a1 - a2))
  | App(App(Con(IntTerm.Mult, _), Con(IntTerm.Int n, _), _), t, _)
  | App(App(Con(IntTerm.Mult, _), t, _), Con(IntTerm.Int n, _), _) ->
    Option.(of_term t >>= fun a ->
            return (mult n a))
  | App(Con(IntTerm.Neg, _), t, _) ->
    Option.(of_term t >>= fun a ->
            return (~- a))
  | _ -> None


