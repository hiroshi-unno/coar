open Core
open Common.Ext
open Common.Combinator
open Logic

type t = (Ident.tvar option, Z.t) Map.Poly.t

let make ax b : t =
  Map.Poly.of_alist_exn ((None, b) :: List.map ~f:(fun (x, a) -> (Some x, a)) ax)

let of_z n = Map.Poly.singleton None n
let of_var v = Map.Poly.of_alist_exn [ (None, Z.zero); (Some v, Z.one) ]

let ( + ) a b =
  Map.Poly.merge a b ~f:(fun ~key:_ -> function
    | `Left c | `Right c -> Some c | `Both (c1, c2) -> Some Z.(c1 + c2))

let ( ~- ) = Map.Poly.map ~f:Z.neg
let ( - ) a b = a + ~-b
let mul n = Map.Poly.map ~f:(fun data -> Z.(n * data))

let to_string =
  Map.Poly.to_alist
  >> String.concat_map_list ~sep:" + " ~f:(fun (key, data) ->
         match key with
         | None -> Z.to_string data
         | Some tvar -> Z.to_string data ^ "*" ^ Ident.name_of_tvar tvar)

let ( = ) = Map.Poly.equal Z.Compare.( = )
let compare = Map.Poly.compare_direct Z.compare
let vars = Map.Poly.keys >> List.filter_opt
let coeffs = Map.Poly.data
let get_coeff_of var a = Map.Poly.find a (Some var)
let remove var a = Map.Poly.remove a (Some var)

let eval ?(default_value = None) map a =
  Map.Poly.fold a ~init:Z.zero ~f:(fun ~key ~data sum ->
      match key with
      | None -> Z.(sum + data)
      | Some tvar -> (
          Z.(
            sum
            + data
              *
              match Map.Poly.find map tvar with
              | Some v -> v
              | None -> Option.value_exn default_value)))

let term_of =
  Map.Poly.to_alist
  >> List.map ~f:(fun (key, data) ->
         match key with
         | None -> IntTerm.mk_int data
         | Some tvar ->
             Term.mk_apps (IntTerm.mk_mul ())
               [ IntTerm.mk_int data; Term.mk_var tvar ])
  >> IntTerm.sum

let rec of_term = function
  | Con (IntTerm.Int n, _) -> Some (of_z n)
  | Var (var, _) -> Some (of_var var)
  | App (App (Con (IntTerm.Add, _), t1, _), t2, _) ->
      Option.(
        of_term t1 >>= fun a1 ->
        of_term t2 >>= fun a2 -> return (a1 + a2))
  | App (App (Con (IntTerm.Sub, _), t1, _), t2, _) ->
      Option.(
        of_term t1 >>= fun a1 ->
        of_term t2 >>= fun a2 -> return (a1 - a2))
  | App (App (Con (IntTerm.Mul, _), Con (IntTerm.Int n, _), _), t, _)
  | App (App (Con (IntTerm.Mul, _), t, _), Con (IntTerm.Int n, _), _) ->
      Option.(of_term t >>= fun a -> return (mul n a))
  | App (Con (IntTerm.Neg, _), t, _) ->
      Option.(of_term t >>= fun a -> return ~-a)
  | _ -> None
