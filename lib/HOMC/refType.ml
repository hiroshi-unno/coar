open Core
open Common.Ext

type 'a t = Base of 'a | Func of 'a t * 'a t

(* let rec hmtt = function
     Base(id) -> [], id
   | Func(Base(id), typ) ->
       let ids, id' = hmtt typ in
       id::ids, id'
   | _ -> failwith "not supported"
*)

let is_base = function Base _ -> true | Func _ -> false

let rec args_and_ret = function
  | Base attr -> ([], Base attr)
  | Func (typ1, typ2) ->
      let typs, typ = args_and_ret typ2 in
      (typ1 :: typs, typ)

let make_type args ret =
  List.fold_right args ~init:ret ~f:(fun t1 t2 -> Func (t1, t2))

let rec attr_of = function
  | Base attr -> [ attr ]
  | Func (typ1, typ2) -> attr_of typ1 @ attr_of typ2

let rec pr ppf = function
  | Base _attr -> Format.fprintf ppf "o" (*ToDo*)
  | Func (typ1, typ2) ->
      if is_base typ1 then Format.fprintf ppf "%a -> %a" pr typ1 pr typ2
      else Format.fprintf ppf "(%a) -> %a" pr typ1 pr typ2
