open Core
open LogicOld

let name_of_sel cons_name i = sprintf "%s#%d" cons_name i

let unit_dt =
  let dt = Datatype.create "unit" [Datatype.mk_dt "unit" []] Datatype.FDt in
  Datatype.add_cons dt (Datatype.mk_cons "()")

let option_dt =
  let param = Sort.mk_fresh_svar () in
  let dt = Datatype.create "option" [Datatype.mk_dt "option" [param]] Datatype.FDt in
  let dt = Datatype.add_cons dt (Datatype.mk_cons "None") in
  Datatype.add_cons dt (Datatype.mk_cons "Some" ~sels:[Datatype.mk_sel (name_of_sel "Some" 0) param])

let list_dt =
  let param = Sort.mk_fresh_svar () in
  let dt = Datatype.create "list" [Datatype.mk_dt "list" [param]] Datatype.FDt in
  let dt = Datatype.add_cons dt @@ Datatype.mk_cons "[]" in
  Datatype.add_cons dt @@
  Datatype.mk_cons "::" ~sels:[Datatype.mk_sel (name_of_sel "::" 0) param;
                               Datatype.mk_insel (name_of_sel "::" 1) "list" [param]]

let exn_dt = Datatype.create "exn" [Datatype.mk_dt "exn" []] Datatype.Undef

let _ = LogicOld.update_ref_dtenv
    (DTEnv.mk_empty ()
     |> Map.Poly.add_exn ~key:"unit" ~data:unit_dt
     |> Map.Poly.add_exn ~key:"option" ~data:option_dt
     (* |> Map.Poly.add_exn ~key:"exn" ~data:exn_dt *)
     |> Map.Poly.add_exn ~key:"list" ~data:list_dt)

let init_dtenv () = Atomic.get LogicOld.ref_dtenv

let is_unit = function
  | T_dt.SDT dt -> Stdlib.(dt = unit_dt)
  | _ -> false
