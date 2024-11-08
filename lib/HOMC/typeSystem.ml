open Core
open Common.Ext
open Common.Combinator
open Ast
open EHMTT

type t = type_t

let con typs typ =
  List.fold_right typs ~init:typ ~f:(fun typ1 typ2 -> Func (typ1, typ2))

let rec args_and_ret = function
  | TVar r -> ([], TVar r (*ToDo*)) (*failwith "args_and_ret"*)
  | In -> ([], In)
  | Out -> ([], Out)
  | Func (typ1, typ2) ->
      let typs, typ = args_and_ret typ2 in
      (typ1 :: typs, typ)

let rec occur r = function
  | TVar r' when Stdlib.(r == r') -> true
  | TVar { contents = None } -> false
  | TVar { contents = Some typ } -> occur r typ
  | In | Out -> false
  | Func (typ1, typ2) -> occur r typ1 || occur r typ2

exception Unify of t * t

let rec unify typ1 typ2 =
  match (typ1, typ2) with
  | In, In | Out, Out -> ()
  | Func (typ11, typ12), Func (typ21, typ22) ->
      let _ = unify typ11 typ21 in
      unify typ12 typ22
  | TVar r1, TVar r2 when Stdlib.(r1 == r2) -> ()
  | TVar { contents = Some typ1 }, _ -> unify typ1 typ2
  | _, TVar { contents = Some typ2 } -> unify typ1 typ2
  | TVar ({ contents = None } as r1), _ ->
      if occur r1 typ2 then raise (Unify (typ1, typ2)) else r1 := Some typ2
  | _, TVar ({ contents = None } as r2) ->
      if occur r2 typ1 then raise (Unify (typ1, typ2)) else r2 := Some typ1
  | _, _ -> raise (Unify (typ1, typ2))

let assoc id env =
  match List.Assoc.find ~equal:Stdlib.( = ) env id with
  | Some r -> r
  | None -> failwith ("non-terminal " ^ Ident.name_of_tvar id ^ " not found")

let assoc_var id env =
  match List.Assoc.find ~equal:Stdlib.( = ) env id with
  | Some r -> r
  | None -> failwith ("variable " ^ Ident.name_of_tvar id ^ " not found")

let assoc_term id env =
  match List.Assoc.find ~equal:Stdlib.( = ) env id with
  | Some r -> r
  | None -> failwith ("terminal " ^ Ident.name_of_tvar id ^ " not found")

let rterm = ref (EHMTT.Var (Ident.Tvar "", ref (TVar (ref None))))

let rec g env t typ =
  rterm := t;
  EHMTT.visit
    (object
       method fd _n = unify In (*ToDo*) typ
       method nonterm id = unify (assoc id env) typ

       method var id ty =
         unify (assoc_var id env) typ;
         ty := assoc_var id env

       method term id =
         unify (assoc_term id env) typ;
         let rec h typ =
           match typ with
           | TVar { contents = None } -> () (*xxx*)
           | TVar { contents = Some typ } -> h typ
           | In | Out -> unify typ Out
           | Func (typ1, typ2) ->
               let _ = unify typ1 Out in
               h typ2
         in
         h typ

       method app t1 t2 =
         let typ' = TVar (ref None) in
         g env t2 typ';
         g env t1 (Func (typ', typ))

       method case id pats =
         unify typ Out;
         unify (assoc_var id env) In;
         List.iter
           ~f:(fun (id, (ids, t)) ->
             unify (assoc_var id env) (con (List.map ~f:(fun _ -> Out) ids) Out);
             g (List.map ~f:(fun id -> (id, In)) ids @ env) t Out)
           pats

       method coerce _id t =
         unify typ In;
         g env t Out

       method copy t =
         unify typ Out;
         g env t In

       method tree _id = unify typ In
       method varorterm _id = failwith "TypeSystem.g"
    end)
    t

let pr = EHMTT.pr_type
let pr_bn ppf (x, t) = Format.fprintf ppf "%s:%a" (Ident.name_of_tvar x) pr t

let f rules =
  let env =
    List.map rules ~f:(fun (id, (ids, _t)) ->
        ( id,
          con (List.map ~f:(fun _ -> TVar (ref None)) ids) (TVar (ref None))
          (*Out*) ))
  in

  let tenv =
    List.map ~f:(fun id -> (id, TVar (ref None)))
    @@ List.unique
    @@ List.concat_map ~f:(snd >> snd >> EHMTT.terms) rules
  in
  let env = env @ tenv in
  List.iter rules ~f:(fun (id, (ids, t)) ->
      let typs, ret = args_and_ret (assoc_var id env) in
      let env = List.map2_exn ~f:Pair.make ids typs @ env in
      try g env t ret
      with Unify (typ1, typ2) ->
        let _ =
          Format.eprintf "unification error for %a in %s: %a and %a@." EHMTT.pr
            !rterm (Ident.name_of_tvar id) pr typ1 pr typ2
        in
        List.iter (List.rev env) ~f:(fun (id, typ) ->
            Format.printf "%s: %a@." (Ident.name_of_tvar id) pr typ);
        failwith "type error");

  (*xxx*)
  List.iter tenv ~f:(fun (id, typ) ->
      let rec h = function
        | TVar { contents = None } -> () (*failwith "TypeSystem.f"*)
        | TVar { contents = Some typ } -> h typ
        | (In | Out) as typ -> unify typ Out
        | Func (typ1, typ2) ->
            unify typ1 Out;
            h typ2
      in
      try h typ
      with Unify (typ1, typ2) ->
        Format.eprintf "unification error for %s: %a and %a@."
          (Ident.name_of_tvar id) pr typ1 pr typ2;
        failwith "type error");
  env
(*  Format.printf "[%a]" (List.pr pr_bn ", ") env *)
