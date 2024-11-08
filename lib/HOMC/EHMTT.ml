open Core
open Common.Ext
open Common.Combinator
open Ast
open Automata

type type_t = TVar of type_t option ref | In | Out | Func of type_t * type_t

let rec pr_type_aux b ppf = function
  | TVar { contents = None } -> Format.fprintf ppf "?"
  | TVar { contents = Some typ } -> pr_type_aux b ppf typ
  | In -> Format.fprintf ppf "i"
  | Out -> Format.fprintf ppf "o"
  | Func (typ1, typ2) ->
      if b then
        Format.fprintf ppf "(%a -> %a)" (pr_type_aux true) typ1
          (pr_type_aux false) typ2
      else
        Format.fprintf ppf "%a -> %a" (pr_type_aux true) typ1 (pr_type_aux b)
          typ2

let pr_type = pr_type_aux false

let rec order_of_type = function
  | TVar { contents = None } -> 0
  | TVar { contents = Some typ } -> order_of_type typ
  | In | Out -> 0
  | Func (t1, t2) -> max (order_of_type t1 + 1) (order_of_type t2)

type term =
  | Fd of int
  | Nonterm of Ident.tvar
  | Var of Ident.tvar * type_t ref
  | Term of Ident.tvar
  | App of term * term
  | Case of Ident.tvar * (Ident.tvar * (Ident.tvar list * term)) list
  | Coerce of Ident.tvar * term * int
  | Copy of term
  | Tree of Ident.tvar
  | VarOrTerm of Ident.tvar

let mk_var x = Var (x, ref (TVar { contents = None }) (*ToDo*))

type rule = Ident.tvar * (Ident.tvar list * term)
type t = rule list

let assoc id rs =
  match List.Assoc.find ~equal:String.equal rs id with
  | Some r -> r
  | None -> failwith ("non-terminal " ^ id ^ " not found")

let reachable id rs =
  let next_nts (_, t) =
    let rec next_nts' = function
      | Fd _n -> []
      | Nonterm id -> [ Ident.name_of_tvar id ]
      | Var _ | Term _ -> []
      | App (t1, t2) -> next_nts' t1 @ next_nts' t2
      | Case (_, pats) -> List.concat_map ~f:(snd >> snd >> next_nts') pats
      | Coerce (_, t, _) -> next_nts' t
      | Tree _ -> []
      | Copy t -> next_nts' t
      | VarOrTerm _ -> failwith "EHMTT.reachable"
    in
    next_nts' t
  in
  List.map ~f:(fun id -> (id, assoc id rs))
  @@ List.reachable [ id ] (fun id -> next_nts (assoc id rs))

let rec coercions = function
  | Fd _n -> []
  | Nonterm _ -> []
  | Var _ -> []
  | Term _ -> []
  | App (t1, t2) -> coercions t1 @ coercions t2
  | Case (_, pats) -> List.concat_map ~f:(snd >> snd >> coercions) pats
  | Coerce (q, t, idx) -> [ (q, t, idx) ]
  | Tree _ -> []
  | Copy _ | VarOrTerm _ -> failwith "EHMTT.coercions"

let visit f = function
  | Fd n -> f#fd n
  | Nonterm id -> f#nonterm id
  | Var (id, ty) -> f#var id ty
  | Term id -> f#term id
  | App (t1, t2) -> f#app t1 t2
  | Case (id, pats) -> f#case id pats
  | Coerce (id, t, _) -> f#coerce id t
  | Copy t -> f#copy t
  | Tree id -> f#tree id
  | VarOrTerm id -> f#varorterm id

let rec fold f = function
  | Fd n -> f#fd n
  | Nonterm id -> f#nonterm id
  | Var (id, _) -> f#var id
  | Term id -> f#term id
  | App (t1, t2) -> f#app (fold f t1) (fold f t2)
  | Case (id, pats) ->
      f#case id
        (List.map pats ~f:(fun (id', (ids, t)) -> (id', (ids, fold f t))))
  | Coerce (id, t, idx) -> f#coerce id (fold f t) idx
  | Copy t -> f#copy (fold f t)
  | Tree id -> f#tree id
  | VarOrTerm id -> f#varorterm id

(* let elimVarOrTerm ids t =
   fold
     (object
        method nonterm id = Nonterm id
        method var id = Var id
        method term id = Term id
        method app t1 t2 = App (t1, t2)
        method case id pats = Case (id, buggy !!!pats)
        method coerce id t = Coerce (id, t)
        method copy t = Copy t
        method tree id = Tree id
        method varorterm id = if List.mem id ids then Var id else Term id
     end)
     t
*)

let rec elimVarOrTerm ids = function
  | (Fd _ | Nonterm _ | Var _ | Term _) as t -> t
  | App (t1, t2) -> App (elimVarOrTerm ids t1, elimVarOrTerm ids t2)
  | Case (id, pats) ->
      Case
        ( id,
          List.map pats ~f:(fun (id', (ids', t)) ->
              (id', (ids', elimVarOrTerm (ids @ ids') t))) )
  | Coerce (id, t, idx) -> Coerce (id, elimVarOrTerm ids t, idx)
  | Copy t -> Copy (elimVarOrTerm ids t)
  | Tree _ as t -> t
  | VarOrTerm id ->
      if List.mem ~equal:Ident.tvar_equal ids id then
        Var (id, { contents = TVar { contents = None } })
      else Term id

let trees =
  fold
    (object
       method fd _n = []
       method nonterm _id = []
       method var _id = []
       method term _id = []
       method app t1 t2 = t1 @ t2
       method case _id = List.concat_map ~f:(snd >> snd)
       method coerce id t _ = id :: t
       method copy t = t
       method tree id = [ id ]
       method varorterm _id = failwith "trees"
    end)

let terms =
  fold
    (object
       method fd _n = []
       method nonterm _id = []
       method var _id = []
       method term id = [ id ]
       method app t1 t2 = t1 @ t2
       method case _id = List.concat_map ~f:(fun (id, (_, t)) -> id :: t)
       method coerce _id t _ = t
       method copy t = t
       method tree _id = []
       method varorterm _id = failwith "terms"
    end)

let size =
  fold
    (object
       method fd _n = 1
       method nonterm _ = 1
       method var _ = 1
       method term _ = 1
       method app t1 t2 = t1 + t2

       method case _ pats =
         1 + List.fold_left ~init:0 (List.map ~f:(snd >> snd) pats) ~f:( + )

       method coerce _ t _ = 1 + t
       method copy t = 1 + t
       method tree _id = 1
       method varorterm _id = failwith "size"
    end)

let count_coerce =
  fold
    (object
       method fd _ = 0
       method nonterm _ = 0
       method var _ = 0
       method term _ = 0
       method app t1 t2 = t1 + t2

       method case _ pats =
         List.fold_left ~init:0 (List.map ~f:(snd >> snd) pats) ~f:( + )

       method coerce _ t _ = 1 + t
       method copy t = t
       method tree _id = 0
       method varorterm _id = failwith "count_coerce"
    end)

let size_of_prog (rules : t) =
  List.fold_left ~init:0 ~f:( + ) @@ List.map ~f:(snd >> snd >> size) rules

let terminals (rules : t) =
  List.unique @@ List.concat_map ~f:(snd >> snd >> terms) rules

let rec pr_aux b ppf = function
  | Fd n -> Format.fprintf ppf "%d" n
  | Nonterm id | Term id -> Format.fprintf ppf "%s" (Ident.name_of_tvar id)
  | Var (id, ty) ->
      Format.fprintf ppf "%s:%a" (Ident.name_of_tvar id) pr_type !ty
  | App (t1, t2) ->
      if b then Format.fprintf ppf "(";
      Format.fprintf ppf "%a %a" (pr_aux false) t1 (pr_aux true) t2;
      if b then Format.fprintf ppf ")"
  | Case (id, pats) ->
      if b then Format.fprintf ppf "(";
      let pr_ ppf (id', (ids, t)) =
        Format.fprintf ppf "%s => %a"
          (String.concat ~sep:" "
             (List.map ~f:Ident.name_of_tvar @@ (id' :: ids)))
          (pr_aux false) t
      in
      Format.fprintf ppf "case %s of %a" (Ident.name_of_tvar id)
        (List.pr pr_ " | ") pats;
      if b then Format.fprintf ppf ")"
  | Coerce (id, t, idx) ->
      if b then Format.fprintf ppf "(";
      Format.fprintf ppf "coerce(%d) %s %a" idx (Ident.name_of_tvar id)
        (pr_aux true) t;
      if b then Format.fprintf ppf ")"
  | Copy t ->
      if b then Format.fprintf ppf "(";
      Format.fprintf ppf "copy %a" (pr_aux true) t;
      if b then Format.fprintf ppf ")"
  | Tree id -> Format.fprintf ppf "%s" (Ident.name_of_tvar id)
  | VarOrTerm _ -> failwith "pr_aux"

let pr = pr_aux false

let pr_rules ppf (rules : t) =
  List.iter rules ~f:(fun (id, (ids, t)) ->
      Format.fprintf ppf "%s -> %a.@,"
        (String.concat_map_list ~sep:" " ~f:Ident.name_of_tvar (id :: ids))
        (pr_aux false) t)

let rec fun_and_args = function
  | App (t1, t2) ->
      let t, ts = fun_and_args t1 in
      (t, ts @ [ t2 ])
  | t -> (t, [])

let app t1 t2 = App (t1, t2)
let apps t ts = List.fold_left ~init:t ts ~f:app

let gen_nt =
  let cnt = ref 0 in
  fun () ->
    cnt := !cnt + 1;
    "N" ^ string_of_int !cnt

let rec unzip = function [] -> [] | (x, y) :: xs -> x :: y :: unzip xs

let rec of_type typ =
  match RefType.args_and_ret typ with
  | typs, RefType.Base (rid, _) ->
      if List.is_empty typs then (Tree rid, [])
      else
        let args =
          List.mapi ~f:(fun i typ -> ("x" ^ string_of_int i, typ)) typs
        in
        let t, rs =
          List.fold_right args
            ~init:(App (Nonterm (Ident.Tvar "Copy"), Tree rid), [])
            ~f:(fun (aid, typ) (t, rs) ->
              let t', rs' = check aid typ t in
              (t', rs @ rs'))
        in
        let id = gen_nt () in
        (Nonterm (Ident.Tvar id), (id, (List.map ~f:fst args, t)) :: rs)
  | _ -> assert false

and check id typ t =
  match RefType.args_and_ret typ with
  | typs, RefType.Base (rid, _) ->
      let ts, rss = List.unzip @@ List.map ~f:of_type typs in
      ( apps
          (Term
             (Ident.Tvar ("coerce" ^ String.capitalize @@ Ident.name_of_tvar rid)))
          [
            (if List.is_empty ts then
               App
                 ( Nonterm (Ident.Tvar "Copy"),
                   Var (Ident.Tvar id, { contents = In }) )
             else apps (Var (Ident.Tvar id, { contents = In })) ts);
            t;
          ],
        List.concat rss )
  | _ -> assert false

let make_tree_copier terminals =
  let pats =
    List.map terminals ~f:(fun (a, n) ->
        let vs =
          List.init n ~f:(fun v -> Ident.Tvar ("x" ^ string_of_int (v + 1)))
        in
        let copies =
          List.map vs ~f:(fun v ->
              App (Nonterm (Ident.Tvar "Copy"), Var (v, ref In)))
        in
        (a, (vs, apps (Term a) copies)))
  in
  (Ident.Tvar "Copy", ([ Ident.Tvar "x" ], Case (Ident.Tvar "x", pats)))

let expandCopy (rules : t) =
  let rec f = function
    | (Fd _ | Nonterm _ | Var (_, _) | Term _) as t -> t
    | App (t1, t2) -> App (f t1, f t2)
    | Case (id, pats) ->
        Case (id, List.map pats ~f:(fun (a, (xs, t)) -> (a, (xs, f t))))
    | Coerce (id, t, idx) -> Coerce (id, f t, idx)
    | Copy t -> App (Nonterm (Ident.Tvar "Copy"), t)
    | Tree _id as t -> t
    | VarOrTerm _id -> failwith "expandCopy"
  in
  List.map ~f:(fun (n, (xs, t)) -> (n, (xs, f t))) rules

let rec subst sub = function
  | (Fd _ | Nonterm _ | Term _) as t -> t
  | Var (id, ty) ->
      let v =
        match List.Assoc.find ~equal:Ident.tvar_equal sub id with
        | Some r -> r
        | None -> id
      in
      Var (v, ty)
  | App (t1, t2) -> App (subst sub t1, subst sub t2)
  | Case (id, pats) ->
      let v =
        match List.Assoc.find ~equal:Ident.tvar_equal sub id with
        | Some r -> r
        | None -> id
      in
      Case
        ( v,
          List.map pats ~f:(fun (a, (xs, t)) ->
              let sub =
                List.filter sub ~f:(fun (x, _) ->
                    not (List.mem ~equal:Ident.tvar_equal xs x))
              in
              (a, (xs, subst sub t))) )
  | Coerce (id, t, idx) -> Coerce (id, subst sub t, idx)
  | Copy t -> Copy (subst sub t)
  | Tree _id as t -> t
  | VarOrTerm _id -> failwith "subst"

let balance = ref true

let nondet_branch br app xs =
  if !balance then
    let rec f xs =
      let partition xs =
        let i = List.length xs / 2 in
        List.split_n xs i
      in
      match xs with
      | [] -> failwith "nondet_branch"
      | [ x ] -> x
      | _ ->
          let ls, rs = partition xs in
          app (app br (f ls)) (f rs)
    in
    f xs
  else
    match List.rev xs with
    | [] -> failwith "nondet_branch"
    | x :: xs ->
        List.fold_right (List.rev xs) ~init:x ~f:(fun x y -> app (app br x) y)

let tbr = Ident.Tvar TTA.br_symbol

let rec rsfd_term_of (trs : TTA.trs) = function
  | Fd n -> RSFD.Fd (Second n)
  | Nonterm id -> RSFD.Nonterm id
  | Var (id, _) -> RSFD.Var id
  | Term id -> RSFD.Term id
  | App (t1, t2) -> RSFD.App (rsfd_term_of trs t1, rsfd_term_of trs t2)
  | Case (id1, xs) ->
      let xs' = rsfd_of trs xs in
      Case
        ( id1,
          List.map trs ~f:(fun (_, ys) ->
              nondet_branch (RSFD.Term tbr) RSFD.app
                (List.map ys ~f:(fun (id2, ids1) ->
                     match
                       List.Assoc.find xs' (Ident.Tvar id2)
                         ~equal:Ident.tvar_equal
                     with
                     | None -> RSFD.fail (Ident.Tvar id2)
                     | Some (ids2, t') ->
                         let sub =
                           List.map2_exn ids1 ids2 ~f:(fun id1 id2 ->
                               (id2, RSFD.Fd (First (Ident.Tvar id1))))
                         in
                         RSFD.subst sub t'))) )
  | Tree id -> RSFD.Fd (First id)
  | Copy _ | Coerce _ | VarOrTerm _ -> failwith "rsfd_of"

and rsfd_of trs (rules : t) : RSFD.t =
  List.map rules ~f:(fun (id, (ids, t)) -> (id, (ids, rsfd_term_of trs t)))

let copy1 x = Ident.Tvar (Ident.name_of_tvar x ^ "_1")
let copy2 x = Ident.Tvar (Ident.name_of_tvar x ^ "_2")

let rec is_intype = function
  | TVar { contents = None } -> false
  | TVar { contents = Some typ } -> is_intype typ
  | In -> true
  | Out -> false
  | Func (_typ1, _typ2) -> false

let rec alpha = function
  | Fd n -> Fd n
  | Term a -> Term a
  (* | Var (x, t) when is_intype !t -> Var (x, t)
     | Var (x, t) -> Var (copy1 x, t) *)
  | Var (_x, _t) as v -> v
  | Nonterm f -> Nonterm (copy1 f)
  | App (t1, t2) -> App (alpha t1, alpha t2)
  | Case (x, pats) ->
      Case (x, List.map pats ~f:(fun (a, (ys, t)) -> (a, (ys, alpha t))))
  | Tree q -> Tree q
  | Coerce (q, _t, _) -> Tree q
  | Copy _ | VarOrTerm _ -> failwith "alpha"

let alphaRules = List.map ~f:(fun (f, (xs, t)) -> (copy1 f, (xs, alpha t)))

let rec coerces = function
  | Fd _n -> []
  | Term _a -> []
  | Var (_x, _t) -> []
  | Nonterm _f -> []
  | App (t1, t2) -> coerces t1 @ coerces t2
  | Case (_x, _pats) -> []
  | Tree _q -> []
  | Coerce (q, t, idx) -> [ (q, t, idx) ]
  | Copy _ | VarOrTerm _ -> failwith "coerces"

let term a = Ident.Tvar ("T_" ^ Ident.name_of_tvar a)

let rec elim_coerce (q, tm, idx) = function
  | Fd n -> Fd n
  | Term a -> Nonterm (term a)
  | Var (_x, t) as v when is_intype !t -> v
  | Var (x, t) -> Var (copy2 x, t)
  | Nonterm f -> Nonterm (copy2 f)
  | App (t1, t2) ->
      app
        (app (elim_coerce (q, tm, idx) t1) (alpha t2))
        (elim_coerce (q, tm, idx) t2)
  | Case (x, pats) ->
      Case
        ( x,
          List.map pats ~f:(fun (a, (xs, t)) ->
              (a, (xs, beta_term (q, tm, idx) t))) )
  | Tree _q as t -> t
  | Coerce (q', _, _) -> Tree q'
  | Copy _ | VarOrTerm _ -> failwith "beta1"

and beta_term (q, tm, idx) term =
  (*  Format.eprintf "Term: %a\n" Term.pr tm; *)
  let cs = coerces term in
  let ec (_, t, _) = elim_coerce (q, tm, idx) t in
  if List.exists cs ~f:(fun (_, _, idx') -> idx = idx') then
    let t1 = alpha tm in
    let t2s = List.map ~f:ec cs in
    (*    let t2 = elim_coerce (q,tm,idx) tm in *)
    let t3 = elim_coerce (q, tm, idx) term in
    nondet_branch (Term tbr) app ((t1 :: t2s) @ [ t3 ])
  else
    let ts = List.map ~f:ec cs in
    let t = elim_coerce (q, tm, idx) term in
    nondet_branch (Term tbr) app (t :: ts)

let beta_rules (q, tm, idx) rules start terminals =
  let make_terminal_fun (a, n) =
    let vs =
      List.init n ~f:(fun v -> Ident.Tvar ("x" ^ string_of_int (v + 1)))
    in
    let vs2 = List.map ~f:copy2 vs in
    let vs12 = unzip (List.zip_exn vs vs2) in
    let vs2' = List.map ~f:(fun v -> Var (v, ref Out)) vs2 in
    let t =
      if n = 0 then Term (Ident.Tvar TTA.success_symbol)
      else nondet_branch (Term tbr) app vs2'
    in
    let rule = (term a, (vs12, t)) in
    rule
  in
  let term_rules = List.map ~f:make_terminal_fun terminals in

  let make_start_rule (f, (xs, _t)) =
    let start_from_f =
      apps (Nonterm (copy2 f))
      @@ List.map (unzip (List.zip_exn xs xs)) ~f:mk_var
    in
    (f, (xs, start_from_f))
  in
  let start_rule =
    make_start_rule @@ List.find_exn rules ~f:(fst >> Stdlib.( = ) start)
  in

  let make_copy1 (f, (xs, t)) = (copy1 f, (xs, alpha t)) in
  let rules1 = List.map ~f:make_copy1 rules in

  let make_copy2 (f, (xs, term)) =
    let xs2 = List.map ~f:copy2 xs in
    let xs12 = unzip (List.zip_exn xs xs2) in
    (copy2 f, (xs12, beta_term (q, tm, idx) term))
  in
  let rules2 = List.map ~f:make_copy2 rules in

  let ret = (start_rule :: rules1) @ rules2 @ term_rules in
  (* Term.pr_rules Format.err_formatter ret; *)
  ret

(* ToDo: if not supported*)
let eta_expand env rules =
  List.map rules ~f:(fun (id, (ids, t)) ->
      try
        let sorts, _ =
          LogicOld.Sort.args_ret_of @@ LogicOld.Sort.mono_type_of
          @@ Map.Poly.find_exn env id
        in
        let d = List.length sorts - List.length ids in
        assert (d >= 0);
        let ids' =
          List.init d ~f:(fun _ -> Ident.mk_fresh_tvar ~prefix:(Some "x") ())
        in
        (id, (ids @ ids', apps t (List.map ids' ~f:mk_var)))
      with _ -> failwith (Ident.name_of_tvar id ^ " is not bound"))
