open Core
open LogicOld
open Common

let verbose = false
module Debug = Debug.Make(val if verbose then Debug.Config.enable else Debug.Config.disable)


type tyconstr =
  | CEq of Sort.t * Sort.t
  | CNum of  Sort.t

let is_ceq = function | CEq _ -> true | _ -> false
let is_cnum = function | CNum _ -> true | _ -> false

let str_of_tyconstr = function
  | CEq (sort1, sort2) -> sprintf "[CEq:%s = %s]" (Term.str_of_sort sort1) (Term.str_of_sort sort2)
  | CNum (sort) -> sprintf "[CNum: %s]"(Term.str_of_sort sort)

let verbose_theta = true
let str_of_tyconstr_set theta = if verbose_theta then Set.Poly.fold theta ~init:"" ~f:(fun ret tyc -> ret ^ "\n"  ^ str_of_tyconstr tyc) else ""

let rec occurs tx t =
  if Stdlib.(=) tx t then true
  else 
    match t with
    | Sort.SArrow (t1, t2) -> occurs tx t1 || occurs tx t2
    | _ -> false

let rec subst_ty theta t =
  let subst_ty_var s =
    fst @@ Set.Poly.fold theta ~init:(s, false) ~f:(
      fun (ret, has_ret) tc -> 
        if has_ret then ret, has_ret
        else 
          match tc with 
          |CEq (tx, t1) ->
            if Stdlib.(=) tx s then t1, true
            else ret, false
          |_ -> ret, false
    )
  in
  let subst_dt theta dt =
    let args = Datatype.args_of dt in
    let args' = List.map args ~f:(subst_ty theta) in
    Datatype.update_args dt args'
  in
  match t with
  | Sort.SVar _ -> subst_ty_var t
  | Sort.SArrow (t2, t3) -> Sort.SArrow (subst_ty theta t2, subst_ty theta t3)
  | T_dt.SDT(dt) -> T_dt.SDT(subst_dt theta dt)
  | _ -> t

let subst_eql theta eql =
  List.map eql ~f:(fun (t1, t2) -> subst_ty theta t1, subst_ty theta t2)

let compose_subst theta2 (theta1: tyconstr Set.Poly.t) =
  let theta11 = 
    Set.Poly.map theta1 ~f:(
      function
      | CEq (tx, t) -> CEq (tx, subst_ty theta2 t)
      | CNum (t) -> CNum (t)
    ) in
  Set.Poly.fold theta2 ~init:theta11 ~f:(
    fun tau ->
      function 
      |CEq (tx, t) ->
        if Set.Poly.exists theta1 ~f:(
            function | CEq (tx1, _) ->  Stdlib.(=) tx tx1 | _ -> false
          ) then tau
        else Set.Poly.add tau @@ CEq (tx, t)
      |CNum (tx) -> Set.Poly.add tau @@ CNum (tx)
  ) 

let unification eql =
  let rec solve eql theta =
    match eql with
    | [] -> theta
    | (t1, t2)::eql2 -> 
      if Stdlib.(=) t1 t2 then solve eql2 theta
      else begin 
        Debug.print @@ lazy (sprintf "unify : [%s] = [%s]" (Term.str_of_sort t1) (Term.str_of_sort t2));
        match (t1, t2) with
        | (Sort.SArrow(t11,t12),Sort.SArrow(t21,t22)) -> 
          solve ((t11,t21)::(t12,t22)::eql2) theta
        | (Sort.SVar _, _) -> 
          if (occurs t1 t2) then failwith "unification failed"
          else solve
              (subst_eql (Set.Poly.singleton @@ CEq (t1, t2)) eql2) 
              (compose_subst (Set.Poly.singleton @@ CEq (t1, t2)) theta)
        | (_, Sort.SVar _) ->
          if (occurs t2 t1)  then failwith "unification failed"
          else solve 
              (subst_eql (Set.Poly.singleton @@ CEq (t2, t1)) eql2) 
              (compose_subst (Set.Poly.singleton @@ CEq (t2, t1)) theta)
        | (T_dt.SDT(dt1), T_dt.SDT(dt2)) ->
          let args1 = Datatype.args_of dt1 in
          let args2 = Datatype.args_of dt2 in
          let eql3 = List.map2_exn args1 args2 ~f:(fun arg1 arg2 -> (arg1, arg2)) in
          solve (eql3 @ eql2) (theta)
        | _ ->
          Debug.print @@ lazy (sprintf "term theta:%s" @@ str_of_tyconstr_set theta);
          failwith (sprintf "unknown case: %s = %s ,unification failed" (Term.str_of_sort t1) (Term.str_of_sort t2))
      end
  in solve eql Set.Poly.empty

let is_unknown_sort = function
  | Sort.SVar _  -> true
  | _ -> false

let rec inf_term term =
  let open Term in
  Debug.print @@ lazy (sprintf "inf term:%s" (str_of term));
  let ty, theta = match term with
    | Var (_, sort, _) -> sort, Set.Poly.empty
    | FunApp(T_num.Value (_, svar), _, _) -> Sort.SVar(svar), Set.Poly.singleton (CNum (Sort.SVar(svar)))
    | FunApp(T_int.Int _, _, _) -> T_int.SInt, Set.Poly.empty
    | FunApp(T_real.Real _, _, _) -> T_real.SReal, Set.Poly.empty
    | FunApp(T_real_int.ToReal, _, _) -> T_real.SReal, Set.Poly.empty
    | FunApp(T_real_int.ToInt, _, _) -> T_int.SInt, Set.Poly.empty
    | FunApp(T_num.NAdd svar, [t1; t2], _) 
    | FunApp(T_num.NMult svar, [t1; t2], _) 
    | FunApp(T_num.NDiv svar, [t1; t2], _) 
    | FunApp(T_num.NSub svar, [t1; t2], _) 
    | FunApp(T_num.NPower svar, [t1; t2], _) ->
      let ty0 = Sort.SVar(svar) in
      let theta0 = Set.Poly.singleton (CNum (Sort.SVar(svar))) in
      let ty1, theta1 = inf_term t1 in
      let ty2, theta2 = inf_term t2 in
      let ty11 = subst_ty theta2 ty1 in
      let theta3 =  unification [ty0, ty2; ty11, ty2] in
      let theta4 = compose_subst theta3 @@ compose_subst theta2 @@ compose_subst theta1 theta0 in
      (if not @@ is_unknown_sort ty11 then ty11 else ty2), theta4
    | FunApp(T_num.NNeg svar, [t1], _) -> 
      let ty0 = Sort.SVar(svar) in
      let theta0 = Set.Poly.singleton (CNum (Sort.SVar(svar))) in
      let ty1, theta1 = inf_term t1 in
      let theta2 = unification [ty0, ty1] in
      let theta2 = compose_subst theta2 @@ compose_subst theta1 theta0 in
      ty1, theta2
    | FunApp(T_int.Add, [t1; t2], _)
    | FunApp(T_int.Sub, [t1; t2], _)
    | FunApp(T_int.Mult, [t1; t2], _)
    | FunApp(T_int.Div, [t1; t2], _)
    | FunApp(T_int.Mod, [t1; t2], _)
    | FunApp(T_int.Power, [t1; t2], _) 
    | FunApp(T_int.Rem, [t1; t2], _) ->
      let ty1, theta1 = inf_term t1 in
      let ty2, theta2 = inf_term t2 in
      let ty11 = subst_ty theta2 ty1 in
      let theta3 = unification [(ty11, T_int.SInt); (ty2, T_int.SInt)] in
      let theta4 = compose_subst theta3 @@ compose_subst theta2 theta1 in
      T_int.SInt, theta4
    | FunApp(T_int.Neg, [t1], _) ->
      let ty1, theta1 = inf_term t1 in
      let theta2 = unification[ty1, T_int.SInt] in
      let theta3 = compose_subst theta2 theta1 in
      T_int.SInt, theta3
    | FunApp(T_real.RAdd, [t1; t2], _)
    | FunApp(T_real.RSub, [t1; t2], _)
    | FunApp(T_real.RMult, [t1; t2], _)
    | FunApp(T_real.RDiv, [t1; t2], _)
    | FunApp(T_real.RPower, [t1; t2], _) ->
      let ty1, theta1 = inf_term t1 in
      let ty2, theta2 = inf_term t2 in
      let ty11 = subst_ty theta2 ty1 in
      let theta3 = unification [(ty11, T_real.SReal); (ty2, T_real.SReal)] in
      let theta4 = compose_subst theta3 @@ compose_subst theta2 theta1 in
      T_real.SReal, theta4
    | FunApp(T_real.RNeg, [t1], _) ->
      let ty1, theta1 = inf_term t1 in
      let theta2 = unification[ty1, T_real.SReal] in
      let theta3 = compose_subst theta2 theta1 in
      T_real.SReal, theta3
    | FunApp(T_dt.DTCons(_, tys, dt), ts, _) -> 
      let tys1, thetas = List.unzip @@ List.map ts ~f:inf_term in
      let theta = unification @@ List.map2_exn tys tys1 ~f:(fun ty ty1 -> (ty, ty1)) in
      Debug.print @@ lazy (sprintf "[after inf cons term]term theta:%s" @@ str_of_tyconstr_set theta);
      (Datatype.sort_of dt), List.fold_left thetas ~init:theta ~f:(fun ret theta -> compose_subst ret theta)
    | FunApp(T_dt.DTSel(_, dt, sort), [t], _) -> 
      let ty_dt = T_dt.SDT(dt) in
      let ty1, theta1 = inf_term t in
      let theta2 = unification [ty_dt, ty1] in
      sort, compose_subst theta1 theta2
    | FunApp(T_bool.Formula phi, _, _) -> inf_formula phi
    | FunApp(T_bool.IfThenElse, [t1;t2;t3], _) ->
      let ty1, theta1 = inf_term t1 in
      let ty2, theta2 = inf_term t2 in
      let ty3, theta3 = inf_term t3 in
      let theta11 = unification[ty1, T_bool.SBool] in
      let ty21 = subst_ty theta3 ty2 in
      let theta4 = unification [ty21, ty3] in
      let theta5 = compose_subst theta3 @@ compose_subst theta2 @@ compose_subst theta4 @@ compose_subst theta11 theta1 in
      (if not @@ is_unknown_sort ty21 then ty21 else ty3), theta5
    | FunApp(T_array.ASelect, [t1; t2], _) ->
      let ty1, theta1 = inf_term t1 in
      let ty2, theta2 = inf_term t2 in
      let tyi = T_array.index_sort_of ty1 in
      let tye = T_array.elem_sort_of ty1 in
      let theta21 = unification[tyi, ty2] in
      tye, compose_subst theta21 @@ compose_subst  theta2 theta1 
    | FunApp(T_array.AStore, [t1; t2; t3], _) ->
      let ty1, theta1 = inf_term t1 in
      let ty2, theta2 = inf_term t2 in
      let ty3, theta3 = inf_term t3 in
      let tyi = T_array.index_sort_of ty1 in
      let tye = T_array.elem_sort_of ty1 in
      let theta21 = unification[tyi, ty2; tye, ty3] in
      ty1, compose_subst theta21 @@ compose_subst theta3 @@ compose_subst theta2 theta1 
    | FunApp(T_array.AConst (T_array.SArray (_, tye) as ty_arr), [t1], _) ->
      let ty1, theta1 = inf_term t1 in
      let theta2 = unification [tye, ty1] in
      ty_arr, compose_subst theta2 theta1 
    | FunApp(FVar(_, sorts), ts, _) ->
      let sargs, ret = List.split_n sorts (List.length sorts - 1) in
      let theta = List.fold2_exn sargs ts ~init:Set.Poly.empty ~f:(
          fun theta ty t -> 
            let ty1, theta1 = inf_term t in
            let theta11 = unification[ty1, ty] in
            compose_subst theta11 @@ compose_subst theta1 theta
        )
      in (List.hd_exn ret), theta
    | FunApp(T_recfvar.RecFVar(_, env, ty, _), ts, _) -> 
      let tys1 = snd @@ List.unzip env in
      let tys2, thetas =  List.unzip @@ List.map ts ~f:(inf_term) in
      let theta1 = unification @@ List.zip_exn tys1 tys2 in
      ty, List.fold_left thetas ~init:theta1 ~f:(fun ret theta -> compose_subst ret theta)
    | _ -> failwith @@ sprintf "inf unkonwn term:%s" (Term.str_of term)
  in
  Debug.print @@ lazy (sprintf "term theta:%s" @@ str_of_tyconstr_set theta);
  ty, theta
and inf_atom atom =
  let open Atom in
  Debug.print @@ lazy (sprintf "inf atom:%s" (str_of atom));
  let ty, theta = match atom with
    | App(Predicate.Psym T_bool.Eq, [t1; t2], _)  | App(Predicate.Psym T_bool.Neq, [t1; t2], _) ->
      let ty1, theta1 = inf_term t1 in
      let ty2, theta2 = inf_term t2 in
      let ty11 = subst_ty theta2 ty1 in
      let theta3 =  unification [ty11, ty2] in
      let theta4 = compose_subst theta3 @@ compose_subst theta2 theta1 in
      T_bool.SBool, theta4
    | App(Predicate.Psym T_num.NGt svar, [t1; t2], _)   | App(Predicate.Psym T_num.NLt svar, [t1; t2], _) 
    | App(Predicate.Psym T_num.NGeq svar, [t1; t2], _)   | App(Predicate.Psym T_num.NLeq svar, [t1; t2], _) ->
      let ty0 = Sort.SVar(svar) in
      let theta0 = Set.Poly.singleton (CNum (Sort.SVar(svar))) in
      let ty1, theta1 = inf_term t1 in
      let ty2, theta2 = inf_term t2 in
      let ty11 = subst_ty theta2 ty1 in
      let theta3 =  unification [ty11, ty2; ty0, ty2] in
      let theta4 = compose_subst theta3 @@ compose_subst theta2 @@ compose_subst theta1 theta0 in
      T_bool.SBool, theta4
    | App(Predicate.Psym T_int.Gt, [t1; t2], _)   | App(Predicate.Psym T_int.Lt, [t1; t2], _) 
    | App(Predicate.Psym T_int.Geq, [t1; t2], _)   | App(Predicate.Psym T_int.Leq, [t1; t2], _) ->
      let ty1, theta1 = inf_term t1 in
      let ty2, theta2 = inf_term t2 in
      let ty11 = subst_ty theta2 ty1 in
      let theta3 = unification [(ty11, T_int.SInt); (ty2, T_int.SInt)] in
      let theta4 = compose_subst theta3 @@ compose_subst theta2 theta1 in
      T_bool.SBool, theta4
    | App(Predicate.Psym T_real.RGt, [t1; t2], _)   | App(Predicate.Psym T_real.RLt, [t1; t2], _) 
    | App(Predicate.Psym T_real.RGeq, [t1; t2], _)   | App(Predicate.Psym T_real.RLeq, [t1; t2], _) ->
      let ty1, theta1 = inf_term t1 in
      let ty2, theta2 = inf_term t2 in
      let ty11 = subst_ty theta2 ty1 in
      let theta3 = unification [(ty11, T_real.SReal); (ty2, T_real.SReal)] in
      let theta4 = compose_subst theta3 @@ compose_subst theta2 theta1 in
      T_bool.SBool, theta4
    | App(Predicate.Psym T_dt.IsCons (_, dt), [t1], _) ->
      let ty1 = T_dt.SDT(dt) in
      let ty2, theta1 = inf_term t1 in
      let theta2 = unification [ty1, ty2] in
      T_bool.SBool, compose_subst theta1 theta2
    | App(Predicate.Var (_, par_tys), ts, _) ->
      let ty_thetas = List.map ts ~f:(fun t -> inf_term t) in
      let theta1 = unification @@ List.fold2_exn par_tys ty_thetas ~init:[] ~f:(
          fun ret par_ty (ty, _) ->
            (ty, par_ty)::ret
        ) in
      let theta2 = List.fold_left ty_thetas ~init:theta1 ~f:(
          fun ret (_, theta) ->
            compose_subst theta ret
        ) in
      T_bool.SBool, theta2
    | App(Predicate.Fixpoint (_, _, _, phi), ts, _) -> 
      Debug.print @@ lazy (sprintf "function formula:%s" (Formula.str_of phi));
      let theta0 = snd @@ inf_formula phi in
      let ty_thetas = List.map ts ~f:(fun t -> inf_term t) in
      let theta1 = List.fold_left ty_thetas ~init:theta0 ~f:(
          fun ret ty_theta ->
            let theta = snd ty_theta in
            compose_subst theta ret
        ) 
      in
      T_bool.SBool, theta1
    | _ -> T_bool.SBool, Set.Poly.empty
  in 
  Debug.print @@ lazy (sprintf "atom theta:%s" @@ str_of_tyconstr_set theta);
  ty, theta
and inf_formula phi =
  let open Formula in
  Debug.print @@ lazy (sprintf "inf formula:%s" (str_of phi));
  let ty, theta = match phi with
    | Atom (atom, _) -> inf_atom atom
    | UnaryOp(_, phi1, _) -> inf_formula phi1
    | BinaryOp(_, phi1, phi2, _) -> 
      let _, theta1 = inf_formula phi1 in
      let _, theta2 = inf_formula phi2 in
      let theta3 = compose_subst theta2 theta1 in
      T_bool.SBool, theta3
    | Bind(_, _, body, _) 
    | LetRec(_, body, _) ->  inf_formula body
  in
  Debug.print @@ lazy (sprintf "formula theta:%s" @@ str_of_tyconstr_set theta);
  ty, theta

let has_cnum theta sort =
  Set.Poly.exists theta ~f:(function | CNum (s) -> Stdlib.(=) s sort | _ -> false)

let look_up theta sort =
  Set.Poly.find theta ~f:(function |CEq (s, _) -> if Stdlib.(=) s sort then true else false | _ -> false)

let rec subst_sort ~default ~eqs ~nums sort =
  match sort with
  | T_dt.SDT(dt) -> 
    let args = Datatype.args_of dt in
    let args' = List.map args ~f:(subst_sort ~default ~eqs ~nums) in
    T_dt.SDT(Datatype.update_args dt args')
  | Sort.SVar _  ->
    begin match look_up eqs sort with
      | Some (CEq (_, sort)) ->
        if has_cnum nums sort then
          match sort with
          | T_int.SInt | T_real.SReal -> sort
          | Sort.SVar _ -> T_int.SInt
          | _ -> failwith "sort must be int / real"
        else sort
      | None -> default
      | _ -> assert false
    end
  | _ -> sort

let subst_dt ~eqs ~nums dt =
  Debug.print @@ lazy (sprintf "subst dt :%s" @@ Datatype.full_name_of dt);
  let args = Datatype.args_of dt in
  let args' = List.map args ~f:(fun arg -> 
      subst_sort ~eqs ~nums ~default:arg arg
    ) in
  Datatype.update_args dt args'

let rec subst_term ~nums ~eqs term  =
  let open Term in
  match term with
  | Var(tvar, sort, info) ->  Var(tvar, subst_sort ~nums ~eqs sort ~default:sort, info)
  | FunApp(T_num.Value (_, svar) as value, _, info) -> 
    let sort = Sort.SVar(svar) in
    FunApp(T_num.fsym_of_num_fsym value @@ subst_sort ~nums ~eqs ~default:T_int.SInt sort, [], info)
  | FunApp(T_real_int.ToReal, [Var(tvar, _, info)], _) -> Var(tvar, T_real.SReal, info)
  | FunApp(T_real_int.ToInt, [Var(tvar, _, info)], _) -> Var(tvar, T_int.SInt, info)
  | FunApp(T_num.NAdd svar as op ,[t1; t2], info)
  | FunApp(T_num.NSub svar as op ,[t1; t2], info)
  | FunApp(T_num.NMult svar as op ,[t1; t2], info)
  | FunApp(T_num.NDiv svar as op ,[t1; t2], info)
  | FunApp(T_num.NPower svar as op ,[t1; t2], info) ->
    let t1' = subst_term ~nums ~eqs t1 in
    let t2' = subst_term ~nums ~eqs t2 in
    let sort = Sort.SVar(svar) in
    FunApp(T_num.fsym_of_num_fsym op @@ subst_sort ~default:T_int.SInt ~nums ~eqs sort, [t1'; t2'], info)
  | FunApp(T_num.NNeg svar as op, [t1], info) ->
    let t1' = subst_term ~nums ~eqs t1 in
    let sort = Sort.SVar(svar) in
    FunApp(T_num.fsym_of_num_fsym op @@ subst_sort ~default:T_int.SInt ~nums ~eqs sort, [t1'], info)
  | FunApp(T_dt.DTCons (name, args, dt), ts, info) ->
    let args' = List.map args ~f:(fun arg -> subst_sort ~default:arg ~nums ~eqs arg) in
    FunApp(T_dt.DTCons (name, args', subst_dt ~nums ~eqs dt), List.map ts ~f:(subst_term ~nums ~eqs), info)
  | FunApp(T_dt.DTSel (name, dt, ret_sort), ts, info) ->
    FunApp(T_dt.DTSel (name, subst_dt ~eqs ~nums dt, subst_sort ~eqs ~nums ret_sort ~default:ret_sort), List.map ts ~f:(subst_term ~nums ~eqs), info)
  | FunApp(T_bool.Formula phi, ts, info) -> FunApp(T_bool.Formula (subst_formula nums eqs phi), ts, info)
  | FunApp(op, ts, info) -> FunApp(op, List.map ts ~f:(subst_term ~nums ~eqs), info)
and subst_atom nums eqs atom =
  let open Atom in
  match atom with
  | App(Predicate.Psym (T_num.NGt svar as op), [t1; t2], info)   | App(Predicate.Psym (T_num.NLt svar as op), [t1; t2], info) 
  | App(Predicate.Psym (T_num.NGeq svar as op), [t1; t2], info)   | App(Predicate.Psym (T_num.NLeq svar as op), [t1; t2], info) -> 
    let t1' = subst_term ~nums ~eqs t1 in
    let t2' = subst_term ~nums ~eqs t2 in
    let sort = Sort.SVar(svar) in
    App(Predicate.Psym (T_num.psym_of_num_psym op @@ subst_sort ~nums ~eqs ~default:sort sort), [t1'; t2'], info)
  | App(Predicate.Psym (T_dt.IsCons (name, dt)), [t], info) ->
    App(Predicate.Psym (T_dt.IsCons (name, subst_dt dt ~nums ~eqs)), [subst_term ~eqs ~nums t], info)
  | App(Predicate.Fixpoint (fix, ps, senv, phi), ts, info) -> 
    App(Predicate.Fixpoint (fix, ps, senv, subst_formula nums eqs phi), List.map ts ~f:(subst_term ~nums ~eqs), info) 
  | App(op, ts, info) -> App(op, List.map ts ~f:(subst_term ~nums ~eqs), info)
  |_ -> atom
and subst_formula nums eqs formula =
  let open Formula in
  match formula with
  | Atom(atom, info) -> Atom(subst_atom nums eqs atom, info)
  | UnaryOp(op, phi1, info) -> UnaryOp(op, subst_formula nums eqs phi1, info)
  | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op, subst_formula nums eqs phi1, subst_formula nums eqs phi2, info)
  | Bind(binder, bounds, body, info) -> Bind(binder, bounds, subst_formula nums eqs body, info)
  | LetRec(funcs, body, info) ->  
    let funcs' = List.map funcs ~f:(fun (fix, p, env, phi) -> (fix, p, env, subst_formula nums eqs phi)) in
    LetRec(funcs' , subst_formula nums eqs body, info) 

let typeinf_term term =
  let theta = snd @@ inf_term term in
  let cnums = Set.Poly.filter theta ~f:is_cnum in
  let ceqs = Set.Poly.filter theta ~f:is_ceq in
  subst_term ~nums:cnums ~eqs:ceqs term

let typeinf phi =
  let theta = snd @@ inf_formula phi in
  let cnums = Set.Poly.filter theta ~f:is_cnum in
  let ceqs = Set.Poly.filter theta ~f:is_ceq in
  Debug.print @@ lazy (sprintf "theta:%s" @@ str_of_tyconstr_set theta);
  let ret = subst_formula cnums ceqs phi in
  Debug.print @@ lazy (sprintf "type infed :%s" (Formula.str_of ret));
  Debug.print @@ lazy (sprintf "dtenv after type inf%s" (DTEnv.str_of @@ DTEnv.of_formula ret));
  ret