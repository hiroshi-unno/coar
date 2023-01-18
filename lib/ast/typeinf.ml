open Core
open LogicOld
open Ident
open Common
open Common.Ext

let verbose = false
module Debug = Debug.Make (val if verbose then Debug.Config.enable else Debug.Config.disable)

(** whether to instantiate Num to Int *)
let instantiate_num_to_int = false

type constr = CEq of Sort.t * Sort.t | CNum of Ident.svar
let is_ceq = function CEq _ -> true | _ -> false
let is_cnum = function CNum _ -> true | _ -> false
let str_of_constr = function
  | CEq (sort1, sort2) ->
    sprintf "  [CEq:%s = %s]"
      (Term.str_of_sort sort1)
      (Term.str_of_sort sort2)
  | CNum svar ->
    sprintf "  [CNum: %s]"
      (Ident.name_of_svar svar)
let str_of_constrs cs = String.concat_map_set ~sep:"\n" ~f:str_of_constr cs

let rec cgen_term senv term = let open Term in
  Debug.print @@ lazy (sprintf "cgen_term: %s" @@ str_of term);
  let senv, ty, constrs =
    match term with
    | Var (var, sort, _) ->
      let sort1 = match Map.Poly.find senv var with None -> sort | Some sort -> sort in
      Map.Poly.set senv ~key:var ~data:sort1,
      sort1,
      Set.Poly.singleton (CEq (sort, sort1))
    | FunApp (FVar (_, sorts), ts, _) ->
      let sargs, ret = List.split_n sorts (List.length sorts - 1) in
      let constrs, senv =
        List.fold2_exn sargs ts ~init:(Set.Poly.empty, senv) ~f:(fun (constrs, senv) ty t ->
            let senv, ty1, constrs1 = cgen_term senv t in
            Set.Poly.union_list [constrs; constrs1; Set.Poly.singleton (CEq (ty1, ty))],
            senv)
      in
      senv, List.hd_exn ret, constrs
    | FunApp (T_bool.Formula phi, _, _) ->
      let senv, constrs = cgen_formula senv phi in
      senv, T_bool.SBool, constrs
    | FunApp (T_bool.IfThenElse, [t1; t2; t3], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      let senv, ty3, constrs3 = cgen_term senv t3 in
      senv, ty2,
      Set.Poly.union_list
        [constrs1; constrs2; constrs3;
         Set.Poly.of_list [CEq (ty1, T_bool.SBool); CEq (ty2, ty3)]]
    | FunApp (T_int.Int _, [], _) ->
      senv, T_int.SInt, Set.Poly.empty
    | FunApp (T_real.Real _, [], _) ->
      senv, T_real.SReal, Set.Poly.empty
    | FunApp (T_real_int.ToReal, [t], _) ->
      let senv, ty, constrs = cgen_term senv t in
      senv, T_real.SReal,
      Set.Poly.union constrs (Set.Poly.singleton (CEq (ty, T_int.SInt)))
    | FunApp (T_real_int.ToInt, [t], _) ->
      let senv, ty, constrs = cgen_term senv t in
      senv, T_int.SInt,
      Set.Poly.union constrs (Set.Poly.singleton (CEq (ty, T_real.SReal)))
    | FunApp (T_num.Value (_, svar), [], _) ->
      senv, Sort.SVar svar, Set.Poly.singleton (CNum svar)
    | FunApp (T_num.NNeg svar, [t1], _) ->
      let senv, ty, constrs = cgen_term senv t1 in
      senv, ty,
      Set.Poly.union constrs (Set.Poly.of_list [CNum svar; CEq (ty, Sort.SVar svar)])
    | FunApp ((T_num.NAdd svar | T_num.NMult svar | T_num.NDiv svar | T_num.NSub svar | T_num.NPower svar), [t1; t2], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      senv, ty1,
      Set.Poly.union_list
        [constrs1; constrs2;
         Set.Poly.of_list [CNum svar; CEq (ty1, Sort.SVar svar); CEq (ty1, ty2)]]
    | FunApp (T_int.Neg, [t1], _) ->
      let senv, ty, constrs = cgen_term senv t1 in
      senv, T_int.SInt,
      Set.Poly.union constrs (Set.Poly.singleton (CEq (ty, T_int.SInt)))
    | FunApp ((T_int.Add | T_int.Sub | T_int.Mult | T_int.Div | T_int.Mod | T_int.Power | T_int.Rem), [t1; t2], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      senv, T_int.SInt,
      Set.Poly.union_list
        [constrs1; constrs2;
         Set.Poly.of_list [CEq (ty1, T_int.SInt); CEq (ty1, ty2)]]
    | FunApp (T_real.RNeg, [t1], _) ->
      let senv, ty, constrs = cgen_term senv t1 in
      senv, T_real.SReal,
      Set.Poly.union constrs (Set.Poly.singleton (CEq (ty, T_real.SReal)))
    | FunApp ((T_real.RAdd | T_real.RSub | T_real.RMult | T_real.RDiv | T_real.RPower), [t1; t2], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      senv, T_real.SReal,
      Set.Poly.union_list
        [constrs1; constrs2;
         Set.Poly.of_list [CEq (ty1, T_real.SReal); CEq (ty1, ty2)]]
    | FunApp (T_dt.DTCons (_, tys, dt), ts, _) ->
      let senv, tys', constrss = cgen_terms senv ts in
      senv, Datatype.sort_of dt,
      Set.Poly.union_list @@
      (Set.Poly.of_list @@ List.map2_exn tys tys' ~f:(fun ty1 ty2 -> CEq (ty1, ty2))) ::
      constrss
    | FunApp (T_dt.DTSel (_, dt, sort), [t], _) ->
      let senv, ty, constrs = cgen_term senv t in
      senv, sort,
      Set.Poly.union constrs (Set.Poly.singleton (CEq (T_dt.SDT dt, ty)))
    | FunApp (T_tuple.TupleCons sorts, ts, _) ->
      let senv, tys, constrss = cgen_terms senv ts in
      senv, T_tuple.STuple tys,
      Set.Poly.union_list @@
      (Set.Poly.of_list @@ List.map2_exn sorts tys ~f:(fun ty1 ty2 -> CEq (ty1, ty2))) ::
      constrss
    | FunApp (T_tuple.TupleSel (sorts, i), [t], _) ->
      let senv, ty, constrs = cgen_term senv t in
      senv, List.nth_exn sorts i,
      Set.Poly.union constrs (Set.Poly.singleton (CEq (T_tuple.STuple sorts, ty)))
    | FunApp (T_array.AConst (s1, s2), [t1], _) ->
      let senv, ty, constrs = cgen_term senv t1 in
      senv, T_array.SArray (s1, s2),
      Set.Poly.union constrs (Set.Poly.singleton (CEq (s2, ty)))
    | FunApp (T_array.ASelect (s1, s2), [t1; t2], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      senv, T_array.elem_sort_of ty1,
      Set.Poly.union_list
        [constrs1; constrs2;
         Set.Poly.of_list
           [CEq (T_array.index_sort_of ty1, ty2);
            CEq (s1, ty2);
            CEq (T_array.elem_sort_of ty1, s2)]]
    | FunApp (T_array.AStore (s1, s2), [t1; t2; t3], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      let senv, ty3, constrs3 = cgen_term senv t3 in
      senv, ty1,
      Set.Poly.union_list
        [constrs1; constrs2; constrs3;
         Set.Poly.of_list
           [CEq (T_array.index_sort_of ty1, ty2);
            CEq (s1, ty2);
            CEq (T_array.elem_sort_of ty1, s2);
            CEq (T_array.elem_sort_of ty1, ty3)]]
    | FunApp (T_string.StringConst _, [], _) ->
      senv, T_string.SString, Set.Poly.empty
    | FunApp ((T_sequence.Epsilon | T_sequence.Symbol _), [], _) ->
      senv, T_sequence.SFinSequence, Set.Poly.empty
    | FunApp ((T_sequence.Concat fin | T_sequence.LeftQuotient fin | T_sequence.RightQuotient fin), [t1; t2], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      senv, ty2,
      Set.Poly.union_list
        [constrs1; constrs2;
         Set.Poly.of_list
           [CEq (ty1, T_sequence.SFinSequence);
            CEq (ty2, if fin then T_sequence.SFinSequence else T_sequence.SInfSequence)]]
    | LetTerm (_, sort, def, body, _) ->
      let senv, ty1, constrs1 = cgen_term senv def in
      let senv, ty2, constrs2 = cgen_term senv body in
      senv, ty2,
      Set.Poly.union_list [constrs1; constrs2; Set.Poly.singleton (CEq (ty1, sort))]
    | _ ->
      failwith @@ sprintf "inf unknown term:%s" (Term.str_of term)
  in
  Debug.print @@ lazy (sprintf "term constrs:%s" @@ str_of_constrs constrs);
  senv, ty, constrs
and cgen_terms senv terms =
  let senv, ret =
    List.fold terms ~init:(senv, []) ~f:(fun (senv, acc) term ->
        let senv', ty, constrs = cgen_term senv term in
        senv', (ty, constrs) :: acc)
  in
  let tys, constrss = List.unzip @@ List.rev ret in
  senv, tys, constrss
and cgen_atom senv atom = let open Atom in
  Debug.print @@ lazy (sprintf "cgen_atom: %s" @@ str_of atom);
  let senv, constrs =
    match atom with
    | App (Predicate.Var (Pvar var, par_tys), ts, _) ->
      let senv, par_tys, constrs0 =
        match Map.Poly.find senv (Tvar var) with
        | Some t ->
          senv, Sort.args_of t,
          Set.Poly.of_list @@ List.map2_exn par_tys (Sort.args_of t) ~f:(fun ty1 ty2 -> CEq (ty1, ty2))
        | None ->
          Map.Poly.add_exn senv ~key:(Tvar var) ~data:(Sort.mk_fun @@ par_tys @ [T_bool.SBool]),
          par_tys,
          Set.Poly.empty
      in
      let senv, tys, constrss = cgen_terms senv ts in
      let constrs1 =
        Set.Poly.of_list @@ List.map2_exn par_tys tys ~f:(fun ty1 ty2 -> CEq (ty1, ty2))
      in
      senv, Set.Poly.union_list @@ constrs0 :: constrs1 :: constrss
    | App (Predicate.Fixpoint (_, _, _, phi), ts, _) ->
      Debug.print @@ lazy (sprintf "function formula:%s" @@ Formula.str_of phi);
      let senv, constrs = cgen_formula senv phi in
      let senv, _tys(*ToDo*), constrss = cgen_terms senv ts in
      senv, Set.Poly.union_list @@ constrs :: constrss
    | App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [t1; t2], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      Debug.print @@ lazy (sprintf "info eq: %s:%s = %s:%s"
                             (Term.str_of t1)
                             (Term.str_of_sort ty1)
                             (Term.str_of t2)
                             (Term.str_of_sort ty2));
      senv,
      Set.Poly.union_list
        [constrs1; constrs2; Set.Poly.singleton (CEq (ty1, ty2))]
    | App (Predicate.Psym (T_num.NGt svar | T_num.NLt svar | T_num.NGeq svar | T_num.NLeq svar), [t1; t2], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      senv,
      Set.Poly.union_list
        [constrs1; constrs2;
         Set.Poly.of_list [CNum svar; CEq (ty1, ty2); CEq (ty1, Sort.SVar svar)]]
    | App (Predicate.Psym (T_int.Gt | T_int.Lt | T_int.Geq | T_int.Leq), [t1; t2], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      senv,
      Set.Poly.union_list
        [constrs1; constrs2;
         Set.Poly.of_list [CEq (ty1, ty2); CEq (ty1, T_int.SInt)]]
    | App (Predicate.Psym (T_real.RGt | T_real.RLt | T_real.RGeq | T_real.RLeq), [t1; t2], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      senv,
      Set.Poly.union_list
        [constrs1; constrs2; Set.Poly.of_list [CEq (ty1, ty2); CEq (ty1, T_real.SReal)]]
    | App (Predicate.Psym (T_tuple.IsTuple sorts | T_tuple.NotIsTuple sorts), [t1], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      senv,
      Set.Poly.union constrs1 (Set.Poly.singleton (CEq (T_tuple.STuple sorts, ty1)))
    | App (Predicate.Psym (T_dt.IsCons (_, dt) | T_dt.NotIsCons (_, dt)), [t1], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      senv, Set.Poly.union constrs1 (Set.Poly.singleton (CEq (T_dt.SDT dt, ty1)))
    | App (Predicate.Psym (T_sequence.IsPrefix fin | T_sequence.NotIsPrefix fin), [t1; t2], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      let sort = if fin then T_sequence.SFinSequence else T_sequence.SInfSequence in
      senv,
      Set.Poly.union_list
        [constrs1; constrs2; Set.Poly.of_list [CEq (ty1, ty2); CEq (ty1, sort)]]
    | App (Predicate.Psym (T_sequence.InRegExp (fin, _regexp) | T_sequence.NotInRegExp (fin, _regexp)), [t1], _) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let sort = if fin then T_sequence.SFinSequence else T_sequence.SInfSequence in
      senv, Set.Poly.union constrs1 (Set.Poly.singleton (CEq (ty1, sort)))
    | _ -> senv, Set.Poly.empty
  in
  Debug.print @@ lazy (sprintf "atom constrs:%s" @@ str_of_constrs constrs);
  senv, constrs
and cgen_rand senv rand = let open Rand in
  Debug.print @@ lazy (sprintf "cgen_rand: %s" @@ str_of rand);
  let senv, ty, constrs =
    match rand with
    | Uniform (t1, t2)
    | Gauss (t1, t2) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      senv, T_real.SReal,
      Set.Poly.union_list
        [constrs1; constrs2;
         Set.Poly.of_list [CEq (ty1, T_real.SReal); CEq (ty2, T_real.SReal)]]
    | IntUniform (t1, t2) ->
      let senv, ty1, constrs1 = cgen_term senv t1 in
      let senv, ty2, constrs2 = cgen_term senv t2 in
      senv, T_int.SInt,
      Set.Poly.union_list
        [constrs1; constrs2;
         Set.Poly.of_list [CEq (ty1, T_int.SInt); CEq (ty2, T_int.SInt)]]
  in
  Debug.print @@ lazy (sprintf "rand constrs: %s" @@ str_of_constrs constrs);
  senv, ty, constrs
and cgen_formula senv phi = let open Formula in
  Debug.print @@ lazy (sprintf "cgen_formula: %s" @@ str_of phi);
  let senv, constrs =
    match phi with
    | Atom (atom, _) ->
      cgen_atom senv atom
    | UnaryOp (_, phi1, _) ->
      cgen_formula senv phi1
    | BinaryOp (_, phi1, phi2, _) ->
      let senv, constrs1 = cgen_formula senv phi1 in
      let senv, constrs2 = cgen_formula senv phi2 in
      senv, Set.Poly.union constrs1 constrs2
    | Bind (Random rand, bounds, body, _) ->
      let senv, ty, constrs1 = cgen_rand senv rand in
      let x, sort = List.hd_exn bounds in
      let senv = Map.Poly.set senv ~key:x ~data:sort in
      let senv, constrs2 = cgen_formula senv body in
      senv, Set.Poly.union_list [constrs1; constrs2; Set.Poly.singleton (CEq (ty, sort))]
    | Bind (_, bounds, body, _) ->
      let senv =
        List.fold bounds ~init:senv ~f:(fun acc (v, sort) -> Map.Poly.set acc ~key:v ~data:sort)
      in
      let senv, constrs = cgen_formula senv body in
      let senv =
        List.fold bounds ~init:senv ~f:(fun acc (v, _) -> Map.Poly.remove acc v)
      in
      senv, constrs
    | LetRec (_, body, _) ->
      cgen_formula senv body
    | LetFormula (var, sort, def, body, info) ->
      let senv, ty, constrs =
        cgen_term senv @@ Term.LetTerm (var, sort, def, T_bool.of_formula body, info)
      in
      senv, Set.Poly.add constrs (CEq (ty, T_bool.SBool))
  in
  Debug.print @@ lazy (sprintf "formula constrs: %s" @@ str_of_constrs constrs);
  senv, constrs

(* val sort_of_name : ?args:Sort.t list -> DTEnv.t -> string -> Sort.t *)
let sort_of_name ?(args=[]) dtenv = function
  | "bool"(* | "Bool"*) -> T_bool.SBool
  | "int"(* | "Int"*) -> T_int.SInt
  | "float"(* | "Real"*) -> T_real.SReal
  | "string" -> T_string.SString
  | "finseq" -> T_sequence.SFinSequence
  | "infseq" -> T_sequence.SInfSequence
  | "int_array" -> T_array.mk_array_sort T_int.SInt T_int.SInt
  (*| "list" -> Datatype.sort_of @@ ConstDatatype.list_dt*)
  | name ->
    match DTEnv.look_up_dt dtenv name with
    | Some dt ->
      if List.is_empty args then Datatype.sort_of dt
      else T_dt.SDT (Datatype.update_args dt args(*ToDo*))
    | _ -> (*ToDo: fix the following ad hoc treatment of recursive types*)
      if List.is_empty args then Sort.SVar (Svar name)
      else T_dt.SUS (name, args)

(* val subtype : (Ident.svar, Sort.t option) Map.Poly.t -> Sort.t -> Sort.t -> (Ident.svar, Sort.t option) Map.Poly.t * (Sort.e list * Sort.e) Set.Poly.t * (Sort.o * Sort.o) Set.Poly.t *)
let rec subtype map s1 s2 =
  (*ToDo: support higher-data-sorts and unresolved sort variables*)
  (*print_endline @@ Term.str_of_sort s1 ^ "\n<: " ^ Term.str_of_sort s2 ^ "\n";*)
  if Stdlib.(s1 = s2) then map, Set.Poly.empty, Set.Poly.empty
  else
    match s1, s2 with
    | Sort.SArrow (s11, se12), Sort.SArrow (s21, se22) ->
      let map, econstrs1, oconstrs1 = subtype map s21 s11 in
      let map, econstrs2, oconstrs2 = subeff map se12 se22 in
      map, Set.Poly.union econstrs1 econstrs2, Set.Poly.union oconstrs1 oconstrs2
    | T_tuple.STuple sorts1, T_tuple.STuple sorts2 ->
      List.fold2_exn sorts1 sorts2
        ~init:(map, Set.Poly.empty, Set.Poly.empty)
        ~f:(fun (map, econstrs, oconstrs) s1 s2 ->
            let map, econstrs', oconstrs' = subtype map s1 s2 in
            map, Set.Poly.union econstrs econstrs', Set.Poly.union oconstrs oconstrs')
    | T_dt.SDT dt1, T_dt.SDT dt2 when String.(dt1.name = dt2.name) ->
      List.fold2_exn (Datatype.args_of dt1) (Datatype.args_of dt2)
        ~init:(map, Set.Poly.empty, Set.Poly.empty)
        ~f:(fun (map, econstrs, oconstrs) s1 s2 ->
            let map, econstrs', oconstrs' = subtype map s1 s2(*ToDo*) in
            map, Set.Poly.union econstrs econstrs', Set.Poly.union oconstrs oconstrs')
    | T_dt.SDT dt1, T_dt.SUS (name2, sorts2) when String.(dt1.name = name2) ->
      (*ToDo: fix the ad hoc use of SUS*)
      List.fold2_exn (Datatype.args_of dt1) sorts2
        ~init:(map, Set.Poly.empty, Set.Poly.empty)
        ~f:(fun (map, econstrs, oconstrs) s1 s2 ->
            let map, econstrs', oconstrs' = subtype map s1 s2(*ToDo*) in
            map, Set.Poly.union econstrs econstrs', Set.Poly.union oconstrs oconstrs')
    | T_dt.SUS (name1, sorts1), T_dt.SDT dt2 when String.(name1 = dt2.name) ->
      (*ToDo: fix the ad hoc use of SUS*)
      List.fold2_exn sorts1 (Datatype.args_of dt2)
        ~init:(map, Set.Poly.empty, Set.Poly.empty)
        ~f:(fun (map, econstrs, oconstrs) s1 s2 ->
            let map, econstrs', oconstrs' = subtype map s1 s2(*ToDo*) in
            map, Set.Poly.union econstrs econstrs', Set.Poly.union oconstrs oconstrs')
    | T_dt.SUS (n1, sorts1), T_dt.SUS (n2, sorts2) when String.(n1 = n2) ->
      List.fold2_exn sorts1 sorts2
        ~init:(map, Set.Poly.empty, Set.Poly.empty)
        ~f:(fun (map, econstrs, oconstrs) s1 s2 ->
            let map, econstrs', oconstrs' = subtype map s1 s2(*ToDo*) in
            map, Set.Poly.union econstrs econstrs', Set.Poly.union oconstrs oconstrs')
    | T_array.SArray (s11, s12), T_array.SArray (s21, s22) ->
      let map, econstrs1, oconstrs1 = subtype map s21 s11(*ToDo*) in
      let map, econstrs2, oconstrs2 = subtype map s11 s21(*ToDo*) in
      let map, econstrs3, oconstrs3 = subtype map s12 s22(*ToDo*) in
      let map, econstrs4, oconstrs4 = subtype map s22 s12(*ToDo*) in
      map, Set.Poly.union_list [econstrs1; econstrs2; econstrs3; econstrs4],
      Set.Poly.union_list [oconstrs1; oconstrs2; oconstrs3; oconstrs4]
    | Sort.SVar svar, s when Map.Poly.mem map svar ->
      (match Map.Poly.find map svar with
       | None -> failwith "[MBcgen.subtype @ 1]"
       | Some None ->
         Map.Poly.set map ~key:svar ~data:(Some s)(*ToDo*), Set.Poly.empty, Set.Poly.empty
       | Some (Some s') -> subtype map s' s)
    | s, Sort.SVar svar when Map.Poly.mem map svar ->
      (match Map.Poly.find map svar with
       | None -> failwith "[MBcgen.subtype @ 2]"
       | Some None ->
         Map.Poly.set map ~key:svar ~data:(Some s)(*ToDo*), Set.Poly.empty, Set.Poly.empty
       | Some (Some s') -> subtype map s s')
    | Sort.SPoly (svs, s1), s2 ->
      let sub = Map.of_set_exn @@ Set.Poly.map svs ~f:(fun svar ->
          svar, Sort.SVar (Ident.mk_fresh_svar ())) in
      let s1 = Term.subst_sorts_sort sub s1 in
      let map =
        List.fold (Map.Poly.data sub) ~init:map ~f:(fun map -> function
            | Sort.SVar svar -> Map.Poly.add_exn map ~key:svar ~data:None | _ -> assert false)
      in
      subtype map s1 s2
    | _, _ ->
      failwith @@ sprintf "[MBcgen.subtype] %s and %s"
        (Term.str_of_sort s1) (Term.str_of_sort s2)
(* val subeff : (Ident.svar, Sort.t option) Map.Poly.t -> Sort.o * Sort.t * Sort.e -> Sort.o * Sort.t * Sort.e -> (Ident.svar, Sort.t option) Map.Poly.t * (Sort.e list * Sort.e) Set.Poly.t * (Sort.o * Sort.o) Set.Poly.t *)
and subeff map (o1, s1, e1) (o2, s2, e2) =
  (*print_endline @@ Term.str_of_sort s1 ^ " <: " ^ Term.str_of_sort s2;*)
  let map, econstrs, oconstrs = subtype map s1 s2 in
  (* assume that (o2, s2, e2) is monomorphic *)
  let sub = Map.Poly.filter_map map ~f:Fn.id in
  map,
  Set.Poly.add econstrs ([Term.subst_sorts_cont sub e1], e2)(*ToDo*),
  Set.Poly.add oconstrs (Term.subst_sorts_opsig sub o2, o1)(*ToDo*)
(* val generalize : sort_env_map -> Sort.t -> Sort.t *)
let generalize senv sort =
  let svs =
    Set.Poly.diff (Term.svs_of_sort sort)
      (Set.Poly.union_list @@ List.map (Map.Poly.data senv) ~f:Term.svs_of_sort)
  in
  let sort = Sort.mk_poly svs sort in
  (*print_endline @@ "generalized: " ^ Term.str_of_sort sort;*)
  sort
(* val instantiate : Sort.t -> Sort.t *)
let rec instantiate = function
  | Sort.SPoly (svs, s) ->
    let sub = Map.of_set_exn @@ Set.Poly.map svs ~f:(fun svar ->
        svar, Sort.SVar (Ident.mk_fresh_svar ())) in
    Term.subst_sorts_sort sub @@ instantiate s
  | s -> s

let rec unify_eff e1 e2 =
  match e1, e2 with
  | Sort.Pure, Sort.Pure -> []
  | Sort.Eff (o11, s11, e11, o12, s12, e12), Sort.Eff (o21, s21, e21, o22, s22, e22) ->
    (s11, s21) ::
    (s12, s22) ::
    unify_eff e11 e21 @
    unify_eff e12 e22 @
    unify_opsig o11 o21 @
    unify_opsig o12 o22
  | _ -> failwith "unify_eff"
and unify_opsig o1 o2 =
  match o1, o2 with
  | Sort.OpSig (map1, _), Sort.OpSig (map2, _) ->
    let lefts, boths, rights = Util.ALMap.split_lbr map1 map2 in
    if List.is_empty lefts && List.is_empty rights then
      snd @@ List.unzip boths
    else failwith "eqs_opsig"
  | _ -> failwith "eqs_opsig"

let rec solve_aux map = function
  | [] -> map
  | (s1, s2) :: eqs ->
    let s1, s2 = Term.subst_sorts_sort map s1, Term.subst_sorts_sort map s2 in
    Debug.print @@ lazy (sprintf "unify : [%s] = [%s]" (Term.str_of_sort s1) (Term.str_of_sort s2));
    if Stdlib.(s1 = s2) then solve_aux map eqs
    else begin
      match s1, s2 with
      | Sort.SArrow (s11, (o1, s12, c1)), Sort.SArrow (s21, (o2, s22, c2)) ->
        solve_aux map ((s11, s21) :: (s12, s22) :: unify_eff c1 c2 @ unify_opsig o1 o2 @ eqs)
      | T_array.SArray (s11, s12), T_array.SArray (s21, s22) ->
        solve_aux map ((s11, s21) :: (s12, s22) :: eqs)
      | T_dt.SDT dt1, T_dt.SDT dt2 ->
        let sorts1 = Datatype.args_of dt1 in
        let sorts2 = Datatype.args_of dt2 in
        if List.length sorts1 = List.length sorts2 then
          solve_aux map (List.zip_exn sorts1 sorts2 @ eqs)
        else
          failwith (sprintf "unification failure: %s = %s @ 1" (Term.str_of_sort s1) (Term.str_of_sort s2))
      | T_dt.SUS (name1, sorts1), T_dt.SUS (name2, sorts2) when String.(name1 = name2) ->
        if List.length sorts1 = List.length sorts2 then
          solve_aux map (List.zip_exn sorts1 sorts2 @ eqs)
        else
          failwith (sprintf "unification failure: %s = %s @ 2" (Term.str_of_sort s1) (Term.str_of_sort s2))
      | T_dt.SUS (name1, sorts1), T_dt.SDT dt2 when String.(name1 = dt2.name) ->
        let sorts2 = Datatype.args_of dt2 in
        if List.length sorts1 = List.length sorts2 then
          solve_aux map (List.zip_exn sorts1 sorts2 @ eqs)
        else
          failwith (sprintf "unification failure: %s = %s @ 3" (Term.str_of_sort s1) (Term.str_of_sort s2))
      | T_dt.SDT dt1, T_dt.SUS (name2, sorts2) when String.(dt1.name = name2) ->
        let sorts1 = Datatype.args_of dt1 in
        if List.length sorts1 = List.length sorts2 then
          solve_aux map (List.zip_exn sorts1 sorts2 @ eqs)
        else
          failwith (sprintf "unification failure: %s = %s @ 4" (Term.str_of_sort s1) (Term.str_of_sort s2))
      | T_tuple.STuple sorts1, T_tuple.STuple sorts2 ->
        if List.length sorts1 = List.length sorts2 then
          solve_aux map (List.zip_exn sorts1 sorts2 @ eqs)
        else
          failwith (sprintf "unification failure: %s = %s @ 5" (Term.str_of_sort s1) (Term.str_of_sort s2))
      | Sort.SVar svar1, Sort.SVar svar2 ->
        let svar, s = if Ident.svar_compare svar1 svar2 < 0 then svar1, Sort.SVar svar2 else svar2, Sort.SVar svar1 in
        solve_aux (update_sort_subst Term.subst_sorts_sort map svar s) eqs
      | Sort.SVar svar, s | s, Sort.SVar svar ->
        if Term.occurs (Sort.SVar svar) s then
          failwith @@ sprintf "unification failure: %s occurs in %s @ 6" (Ident.name_of_svar svar) (Term.str_of_sort s)
        else
          solve_aux (update_sort_subst Term.subst_sorts_sort map svar s) eqs
      | _ ->
        failwith (sprintf "unification failure: %s = %s @ 7" (Term.str_of_sort s1) (Term.str_of_sort s2))
    end
let solve cs =
  let eqs = Set.Poly.to_list @@ Set.Poly.filter_map cs ~f:(function CEq (s1, s2) -> Some (s1, s2) | CNum _ -> None) in
  let nums = Set.Poly.filter_map cs ~f:(function CEq _ -> None | CNum svar -> Some svar) in
  let map = solve_aux Map.Poly.empty eqs in
  Set.Poly.filter_map nums ~f:(fun svar ->
      match Map.Poly.find map svar with
      | None -> Some svar
      | Some (Sort.SVar svar') -> Some svar'
      | Some T_int.SInt | Some T_real.SReal -> None
      | Some sort -> failwith @@ sprintf "%s is not Num sort" @@ Term.str_of_sort sort),
  map

let elim_nums ?(to_sus=false) nums map =
  (*assert (Set.Poly.is_empty @@ Set.Poly.inter nums (Set.Poly.of_list @@ Map.Poly.keys map));*)
  let map_nums = Map.of_set_exn @@ Set.Poly.map nums ~f:(fun svar ->
      svar,
      if instantiate_num_to_int then T_int.SInt
      else if (*ToDo*)false && to_sus then T_dt.SUS (Ident.name_of_svar svar, [])
      else Sort.SVar svar(* ToDo: z3 does not support polymophic (in)equalities *))
  in
  Map.force_merge map_nums map

let typeinf_term ?(to_sus=false) term =
  let _, _, constrs = cgen_term Map.Poly.empty term in
  let nums, map = solve constrs in
  let map = elim_nums ~to_sus nums map in
  Term.subst_sorts map term
let typeinf_atom ?(to_sus=false) atom =
  let _, constrs = cgen_atom Map.Poly.empty atom in
  let nums, map = solve constrs in
  let map = elim_nums ~to_sus nums map in
  Atom.subst_sorts map atom
let typeinf_formula ?(to_sus=false) phi =
  let _, constrs = cgen_formula Map.Poly.empty phi in
  let nums, map = solve constrs in
  let map = elim_nums ~to_sus nums map in
  Formula.subst_sorts map phi
let typeinf ?(to_sus=false) phis =
  Debug.print @@ lazy ("============== inference start ===================");
  let phis' =
    if true(**) then
      let _, constrs = cgen_formula Map.Poly.empty (Formula.and_of phis) in
      let nums, map = solve constrs in
      let map = elim_nums ~to_sus nums map in
      List.map phis ~f:(Formula.subst_sorts map)
    else
      List.map phis ~f:(fun phi ->
          let _, constrs = cgen_formula Map.Poly.empty phi in
          let nums, map = try solve constrs with Failure s -> failwith @@ s ^ " @ " ^ Formula.str_of phi in
          let map = elim_nums ~to_sus nums map in
          Formula.subst_sorts map phi)
  in
  Debug.print @@ lazy ("============== inference end =====================");
  Debug.print @@ lazy (sprintf "type inferred: %s" @@ Formula.str_of @@ Formula.and_of phis');
  Debug.print @@ lazy (sprintf "dsenv after type inference: %s" @@ DTEnv.str_of @@ DTEnv.of_formula @@ Formula.and_of phis');
  phis'
