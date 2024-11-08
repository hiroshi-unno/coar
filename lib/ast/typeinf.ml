open Core
open Common
open Common.Ext
open Common.Combinator
open Ident
open LogicOld

type constr = CEq of Sort.t * Sort.t | CNum of Ident.svar

let is_ceq = function CEq _ -> true | _ -> false
let is_cnum = function CNum _ -> true | _ -> false

let str_of_constr = function
  | CEq (sort1, sort2) ->
      sprintf "  [CEq:%s = %s]" (Term.str_of_sort sort1)
        (Term.str_of_sort sort2)
  | CNum svar -> sprintf "  [CNum: %s]" (Ident.name_of_svar svar)

let str_of_constrs = String.concat_map_set ~sep:"\n" ~f:str_of_constr

let rec cgen_term ~print senv term =
  let open Term in
  print @@ lazy (sprintf "cgen_term: %s" @@ str_of term);
  let senv, ty, constrs =
    match term with
    | Var (var, sort, _) -> (
        match Map.Poly.find senv var with
        | None ->
            ( Map.Poly.set senv ~key:var ~data:sort (*ToDo*),
              sort,
              Set.Poly.empty )
        | Some sort1 ->
            ( Map.Poly.set senv ~key:var ~data:sort1 (*ToDo*),
              sort1,
              Set.Poly.singleton (CEq (sort, sort1)) ))
    | FunApp (FVar (_, sorts), ts, _) ->
        let sargs, ret = List.rest_last sorts in
        let constrs, senv =
          List.fold2_exn sargs ts ~init:(Set.Poly.empty, senv)
            ~f:(fun (constrs, senv) ty t ->
              let senv, ty1, constrs1 = cgen_term ~print senv t in
              ( Set.Poly.union_list
                  [ constrs; constrs1; Set.Poly.singleton (CEq (ty1, ty)) ],
                senv ))
        in
        (senv, ret, constrs)
    | FunApp (T_bool.Formula phi, _, _) ->
        let senv, constrs = cgen_formula ~print senv phi in
        (senv, T_bool.SBool, constrs)
    | FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], _) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        let senv, ty3, constrs3 = cgen_term ~print senv t3 in
        ( senv,
          ty2,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              constrs3;
              Set.Poly.of_list [ CEq (ty1, T_bool.SBool); CEq (ty2, ty3) ];
            ] )
    | FunApp (T_int.Int _, [], _) -> (senv, T_int.SInt, Set.Poly.empty)
    | FunApp (T_real.Real _, [], _) -> (senv, T_real.SReal, Set.Poly.empty)
    | FunApp (T_real.Alge _, [ t ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t in
        ( senv,
          T_real.SReal,
          Set.union constrs (Set.Poly.singleton (CEq (ty, T_real.SReal))) )
    | FunApp (T_bv.BVNum (size, _), [], _) ->
        (senv, T_bv.SBV size, Set.Poly.empty)
    | FunApp (T_num.Value (_, svar), [], _) ->
        (senv, Sort.SVar svar, Set.Poly.singleton (CNum svar))
    | FunApp ((T_int.Neg | T_int.Abs), [ t1 ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t1 in
        ( senv,
          T_int.SInt,
          Set.union constrs (Set.Poly.singleton (CEq (ty, T_int.SInt))) )
    | FunApp (T_irb.RealToInt, [ t ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t in
        ( senv,
          T_int.SInt,
          Set.union constrs (Set.Poly.singleton (CEq (ty, T_real.SReal))) )
    | FunApp ((T_real.RNeg | T_real.RAbs), [ t1 ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t1 in
        ( senv,
          T_real.SReal,
          Set.union constrs (Set.Poly.singleton (CEq (ty, T_real.SReal))) )
    | FunApp (T_irb.IntToReal, [ t ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t in
        ( senv,
          T_real.SReal,
          Set.union constrs (Set.Poly.singleton (CEq (ty, T_int.SInt))) )
    | FunApp (T_irb.IntToBV size, [ t ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t in
        ( senv,
          T_bv.SBV size,
          Set.union constrs (Set.Poly.singleton (CEq (ty, T_int.SInt))) )
    | FunApp (T_irb.BVToInt size, [ t ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t in
        ( senv,
          T_int.SInt,
          Set.union constrs (Set.Poly.singleton (CEq (ty, T_bv.SBV size))) )
    | FunApp (T_num.NNeg svar, [ t1 ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t1 in
        ( senv,
          ty,
          Set.union constrs
            (Set.Poly.of_list [ CNum svar; CEq (ty, Sort.SVar svar) ]) )
    | FunApp
        ( T_num.(
            ( NAdd svar
            | NSub svar
            | NMult svar
            | NDiv svar
            | NMod svar
            | NRem svar
            | NPower svar )),
          [ t1; t2 ],
          _ ) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          ty1,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list
                [ CNum svar; CEq (ty1, Sort.SVar svar); CEq (ty1, ty2) ];
            ] )
    | FunApp (T_int.(Add | Sub | Mult | Div | Mod | Power | Rem), [ t1; t2 ], _)
      ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          T_int.SInt,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list [ CEq (ty1, T_int.SInt); CEq (ty1, ty2) ];
            ] )
    | FunApp (T_real.(RAdd | RSub | RMult | RDiv | RPower), [ t1; t2 ], _) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          T_real.SReal,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list [ CEq (ty1, T_real.SReal); CEq (ty1, ty2) ];
            ] )
    | FunApp
        ( T_bv.(
            ( BVAdd size
            | BVSub size
            | BVMult size
            | BVDiv size
            | BVMod size
            | BVRem size
            | BVSHL size
            | BVLSHR size
            | BVASHR size
            | BVOr size
            | BVAnd size )),
          [ t1; t2 ],
          _ ) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          T_bv.SBV size,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list [ CEq (ty1, T_bv.SBV size); CEq (ty1, ty2) ];
            ] )
    | FunApp (T_dt.DTCons (_, tys, dt), ts, _) ->
        let senv, tys', constrss = cgen_terms ~print senv ts in
        ( senv,
          Datatype.sort_of dt,
          Set.Poly.union_list
          @@ (Set.Poly.of_list
             @@ List.map2_exn tys tys' ~f:(fun ty1 ty2 -> CEq (ty1, ty2)))
             :: constrss )
    | FunApp (T_dt.DTSel (_, dt, sort), [ t ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t in
        ( senv,
          sort,
          Set.union constrs (Set.Poly.singleton (CEq (T_dt.SDT dt, ty))) )
    | FunApp (T_tuple.TupleCons sorts, ts, _) ->
        let senv, tys, constrss = cgen_terms ~print senv ts in
        ( senv,
          T_tuple.STuple tys,
          Set.Poly.union_list
          @@ (Set.Poly.of_list
             @@ List.map2_exn sorts tys ~f:(fun ty1 ty2 -> CEq (ty1, ty2)))
             :: constrss )
    | FunApp (T_tuple.TupleSel (sorts, i), [ t ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t in
        ( senv,
          List.nth_exn sorts i,
          Set.union constrs
            (Set.Poly.singleton (CEq (T_tuple.STuple sorts, ty))) )
    | FunApp (T_ref.Ref sort, [ t ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t in
        ( senv,
          T_ref.SRef sort,
          Set.union constrs (Set.Poly.singleton (CEq (sort, ty))) )
    | FunApp (T_ref.Deref sort, [ t ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t in
        ( senv,
          sort,
          Set.union constrs (Set.Poly.singleton (CEq (T_ref.SRef sort, ty))) )
    | FunApp (T_ref.Update sort, [ t1; t2 ], _) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          Datatype.sort_of @@ Datatype.mk_unit_dt (),
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.singleton (CEq (T_ref.SRef sort, ty1));
              Set.Poly.singleton (CEq (sort, ty2));
            ] )
    | FunApp (T_array.AConst (s1, s2), [ t1 ], _) ->
        let senv, ty, constrs = cgen_term ~print senv t1 in
        ( senv,
          T_array.SArray (s1, s2),
          Set.union constrs (Set.Poly.singleton (CEq (s2, ty))) )
    | FunApp (T_array.ASelect (s1, s2), [ t1; t2 ], _) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          s2,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list
                [ CEq (ty1, T_array.SArray (ty2, s2)); CEq (s1, ty2) ];
            ] )
    | FunApp (T_array.AStore (s1, s2), [ t1; t2; t3 ], _) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        let senv, ty3, constrs3 = cgen_term ~print senv t3 in
        ( senv,
          ty1,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              constrs3;
              Set.Poly.of_list
                [
                  CEq (ty1, T_array.SArray (ty2, ty3));
                  CEq (s1, ty2);
                  CEq (ty3, s2);
                ];
            ] )
    | FunApp (T_string.StrConst _, [], _) ->
        (senv, T_string.SString, Set.Poly.empty)
    | FunApp (T_sequence.(SeqEpsilon | SeqSymbol _), [], _) ->
        (senv, T_sequence.SSequence true, Set.Poly.empty)
    | FunApp
        ( T_sequence.(SeqConcat fin | SeqLeftQuotient fin | SeqRightQuotient fin),
          [ t1; t2 ],
          _ ) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          ty2,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list
                [
                  CEq (ty1, T_sequence.SSequence true);
                  CEq (ty2, T_sequence.SSequence fin);
                ];
            ] )
    | FunApp (T_regex.(RegEmpty | RegFull | RegEpsilon), [], _) ->
        (senv, T_regex.SRegEx, Set.Poly.empty)
    | FunApp (T_regex.RegStr, [ t1 ], _) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        ( senv,
          T_regex.SRegEx,
          Set.Poly.union_list
            [ constrs1; Set.Poly.singleton @@ CEq (ty1, T_string.SString) ] )
    | FunApp (T_regex.(RegComplement | RegStar | RegPlus | RegOpt), [ t1 ], _)
      ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        ( senv,
          T_regex.SRegEx,
          Set.Poly.union_list
            [ constrs1; Set.Poly.singleton @@ CEq (ty1, T_regex.SRegEx) ] )
    | FunApp (T_regex.(RegConcat | RegUnion | RegInter), [ t1; t2 ], _) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          T_regex.SRegEx,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list
                [ CEq (ty1, T_regex.SRegEx); CEq (ty2, T_regex.SRegEx) ];
            ] )
    | LetTerm (_, sort, def, body, _) ->
        let senv, ty1, constrs1 = cgen_term ~print senv def in
        let senv, ty2, constrs2 = cgen_term ~print senv body in
        ( senv,
          ty2,
          Set.Poly.union_list
            [ constrs1; constrs2; Set.Poly.singleton (CEq (ty1, sort)) ] )
    | _ -> failwith @@ sprintf "unknown term:%s" (Term.str_of term)
  in
  print @@ lazy (sprintf "term constrs:%s" @@ str_of_constrs constrs);
  (senv, ty, constrs)

and cgen_terms ~print senv terms =
  let senv, ret =
    List.fold terms ~init:(senv, []) ~f:(fun (senv, acc) term ->
        let senv', ty, constrs = cgen_term ~print senv term in
        (senv', (ty, constrs) :: acc))
  in
  let tys, constrss = List.unzip @@ List.rev ret in
  (senv, tys, constrss)

and cgen_atom ~print senv atom =
  let open Atom in
  print @@ lazy (sprintf "cgen_atom: %s" @@ str_of atom);
  let senv, constrs =
    match atom with
    | App (Predicate.Var (Pvar var, par_tys), ts, _) ->
        let senv, par_tys, constrs0 =
          match Map.Poly.find senv (Tvar var) with
          | Some t ->
              print
              @@ lazy
                   (sprintf "assigned type of %s: %s" var (Term.str_of_sort t));
              ( senv,
                Sort.args_of t,
                Set.Poly.of_list
                @@ List.map2_exn par_tys (Sort.args_of t) ~f:(fun ty1 ty2 ->
                       CEq (ty1, ty2)) )
          | None ->
              ( Map.Poly.add_exn senv ~key:(Tvar var)
                  ~data:(Sort.mk_fun @@ par_tys @ [ T_bool.SBool ]),
                par_tys,
                Set.Poly.empty )
        in
        let senv, tys, constrss = cgen_terms ~print senv ts in
        let constrs1 =
          Set.Poly.of_list
          @@ List.map2_exn par_tys tys ~f:(fun ty1 ty2 -> CEq (ty1, ty2))
        in
        (senv, Set.Poly.union_list @@ (constrs0 :: constrs1 :: constrss))
    | App (Predicate.Fixpoint (_, _, _, phi), ts, _) ->
        print @@ lazy (sprintf "function formula:%s" @@ Formula.str_of phi);
        let senv, constrs = cgen_formula ~print senv phi in
        let senv, _tys (*ToDo*), constrss = cgen_terms ~print senv ts in
        (senv, Set.Poly.union_list @@ (constrs :: constrss))
    | App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ t1; t2 ], _) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        print
        @@ lazy
             (sprintf "info eq: %s:%s = %s:%s" (Term.str_of t1)
                (Term.str_of_sort ty1) (Term.str_of t2) (Term.str_of_sort ty2));
        ( senv,
          Set.Poly.union_list
            [ constrs1; constrs2; Set.Poly.singleton (CEq (ty1, ty2)) ] )
    | App (Predicate.Psym T_int.(Gt | Lt | Geq | Leq), [ t1; t2 ], _) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list [ CEq (ty1, ty2); CEq (ty1, T_int.SInt) ];
            ] )
    | App (Predicate.Psym T_real.(RGt | RLt | RGeq | RLeq), [ t1; t2 ], _) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list [ CEq (ty1, ty2); CEq (ty1, T_real.SReal) ];
            ] )
    | App
        ( Predicate.Psym T_bv.(BVGt size | BVLt size | BVGeq size | BVLeq size),
          [ t1; t2 ],
          _ ) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list [ CEq (ty1, ty2); CEq (ty1, T_bv.SBV size) ];
            ] )
    | App
        ( Predicate.Psym T_num.(NGt svar | NLt svar | NGeq svar | NLeq svar),
          [ t1; t2 ],
          _ ) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list
                [ CNum svar; CEq (ty1, ty2); CEq (ty1, Sort.SVar svar) ];
            ] )
    | App (Predicate.Psym T_tuple.(IsTuple sorts | NotIsTuple sorts), [ t1 ], _)
      ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        ( senv,
          Set.union constrs1
            (Set.Poly.singleton (CEq (T_tuple.STuple sorts, ty1))) )
    | App (Predicate.Psym T_dt.(IsCons (_, dt) | NotIsCons (_, dt)), [ t1 ], _)
      ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        (senv, Set.union constrs1 (Set.Poly.singleton (CEq (T_dt.SDT dt, ty1))))
    | App
        ( Predicate.Psym T_sequence.(IsPrefix fin | NotIsPrefix fin),
          [ t1; t2 ],
          _ ) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        let sort = T_sequence.SSequence fin in
        ( senv,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list [ CEq (ty1, ty2); CEq (ty1, sort) ];
            ] )
    | App
        ( Predicate.Psym
            T_sequence.(
              SeqInRegExp (fin, _regexp) | NotSeqInRegExp (fin, _regexp)),
          [ t1 ],
          _ ) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let sort = T_sequence.SSequence fin in
        (senv, Set.union constrs1 (Set.Poly.singleton (CEq (ty1, sort))))
    | App (Predicate.Psym T_regex.(StrInRegExp | NotStrInRegExp), [ t1; t2 ], _)
      ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list
                [ CEq (ty1, T_string.SString); CEq (ty2, T_regex.SRegEx) ];
            ] )
    | _ -> (senv, Set.Poly.empty)
  in
  print @@ lazy (sprintf "atom constrs:\n%s" @@ str_of_constrs constrs);
  (senv, constrs)

and cgen_rand ~print senv rand =
  let open Rand in
  print @@ lazy (sprintf "cgen_rand: %s" @@ str_of rand);
  let senv, ty, constrs =
    match rand with
    | Uniform (t1, t2) | Gauss (t1, t2) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          T_real.SReal,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list
                [ CEq (ty1, T_real.SReal); CEq (ty2, T_real.SReal) ];
            ] )
    | IntUniform (t1, t2) ->
        let senv, ty1, constrs1 = cgen_term ~print senv t1 in
        let senv, ty2, constrs2 = cgen_term ~print senv t2 in
        ( senv,
          T_int.SInt,
          Set.Poly.union_list
            [
              constrs1;
              constrs2;
              Set.Poly.of_list [ CEq (ty1, T_int.SInt); CEq (ty2, T_int.SInt) ];
            ] )
  in
  print @@ lazy (sprintf "rand constrs: %s" @@ str_of_constrs constrs);
  (senv, ty, constrs)

and cgen_formula ~print senv phi =
  let open Formula in
  print @@ lazy (sprintf "cgen_formula: %s" @@ str_of phi);
  let senv, constrs =
    match phi with
    | Atom (atom, _) -> cgen_atom ~print senv atom
    | UnaryOp (_, phi1, _) -> cgen_formula ~print senv phi1
    | BinaryOp (_, phi1, phi2, _) ->
        let senv, constrs1 = cgen_formula ~print senv phi1 in
        let senv, constrs2 = cgen_formula ~print senv phi2 in
        (senv, Set.union constrs1 constrs2)
    | Bind (Random rand, bounds, body, _) ->
        let senv, ty, constrs1 = cgen_rand ~print senv rand in
        let x, sort = List.hd_exn bounds in
        let senv = Map.Poly.set senv ~key:x ~data:sort in
        let senv, constrs2 = cgen_formula ~print senv body in
        ( senv,
          Set.Poly.union_list
            [ constrs1; constrs2; Set.Poly.singleton (CEq (ty, sort)) ] )
    | Bind (_, bounds, body, _) ->
        let senv =
          List.fold bounds ~init:senv ~f:(fun acc (v, sort) ->
              Map.Poly.set acc ~key:v ~data:sort)
        in
        let senv, constrs = cgen_formula ~print senv body in
        let senv =
          List.fold bounds ~init:senv ~f:(fun acc -> fst >> Map.Poly.remove acc)
        in
        (senv, constrs)
    | LetRec (_, body, _) -> cgen_formula ~print senv body
    | LetFormula (var, sort, def, body, info) ->
        let senv, ty, constrs =
          cgen_term ~print senv
          @@ Term.LetTerm (var, sort, def, T_bool.of_formula body, info)
        in
        (senv, Set.add constrs (CEq (ty, T_bool.SBool)))
  in
  print @@ lazy (sprintf "formula constrs: %s" @@ str_of_constrs constrs);
  (senv, constrs)

(* val sort_of_name : ?args:Sort.t list -> DTEnv.t -> string -> Sort.t *)
let sort_of_name ?(rectyps = None) dtenv ?(args = []) = function
  | "bool" (* | "Bool"*) -> T_bool.SBool
  | "int" (* | "Int"*) -> T_int.SInt
  | "float" | "real" (* | "Real"*) -> T_real.SReal
  | "prop" -> T_real.SReal (*ToDo*)
  | "string" -> T_string.SString
  | "finseq" -> T_sequence.SSequence true
  | "infseq" -> T_sequence.SSequence false
  | "regex" -> T_regex.SRegEx
  | "int_array" -> T_array.mk_array_sort T_int.SInt T_int.SInt
  (*| "list" -> Datatype.sort_of list_dt*)
  | "Stdlib.ref" -> (
      match args with
      | [ sort ] -> T_ref.SRef sort
      | _ -> failwith "sort_of_name")
  | name -> (
      match DTEnv.look_up_dt dtenv name with
      | Some dt ->
          if List.is_empty args then Datatype.sort_of dt
          else T_dt.SDT (Datatype.update_params dt args (*ToDo*))
      | _ -> (
          match rectyps with
          | None ->
              assert (List.is_empty args);
              Sort.SVar (Svar name) (*ToDo*)
          | Some datatypes -> (
              match
                List.find datatypes ~f:(Datatype.name_of_dt >> String.( = ) name)
              with
              | None ->
                  assert (List.is_empty args);
                  Sort.SVar (Svar name) (*ToDo*)
              | Some _ -> (*recursive types*) T_dt.SUS (name, args))))

(* val subtype : (Ident.svar, Sort.t option) Map.Poly.t -> Sort.t -> Sort.t -> (Ident.svar, Sort.t option) Map.Poly.t * (Sort.e list * Sort.e) Set.Poly.t * (Sort.o * Sort.o) Set.Poly.t *)
let rec subtype map s1 s2 =
  (*ToDo: support higher-data-sorts and unresolved sort variables*)
  (*print_endline @@ Term.str_of_sort s1 ^ "\n<: " ^ Term.str_of_sort s2 ^ "\n";*)
  if Stdlib.(s1 = s2) then (map, Set.Poly.empty, Set.Poly.empty)
  else
    match (s1, s2) with
    | Sort.SArrow (s11, se12), Sort.SArrow (s21, se22) ->
        let map, econstrs1, oconstrs1 = subtype map s21 s11 in
        let map, econstrs2, oconstrs2 = subeff map se12 se22 in
        (map, Set.union econstrs1 econstrs2, Set.union oconstrs1 oconstrs2)
    | T_bv.SBV size1, T_bv.SBV size2
      when match (size1, size2) with
           | None, _ | _, None -> true (*ToDo*)
           | Some s1, Some s2 -> Stdlib.(s1 = s2) ->
        (map, Set.Poly.empty, Set.Poly.empty)
    | T_tuple.STuple sorts1, T_tuple.STuple sorts2 ->
        List.fold2_exn sorts1 sorts2 ~init:(map, Set.Poly.empty, Set.Poly.empty)
          ~f:(fun (map, econstrs, oconstrs) s1 s2 ->
            let map, econstrs', oconstrs' = subtype map s1 s2 in
            (map, Set.union econstrs econstrs', Set.union oconstrs oconstrs'))
    | T_ref.SRef s1, T_ref.SRef s2 ->
        let map, econstrs1, oconstrs1 = subtype map s1 s2 in
        let map, econstrs2, oconstrs2 = subtype map s2 s1 in
        (map, Set.union econstrs1 econstrs2, Set.union oconstrs1 oconstrs2)
    | T_dt.SDT dt1, T_dt.SDT dt2 when String.(dt1.name = dt2.name) ->
        List.fold2_exn (Datatype.params_of dt1) (Datatype.params_of dt2)
          ~init:(map, Set.Poly.empty, Set.Poly.empty)
          ~f:(fun (map, econstrs, oconstrs) s1 s2 ->
            let map, econstrs', oconstrs' = subtype map s1 s2 (*ToDo*) in
            (map, Set.union econstrs econstrs', Set.union oconstrs oconstrs'))
    | T_dt.SDT dt1, T_dt.SUS (name2, sorts2) when String.(dt1.name = name2) ->
        (*ToDo: fix the ad hoc use of SUS*)
        List.fold2_exn (Datatype.params_of dt1) sorts2
          ~init:(map, Set.Poly.empty, Set.Poly.empty)
          ~f:(fun (map, econstrs, oconstrs) s1 s2 ->
            let map, econstrs', oconstrs' = subtype map s1 s2 (*ToDo*) in
            (map, Set.union econstrs econstrs', Set.union oconstrs oconstrs'))
    | T_dt.SUS (name1, sorts1), T_dt.SDT dt2 when String.(name1 = dt2.name) ->
        (*ToDo: fix the ad hoc use of SUS*)
        List.fold2_exn sorts1 (Datatype.params_of dt2)
          ~init:(map, Set.Poly.empty, Set.Poly.empty)
          ~f:(fun (map, econstrs, oconstrs) s1 s2 ->
            let map, econstrs', oconstrs' = subtype map s1 s2 (*ToDo*) in
            (map, Set.union econstrs econstrs', Set.union oconstrs oconstrs'))
    | T_dt.SUS (n1, sorts1), T_dt.SUS (n2, sorts2) when String.(n1 = n2) ->
        List.fold2_exn sorts1 sorts2 ~init:(map, Set.Poly.empty, Set.Poly.empty)
          ~f:(fun (map, econstrs, oconstrs) s1 s2 ->
            let map, econstrs', oconstrs' = subtype map s1 s2 (*ToDo*) in
            (map, Set.union econstrs econstrs', Set.union oconstrs oconstrs'))
    | T_array.SArray (s11, s12), T_array.SArray (s21, s22) ->
        let map, econstrs1, oconstrs1 = subtype map s21 s11 (*ToDo*) in
        let map, econstrs2, oconstrs2 = subtype map s11 s21 (*ToDo*) in
        let map, econstrs3, oconstrs3 = subtype map s12 s22 (*ToDo*) in
        let map, econstrs4, oconstrs4 = subtype map s22 s12 (*ToDo*) in
        ( map,
          Set.Poly.union_list [ econstrs1; econstrs2; econstrs3; econstrs4 ],
          Set.Poly.union_list [ oconstrs1; oconstrs2; oconstrs3; oconstrs4 ] )
    | Sort.SVar svar, s when Map.Poly.mem map svar -> (
        match Map.Poly.find map svar with
        | None -> failwith "[Typeinf.subtype @ 1]"
        | Some None ->
            if false then
              print_endline
              @@ sprintf "%s -> %s" (Ident.name_of_svar svar)
                   (Term.str_of_sort s);
            ( Map.Poly.set map ~key:svar ~data:(Some s) (*ToDo*),
              Set.Poly.empty,
              Set.Poly.empty )
        | Some (Some s') -> subtype map s' s)
    | s, Sort.SVar svar when Map.Poly.mem map svar -> (
        match Map.Poly.find map svar with
        | None -> failwith "[Typeinf.subtype @ 2]"
        | Some None ->
            if false then
              print_endline
              @@ sprintf "%s -> %s" (Ident.name_of_svar svar)
                   (Term.str_of_sort s);
            ( Map.Poly.set map ~key:svar ~data:(Some s) (*ToDo*),
              Set.Poly.empty,
              Set.Poly.empty )
        | Some (Some s') -> subtype map s s')
    (*| Sort.SVar svar1, Sort.SVar svar2 ->
          let svar1, svar2 =
            if Stdlib.(svar1 < svar2) then (svar1, svar2) else (svar2, svar1)
          in
          ( Map.Poly.set map ~key:svar1 ~data:(Some (Sort.SVar svar2)) (*ToDo*),
            Set.Poly.empty,
            Set.Poly.empty )
      | Sort.SVar svar, s | s, Sort.SVar svar ->
          ( Map.Poly.set map ~key:svar ~data:(Some s) (*ToDo*),
            Set.Poly.empty,
            Set.Poly.empty )*)
    | Sort.SPoly (svs, s1), s2 ->
        let sub =
          Map.of_set_exn
          @@ Set.Poly.map svs ~f:(fun svar -> (svar, Sort.mk_fresh_svar ()))
        in
        let s1 = Term.subst_sorts_sort sub s1 in
        let map =
          List.fold (Map.Poly.data sub) ~init:map ~f:(fun map -> function
            | Sort.SVar svar -> Map.Poly.add_exn map ~key:svar ~data:None
            | _ -> assert false)
        in
        subtype map s1 s2
    | _, _ ->
        failwith
        @@ sprintf "[Typeinf.subtype] %s and %s" (Term.str_of_sort s1)
             (Term.str_of_sort s2)

(* val subeff : (Ident.svar, Sort.t option) Map.Poly.t -> Sort.c -> Sort.c -> (Ident.svar, Sort.t option) Map.Poly.t * (Sort.e list * Sort.e) Set.Poly.t * (Sort.o * Sort.o) Set.Poly.t *)
and subeff map c1 c2 =
  (*print_endline @@ Term.str_of_sort s1 ^ " <: " ^ Term.str_of_sort s2;*)
  let map, econstrs, oconstrs = subtype map c1.val_type c2.val_type in
  (* assume that (o2, s2, e2) is monomorphic *)
  let sub = Map.Poly.filter_map map ~f:Fn.id in
  ( map,
    Set.add econstrs ([ Term.subst_sorts_cont sub c1.cont_eff ], c2.cont_eff)
    (*ToDo*),
    Set.add oconstrs (Term.subst_sorts_opsig sub c2.op_sig, c1.op_sig) )
(*ToDo*)

(* val generalize : sort_env_map -> Sort.t -> Sort.t *)
let generalize senv sort =
  let svs =
    Set.diff (Term.svs_of_sort sort)
      (Set.Poly.union_list @@ List.map (Map.Poly.data senv) ~f:Term.svs_of_sort)
  in
  let sort = Sort.mk_poly svs sort in
  (*print_endline @@ "generalized: " ^ Term.str_of_sort sort;*)
  sort

(* val instantiate : Sort.t -> Sort.t *)
let rec instantiate = function
  | Sort.SPoly (svs, s) ->
      let sub =
        Map.of_set_exn
        @@ Set.Poly.map svs ~f:(fun svar -> (svar, Sort.mk_fresh_svar ()))
      in
      Term.subst_sorts_sort sub @@ instantiate s
  | s -> s

let rec unify_eff e1 e2 =
  match (e1, e2) with
  | (Sort.Pure | Sort.Closed), (Sort.Pure | Sort.Closed) -> []
  | Sort.Eff (c11, c12), Sort.Eff (c21, c22) ->
      unify_triple c11 c21 @ unify_triple c12 c22
  | _ -> failwith "unify_eff"

and unify_opsig o1 o2 =
  match (o1, o2) with
  | Sort.OpSig (map1, _), Sort.OpSig (map2, _) ->
      let lefts, boths, rights = Util.ALMap.split_lbr map1 map2 in
      if List.is_empty lefts && List.is_empty rights then
        snd @@ List.unzip boths
      else failwith "unify_opsig"
  | _ -> failwith "unify_opsig"

and unify_triple c1 c2 =
  ((c1.val_type, c2.val_type) :: unify_eff c1.cont_eff c2.cont_eff)
  @ unify_opsig c2.op_sig c1.op_sig

let rec unify_sort ~print map = function
  | [] -> map
  | (s1, s2) :: eqs -> (
      let s1, s2 =
        (Term.subst_sorts_sort map s1, Term.subst_sorts_sort map s2)
      in
      print
      @@ lazy
           (sprintf "unify : %s = %s" (Term.str_of_sort s1)
              (Term.str_of_sort s2));
      if Stdlib.(s1 = s2) then unify_sort ~print map eqs
      else
        match (s1, s2) with
        | Sort.SArrow (s1, t1), Sort.SArrow (s2, t2) ->
            unify_sort ~print map (((s1, s2) :: unify_triple t1 t2) @ eqs)
        | T_bv.SBV size1, T_bv.SBV size2
          when match (size1, size2) with
               | None, _ | _, None -> true (*ToDo*)
               | Some s1, Some s2 -> Stdlib.(s1 = s2) ->
            map
        | T_array.SArray (s11, s12), T_array.SArray (s21, s22) ->
            unify_sort ~print map ((s11, s21) :: (s12, s22) :: eqs)
        | T_dt.SDT dt1, T_dt.SDT dt2 ->
            let sorts1 = Datatype.params_of dt1 in
            let sorts2 = Datatype.params_of dt2 in
            if List.eq_length sorts1 sorts2 then
              unify_sort ~print map (List.zip_exn sorts1 sorts2 @ eqs)
            else
              failwith
                (sprintf "unification failure: %s = %s @ 1"
                   (Term.str_of_sort s1) (Term.str_of_sort s2))
        | T_dt.SUS (name1, sorts1), T_dt.SUS (name2, sorts2)
          when String.(name1 = name2) ->
            if List.eq_length sorts1 sorts2 then
              unify_sort ~print map (List.zip_exn sorts1 sorts2 @ eqs)
            else
              failwith
                (sprintf "unification failure: %s = %s @ 2"
                   (Term.str_of_sort s1) (Term.str_of_sort s2))
        | T_dt.SUS (name1, sorts1), T_dt.SDT dt2 when String.(name1 = dt2.name)
          ->
            let sorts2 = Datatype.params_of dt2 in
            if List.eq_length sorts1 sorts2 then
              unify_sort ~print map (List.zip_exn sorts1 sorts2 @ eqs)
            else
              failwith
                (sprintf "unification failure: %s = %s @ 3"
                   (Term.str_of_sort s1) (Term.str_of_sort s2))
        | T_dt.SDT dt1, T_dt.SUS (name2, sorts2) when String.(dt1.name = name2)
          ->
            let sorts1 = Datatype.params_of dt1 in
            if List.eq_length sorts1 sorts2 then
              unify_sort ~print map (List.zip_exn sorts1 sorts2 @ eqs)
            else
              failwith
                (sprintf "unification failure: %s = %s @ 4"
                   (Term.str_of_sort s1) (Term.str_of_sort s2))
        | T_tuple.STuple sorts1, T_tuple.STuple sorts2 ->
            if List.eq_length sorts1 sorts2 then
              unify_sort ~print map (List.zip_exn sorts1 sorts2 @ eqs)
            else
              failwith
                (sprintf "unification failure: %s = %s @ 5"
                   (Term.str_of_sort s1) (Term.str_of_sort s2))
        | Sort.SVar svar1, Sort.SVar svar2 ->
            let svar, s =
              if Ident.svar_compare svar1 svar2 < 0 then (svar1, Sort.SVar svar2)
              else (svar2, Sort.SVar svar1)
            in
            unify_sort ~print
              (update_sort_subst Term.subst_sorts_sort map svar s)
              eqs
        | Sort.SVar svar, s | s, Sort.SVar svar ->
            if Term.occurs svar s then
              failwith
              @@ sprintf "unification failure: %s occurs in %s @ 6"
                   (Ident.name_of_svar svar) (Term.str_of_sort s)
            else
              unify_sort ~print
                (update_sort_subst Term.subst_sorts_sort map svar s)
                eqs
        | _ ->
            failwith
              (sprintf "unification failure: %s = %s @ 7" (Term.str_of_sort s1)
                 (Term.str_of_sort s2)))

let solve ~print cs =
  let eqs =
    Set.to_list
    @@ Set.Poly.filter_map cs ~f:(function
         | CEq (s1, s2) -> Some (s1, s2)
         | CNum _ -> None)
  in
  let nums =
    Set.Poly.filter_map cs ~f:(function
      | CEq _ -> None
      | CNum svar -> Some svar)
  in
  let map = unify_sort ~print Map.Poly.empty eqs in
  ( Set.Poly.filter_map nums ~f:(fun svar ->
        match Map.Poly.find map svar with
        | None -> Some svar
        | Some (Sort.SVar svar') -> Some svar'
        | Some (T_int.SInt | T_real.SReal | T_bv.SBV _) -> None
        | Some sort ->
            failwith @@ sprintf "%s is not Num sort" @@ Term.str_of_sort sort),
    map )

let elim_nums ?(to_sus = false) ?(instantiate_num_to_int = false) nums map =
  (*assert (Set.is_empty @@ Set.inter nums (Map.Poly.key_set map));*)
  let map_nums =
    Map.of_set_exn
    @@ Set.Poly.map nums ~f:(fun svar ->
           ( svar,
             if instantiate_num_to_int (* instantiate Num to Int *) then
               T_int.SInt
             else if (*ToDo*) false && to_sus then
               T_dt.SUS (Ident.name_of_svar svar, [])
             else
               Sort.SVar
                 svar (* ToDo: z3 does not support polymophic (in)equalities *)
           ))
  in
  Map.force_merge map_nums
    (Map.Poly.map map ~f:(Term.subst_sorts_sort map_nums))

let typeinf_term ~print ?(to_sus = false) ?(instantiate_num_to_int = false) term
    =
  let _, _, constrs = cgen_term ~print Map.Poly.empty term in
  let nums, map = solve ~print constrs in
  let map = elim_nums ~to_sus ~instantiate_num_to_int nums map in
  Term.subst_sorts map term

let typeinf_atom ~print ?(to_sus = false) ?(instantiate_num_to_int = false) atom
    =
  let _, constrs = cgen_atom ~print Map.Poly.empty atom in
  let nums, map = solve ~print constrs in
  let map = elim_nums ~to_sus ~instantiate_num_to_int nums map in
  Atom.subst_sorts map atom

let typeinf_formula ~print ?(to_sus = false) ?(instantiate_num_to_int = false)
    phi =
  let _, constrs = cgen_formula ~print Map.Poly.empty phi in
  let nums, map = solve ~print constrs in
  let map = elim_nums ~to_sus ~instantiate_num_to_int nums map in
  Formula.subst_sorts map phi

let typeinf ~print ?(to_sus = false) ?(instantiate_num_to_int = false) phis =
  print @@ lazy "============== inference start ===================";
  let phis' =
    if true (* *) then
      let _, constrs =
        cgen_formula ~print Map.Poly.empty (Formula.and_of phis)
      in
      let nums, map = solve ~print constrs in
      let map = elim_nums ~to_sus ~instantiate_num_to_int nums map in
      List.map phis ~f:(Formula.subst_sorts map)
    else
      List.map phis ~f:(fun phi ->
          let _, constrs = cgen_formula ~print Map.Poly.empty phi in
          let nums, map =
            try solve ~print constrs
            with Failure s -> failwith @@ s ^ " @ " ^ Formula.str_of phi
          in
          let map = elim_nums ~to_sus ~instantiate_num_to_int nums map in
          Formula.subst_sorts map phi)
  in
  print @@ lazy "============== inference end =====================";
  print
  @@ lazy (sprintf "type inferred: %s" @@ Formula.str_of @@ Formula.and_of phis');
  print
  @@ lazy
       (sprintf "datatype env after type inference: %s"
       @@ DTEnv.str_of @@ DTEnv.of_formula @@ Formula.and_of phis');
  phis'
