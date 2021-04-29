open Core
open Common
open Util
open LogicOld

(*val eval_term: Term.t -> Value.t*)
let rec eval_term = let open Term in function
    | Var _ -> failwith "Any term variables should be removed before evaluating formula."
    | FunApp (T_int.Int i, [], _) -> Value.Int i
    | FunApp (T_real.Real r, [], _) -> Value.Real r
    | FunApp (T_bool.Formula phi, [], _) -> Value.Bool (eval phi)
    | FunApp ((T_int.Neg | T_real.RNeg), [t1], _) -> Value.neg (eval_term t1)
    | FunApp ((T_int.Abs | T_real.RAbs), [t1], _) -> Value.abs (eval_term t1)
    | FunApp ((T_int.Add | T_real.RAdd), [t1; t2], _) -> Value.add (eval_term t1) (eval_term t2)
    | FunApp ((T_int.Sub | T_real.RSub), [t1; t2], _) -> Value.sub (eval_term t1) (eval_term t2)
    | FunApp ((T_int.Mult | T_real.RMult), [t1; t2], _) -> Value.mult (eval_term t1) (eval_term t2)
    | FunApp ((T_int.Div | T_real.RDiv), [t1; t2], _) -> Value.div (eval_term t1) (eval_term t2)
    | FunApp (T_int.Mod, [t1; t2], _) -> Value.bmod (eval_term t1) (eval_term t2)
    | FunApp (T_int.Power, [t1; t2], _) -> Value.pow (eval_term t1) (eval_term t2)
    | FunApp (T_bool.IfThenElse, [t1; t2; t3], _) -> Value.ite (eval_term t1) (eval_term t2) (eval_term t3)
    (* | FunApp ((T_recfvar.RecFVar _), _, _) as t -> T_recfvar.eval_term (eval_term) (simplify_term) t  *)
    | _ -> failwith "Unimplemented in eval_term"
(*val eval_pred: pred_sym -> Term.t list -> bool*)
and eval_pred pred_sym terms =
  match pred_sym, List.map ~f:eval_term terms with
  | T_int.Leq, [t1; t2] | T_real.RLeq, [t1; t2] -> Value.compare Z.Compare.(<=) Q.(<=) t1 t2
  | T_int.Geq, [t1; t2] | T_real.RGeq, [t1; t2] -> Value.compare Z.Compare.(>=) Q.(>=) t1 t2
  | T_int.Lt, [t1; t2]  | T_real.RLt, [t1; t2]  -> Value.compare Z.Compare.(<) Q.(<) t1 t2
  | T_int.Gt, [t1; t2]  | T_real.RGt, [t1; t2]  -> Value.compare Z.Compare.(>) Q.(>) t1 t2
  | T_bool.Eq, [t1; t2]  -> Value.compare Z.Compare.(=) Q.(=) ~opb:Stdlib.(=) t1 t2
  | T_bool.Neq, [t1; t2] -> Value.compare Z.Compare.(<>) Q.(<>) ~opb:Stdlib.(<>) t1 t2
  | T_int.PDiv, [t1; t2] -> Value.compare Z.Compare.(=) Q.(=) (Value.bmod t2 t1) (Value.Int (Z.zero))
  | T_int.NPDiv, [t1; t2] -> Value.compare Z.Compare.(<>) Q.(<>) (Value.bmod t2 t1) (Value.Int (Z.zero))
  | _ -> failwith "invalid comparation@app_pred."
(*val eval_atom: Atom.t -> bool*)
and eval_atom = let open Atom in function
    | True _ -> true | False _ -> false
    | App (Predicate.Psym pred_sym, terms, _) -> eval_pred pred_sym terms
    | App ((Predicate.Var(_, _) | Predicate.Fixpoint(_, _, _, _)), _, _) -> 
      failwith "Predicate variables and fixpoints cannot be evaluated into bool value."
(*val eval: Formula.t -> bool*)
and eval = let open Formula in function
    | Atom (atom, _) -> eval_atom atom
    | UnaryOp (Not, phi, _) -> not (eval phi)
    | BinaryOp (And, phi1, phi2, _) -> (eval phi1) && (eval phi2)
    | BinaryOp (Or, phi1, phi2, _) -> (eval phi1) || (eval phi2)
    | BinaryOp (Imply, phi1, phi2, _) -> not (eval phi1) || (eval phi2)
    | BinaryOp (Iff, phi1, phi2, _) -> Stdlib.(=) (eval phi1) (eval phi2)
    | LetRec(_, _, _) | Bind(_, _, _, _) -> failwith "LetRec and Bind cannot be evaluated into bool value."


(*val simplify_term: Term.t -> Term.t*)
and simplify_term = let open Term in function
    | Var (tvar, sort, info) -> Var (tvar, sort, info)
    | FunApp(T_bool.IfThenElse, ([t1; t2; t3] as ts), info) ->
      let t1 = simplify_term t1 in
      if T_bool.is_true t1 then simplify_term t2
      else if T_bool.is_false t1 then simplify_term t3
      else if Stdlib.(=) t2 t3 then simplify_term t2
      else if T_bool.is_true @@ simplify_term t2 && T_bool.is_false @@ simplify_term t3 then t1
      else if T_bool.is_false @@ simplify_term t2 && T_bool.is_true @@ simplify_term t3 then T_bool.neg t1
      else FunApp(T_bool.IfThenElse, List.map ts ~f:simplify_term, info)
    | FunApp (fun_sym, terms, info) ->
      let ts = List.map ~f:simplify_term terms in
      try of_value @@ eval_term (FunApp (fun_sym, ts, info)) with _ ->
      match fun_sym, ts with
      | T_bool.Formula phi, [] -> FunApp(T_bool.Formula (simplify phi), [], info)
      | T_int.Neg, [t] ->
        begin
          match t with
          | FunApp(T_int.Neg, [t1], _) -> t1
          | FunApp(T_int.Mult, [Term.FunApp(T_int.Int n, [], _); t1], _)
          | FunApp(T_int.Mult, [t1; Term.FunApp(T_int.Int n, [], _)], _) ->
            T_int.mk_mult (T_int.mk_int Z.(-n)) t1
          | _ -> FunApp(fun_sym, [t], info)
        end
      | T_real.RNeg, [t] -> 
        begin
          match t with
          | FunApp(T_real.RNeg, [t1], _) -> t1
          | FunApp(T_real.RMult, [Term.FunApp(T_real.Real r, [], _); t1], _)
          | FunApp(T_real.RMult, [t1; Term.FunApp(T_real.Real r, [], _)], _) ->
            T_real.mk_rmult (T_real.mk_real Q.(-r)) t1
          | _ -> FunApp(fun_sym, [t], info)
        end
      | T_int.Add, [t1; t2] ->
        if T_int.is_zero t2 then t1
        else if T_int.is_zero t1 then t2
        else FunApp (fun_sym, [t1; t2], info)
      | T_real.RAdd, [t1; t2] ->
        if T_real.is_rzero t2 then t1
        else if T_real.is_rzero t1 then t2
        else FunApp (fun_sym, [t1; t2], info)
      | T_int.Sub, [t1; t2] ->
        if T_int.is_zero t2 then t1
        else if T_int.is_zero t1 then T_int.mk_neg t2
        else FunApp (fun_sym, [t1; t2], info)
      | T_real.RSub, [t1; t2] ->
        if T_real.is_rzero t2 then t1
        else if T_real.is_rzero t1 then T_real.mk_rneg t2
        else FunApp (fun_sym, [t1; t2], info)
      | T_int.Mult, [t1; t2] ->
        if T_int.is_zero t1 || T_int.is_zero t2 then T_int.zero ()
        else if T_int.is_unit t1 then t2
        else if T_int.is_unit t2 then t1
        else if T_int.is_minus_one t1 then T_int.mk_neg t2
        else if T_int.is_minus_one t2 then T_int.mk_neg t1
        else FunApp (fun_sym, [t1; t2], info)
      | T_real.RMult, [t1; t2] ->
        if T_real.is_rzero t1 || T_real.is_rzero t2 then T_real.rzero ()
        else if T_real.is_runit t1 then t2
        else if T_real.is_runit t2 then t1
        else if T_real.is_rminus_one t1 then T_real.mk_rneg t2
        else if T_real.is_rminus_one t2 then T_real.mk_rneg t1
        else FunApp (fun_sym, [t1; t2], info)
      | T_int.Div, [t1; t2] ->
        if T_int.is_unit t2 then t1 else FunApp (fun_sym, [t1; t2], info)
      | T_real.RDiv, [t1; t2] ->
        if T_real.is_runit t2 then t1 else FunApp (fun_sym, [t1; t2], info)
      | T_int.Mod, [t1; t2] -> 
        if T_int.is_unit t2 then T_int.zero () else FunApp (fun_sym, [t1; t2], info)
      | T_recfvar.RecFVar (tvar, env, ret_sort, body), args -> 
        if List.exists args ~f:(Term.is_pathexp) then T_recfvar.mk_recfvar_app tvar env ret_sort body args
        else
          let senv = List.fold2_exn env args ~init:Map.Poly.empty ~f:(fun senv (tvar, _) t -> Map.Poly.add_exn senv ~key:tvar ~data:(simplify_term t))in
          let body' = Term.subst senv body in
          let body' = Term.map_term body' ~f:(
              function 
                Term.FunApp(T_recfvar.RecFVar (tvar, env, ret_sort, Term.Var(tvar1, _, _)), args, info) as t ->
                if(Stdlib.(=) tvar tvar1) then
                  Term.FunApp(T_recfvar.RecFVar (tvar, env, ret_sort, body), args, info)
                else t
              | t -> t) in
          (* print_endline @@ sprintf "%s => %s" (Term.str_of body) (Term.str_of body'); *)
          simplify_term body' 
      | T_array.ASelect, [arr; ti] ->
        begin match T_array.eval_select arr ti with
          | Some te -> simplify_term te
          | None -> FunApp (fun_sym, ts, info) 
        end
      | T_dt.DTSel (sel_name, dt, _), [t1] ->
        begin match t1 with
          | FunApp (T_dt.DTCons (cons_name, _, _), ts, _) -> 
            begin match Datatype.look_up_cons dt cons_name with
              | Some (cons) -> 
                let sels = Datatype.sels_of_cons cons in
                begin match List.fold2_exn sels ts ~init:None ~f:(
                    fun ret sel t ->
                      match ret with
                      | Some _ -> ret
                      | None -> if Stdlib.(=) (Datatype.name_of_sel sel) sel_name then Some t else None
                  ) with
                | Some t -> t
                | None -> FunApp (fun_sym, [t1], info)
                end
              | None -> assert false
            end
          | _ -> FunApp (fun_sym, [t1], info)
        end
      | fun_sym, ts -> FunApp (fun_sym, ts, info) (* including T_int.int, T_real.Real *)
(*val simplify_pred: Predicate.t -> Predicate.t*)
and simplify_pred = let open Predicate in function
    | Var (var, sort) -> Var (var, sort)
    | Psym psym -> Psym psym
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      Fixpoint(fixpoint, pvar, bounds, simplify body)
(*val simplify_pred_neg: Predicate.t -> Predicate.t*)
and simplify_pred_neg = let open Predicate in function
    | Var _ -> assert false (* handled with simplify_atom_neg *)
    | Psym T_int.Leq -> Psym T_int.Gt | Psym T_real.RLeq -> Psym T_real.RGt
    | Psym T_int.Geq -> Psym T_int.Lt | Psym T_real.RGeq -> Psym T_real.RLt
    | Psym T_int.Lt -> Psym T_int.Geq | Psym T_real.RLt -> Psym T_real.RGeq
    | Psym T_int.Gt -> Psym T_int.Leq | Psym T_real.RGt -> Psym T_real.RLeq
    | Psym T_bool.Eq -> Psym T_bool.Neq
    | Psym T_bool.Neq -> Psym T_bool.Eq
    | Psym (T_dt.IsCons (name, dt)) -> Psym (T_dt.IsNotCons (name, dt))
    | Psym (T_dt.IsNotCons (name, dt)) -> Psym (T_dt.IsCons (name, dt))
    | Psym _ -> assert false
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      Fixpoint(flip_fixpoint fixpoint, pvar, bounds, simplify_neg body)
(*val simplify_atom: Atom.t -> Formula.t*)
and simplify_atom = let open Atom in function
    | True _ -> Formula.mk_true ()
    | False _ -> Formula.mk_false ()
    | App(pred, terms, info) ->
      let pred' = simplify_pred pred in
      let terms' = List.map ~f:simplify_term terms in
      match pred', terms' with
      | Predicate.Psym T_bool.Eq, [t1; t2] when Stdlib.(=) t1 t2 -> Formula.mk_true ()
      | Predicate.Psym T_bool.Neq, [t1; t2] when Stdlib.(=) t1 t2 -> Formula.mk_false ()
      | Predicate.Psym T_bool.Eq, [t1; t2] when T_bool.is_true t1 && not @@ Term.is_var t2 -> simplify @@ Formula.of_bool_term t2
      | Predicate.Psym T_bool.Eq, [t1; t2] when T_bool.is_false t1 && not @@ Term.is_var t2 -> simplify_neg @@ Formula.of_bool_term t2
      | Predicate.Psym T_bool.Neq, [t1; t2] when T_bool.is_true t1 && not @@ Term.is_var t2 -> simplify_neg @@ Formula.of_bool_term t2
      | Predicate.Psym T_bool.Neq, [t1; t2] when T_bool.is_false t1 && not @@ Term.is_var t2 -> simplify @@ Formula.of_bool_term t2
      | Predicate.Psym T_bool.Eq, [t1; t2] when T_bool.is_true t2 && not @@ Term.is_var t1 -> simplify @@ Formula.of_bool_term t1
      | Predicate.Psym T_bool.Eq, [t1; t2] when T_bool.is_false t2 && not @@ Term.is_var t1 -> simplify_neg @@ Formula.of_bool_term t1
      | Predicate.Psym T_bool.Neq, [t1; t2] when T_bool.is_true t2 && not @@ Term.is_var t1 -> simplify_neg @@ Formula.of_bool_term t1
      | Predicate.Psym T_bool.Neq, [t1; t2] when T_bool.is_false t2 && not @@ Term.is_var t1 -> simplify @@ Formula.of_bool_term t1
      | Predicate.Psym T_bool.Eq, [t1; t2] when Stdlib.(=) (Term.sort_of t1) T_bool.SBool ->
        if Term.is_var t1 || Term.is_var t2 then
          Formula.mk_atom (App (Predicate.Psym T_bool.Eq, [t1; t2], info))(*ToDo*)
        else
          let p1 = Formula.of_bool_term t1 in
          let p2 = Formula.of_bool_term t2 in
          simplify @@ Formula.mk_or (Formula.mk_and p1 p2) (Formula.mk_and (Formula.mk_neg p1) (Formula.mk_neg p2)) ~info
      | Predicate.Psym T_bool.Neq, [t1; t2] when Stdlib.(=) (Term.sort_of t1) T_bool.SBool ->
        if Term.is_var t1 || Term.is_var t2 then
          Formula.mk_atom (App (Predicate.Psym T_bool.Neq, [t1; t2], info))(*ToDo*)
        else
          let p1 = Formula.of_bool_term t1 in
          let p2 = Formula.of_bool_term t2 in
          simplify @@ Formula.mk_or (Formula.mk_and (Formula.mk_neg p1) p2) (Formula.mk_and p1 (Formula.mk_neg p2)) ~info
      | Predicate.Psym T_bool.Eq, [Term.FunApp(T_int.Neg, [t1], _); t2] ->
        simplify_atom (T_bool.mk_eq t1 (T_int.mk_neg t2))
      | Predicate.Psym T_bool.Eq, [Term.FunApp(T_real.RNeg, [t1], _); t2] ->
        simplify_atom (T_bool.mk_eq t1 (T_real.mk_rneg t2))
      | Predicate.Psym T_bool.Eq, [Term.FunApp(T_int.Mult, [Term.FunApp(T_int.Int n, [], _); t1], _); t2]
        when Z.Compare.(=) n Z.minus_one ->
        simplify_atom (T_bool.mk_eq t1 (T_int.mk_neg t2))
      | Predicate.Psym T_bool.Eq, [Term.FunApp(T_real.RMult, [Term.FunApp(T_real.Real r, [], _); t1], _); t2]
        when Q.(=) r Q.minus_one ->
        simplify_atom (T_bool.mk_eq t1 (T_real.mk_rneg t2))
      | Predicate.Psym T_bool.Eq, [Term.FunApp(T_int.Mult, [t1; Term.FunApp(T_int.Int n, [], _)], _); t2]
        when Z.Compare.(=) n Z.minus_one ->
        simplify_atom (T_bool.mk_eq t1 (T_int.mk_neg t2))
      | Predicate.Psym T_bool.Eq, [Term.FunApp(T_real.RMult, [t1; Term.FunApp(T_real.Real r, [], _)], _); t2]
        when Q.(=) r Q.minus_one ->
        simplify_atom (T_bool.mk_eq t1 (T_real.mk_rneg t2))
      | Predicate.Psym T_bool.Neq, [Term.FunApp(T_int.Neg, [t1], _); t2] ->
        simplify_atom (T_bool.mk_neq t1 (T_int.mk_neg t2))
      | Predicate.Psym T_bool.Neq, [Term.FunApp(T_real.RNeg, [t1], _); t2] ->
        simplify_atom (T_bool.mk_neq t1 (T_real.mk_rneg t2))
      | Predicate.Psym T_bool.Neq, [Term.FunApp(T_int.Mult, [Term.FunApp(T_int.Int n, [], _); t1], _); t2]
        when Z.Compare.(=) n Z.minus_one ->
        simplify_atom (T_bool.mk_neq t1 (T_int.mk_neg t2))
      | Predicate.Psym T_bool.Neq, [Term.FunApp(T_real.RMult, [Term.FunApp(T_real.Real r, [], _); t1], _); t2]
        when Q.(=) r Q.minus_one ->
        simplify_atom (T_bool.mk_neq t1 (T_real.mk_rneg t2))
      | Predicate.Psym T_bool.Neq, [Term.FunApp(T_int.Mult, [t1; Term.FunApp(T_int.Int n, [], _)], _); t2]
        when Z.Compare.(=) n Z.minus_one ->
        simplify_atom (T_bool.mk_neq t1 (T_int.mk_neg t2))
      | Predicate.Psym T_bool.Neq, [Term.FunApp(T_real.RMult, [t1; Term.FunApp(T_real.Real r, [], _)], _); t2]
        when Q.(=) r Q.minus_one ->
        simplify_atom (T_bool.mk_neq t1 (T_real.mk_rneg t2))
      | Predicate.Psym T_bool.Eq, [Term.FunApp(T_dt.DTCons (name1, _, _), ts1, _); Term.FunApp(T_dt.DTCons (name2, _, _), ts2, _)] ->
        if not @@ Stdlib.(=) name1 name2 then Formula.mk_false ()
        else simplify @@ Formula.and_of @@ List.map2_exn ts1 ts2 ~f:Formula.eq
      | Predicate.Psym T_bool.Neq, [Term.FunApp(T_dt.DTCons (name1, _, _), ts1, _); Term.FunApp(T_dt.DTCons (name2, _, _), ts2, _)] -> 
        if not @@ Stdlib.(=) name1 name2 then Formula.mk_true ()
        else simplify @@ Formula.or_of @@ List.map2_exn ts1 ts2 ~f:Formula.neq
      | Predicate.Psym (T_dt.IsCons (name, _)), [Term.FunApp(T_dt.DTCons(name1, _, _), _, _)] -> 
        if Stdlib.(=) name1 name then Formula.mk_true () else Formula.mk_false ()
      | Predicate.Psym (T_dt.IsNotCons (name, _)), [Term.FunApp(T_dt.DTCons(name1, _, _), _, _)] -> 
        if Stdlib.(=) name1 name then Formula.mk_false () else Formula.mk_true ()
      | _, _ ->
        try
          if eval_atom (App (pred', terms', info)) then Formula.mk_true () else Formula.mk_false ()
        with _ -> Formula.mk_atom (App (pred', terms', info))
(*val simplify_atom_neg: Atom.t -> Formula.t*)
and simplify_atom_neg atom = let open Atom in 
  try begin match atom with
    | True _ -> Formula.mk_false ()
    | False _ -> Formula.mk_true ()
    | App(Predicate.Var (var, sort), args, info) ->
      Formula.mk_neg @@ Formula.mk_atom @@
      App(Predicate.Var (var, sort), List.map ~f:simplify_term args, info)
    | App(pred, args, info) ->
      simplify_atom (App (simplify_pred_neg pred, List.map ~f:simplify_term args, info))
  end with _ -> Formula.mk_neg @@ Formula.mk_atom atom
and simplify_andor_norec op phi1 phi2 info = let open Formula in
  match (op, phi1, phi2) with
  | And, Atom (Atom.False info', info), _
  | And, _, Atom (Atom.False info', info)
    -> Atom (Atom.False info', info)

  | Or, Atom (Atom.True info', info), _
  | Or, _, Atom (Atom.True info', info)
    -> Atom(Atom.True info', info)

  | And, Atom (Atom.True _, _), phi
  | And, phi, Atom (Atom.True _, _)
  | Or, Atom (Atom.False _, _), phi
  | Or, phi, Atom (Atom.False _, _)
    -> phi

  (* adhoc simplification rules *)
  | And,
    Atom (Atom.App (Predicate.Psym T_int.Geq, [t11; t12], _), _),
    Atom (Atom.App (Predicate.Psym T_int.Leq, [t21; t22], _), _)
  | And,
    Atom (Atom.App (Predicate.Psym T_int.Leq, [t11; t12], _), _),
    Atom (Atom.App (Predicate.Psym T_int.Geq, [t21; t22], _), _)
  | And,
    Atom (Atom.App (Predicate.Psym T_real.RGeq, [t11; t12], _), _),
    Atom (Atom.App (Predicate.Psym T_real.RLeq, [t21; t22], _), _)
  | And,
    Atom (Atom.App (Predicate.Psym T_real.RLeq, [t11; t12], _), _),
    Atom (Atom.App (Predicate.Psym T_real.RGeq, [t21; t22], _), _)
    when Stdlib.(=) t11 t21 && Stdlib.(=) t12 t22 ->
    simplify @@ Formula.eq t11 t12

  | And,
    BinaryOp(Or,
             Atom (Atom.App (Predicate.Psym T_bool.Eq, [Term.Var (x11, _, _); t11], _), _),
             Atom (Atom.App (Predicate.Psym T_bool.Eq, [Term.Var (x21, _, _); t21], _), _), _),
    BinaryOp(Or,
             Atom (Atom.App (Predicate.Psym T_bool.Neq, [Term.Var (x12, _, _); t12], _), _),
             Atom (Atom.App (Predicate.Psym T_bool.Neq, [Term.Var (x22, _, _); t22], _), _), _)
    when Stdlib.(=) x11 x12 && Stdlib.(=) x21 x22 &&
         T_bool.is_true t11 && T_bool.is_true t21 && T_bool.is_true t12 && T_bool.is_true t22 ->
    (* (x \/ y) /\ (not x \/ not y) iff (x <> y) *)
    Formula.neq (Term.mk_var x11 T_bool.SBool) (Term.mk_var x21 T_bool.SBool)

  | (op, phi1, phi2) -> BinaryOp(op, phi1, phi2, info)
(*val simplify: Formula.t -> Formula.t*)
and simplify ?(next=fun phi -> phi)phi = 
  let open Formula in 
  let rec aux ~next =function
    | Atom (atom, _) -> next @@ simplify_atom atom
    | UnaryOp(Not, phi, _) -> simplify_neg phi ~next
    | BinaryOp(Imply, phi1, phi2, info) ->
      aux (BinaryOp(Or, UnaryOp(Not, phi1, Dummy), phi2, info)) ~next
    | BinaryOp(Iff, phi1, phi2, info) ->
      aux (BinaryOp(And, BinaryOp(Imply, phi1, phi2, Dummy), BinaryOp(Imply, phi2, phi1, Dummy), info)) ~next
    | BinaryOp(op, phi1, phi2, info) ->
      aux phi1 ~next:(fun phi1' -> aux phi2 ~next:(fun phi2' -> next @@ simplify_andor_norec op phi1' phi2' info))
    | Bind(binder, bounds, phi, info) ->
      aux phi ~next:(fun phi' -> next @@ (
          match phi' with
          | Bind(binder', bounds', phi'', _) ->
            if Stdlib.(=) binder' binder then
              Bind(binder, SortEnv.append bounds' bounds, phi'', info)
            else
              Bind(binder, bounds, phi', info)
          | _ -> Bind(binder, bounds, phi', info)))
    | LetRec(funcs, phi, info) ->
      aux phi ~next:(fun phi' -> next @@ LetRec(List.map funcs ~f:(fun (fix, pvar, bounds, body) -> fix, pvar, bounds, simplify body), phi', info))
  in aux phi ~next
(*val simplify_neg: Formula.t -> Formula.t*)
and simplify_neg ?(next=fun phi -> phi) phi = 
  let open Formula in 
  let rec aux ~next =function
    | Atom (atom, _) -> next @@ simplify_atom_neg atom
    | UnaryOp(Not, phi, _) -> simplify phi ~next
    | BinaryOp(Imply, phi1, phi2, info) -> simplify_neg (BinaryOp(Or, UnaryOp(Not, phi1, Dummy), phi2, info)) ~next
    | BinaryOp(Iff, phi1, phi2, info) -> simplify_neg (BinaryOp(And, BinaryOp(Imply, phi1, phi2, Dummy), BinaryOp(Imply, phi2, phi1, Dummy), info)) ~next
    | BinaryOp(And, phi1, phi2, info) ->
      aux phi1 ~next:(fun phi1' -> aux phi2 ~next:(fun phi2' -> next @@ simplify_andor_norec Or phi1' phi2' info))
    | BinaryOp(Or, phi1, phi2, info) -> 
      aux phi1 ~next:(fun phi1' -> aux phi2 ~next:(fun phi2' -> next @@ simplify_andor_norec And phi1' phi2' info))
    | Bind(binder, bounds, phi, info) -> simplify (Bind(flip_quantifier binder, bounds, UnaryOp(Not, phi, Dummy), info)) ~next
    | LetRec(funcs, phi, info) ->
      let f = let pvars = List.map ~f:(fun (_, pvar, _, _) -> pvar) funcs in
        fun phi -> List.fold ~f:(fun phi pvar -> subst_neg pvar phi) ~init:phi pvars in
      aux phi ~next:(fun phi' -> 
          next @@ LetRec(List.map funcs ~f:(fun (fix, pvar, bounds, body) -> Predicate.flip_fixpoint fix, pvar, bounds, simplify_neg @@ f body), f phi', info))
  in aux phi ~next

let is_sat is_sat phi =
  try eval phi
  with _ -> (* reachable here if phi may cause division by 0 *) is_sat phi

let valid_check_records = Hashtbl.Poly.create ()

let rec local_is_valid is_valid phi =
  match phi with
  | Formula.Atom (atom, _ ) -> begin match is_valid_atom atom with | Some ret ->  ret | _ ->  is_valid phi end
  | Formula.BinaryOp(Formula.And, phi1, phi2, _) -> local_is_valid is_valid phi1 && local_is_valid is_valid phi2
  | Formula.UnaryOp(_, phi1, _) -> 
    begin match simplify_neg phi1 with
      | Formula.UnaryOp(_, _, _) -> is_valid phi
      | phi_neg -> local_is_valid is_valid phi_neg
    end
  | Formula.Bind(Formula.Forall , _, phi, _) -> local_is_valid is_valid phi
  | _ -> is_valid phi
(* cons x y = tl z*)
and is_valid_atom atom =
  match atom with
  | Atom.True _ -> Some true
  | Atom.False _ -> Some false
  | Atom.App((Predicate.Psym (T_int.Gt | T_int.Lt | T_real.RGt | T_real.RLt)), [t1; t2], _) ->
    if Stdlib.(=) t1 t2 then Some false
    else if Term.is_pathexp t1 then
      if Set.Poly.mem (Term.pathexps_of t2) t1 then Some false else None
    else if Term.is_pathexp t2 then
      if Set.Poly.mem (Term.pathexps_of t1) t2 then Some false else None
    else None
  | Atom.App((Predicate.Psym (T_bool.Neq)), [t1; t2], _) ->
    if Stdlib.(=) t1 t2 then Some false
    else if Term.is_pathexp t1 then
      if Set.Poly.mem (Term.pathexps_of t2) t1 then Some false else None
    else if Term.is_pathexp t2 then
      if Set.Poly.mem (Term.pathexps_of t1) t2 then Some false else None
    else None
  | Atom.App((Predicate.Psym (T_bool.Eq)), [t1; t2], _) ->
    if Stdlib.(=) t1 t2 then Some true
    else if Term.is_pathexp t1 then
      if Set.Poly.mem (Term.pathexps_of t2) t1 then Some false else None
    else if Term.is_pathexp t2 then
      if Set.Poly.mem (Term.pathexps_of t1) t2 then Some false else None
    else None
  | Atom.App((Predicate.Psym T_dt.IsCons _), [t1], _) -> 
    if Term.is_pathexp t1 then Some false else None
  | _ -> None


let is_valid_aux is_valid phi =
  let phi = Formula.nnf_of phi in
  match Hashtbl.Poly.find valid_check_records phi with
  | Some rcd -> rcd
  | None -> 
    let ret = is_valid phi in
    Hashtbl.Poly.set valid_check_records ~key:phi ~data:ret; ret

let is_valid is_valid phi =
  try eval phi
  with _ -> (* reachable here if phi may cause division by 0 *) 
    is_valid_aux is_valid phi

(* return
   Some true if cond => phi is valid
   Some false if cond => not phi is valid
   None otherwise *)
let check ?(cond=Formula.mk_true ()) is_valid_fun phi =
  let is_valid phi =
    try eval phi with _ -> (* reachable here if phi may cause division by 0 *)
      is_valid_aux is_valid_fun phi
  in
  if is_valid (simplify @@ Formula.mk_imply cond phi) then Some true
  else if is_valid (simplify @@ Formula.mk_imply cond (Formula.mk_neg phi)) then Some false
  else None
