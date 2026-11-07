open Core
open Common.Ext
open Ast
open Ast.LogicOld

type t = Lp.Problem.t

let lp_var_of_tvar tvar sort =
  match sort with
  | T_int.SInt ->
      Lp.var ~integer:true ~lb:Float.neg_infinity ~ub:Float.infinity
      @@ Ident.name_of_tvar tvar
  | T_real.SReal ->
      Lp.var ~integer:false ~lb:Float.neg_infinity ~ub:Float.infinity
      @@ Ident.name_of_tvar tvar
  | _ -> failwith "Type of lp var mast be int or real."

let lp_binop_of_fun_sym = function
  | T_int.Add | T_real.RAdd -> Lp.( ++ )
  | T_int.Sub | T_real.RSub -> Lp.( -- )
  | T_int.Mul | T_real.RMul -> Lp.( *~ )
  | T_int.Div _ | T_real.RDiv -> Lp.( /~ )
  | _ -> failwith "Fun_sym translate error."

let rec lp_term_of_term term =
  match term with
  | Term.Var (tvar, ((T_int.SInt | T_real.SReal) as sort), _) ->
      lp_var_of_tvar tvar sort
  | Term.Var (tvar, _, _) ->
      failwith (Ident.name_of_tvar tvar ^ "'s sort mast be int or real.")
  | Term.FunApp (T_int.Neg, [ t ], _) -> Lp.( ~-- ) (lp_term_of_term t)
  | Term.FunApp (T_real.RNeg, [ t ], _) -> Lp.( ~-- ) (lp_term_of_term t)
  | Term.FunApp (op, [ t1; t2 ], _) ->
      lp_binop_of_fun_sym op (lp_term_of_term t1) (lp_term_of_term t2)
  | Term.FunApp (T_int.Int i, _, _) ->
      if Z.equal i Z.one then Lp.one
      else if Z.equal i Z.zero then Lp.zero
      else Lp.c @@ Z.to_float i
  | Term.FunApp (T_real.Real r, _, _) ->
      Lp.c @@ Q.to_float r (* TODO: support for multi precision R on Integer *)
  | Term.FunApp (_, ts, _) ->
      failwith
        (sprintf "Term [%s] cannot be translated to lp_term.:%d"
           (Term.str_of term) (List.length ts))
  | _ -> failwith @@ "[lp_term_of_term] unsupported : " ^ Term.str_of term

let lp_cnstr_of_atom ?(precision = 0.00001) atom =
  let open Lp in
  let _ = precision in
  match atom with
  | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) ->
      [ lp_term_of_term t1 =~ lp_term_of_term t2 ]
  | Atom.App (Predicate.Psym T_int.Geq, [ t1; t2 ], _) ->
      [ lp_term_of_term t1 >~ lp_term_of_term t2 ]
  | Atom.App (Predicate.Psym T_int.Leq, [ t1; t2 ], _) ->
      [ lp_term_of_term t1 <~ lp_term_of_term t2 ]
  | Atom.App (Predicate.Psym T_int.Gt, [ t1; t2 ], _) ->
      [ lp_term_of_term t1 >~ lp_term_of_term t2 ++ one ]
  | Atom.App (Predicate.Psym T_int.Lt, [ t1; t2 ], _) ->
      [ lp_term_of_term t1 <~ lp_term_of_term t2 -- one ]
  | Atom.App (Predicate.Psym T_real.RGeq, [ t1; t2 ], _) ->
      [ lp_term_of_term t1 >~ lp_term_of_term t2 ]
  | Atom.App (Predicate.Psym T_real.RLeq, [ t1; t2 ], _) ->
      [ lp_term_of_term t1 <~ lp_term_of_term t2 ]
  | Atom.App (Predicate.Psym T_real.RGt, [ t1; t2 ], _) ->
      [ lp_term_of_term t1 >~ lp_term_of_term t2 ++ c precision ]
  | Atom.App (Predicate.Psym T_real.RLt, [ t1; t2 ], _) ->
      [ lp_term_of_term t1 <~ lp_term_of_term t2 -- c precision ]
  | Atom.App (Predicate.Psym T_bool.Neq, _, _) ->
      (* a disequality is a disjunction, not one linear row *)
      failwith
        (sprintf "Atom [%s] cannot be translate to lp_cnstr." (Atom.str_of atom))
  | Atom.True _ -> [ zero =~ zero ]
  | Atom.False _ -> [ zero =~ one ]
  | Atom.App (_, _, _) ->
      failwith
        (sprintf "Atom [%s] cannot be translate to lp_cnstr." (Atom.str_of atom))

(* The rows are a floating-point image of the atoms, not their meaning:
   constants are rounded to floats, integer division becomes real division,
   and a strict real inequality is tightened by [precision].  So a solution of
   the rows is only a candidate for the atoms and must be checked against them
   exactly, and the rows being infeasible says nothing about the atoms.
   Raises [Failure] on a symbol or atom with no linear row. *)
let of_atoms atoms =
  let lp_cnstrs =
    List.fold_left atoms ~init:[] ~f:(fun lp_cnstrs atom ->
        lp_cnstrs @ lp_cnstr_of_atom atom)
  in
  Lp.make (Lp.minimize Lp.zero) lp_cnstrs
