open Core
open Ast
open Ast.LogicOld
open Apronext

let mk_varmap vars =
  List.fold vars ~init:Map.Poly.empty ~f:(fun map tvar ->
      let name = Ident.name_of_tvar tvar in
      let var = Apron.Var.of_string name in
      Map.Poly.add_exn map ~key:tvar ~data:var)

let mk_real_env varmap =
  let vararray = Array.of_list @@ Map.Poly.data varmap in
  Environmentext.make [||] vararray

let mk_int_env varmap =
  let vararray = Array.of_list @@ Map.Poly.data varmap in
  Environmentext.make vararray [||]

let mk_expr env = Apron.Linexpr1.make env

let of_real_psym psym =
  match psym with
  | T_bool.Eq -> Apron.Lincons0.EQ
  | T_bool.Neq -> Apron.Lincons0.DISEQ
  | T_real.RGeq -> Apron.Lincons0.SUPEQ
  | T_real.RGt -> Apron.Lincons0.SUP
  | _ -> assert false

let of_int_psym psym =
  match psym with
  | T_bool.Eq -> Apron.Lincons0.EQ
  | T_bool.Neq -> Apron.Lincons0.DISEQ
  | T_int.Geq -> Apron.Lincons0.SUPEQ
  | T_int.PDiv | T_int.NotPDiv -> failwith "not support pdiv" (*TODO*)
  | _ -> assert false

let of_real_term term varmap =
  let monomials = Normalizer.linear_real_monomials_of (Value.Real Q.one) term in
  Map.Poly.fold monomials ~init:([], None) ~f:(fun ~key ~data:coeff (l, op) ->
      let coeff = Q.to_string @@ Value.real_of coeff in
      match key with
      | Some (Term.Var (tvar, T_real.SReal, _)) ->
          let var = Map.Poly.find_exn varmap tvar in
          let cv = (Coeffext.Scalar (Mpqf (Mpqf.of_string coeff)), var) in
          (cv :: l, op)
      | None -> (
          match op with
          | Some _ -> assert false
          | None ->
              let c = Coeffext.Scalar (Scalarext.Mpqf (Mpqf.of_string coeff)) in
              (l, Some c))
      | _ -> assert false)

let of_int_term term varmap =
  let monomials = Normalizer.linear_int_monomials_of (Value.Int Z.one) term in
  Map.Poly.fold monomials ~init:([], None) ~f:(fun ~key ~data:coeff (l, op) ->
      let coeff = Z.to_string @@ Value.int_of coeff in
      match key with
      | Some (Term.Var (tvar, T_int.SInt, _)) ->
          let var = Map.Poly.find_exn varmap tvar in
          let cv = (Coeffext.Scalar (Mpqf (Mpqf.of_string coeff)), var) in
          (cv :: l, op)
      | None -> (
          match op with
          | Some _ -> assert false
          | None ->
              let c = Coeffext.Scalar (Scalarext.Mpqf (Mpqf.of_string coeff)) in
              (l, Some c))
      | _ -> assert false)

(*atom is already normalized*)
let of_real_atom atom varmap =
  match atom with
  | Atom.True _ -> None
  | Atom.False _ -> assert false
  | Atom.App (Predicate.Psym pred, [ t; _t0 ], _)
    when match pred with
         | T_bool.(Eq | Neq) | T_real.(RGeq | RGt) -> true
         | _ -> false ->
      let typ = of_real_psym pred in
      let env = mk_real_env varmap in
      let cons = Linconsext.make (mk_expr env) typ in
      let cv, c = of_real_term t varmap in
      Linconsext.set_list cons cv c;
      Some cons
  | _ -> assert false

let of_int_atom atom varmap =
  match atom with
  | Atom.True _ -> None
  | Atom.False _ -> assert false
  | Atom.App (Predicate.Psym pred, [ t; _t0 ], _)
    when match pred with T_bool.(Eq | Neq) | T_int.Geq -> true | _ -> false ->
      let typ = of_int_psym pred in
      let env = mk_int_env varmap in
      let cons = Linconsext.make (mk_expr env) typ in
      let cv, c = of_int_term t varmap in
      Linconsext.set_list cons cv c;
      Some cons
  | Atom.App (Predicate.Psym pred, [ _c; _t ], _)
    when match pred with T_int.(PDiv | NotPDiv) -> true | _ -> false ->
      failwith "not support pdiv"
  | _ -> assert false

let to_real_term coeff =
  let s = Mpqf.to_string @@ Coeffext.to_mpqf coeff in
  T_real.mk_real (Q.of_string s)

let to_int_term coeff =
  let s = Mpqf.to_string @@ Coeffext.to_mpqf coeff in
  T_int.mk_int (Z.of_string s)

let to_model varmap generator =
  let typ = Generatorext.get_typ generator in
  match typ with
  | VERTEX ->
      let expr = Generatorext.get_linexpr1 generator in
      let model =
        Map.Poly.map varmap ~f:(fun var ->
            let coeff = Apron.Linexpr1.get_coeff expr var in
            to_real_term coeff)
      in
      Some model
  | RAY | LINE -> None
  | _ -> assert false

let to_ray varmap generator =
  let typ = Generatorext.get_typ generator in
  match typ with
  | RAY ->
      let expr = Generatorext.get_linexpr1 generator in
      let ray =
        Map.Poly.map varmap ~f:(fun var ->
            let coeff = Apron.Linexpr1.get_coeff expr var in
            to_real_term coeff)
      in
      Some [ ray ]
  | LINE ->
      let expr = Generatorext.get_linexpr1 generator in
      let pray =
        Map.Poly.map varmap ~f:(fun var ->
            let coeff = Apron.Linexpr1.get_coeff expr var in
            to_real_term coeff)
      in
      let mray =
        Map.Poly.map pray ~f:(fun p ->
            Evaluator.simplify_term @@ T_real.mk_rneg p)
      in
      Some [ pray; mray ]
  | VERTEX -> None
  | _ -> assert false

let to_real_psym = function
  | Apron.Tcons0.EQ -> T_bool.Eq
  | Apron.Tcons0.DISEQ -> T_bool.Neq
  | Apron.Tcons0.SUPEQ -> T_real.RGeq
  | Apron.Tcons0.SUP -> T_real.RGt
  | _ -> assert false

let to_int_psym = function
  | Apron.Tcons0.EQ -> T_bool.Eq
  | Apron.Tcons0.DISEQ -> T_bool.Neq
  | Apron.Tcons0.SUPEQ -> T_int.Geq
  | Apron.Tcons0.SUP -> T_int.Gt
  | Apron.Tcons0.EQMOD _ -> T_int.PDiv

let to_real_atom cons varmap =
  let typ = Linconsext.get_typ cons in
  let cterm = to_real_term @@ Linconsext.get_cst cons in
  let terms =
    Map.Poly.fold varmap ~init:[] ~f:(fun ~key:tvar ~data:var l ->
        let coeff = Linconsext.get_coeff cons var in
        let term =
          T_real.mk_rmul (to_real_term coeff) (Term.mk_var tvar T_real.SReal)
        in
        term :: l)
  in
  let term = Evaluator.simplify_term @@ T_real.mk_rsum cterm terms in
  let t0 = T_real.rzero () in
  Atom.mk_psym_app (to_real_psym typ) [ term; t0 ]

let to_int_atom cons varmap =
  let typ = Linconsext.get_typ cons in
  let cterm = to_int_term @@ Linconsext.get_cst cons in
  let terms =
    Map.Poly.fold varmap ~init:[] ~f:(fun ~key:tvar ~data:var l ->
        let coeff = Linconsext.get_coeff cons var in
        let term =
          T_int.mk_mul (to_int_term coeff) (Term.mk_var tvar T_int.SInt)
        in
        term :: l)
  in
  let term = Evaluator.simplify_term @@ T_int.mk_sum cterm terms in
  let psym = to_int_psym typ in
  match psym with
  | T_bool.(Eq | Neq) | T_int.(Geq | Gt) ->
      let t0 = T_int.zero () in
      Atom.mk_psym_app psym [ term; t0 ]
  | T_int.PDiv -> failwith "not support pdiv"
  | _ -> assert false

let mk_real_polyhedron varmap atoms =
  let env = mk_real_env varmap in
  let conslist =
    List.fold atoms ~init:[] ~f:(fun l a ->
        match of_real_atom a varmap with Some cons -> cons :: l | None -> l)
  in
  Apol.of_lincons_list env conslist

let mk_int_polyhedron varmap atoms =
  let env = mk_int_env varmap in
  let conslist =
    List.fold atoms ~init:[] ~f:(fun l a ->
        match of_int_atom a varmap with Some cons -> cons :: l | None -> l)
  in
  Apol.of_lincons_list env conslist

let mk_vertex polyhedron varmap =
  let gen = Apol.to_generator_list polyhedron in
  List.fold gen ~init:[] ~f:(fun l g ->
      match to_model varmap g with Some m -> m :: l | None -> l)

let mk_ray polyhedron varmap =
  let gen = Apol.to_generator_list polyhedron in
  List.fold gen ~init:[] ~f:(fun l g ->
      match to_ray varmap g with Some m -> m @ l | None -> l)

let mk_real_atoms polyhedron varmap =
  let conslist = Apol.to_lincons_list polyhedron in
  List.map conslist ~f:(fun cons -> to_real_atom cons varmap)

let mk_int_atoms polyhedron varmap =
  let conslist = Apol.to_lincons_list polyhedron in
  List.map conslist ~f:(fun cons -> to_int_atom cons varmap)

let separate_real_polyhedron polyhedron atom varmap =
  match of_real_atom atom varmap with
  | Some cons -> Apol.filter_lincons polyhedron cons
  | None -> assert false

let separate_int_polyhedron polyhedron atom varmap =
  match of_int_atom atom varmap with
  | Some cons -> Apol.filter_lincons polyhedron cons
  | None -> assert false

let real_poly_to_string polyhedron varmap =
  let atoms = mk_real_atoms polyhedron varmap in
  "polyhedron\n" ^ List.to_string atoms ~f:Atom.str_of

let int_poly_to_string polyhedron varmap =
  let atoms = mk_int_atoms polyhedron varmap in
  "polyhedron\n" ^ List.to_string atoms ~f:Atom.str_of
