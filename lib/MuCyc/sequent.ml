open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open Config

(** Sequents *)

type guard = int Set.Poly.t
(** Sequent (e.g. [A x, y. E z, w. { P(x,y), Q(x,y), R(x,y,z) x = y |- Q(x,w) }]) *)
type t = {
  eqvars : (*existentially quantified variables*)sort_env_map;
  left_atms : (Atom.t * guard) list;
  left_phi : Formula.t;
  right_atms : (Atom.t * guard) list;
  right_phi : Formula.t
}

(** {6 Destructors} *)

let to_formula (e : t) =
  Formula.exists (Map.Poly.to_alist e.eqvars) @@
  Formula.mk_imply
    (Evaluator.simplify @@
     Formula.and_of @@ e.left_phi :: List.map e.left_atms ~f:(fst >> Formula.mk_atom))
    (Evaluator.simplify @@
     Formula.or_of @@ e.right_phi :: List.map e.right_atms ~f:(fst >> Formula.mk_atom))

(** {6 Constructors} *)

(*
(** Create from formulas with pva
  e.g. [Sequent.make \[p(x); x > 2; q(x)\] \[10 > x; x > 5\]] *)
  let make ?(eqvars=Map.Poly.empty) phis1 phis2 =
    let pvs = List.concat_map ~f:Formula.fvs (phis1 @ phis2) in
    let p1, f1 = List.partition ~f:(Formula.is_pva pvs) phis1 in
    let p2, f2 = List.partition ~f:(Formula.is_pva pvs) phis2 in
    { eqvars = eqvars;
      left_atms = List.map ~f:(fun p -> Pva.of_formula p, []) p1;
      left_phi = Formula.and_of f1;
      right_atms = List.map ~f:(fun p -> Pva.of_formula p, []) p2;
      right_phi = Formula.and_of f2 }
*)

let guard atm = atm, Set.Poly.empty
let ext_guard (atm, guard) i = atm, Set.add guard i
let ext_guard_list atms i = List.map ~f:(Fn.flip ext_guard i) atms

let of_formula exi_senv phi : t Set.Poly.t =
  Set.Poly.map ~f:(fun (ps, ns, phi) ->
      { eqvars = Map.Poly.empty;
        left_atms = Set.to_list @@ Set.Poly.map ~f:guard ns;
        left_phi = Formula.negate phi;
        right_atms = Set.to_list @@ Set.Poly.map ~f:guard ps;
        right_phi = Formula.mk_false ()}) @@
  Formula.cnf_of exi_senv @@ snd @@
  Formula.rm_quant ~forall:true @@ Evaluator.simplify @@
  (*LogicOld.Formula.elim_let_with_unknowns (Map.key_set exi_senv) @@
    Normalizer.normalize_let ~rename:true*) phi

(** Generate determinacy conjecture [p(~x,y1), p(~x,y2) |- y1 = y2] from predicates *)
let generate_determinacy_conjecture preds =
  List.filter_map preds ~f:(fun ((_fix, pvar, senv0, _body) : MuCLP.Pred.t) ->
      match senv0 with
      | [] -> None
      | _ ->
        let senv, (y1, s) =
          List.rest_last @@ mk_fresh_sort_env_list @@ List.map ~f:snd senv0
        in
        let y2 = Ident.mk_fresh_tvar () in
        Some {
          eqvars = Map.Poly.empty;
          left_atms = [
            guard @@ Atom.pvar_app_of_senv pvar (senv @ [y1, s]);
            guard @@ Atom.pvar_app_of_senv pvar (senv @ [y2, s])
          ];
          left_phi = Formula.mk_true ();
          right_atms = [];
          right_phi = Formula.eq (Term.mk_var y1 s) (Term.mk_var y2 s)
        })

(** {6 Inspectors} *)

let tvs_of sequent =
  Set.diff
    (Set.Poly.union_list @@
     Formula.tvs_of sequent.left_phi ::
     Formula.tvs_of sequent.right_phi ::
     List.map ~f:(fst >> Atom.tvs_of) sequent.left_atms @
     List.map ~f:(fst >> Atom.tvs_of) sequent.right_atms) @@
  Map.Poly.key_set sequent.eqvars
(*
  let pvs ent =
    let pvsL ent = List.map ~f:Pva.ident_of (lpvams_of ent |> List.map ~f:fst) in
    let pvsR ent = List.map ~f:Pva.ident_of (rpvams_of ent |> List.map ~f:fst) in
    pvsL ent @ pvsR ent
*)

(** {6 Operators} *)

let map_atm ~f = List.map ~f:(fun (atm, m) -> f atm, m)

let simplify (sequent : t) =
  {
    eqvars = sequent.eqvars;
    left_atms = List.unique @@ sequent.left_atms;
    left_phi = Evaluator.simplify @@ sequent.left_phi;
    right_atms = List.unique @@ sequent.right_atms;
    right_phi = Evaluator.simplify @@ sequent.right_phi
  }

(** e.g. p(x-1) ~> (p(v1), v1=x-1) for fresh v1 *)
let normalize_atom atm =
  let pvar, sorts, ts, _ = Atom.let_pvar_app atm in
  let senv = mk_fresh_sort_env_list sorts in
  (pvar, senv),
  Formula.and_of @@ List.map2_exn senv ts ~f:(fun (x, s) -> Formula.eq (Term.mk_var x s))

(** e.g. p(x-1){(1)} |- p(x+1) ~> A v1, v2. { p(v1){(1)}, v1=x-1, v2=x+1 |- p(v2) } *)
let normalize sequent =
  let atms1, phis1 =
    List.unzip_map (fun (atm, m) ->
        let (pvar, senv), phi = normalize_atom atm in
        (Atom.mk_pvar_app pvar (List.map ~f:snd senv) (Term.of_sort_env senv),
         m), phi)
      sequent.left_atms
  in
  let atms2, phis2 =
    List.unzip_map (fun (atm, m) ->
        let (pvar, senv), phi = normalize_atom atm in
        (Atom.mk_pvar_app pvar (List.map ~f:snd senv) (Term.of_sort_env senv),
         m), phi)
      sequent.right_atms
  in
  { sequent with
    left_atms = atms1;
    left_phi = Formula.and_of (sequent.left_phi :: phis1 @ phis2);
    right_atms = atms2 }

let normalize_body seq =
  (** assume that the RHS atoms are already normalized *)
  let left_atms', eqss =
    List.unzip @@ List.map seq.left_atms ~f:(fun (atm, guard) ->
        let pvar, sorts, args, _ = Atom.let_pvar_app atm in
        let args' = List.map2_exn args sorts ~f:(fun _ -> Term.mk_var (Ident.mk_fresh_tvar ())) in
        (Atom.mk_pvar_app pvar sorts args', guard),
        List.map2_exn args' args ~f:Formula.eq)
  in
  let bounds =
    Logic.of_old_sort_env_map @@ Map.of_set_exn @@ Set.Poly.union_list @@ List.map ~f:Atom.term_sort_env_of @@
    List.map ~f:fst (left_atms' @ seq.right_atms)
  in
  let phi1 =
    Formula.and_of @@ seq.left_phi :: Formula.negate seq.right_phi :: List.concat eqss
  in
  let uni_senv =
    Logic.of_old_sort_env_map @@ Map.of_set_exn @@ Formula.term_sort_env_of phi1
  in
  (*print_endline @@ "1: " ^ Formula.str_of phi1;*)
  let phi2 = Evaluator.simplify_neg @@ snd @@ Qelim.qelim_old bounds Map.Poly.empty (uni_senv, Evaluator.simplify_neg phi1) in
  (*print_endline @@ "2: " ^ Formula.str_of phi2;*)
  let phi3 = (*Formula.elim_let_equi false(*ToDo*) @@ Normalizer.normalize_let ~rename:true*) phi2 in
  (*print_endline @@ "3: " ^ Formula.str_of phi3;*)
  (*let phi3 = Z3Smt.Z3interface.simplify ~id:None Map.Poly.empty(* TODO *)~timeout:(Some 5000) phi3 in*)
  let _n, phi4 = Formula.quantify_except ~exists:true (Map.key_set bounds) phi3 in
  let _s = Formula.ast_size phi4 in
  (*print_endline @@ "4 (" ^ string_of_int n ^ ", " ^ string_of_int s ^ "): " ^ Formula.str_of phi4;*)
  let phi5 =
    (*Normalizer.normalize @@*) Evaluator.simplify @@
    (*if s * n <= 400(*ToDo*) then Z3Smt.Z3interface.qelim ~id:None ~fenv:(LogicOld.get_fenv ()) phi4
    else*) phi4
  in
  (*print_endline @@ "5: " ^ Formula.str_of phi5;*)
  { seq with left_atms = left_atms'; left_phi = phi5; right_phi = Formula.mk_false () }

(*let forall_elim tenv sequent =
  let bvs =
  Set.union
  (Set.Poly.of_list @@
   List.concat_map ~f:(fst >> Atom.let_pvar_app >> fun (_, _, args, _) ->
                       List.map args ~f:(Term.let_var >> fst >> fst))
     (sequent.left_atms @ sequent.right_atms))
  (Formula.tvs_of sequent.right_phi)
  in
  { sequent with
  left_phi = Qelim.elim_fvs_heap ~not_elim_fvs:bvs @@ Qelim.fa_elim tenv bvs sequent.left_phi;
  right_atms = List.map ~f:(fun (atm, _(*ToDo*)) -> atm, []) sequent.right_atms }*)

(** {6 Printers} *)

let pr ?(wo_guard=false) ppf sequent =
  let pr_phi ppf phi =
    if Fn.non Formula.is_true phi then Format.fprintf ppf "%s@;" (Formula.str_of phi)
  in
  let pr_eqvars ppf eqvars =
    if Fn.non Map.Poly.is_empty eqvars then
      Format.fprintf ppf "E %s. " (str_of_sort_env_map Term.str_of_sort eqvars)
  in
  let pr_i ppf i = Format.fprintf ppf "(%a)" Integer.pr i in
  let pr_atm ?(wo_guard = false) ppf (atm, guard) =
    if wo_guard then
      Format.fprintf ppf "%s" (Atom.str_of atm)
    else
      Format.fprintf ppf "%s {%a}" (Atom.str_of atm) (List.pr pr_i ",") @@
      Set.to_list guard
  in
  let pr_atms ppf atms =
    if Fn.non List.is_empty atms then
      Format.fprintf ppf "%a,@;" (List.pr (pr_atm ~wo_guard) ",@;") atms
  in
  Format.fprintf ppf "%a@[<v>@[<v>@[<v>%a%a@]  |- @[<v>%a%a@]@]@]"
    pr_eqvars sequent.eqvars
    pr_atms sequent.left_atms pr_phi sequent.left_phi
    pr_atms sequent.right_atms pr_phi sequent.right_phi
let pr_tex ppf _sequent = Format.fprintf ppf "not implemented"

(** {6 Inspectors} *)

(** faster than [equal] *)
let equal_light e1 e2 =
  let e1 = simplify e1 in
  let e2 = simplify e2 in
  Map.Poly.equal Stdlib.(=) e1.eqvars e2.eqvars &&
  Stdlib.(e1.left_atms = e2.left_atms &&
          e1.left_phi = e2.left_phi &&
          e1.right_atms = e2.right_atms &&
          e1.right_phi = e2.right_phi)

(** more precise than [equal_light] *)
let equal e1 e2 =
  Map.Poly.equal Stdlib.(=) e1.eqvars e2.eqvars &&
  List.equal Stdlib.(=) e1.left_atms e2.left_atms &&
  List.equal Stdlib.(=) e1.right_atms e2.right_atms &&
  Z3Smt.Z3interface.is_valid ~id:None (FunEnv.mk_empty ())
    (Formula.mk_iff e1.left_phi e2.left_phi) &&
  Z3Smt.Z3interface.is_valid ~id:None (FunEnv.mk_empty ())
    (Formula.mk_iff e1.right_phi e2.right_phi)

let subst tsub sequent =
  let tsub = Map.Poly.filter_keys tsub ~f:(Fn.non @@ Map.Poly.mem sequent.eqvars) in
  { sequent with
    left_atms = map_atm ~f:(Atom.subst tsub) sequent.left_atms;
    left_phi = Formula.subst tsub @@ sequent.left_phi;
    right_atms = map_atm ~f:(Atom.subst tsub) sequent.right_atms;
    right_phi = Formula.subst tsub @@ sequent.right_phi }

let rename ren sequent =
  let ren = Map.Poly.filter_keys ren ~f:(Fn.non @@ Map.Poly.mem sequent.eqvars) in
  { sequent with
    left_atms = map_atm ~f:(Atom.rename ren) sequent.left_atms;
    left_phi = Formula.rename ren @@ sequent.left_phi;
    right_atms = map_atm ~f:(Atom.rename ren) sequent.right_atms;
    right_phi = Formula.rename ren @@ sequent.right_phi }

let refresh_tvar sequent =
  rename (Map.of_set_exn @@ Set.Poly.map (tvs_of sequent) ~f:(fun x -> x, Ident.mk_fresh_tvar ())) sequent

let subst_preds_right psub sequent =
  { sequent with
    right_atms = [];
    right_phi = Formula.or_of @@
      sequent.right_phi :: List.map sequent.right_atms ~f:(fst >> Atom.subst_preds psub)}

let instantiate tsub sequent =
  let tsub = Map.Poly.filter_keys tsub ~f:(Map.Poly.mem sequent.eqvars) in
  { eqvars = Map.Poly.filter_keys sequent.eqvars ~f:(Fn.non @@ Map.Poly.mem tsub);
    left_atms = map_atm ~f:(Atom.subst tsub) sequent.left_atms;
    left_phi = Formula.subst tsub @@ sequent.left_phi;
    right_atms = map_atm ~f:(Atom.subst tsub) sequent.right_atms;
    right_phi = Formula.subst tsub @@ sequent.right_phi }

let make_sigmas atms1 pvars2 =
  List.fold_right pvars2 ~init:[] ~f:(fun (pvar2, args2) sigmas ->
      List.filter_map atms1 ~f:(fun atm1 ->
          let pvar1, _, ts1, _ = Atom.let_pvar_app atm1 in
          if Stdlib.(pvar1 = pvar2) then Some ts1 else None)
      |> List.map ~f:(List.map2_exn ~f:(fun (x2, _s2) t1 -> x2, t1) args2)
      |> Fn.flip List.cons sigmas)

(* Make candidate instantiations for eqvars
 *  e.g.
 *   Input: E e1,e2. (p(x,y), p(z,x), x=w |- p(x,e1), p(e2,w))
 *      (1) Enumerate candidates  : [ [x,e1 |-> x,y; x,e1 |-> z,x];
 *                                    [e2,w |-> x,y; e2,w |-> z,x] ]
 *      (2) Remove inconsistent   : [ [x,e1 |-> x,y;             ];
 *                                    [              e2,w |-> z,x] ]
 *      (3) Get all combination   : [ x,e1,e2,w |-> x,y,z,x; ]
 *      (4) Omit univ. quantified : [ e1,e2 |-> y,z; ]
 *      (5) Remove unsuccesssful  : [ e1,e2 |-> y,z; ]
 *   Output: [ e1,e2 |-> y,z; ]
*)
let mk_eqvars_inst _sequent = [[]](*ToDo*)
(*let safe (x, t) =
  Map.Poly.mem sequent.eqvars x ||
  Z3Smt.Z3interface.is_valid ~id:None (FunEnv.mk_empty ())
    (Formula.mk_imply sequent.left_phi
       (Formula.eq (Term.mk_var x @@ Term.sort_of t) t))
  in
  let success th =
  let th = Map.Poly.of_alist_exn th in
  let pvas1 =
    List.map sequent.right_atms ~f:(fun (atm, _) ->
        let pvar, _, args, _ = Atom.let_pvar_app @@ Atom.subst th atm in
        pvar, args)
  in
  let pvas2 =
    List.map sequent.left_atms ~f:(fun (atm, _) ->
        let pvar, _, args, _ = Atom.let_pvar_app atm in
        pvar, args)
  in
  let equal (pvar1, args1) (pvar2, args2) =
    Stdlib.(pvar1 = pvar2) &&
    List.for_all2_exn args1 args2 ~f:(fun t1 t2 ->
        Z3Smt.Z3interface.is_valid ~id:None (FunEnv.mk_empty ())
          (Formula.mk_imply sequent.left_phi (Formula.eq t1 t2)))
  in
  List.for_all pvas1 ~f:(fun pva1 -> List.exists pvas2 ~f:(equal pva1))
  in
  let sequent = normalize sequent in
  (* (1) *)
  make_sigmas
  (List.map sequent.left_atms ~f:fst)
  (List.map sequent.right_atms
     ~f:(fst >> fun atm ->
         let pvar, _, ts, _ = Atom.let_pvar_app atm in
         pvar, List.map ts ~f:(fun t -> fst @@ Term.let_var t)))
  (* (2) *)
  |> List.map ~f:(List.filter ~f:(List.for_all ~f:safe))
  (* (3) *)
  |> Vector.product List.concat
  (* (4) *)
  |> List.map ~f:(List.filter ~f:(fst >> Map.Poly.mem sequent.eqvars))
  (* (5) *)
  |> List.filter ~f:success*)

(** return true if the sequent is valid *)
let is_valid sequent =
  let sequent = normalize sequent in
  List.exists ~f:(fun th ->
      let sequent = instantiate (Map.Poly.of_alist_exn th) sequent in
      Z3Smt.Z3interface.is_valid ~id:None (FunEnv.mk_empty ()) @@
      Evaluator.simplify @@
      Formula.exists (Map.Poly.to_alist sequent.eqvars)(* bind remaining eqvars *) @@
      Formula.mk_imply sequent.left_phi sequent.right_phi ||
      List.exists sequent.right_atms ~f:(fun (pvar_right, _) ->
          let right_pvar, _, right_args, _ = Atom.let_pvar_app pvar_right in
          List.exists sequent.left_atms ~f:(fun (pvar_left, _) ->
              let left_pvar, _, left_args, _ = Atom.let_pvar_app pvar_left in
              Stdlib.(left_pvar = right_pvar) &&
              Z3Smt.Z3interface.is_valid ~id:None (FunEnv.mk_empty ()) @@
              Evaluator.simplify @@
              Formula.exists (Map.Poly.to_alist sequent.eqvars)(* bind remaining eqvars *) @@
              Formula.mk_imply sequent.left_phi
                (Formula.and_of @@ List.map2_exn left_args right_args ~f:Formula.eq)))) @@
  mk_eqvars_inst sequent
let is_valid ~print sequent =
  let cands = (*elim_forall_heap_with_heuristics tsub*)[sequent] in
  if Fn.non List.is_empty cands then
    List.exists cands ~f:(fun sequent ->
        print @@ lazy
          (Format.asprintf ":: Checking a candidate@.  %a" (pr ~wo_guard:false) sequent);
        is_valid sequent)
  else is_valid sequent
let is_valid ~print ~config sequent =
  Timer.enable_timeout config.timeout_check_valid Fn.id ignore
    (fun () -> is_valid ~print sequent)
    (fun _ ret  -> ret)
    (fun _ exc -> raise exc)

(*
(** Eliminate universal quantification on heap variables on LHS of sequent.
    1. Convert into PNF normal form
    e.g. Given formula: [phi1 /\ (A x1,x2. not phi2) |- false]
      PNF version  : [E x1,x2. (phi1 /\ not phi2 |- false)]
    2. Instantiate and generate candidates using heuristics
    e.g. [ [(x1,(l|->Nil) * h1); (x2,(l|->Nil) * h1)];
        [(x1,(l|->Nil) * h2); (x2,(l|->Nil) * h2)];
        ... ]
*)
let rec elim_forall_heap_with_heuristics tsub sequent =
  let subst_exists tsub sequent =
    let open Formula in
    let phi' =
      (*method fforall (id,ty) phi' =
        let subst_heap_conj v (h1,h2) t =
          Formula.subst [(v,Term.Heap.mk_separate h1 h2)] t
        in
        subst_heap_conj id (List.assoc id tsub) phi'
        method fexists xty phi' = exists [xty] phi'*)
      sequent.left_phi
    in
    { sequent with left_atms = sequent.left_atms; left_phi = phi' }
  in
  let mk_candidates heap_evars singletons =
    let singletons_with_emp =
      let emp = Term.Heap.mk_empty () in
      singletons @ List.map ~f:(fun _ -> emp) heap_evars
    in
    let kcombination k list =
      let rec aux k acc emit = function
        | [] -> acc
        | h :: t ->
          if k = 1 then aux k (emit [h] acc) emit t else
            let new_emit x = emit (h :: x) in
            aux k (aux (k-1) acc new_emit t) emit t
      in
      let emit x acc = x :: acc in
      aux k [] emit list
    in
    kcombination (List.length heap_evars) singletons_with_emp
    |> List.concat_map List.permutations
    |> List.map ~f:(fun tlist ->
        List.map2_exn ~f:(fun x t -> (x,(t,Term.mk_var x))) heap_evars tlist)
    |> List.unique
  in
  let heap_evars phi =
    Formula.fold
      (object
        method fatom _ = []
        method ftrue () = []
        method ffalse () = []
        method fnot _ = []
        method fand l1 l2 = l1 @ l2
        method for_ l1 l2 = l1 @ l2
        method fimply l1 l2 = l1 @ l2
        method fiff l1 l2 = l1 @ l2
        method fforall (id,ty) l = if Type.is_heap ty then id :: l else l
        method fexists _ l = l
        method fbox _ l = l
        method fdiamond _ l = l
        method fmu _ l = l
        method fnu _ l = l
      end) phi
  in
  let singletons phi =
    phi
    |> Formula.to_term
    |> Term.Heap.singleton_heaps
    |> List.unique
  in
  let he = heap_evars sequent.left_phi |> List.unique in
  let si = singletons sequent.left_phi in
  let cand = mk_candidates he si in
  if he != [] then
    begin
      Format.printf "heap_evars = %a@." Idnt.pr_list he;
      Format.printf "sigletons = %a@." Term.pr_list si;
      Format.printf "candidates = %a@."
        (List.pr (List.pr (Pair.pr Idnt.pr (Pair.pr Term.pr Term.pr)) ",@;") ";@.") cand;
    end;
  List.map ~f:(fun tsub -> subst_exists tsub sequent) cand
*)

(*
(** {6 Type Inference Algorithms} *)

let ktenv ent =
  let (pvams_l,phi_l,evars,pvams_r,phi_r) = tuple_of ent in
  let pvas_l = List.map ~f:fst pvams_l in
  let pvas_r = List.map ~f:fst pvams_r in
  let cs =
    (Idnt.make "?DummyConstructor", 0) ::
    List.concat_map ~f:Pva.kons pvas_l @
    ExtFormula.Formula.kons phi_l @
    List.concat_map ~f:Pva.kons pvas_r @
    ExtFormula.Formula.kons phi_r
  in
  let ty = Type.mk_adt (Idnt.make "atom") (List.map ~f:fst cs) in
  List.map
    ~f:(Pair.map_snd (fun i -> Type.mk_fun_args_ret (List.gen i (fun _ -> Type.new_var ())) ty))
    cs

let cgen tenv ent =
  let tenv = tenv @ (fvs ent |> TypEnv.of_vars) in
  let (pvams_l, phi_l, evars, pvams_r, phi_r) = tuple_of ent in
  let (pvas_l, ml) = List.split pvams_l in
  let (pvas_r, mr) = List.split pvams_r in
  let constr, ent =
    let constr1, pvas_l' =
      pvas_l
      |> List.map ~f:(SimTypInfer.cgen_pva tenv)
      |> List.split
      |> Pair.map List.concat id
    in
    let constr2, phi_l' = SimTypInfer.cgen_formula tenv phi_l in
    let constr3, pvas_r' =
      pvas_r
      |> List.map ~f:(SimTypInfer.cgen_pva tenv)
      |> List.split
      |> Pair.map List.concat id
    in
    let constr4, phi_r' = SimTypInfer.cgen_formula tenv phi_r in
    let evars' = List.filter ~f:(fun (id,ty) -> List.mem_assoc id evars) tenv in
    constr1 @ constr2 @ constr3 @ constr4,
    of_tuple (List.zip pvas_l' ml, phi_l', evars', List.zip pvas_r' mr, phi_r')
  in
  constr, ent

let infer tenv ent =
  let tenv =
    tenv @
    ktenv ent @
    (fvs ent |> TypEnv.of_vars) @
    (pvs ent |> TypEnv.of_vars)
  in
  let constr, ent' = cgen tenv ent in
  let tsub =
    try constr |> Type.unify
    with AbsTerm.CannotUnify ->
      Format.printf "unification error:@.  %a@.  %a@." TypEnv.pr tenv pr ent;
      assert false
  in
  TypEnv.subst tsub tenv, subst tsub ent'
*)
