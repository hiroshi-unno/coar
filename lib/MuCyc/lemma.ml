open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(** Lemma *)

type t = {
  guard : ((Ident.pvar * sort_env_list) * int) option;
  sequent : Sequent.t;
}

(** {6 Constructors} *)

let make guard sequent = { guard; sequent }
(*let make ?(evars=[]) phis1 phis2 =
  let guard = None in
  let sequent = Sequent.make ~evars phis1 phis2 in
  { guard=guard; sequent=sequent }*)

let of_sequent sequent = { guard = None; sequent }

(** {6 Inspectors} *)

let is_induction_hypothesis lemma =
  match lemma.guard with Some _ -> true | None -> false

let is_user_defined_lemma lemma =
  match lemma.guard with Some _ -> false | None -> true

let guard_pvar lemma =
  match lemma.guard with Some (pvar, _i) -> pvar | None -> assert false

let guard_i lemma =
  match lemma.guard with Some (_pvar, i) -> i | None -> assert false

(** {6 Operators} *)

let subst tsub lemma =
  { guard = lemma.guard; sequent = Sequent.subst tsub lemma.sequent }

(*
let update_guard_pvar new_pvar elem =
  {
  guard =
    (match elem.guard with
     | Some (pvar, i) -> Some(new_pvar, i)
     | None -> assert false);
  sequent = elem.sequent;
  }
  let update_sequent new_ent elem =
  {
  guard = elem.guard;
  sequent = new_ent;
  }
*)

let generate_from_preds _preds = Set.Poly.empty
(*ToDo*)
(*let generate_from_preds preds =
  let of_psub_elem (p, (tenv, phi)) =
    let pvam_l = [(Pvar.make p tenv |> Pva.of_pvar,[])] in
    {
      guard = None;
      sequent = Sequent.of_tuple (pvam_l, Formula.mk_true, [], [], phi);
    }
  in
  let psub =
    try FwAIHCSSolver.solve ~wide:true preds with _ -> []
  in
  let not_useful e = Formula.is_true (Sequent.rphi_of e.sequent) in
  List.map of_psub_elem psub
  |> List.remove_if not_useful (* Remove ... |- true *)*)

(*let forall_elim tenv lemma =
  let with_g = Sequent.forall_elim tenv @@ {
      lemma.sequent with
      left_atms(*ToDo*) =
        [Sequent.guard @@ Atom.pvar_app_of_senv (guard_pvar lemma)] @
        lemma.sequent.left_atms }
  in
  { lemma with sequent = { lemma.sequent with left_phi = with_g.left_phi } }*)

(** p(x,y,z), q(y,z,w), x=0 |- false
    ~> p(v1,v2,v3), q(v4,v5,v6), v1=0 /\ v2=v4 /\ v3=v5 |- false *)
let normalize lemma =
  let to_pvars pvams =
    List.map pvams ~f:(fun (pva, _) ->
        let atm, phi = Sequent.normalize_atom pva in
        assert (Formula.is_true phi);
        atm)
  in
  let fresh_pvars pvars phi =
    let vmap = ref [] in
    let phi' = ref phi in
    let atms =
      List.map pvars ~f:(fun (pvar, senv) ->
          ( pvar,
            List.map senv ~f:(fun (v, s) ->
                let v' = Ident.mk_fresh_tvar () in
                if List.Assoc.mem ~equal:Stdlib.( = ) !vmap v then
                  let eq =
                    Formula.eq
                      (Term.mk_var
                         (List.Assoc.find_exn ~equal:Stdlib.( = ) !vmap v)
                         s)
                      (Term.mk_var v' s)
                  in
                  phi' := Formula.mk_and !phi' eq
                else vmap := (v, v') :: !vmap;
                (v', s)) ))
    in
    (atms, Formula.rename (Map.Poly.of_alist_exn !vmap) !phi')
  in
  if is_induction_hypothesis lemma then
    let pvars1', phi1' =
      fresh_pvars
        (guard_pvar lemma :: to_pvars lemma.sequent.left_atms)
        lemma.sequent.left_phi
    in
    match pvars1' with
    | hd :: tl ->
        {
          guard = Some (hd, guard_i lemma);
          sequent =
            {
              lemma.sequent with
              left_atms =
                List.map ~f:(uncurry Atom.pvar_app_of_senv >> Sequent.guard) tl;
              left_phi = phi1';
            };
        }
    | [] -> failwith ""
  else
    let pvars1', phi1' =
      fresh_pvars (to_pvars lemma.sequent.left_atms) lemma.sequent.left_phi
    in
    {
      guard = None;
      sequent =
        {
          lemma.sequent with
          left_atms =
            List.map ~f:(uncurry Atom.pvar_app_of_senv >> Sequent.guard) pvars1';
          left_phi = phi1';
        };
    }

(** {6 Printers} *)

let pr_guard ppf = function
  | None -> Format.fprintf ppf ""
  | Some ((pvar, senv), alpha) ->
      Format.fprintf ppf "(%d) %s(%s)@;" alpha (Ident.name_of_pvar pvar)
        (str_of_sort_env_list (fun _sort -> "") senv)

let pr ppf lemma =
  Format.fprintf ppf "%a%a" pr_guard lemma.guard
    (Sequent.pr ~wo_guard:true)
    lemma.sequent

let pr_list ?(wo_guard = true) ppf t =
  if wo_guard then List.pr pr "@;" ppf t
  else
    let rec aux i = function
      | [] -> ()
      | hd :: [] -> Format.fprintf ppf "[%d] @[<v>%a@]" i pr hd
      | hd :: tl ->
          Format.fprintf ppf "[%d] @[<v>%a@]@;" i pr hd;
          aux (i - 1) tl
    in
    aux (List.length t) t

let pr_list_tex ppf _t = Format.fprintf ppf "not implemented"

(*
(** {6 Type Inference Algorithm} *)

let cgen_elem tenv elem =
  let constr, sequent' = Sequent.cgen tenv elem.sequent in
  constr, make elem.guard sequent'
  let ktenv sequent = Sequent.ktenv sequent.sequent

*)
