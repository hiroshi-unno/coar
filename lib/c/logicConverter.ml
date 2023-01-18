open Core
open Common
open CSyntax
open Ast
open Ast.LogicOld

(* for ba_of_ltl *)

let verbose = false
module Debug = Debug.Make (val Debug.Config.(if verbose then enable else disable))

let rec subst_formulas ?(subst=Map.Poly.empty) ltl =
  if Ltl.is_f ltl then
    let ltl = Ltl.let_f ltl in
    let ltl, subst = subst_formulas ~subst ltl in
    Ltl.mk_f ltl, subst
  else if Ltl.is_g ltl then
    let ltl = Ltl.let_g ltl in
    let ltl, subst = subst_formulas ~subst ltl in
    Ltl.mk_g ltl, subst
  else if Ltl.is_u ltl then
    let ltl1, ltl2 = Ltl.let_u ltl in
    let ltl1, subst = subst_formulas ~subst ltl1 in
    let ltl2, subst = subst_formulas ~subst ltl2 in
    Ltl.mk_u ltl1 ltl2, subst
  else if Ltl.is_binop ltl then
    let binop, ltl1, ltl2 = Ltl.let_binop ltl in
    let ltl1, subst = subst_formulas ~subst ltl1 in
    let ltl2, subst = subst_formulas ~subst ltl2 in
    Ltl.mk_binop binop ltl1 ltl2, subst
  else if Ltl.is_neg ltl then
    let ltl = Ltl.let_neg ltl in
    let ltl, subst = subst_formulas ~subst ltl in
    Ltl.mk_neg ltl, subst
  else if Ltl.is_p ltl then
    let fml = Ltl.let_p ltl in
    let varname = Map.Poly.length subst + 1 |> Printf.sprintf "p%d" in
    let pvar = Ident.Pvar varname in
    let fml' = Formula.mk_atom (Atom.mk_app (Predicate.mk_var pvar []) [] ~info:Dummy) ~info:Dummy in
    let subst = Map.Poly.add_exn subst ~key:pvar ~data:fml in
    Ltl.mk_p fml', subst
  else failwith @@ Printf.sprintf "not implemented: %s" (Ltl.string_of ltl)

let bastr_of_ltlstr ltlstr =
  (try Common.Util.Command.sync_command "ltl3ba" ["-f"; "\""^ltlstr^"\""] []
   with _ -> Common.Util.Command.sync_command "./ltl3ba" ["-f"; "\""^ltlstr^"\""] [])
  |> String.concat ~sep:"\n"

let ba_subst_pvar subst ba =
  let states, initial_state, final_states, transition = BuchiAutomaton.let_ba ba in
  let transition = Array.map
      ~f:(List.map
            ~f:(fun (to_id, cond) ->
                to_id, Formula.subst_pvar subst cond))
      transition
  in
  BuchiAutomaton.mk_ba ~states ~initial_state ~final_states ~transition

let ba_of_ltl ltl =
  (* subst each formula with some predicate variable *)
  let ltl = Ltl.simplify ltl in
  let ltl, subst = subst_formulas ltl in
  let ltlstr = Ltl.string_of ltl in
  let bastr = bastr_of_ltlstr ltlstr in
  Debug.print @@ lazy "[Buchi Automaton(raw)]";
  Debug.print @@ lazy bastr;
  Debug.print @@ lazy "";
  match BaParser.parse bastr with
  | Ok ba ->
    let ba = ba_subst_pvar subst ba in
    ba
  | Error err ->
    failwith err

(* for hmes_of_ba *)
let hmes_of_ba ba =
  let states, initial_state, final_states, transition = BuchiAutomaton.let_ba ba in
  let hmespvar_of_state node =
    Ident.Pvar ("Q"^(string_of_int node))
  in
  let hmesfunc_of_transition toes =
    List.map
      ~f:(fun (state, cond_fml) ->
          let left =
            cond_fml
            |> Evaluator.simplify
            |> HMESFormula.of_formula
          in
          let right =
            hmespvar_of_state state
            |> HMESAtom.mk_pvar
            |> HMESFormula.mk_atom
            |> HMESFormula.mk_dia
          in
          HMESFormula.mk_and left right
        )
      toes
    |> HMESFormula.or_of
  in
  let nu_preds =
    List.fold_left
      ~f:(fun nu_preds state ->
          if Set.Poly.mem final_states state then
            HMES.mk_func
              Predicate.Nu
              (hmespvar_of_state state)
              (hmesfunc_of_transition transition.(state))
            :: nu_preds
          else
            nu_preds
        )
      ~init:[]
      (List.init states ~f:Fn.id)
  in
  let mu_preds =
    List.fold_left
      ~f:(fun mu_preds state ->
          if Set.Poly.mem final_states state then
            mu_preds
          else
            HMES.mk_func
              Predicate.Mu
              (hmespvar_of_state state)
              (hmesfunc_of_transition transition.(state))
            :: mu_preds
        )
      ~init:[]
      (List.init states ~f:Fn.id)
  in
  HMES.mk_hmes
    (nu_preds @ mu_preds)
    (hmespvar_of_state initial_state)
