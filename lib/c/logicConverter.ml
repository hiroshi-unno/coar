open Core
open CSyntax
open Ast
open Ast.LogicOld

(* for ba_of_ltl *)

let rec subst_formulas ?(subst = Map.Poly.empty) ltl =
  if Ltl.is_f ltl then
    let ltl = Ltl.let_f ltl in
    let ltl, subst = subst_formulas ~subst ltl in
    (Ltl.mk_f ltl, subst)
  else if Ltl.is_g ltl then
    let ltl = Ltl.let_g ltl in
    let ltl, subst = subst_formulas ~subst ltl in
    (Ltl.mk_g ltl, subst)
  else if Ltl.is_x ltl then
    let ltl = Ltl.let_x ltl in
    let ltl, subst = subst_formulas ~subst ltl in
    (Ltl.mk_x ltl, subst)
  else if Ltl.is_u ltl then
    let ltl1, ltl2 = Ltl.let_u ltl in
    let ltl1, subst = subst_formulas ~subst ltl1 in
    let ltl2, subst = subst_formulas ~subst ltl2 in
    (Ltl.mk_u ltl1 ltl2, subst)
  else if Ltl.is_binop ltl then
    let binop, ltl1, ltl2 = Ltl.let_binop ltl in
    let ltl1, subst = subst_formulas ~subst ltl1 in
    let ltl2, subst = subst_formulas ~subst ltl2 in
    (Ltl.mk_binop binop ltl1 ltl2, subst)
  else if Ltl.is_neg ltl then
    let ltl = Ltl.let_neg ltl in
    let ltl, subst = subst_formulas ~subst ltl in
    (Ltl.mk_neg ltl, subst)
  else if Ltl.is_p ltl then
    let fml = Ltl.let_p ltl in
    (* One proposition per distinct atomic formula, not per occurrence.  Each
       occurrence used to get its own [p<n>], so a property mentioning
       [output = 23] nine times reached ltl3ba as nine unrelated propositions
       p1 .. p9; the automaton it built had 137 states where the same formula
       over one proposition has 2, and the C-to-muCLP product (one predicate
       per automaton state and program statement) grew by the same factor --
       178,648 predicates instead of 2,608 on the 263-conditional P15 files of
       the CAV 2015 LTL corpus, 13.6 GB and 220 s of which 107 s were type
       inference.  The two automata accept the same language, so the muCLP's
       meaning is unchanged; only its size is. *)
    let pvar =
      match
        List.find (Map.Poly.to_alist subst) ~f:(fun (_, (_, fml0)) ->
            Stdlib.(fml0 = fml))
      with
      | Some (pvar, _) -> pvar
      | None -> Ident.Pvar (Map.Poly.length subst + 1 |> sprintf "p%d")
    in
    let fml' = Formula.mk_atom @@ Atom.mk_pvar_app pvar [] [] in
    let subst =
      if Map.Poly.mem subst pvar then subst
      else Map.Poly.add_exn subst ~key:pvar ~data:([], fml)
    in
    (Ltl.mk_p fml', subst)
  else failwith @@ sprintf "not implemented: %s" (Ltl.string_of ltl)

(* The formula in LTL3BA's input syntax, every binary subformula and every
   operand of a prefix operator in parentheses.  LTL3BA (like LTL2BA, from which
   its parser comes) gives [||] and [&&] one precedence and associates them to
   the left, so `p1 || p2 && p3` is read as `(p1 || p2) && p3`; a printer
   relying on [&&] binding tighter than [||] handed it a different formula.
   Requires: every atom is a nullary predicate variable application, as
   [subst_formulas] leaves it, whose name is a lowercase LTL3BA identifier.
   Ensures: LTL3BA reads exactly the formula given, whatever its operator
   precedences. *)
let rec ltl3ba_string_of = function
  | Ltl.F phi -> sprintf "F(%s)" (ltl3ba_string_of phi)
  | Ltl.G phi -> sprintf "G(%s)" (ltl3ba_string_of phi)
  | Ltl.X phi -> sprintf "X(%s)" (ltl3ba_string_of phi)
  | Ltl.NEG phi -> sprintf "!(%s)" (ltl3ba_string_of phi)
  | Ltl.U (phi1, phi2) ->
      sprintf "(%s) U (%s)" (ltl3ba_string_of phi1) (ltl3ba_string_of phi2)
  | Ltl.AND (phi1, phi2) ->
      sprintf "(%s) && (%s)" (ltl3ba_string_of phi1) (ltl3ba_string_of phi2)
  | Ltl.OR (phi1, phi2) ->
      sprintf "(%s) || (%s)" (ltl3ba_string_of phi1) (ltl3ba_string_of phi2)
  | Ltl.P fml ->
      let atom, _ = Formula.let_atom fml in
      let pvar, _, _, _ = Atom.let_pvar_app atom in
      Ident.name_of_pvar pvar

(* The command runs under [bash -c '...'], so the formula is double-quoted for
   that shell: [ltl3ba_string_of] emits no quote, [$], backquote or backslash.
   [resolve_tool] already prefers [./ltl3ba]; a non-zero exit (the tool
   missing, which bash reports as "command not found", or a formula LTL3BA
   rejects) is reported with LTL3BA's own output rather than as "not found". *)
let bastr_of_ltlstr ltlstr =
  (let args = [ "-f"; "\"" ^ ltlstr ^ "\"" ] in
   try
     Common.Util.Command.sync_command
       (Common.Util.Command.resolve_tool "ltl3ba")
       args []
   with Common.Util.Command.Shell_error out ->
     failwith
       (sprintf
          "ltl3ba failed on %s (install it or put it in the current \
           directory): %s"
          ltlstr out))
  |> String.concat ~sep:"\n"

let ba_subst_pvar subst ba =
  let states, initial_state, final_states, transition =
    BuchiAutomaton.let_ba ba
  in
  let transition =
    Array.map transition
      ~f:
        (List.map ~f:(fun (to_id, cond) ->
             (to_id, Formula.subst_preds subst cond)))
  in
  BuchiAutomaton.mk_ba ~states ~initial_state ~final_states ~transition

let ba_of_ltl ~print ltl =
  (* subst each formula with some predicate variable *)
  let ltl = Ltl.simplify ltl in
  let ltl, subst = subst_formulas ltl in
  let ltlstr = ltl3ba_string_of ltl in
  let bastr = bastr_of_ltlstr ltlstr in
  print @@ lazy "[Buchi Automaton(raw)]";
  print @@ lazy bastr;
  print @@ lazy "";
  match BaParser.from_string bastr with
  | Ok ba -> ba_subst_pvar subst ba
  | Error err -> failwith err

(* for hmes_of_ba *)
let hmes_of_ba ba =
  let states, initial_state, final_states, transition =
    BuchiAutomaton.let_ba ba
  in
  let hmespvar_of_state node = Ident.Pvar ("Q" ^ string_of_int node) in
  (* A state's equation is the disjunction of [cond /\ <>Q'] over its outgoing
     transitions.  A state without any (the claim's `false;`, e.g. the only
     state of an unsatisfiable formula's automaton) accepts no word, so its
     body is false: [HMESFormula.or_of] maps the empty list to true, which made
     such a state accept every run and a valid property come out invalid. *)
  let hmesfunc_of_transition = function
    | [] -> HMESAtom.mk_false () |> HMESFormula.mk_atom
    | toes ->
        List.map
          ~f:(fun (state, cond_fml) ->
            let left =
              cond_fml |> Evaluator.simplify |> HMESFormula.of_formula
            in
            let right =
              hmespvar_of_state state |> HMESAtom.mk_pvar
              |> HMESFormula.mk_atom |> HMESFormula.mk_dia
            in
            HMESFormula.mk_and left right)
          toes
        |> HMESFormula.or_of
  in
  let nu_preds, mu_preds =
    List.fold_left ~init:([], []) (List.init states ~f:Fn.id)
      ~f:(fun (nu_preds, mu_preds) state ->
        if Set.mem final_states state then
          ( HMES.mk_func Predicate.Nu (hmespvar_of_state state)
              (hmesfunc_of_transition transition.(state))
            :: nu_preds,
            mu_preds )
        else
          ( nu_preds,
            HMES.mk_func Predicate.Mu (hmespvar_of_state state)
              (hmesfunc_of_transition transition.(state))
            :: mu_preds ))
  in
  HMES.mk_hmes (nu_preds @ mu_preds) (hmespvar_of_state initial_state)
