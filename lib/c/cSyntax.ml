open Core
open Common.Ext
open Ast
open Ast.LogicOld

exception SyntaxError of string
exception SemanticError of string

module Define = struct
  type t = DEF of (string * int)

  let mk_def key value = DEF (key, value)
  let let_def = function DEF (key, value) -> (key, value)

  let rec subst_of_defines = function
    | [] -> Map.Poly.empty
    | DEF (key, value) :: tail ->
        let tvar = Ident.Tvar key in
        let term = T_int.from_int value in
        Map.Poly.add_exn (subst_of_defines tail) ~key:tvar ~data:term
end

module rec Ctl : sig
  type t =
    | AF of t
    | EF of t
    | AG of t
    | EG of t
    | OR of t * t
    | AND of t * t
    | IMP of t * t
    | AP of Formula.t

  type unwrap_result = PHI of t | PHI2 of t * t | FORMULA of Formula.t

  val is_af : t -> bool
  val is_ef : t -> bool
  val is_ag : t -> bool
  val is_eg : t -> bool
  val is_and : t -> bool
  val is_or : t -> bool
  val is_imp : t -> bool
  val is_ap : t -> bool
  val is_unop : t -> bool
  val is_binop : t -> bool
  val is_a : t -> bool
  val is_e : t -> bool
  val is_f : t -> bool
  val is_g : t -> bool
  val mk_af : t -> t
  val mk_ef : t -> t
  val mk_ag : t -> t
  val mk_eg : t -> t
  val mk_and : t -> t -> t
  val mk_or : t -> t -> t
  val mk_imp : t -> t -> t
  val mk_ap : Formula.t -> t
  val let_af : t -> t
  val let_ef : t -> t
  val let_ag : t -> t
  val let_eg : t -> t
  val let_ap : t -> Formula.t
  val string_of : t -> string
  val get_fv : t -> Variables.t
  val unwrap : t -> unwrap_result
  val let_unop : t -> t
  val let_binop : t -> Formula.binop * t * t
  val get_inner_phis : t -> t list
  val simplify : t -> t
  val simplify_neg : t -> t
  val make_all_e : t -> t
end = struct
  type t =
    | AF of t
    | EF of t
    | AG of t
    | EG of t
    | OR of t * t
    | AND of t * t
    | IMP of t * t
    | AP of Formula.t

  type unwrap_result = PHI of t | PHI2 of t * t | FORMULA of Formula.t

  let is_af = function AF _ -> true | _ -> false
  let is_ef = function EF _ -> true | _ -> false
  let is_ag = function AG _ -> true | _ -> false
  let is_eg = function EG _ -> true | _ -> false
  let is_and = function AND _ -> true | _ -> false
  let is_or = function OR _ -> true | _ -> false
  let is_imp = function IMP _ -> true | _ -> false
  let is_ap = function AP _ -> true | _ -> false
  let is_unop = function AF _ | EF _ | AG _ | EG _ -> true | _ -> false
  let is_binop = function OR _ | AND _ | IMP _ -> true | _ -> false
  let is_a = function AF _ | AG _ -> true | _ -> false
  let is_e = function EF _ | EG _ -> true | _ -> false
  let is_f = function AF _ | EF _ -> true | _ -> false
  let is_g = function AG _ | EG _ -> true | _ -> false
  let mk_af phi = AF phi
  let mk_ef phi = EF phi
  let mk_ag phi = AG phi
  let mk_eg phi = EG phi
  let mk_and phi1 phi2 = AND (phi1, phi2)
  let mk_or phi1 phi2 = OR (phi1, phi2)
  let mk_imp phi1 phi2 = IMP (phi1, phi2)
  let mk_ap fml = AP fml
  let let_af = function AF phi -> phi | _ -> assert false
  let let_ef = function EF phi -> phi | _ -> assert false
  let let_ag = function AG phi -> phi | _ -> assert false
  let let_eg = function EG phi -> phi | _ -> assert false
  let let_ap = function AP fml -> fml | _ -> assert false

  let rec string_of = function
    | AF phi -> sprintf "AF(%s)" (string_of phi)
    | EF phi -> sprintf "EF(%s)" (string_of phi)
    | AG phi -> sprintf "AG(%s)" (string_of phi)
    | EG phi -> sprintf "EG(%s)" (string_of phi)
    | OR (phi1, phi2) -> sprintf "OR(%s, %s)" (string_of phi1) (string_of phi2)
    | AND (phi1, phi2) ->
        sprintf "AND(%s, %s)" (string_of phi1) (string_of phi2)
    | IMP (phi1, phi2) ->
        sprintf "IMP(%s, %s)" (string_of phi1) (string_of phi2)
    | AP fml -> sprintf "AP(%s)" (Formula.str_of fml)

  let rec get_fv = function
    | AF phi | EF phi | AG phi | EG phi -> get_fv phi
    | OR (phi1, phi2) | AND (phi1, phi2) | IMP (phi1, phi2) ->
        Variables.union (get_fv phi1) (get_fv phi2)
    | AP fml ->
        Formula.tvs_of fml |> Set.to_list
        |> List.map ~f:Ast.Ident.name_of_tvar
        |> Variables.of_list

  let unwrap = function
    | AF phi | EF phi | AG phi | EG phi -> PHI phi
    | OR (phi1, phi2) | AND (phi1, phi2) | IMP (phi1, phi2) -> PHI2 (phi1, phi2)
    | AP fml -> FORMULA fml

  let let_unop phi = match unwrap phi with PHI phi -> phi | _ -> assert false

  let let_binop phi =
    match phi with
    | OR (phi1, phi2) -> (Formula.Or, phi1, phi2)
    | AND (phi1, phi2) -> (Formula.And, phi1, phi2)
    | IMP (phi1, phi2) -> (Formula.Imply, phi1, phi2)
    | _ -> assert false

  let rec simplify = function
    | AF phi -> AF (simplify phi)
    | EF phi -> EF (simplify phi)
    | AG phi -> AG (simplify phi)
    | EG phi -> EG (simplify phi)
    | AP fml -> AP (Evaluator.simplify fml)
    | OR (phi1, phi2) -> OR (simplify phi1, simplify phi2)
    | AND (phi1, phi2) -> AND (simplify phi1, simplify phi2)
    | IMP (phi1, phi2) -> OR (simplify_neg phi1, simplify phi2)

  and simplify_neg = function
    | AF phi -> EG (simplify_neg phi)
    | EF phi -> AG (simplify_neg phi)
    | AG phi -> EF (simplify_neg phi)
    | EG phi -> AF (simplify_neg phi)
    | AP fml -> AP (Evaluator.simplify_neg fml)
    | OR (phi1, phi2) -> AND (simplify_neg phi1, simplify_neg phi2)
    | AND (phi1, phi2) -> OR (simplify_neg phi1, simplify_neg phi2)
    | IMP (phi1, phi2) -> AND (simplify phi1, simplify_neg phi2)

  let rec make_all_e = function
    | AF phi | EF phi -> EF (make_all_e phi)
    | AG phi | EG phi -> EG (make_all_e phi)
    | AP fml -> AP fml
    | OR (phi1, phi2) -> OR (make_all_e phi1, make_all_e phi2)
    | AND (phi1, phi2) -> AND (make_all_e phi1, make_all_e phi2)
    | IMP (phi1, phi2) -> IMP (make_all_e phi1, make_all_e phi2)

  let get_inner_phis phi =
    match unwrap phi with
    | PHI phi -> [ phi ]
    | PHI2 (phi1, phi2) -> [ phi1; phi2 ]
    | FORMULA _ -> []
end

module rec Ltl : sig
  type t =
    | F of t
    | G of t
    | X of t
    | U of t * t
    | OR of t * t
    | AND of t * t
    | NEG of t
    | P of Formula.t

  val is_f : t -> bool
  val is_g : t -> bool
  val is_x : t -> bool
  val is_u : t -> bool
  val is_and : t -> bool
  val is_or : t -> bool
  val is_neg : t -> bool
  val is_p : t -> bool
  val is_unop : t -> bool
  val is_binop : t -> bool
  val mk_f : t -> t
  val mk_g : t -> t
  val mk_x : t -> t
  val mk_u : t -> t -> t
  val mk_r : t -> t -> t
  val mk_wu : t -> t -> t
  val mk_and : t -> t -> t
  val mk_or : t -> t -> t
  val mk_neg : t -> t
  val mk_p : Formula.t -> t
  val mk_binop : Formula.binop -> t -> t -> t
  val let_f : t -> t
  val let_g : t -> t
  val let_x : t -> t
  val let_u : t -> t * t
  val let_and : t -> t * t
  val let_or : t -> t * t
  val let_neg : t -> t
  val let_p : t -> Formula.t
  val string_of : ?priority:int -> t -> string
  val get_fv : t -> Variables.t
  val let_unop : t -> t
  val let_binop : t -> Formula.binop * t * t
  val simplify : t -> t
  val simplify_neg : t -> t
end = struct
  type t =
    | F of t
    | G of t
    | X of t
    | U of t * t
    | OR of t * t
    | AND of t * t
    | NEG of t
    | P of Formula.t

  let is_f = function F _ -> true | _ -> false
  let is_g = function G _ -> true | _ -> false
  let is_x = function X _ -> true | _ -> false
  let is_u = function U _ -> true | _ -> false
  let is_and = function AND _ -> true | _ -> false
  let is_or = function OR _ -> true | _ -> false
  let is_neg = function NEG _ -> true | _ -> false
  let is_p = function P _ -> true | _ -> false
  let is_unop = function F _ | G _ | X _ -> true | _ -> false
  let is_binop = function OR _ | AND _ -> true | _ -> false
  let mk_f phi = F phi
  let mk_g phi = G phi
  let mk_x phi = X phi
  let mk_u phi1 phi2 = U (phi1, phi2)
  let mk_r phi1 phi2 = NEG (U (NEG phi1, NEG phi2))
  let mk_wu phi1 phi2 = OR (U (phi1, phi2), G phi1)
  let mk_and phi1 phi2 = AND (phi1, phi2)
  let mk_or phi1 phi2 = OR (phi1, phi2)
  let mk_neg phi = NEG phi
  let mk_p fml = P fml

  let mk_binop binop phi1 phi2 =
    match binop with
    | Formula.And -> mk_and phi1 phi2
    | Formula.Or -> mk_or phi1 phi2
    | _ -> failwith "Ltl.mk_binop: irregal binop"

  let let_f = function F phi -> phi | _ -> assert false
  let let_g = function G phi -> phi | _ -> assert false
  let let_x = function X phi -> phi | _ -> assert false
  let let_u = function U (phi1, phi2) -> (phi1, phi2) | _ -> assert false
  let let_and = function AND (phi1, phi2) -> (phi1, phi2) | _ -> assert false
  let let_or = function OR (phi1, phi2) -> (phi1, phi2) | _ -> assert false
  let let_neg = function NEG phi -> phi | _ -> assert false
  let let_p = function P fml -> fml | _ -> assert false

  module Priority = struct
    let atom = 8
    let binary_and = 6
    let binary_or = 4
    let binary_u = 2
  end

  let rec string_of ?(priority = 0) = function
    | F phi ->
        sprintf "F%s" (string_of ~priority:Priority.atom phi)
        |> LogicOld.Priority.add_paren priority Priority.atom
    | G phi ->
        sprintf "G%s" (string_of ~priority:Priority.atom phi)
        |> LogicOld.Priority.add_paren priority Priority.atom
    | X phi ->
        sprintf "X%s" (string_of ~priority:Priority.atom phi)
        |> LogicOld.Priority.add_paren priority Priority.atom
    | U (phi1, phi2) ->
        sprintf "%s U %s"
          (String.paren @@ string_of ~priority:Priority.binary_u phi1)
          (String.paren @@ string_of ~priority:Priority.binary_u phi2)
        |> LogicOld.Priority.add_paren priority Priority.binary_u
    | OR (phi1, phi2) ->
        sprintf "%s \\/ %s"
          (string_of ~priority:Priority.binary_or phi1)
          (string_of ~priority:Priority.binary_or phi2)
        |> LogicOld.Priority.add_paren priority Priority.binary_or
    | AND (phi1, phi2) ->
        sprintf "%s /\\ %s"
          (string_of ~priority:Priority.binary_and phi1)
          (string_of ~priority:Priority.binary_and phi2)
        |> LogicOld.Priority.add_paren priority Priority.binary_and
    | NEG phi ->
        sprintf "!%s" (string_of ~priority:Priority.atom phi)
        |> LogicOld.Priority.add_paren priority Priority.atom
    | P fml ->
        let priority' =
          if priority = Priority.atom then LogicOld.Priority.neg_deref
          else if priority = Priority.binary_and then
            LogicOld.Priority.binary_and
          else if priority = Priority.binary_or then LogicOld.Priority.binary_or
          else priority
        in
        sprintf "%s" (Formula.str_of ~priority:priority' fml)
        |> LogicOld.Priority.add_paren priority Priority.atom

  let rec get_fv = function
    | F phi | G phi | X phi | NEG phi -> get_fv phi
    | U (phi1, phi2) | OR (phi1, phi2) | AND (phi1, phi2) ->
        Variables.union (get_fv phi1) (get_fv phi2)
    | P fml ->
        Formula.tvs_of fml |> Set.to_list
        |> List.map ~f:Ident.name_of_tvar
        |> Variables.of_list

  let let_unop = function F phi | G phi | X phi -> phi | _ -> assert false

  let let_binop phi =
    match phi with
    | U _ -> failwith "not implemented"
    | OR (phi1, phi2) -> (Formula.Or, phi1, phi2)
    | AND (phi1, phi2) -> (Formula.And, phi1, phi2)
    | _ -> assert false

  let rec simplify = function
    | F phi -> F (simplify phi)
    | G phi -> G (simplify phi)
    | X phi -> X (simplify phi)
    | P fml -> P (Evaluator.simplify fml)
    | U (phi1, phi2) -> U (simplify phi1, simplify phi2)
    | OR (phi1, phi2) -> OR (simplify phi1, simplify phi2)
    | AND (phi1, phi2) -> AND (simplify phi1, simplify phi2)
    | NEG phi -> simplify_neg phi

  and simplify_neg = function
    | F phi -> G (simplify_neg phi)
    | G phi -> F (simplify_neg phi)
    | X phi -> X (simplify_neg phi)
    | P fml -> P (Evaluator.simplify_neg fml)
    | U (phi1, phi2) -> NEG (U (phi1, phi2))
    | OR (phi1, phi2) -> AND (simplify_neg phi1, simplify_neg phi2)
    | AND (phi1, phi2) -> OR (simplify_neg phi1, simplify_neg phi2)
    | NEG phi -> simplify phi
end

module rec BuchiAutomaton : sig
  (* state count, initial state id, final state ids, transition *)
  type 'a t = BA of int * int * int Set.Poly.t * (int * 'a) list array

  val mk_ba :
    states:int ->
    initial_state:int ->
    final_states:int Set.Poly.t ->
    transition:(int * 'a) list array ->
    'a t

  val init_ba :
    states:int ->
    initial_state:int ->
    final_states:int list ->
    transition:(int * int * 'a) list ->
    'a t

  val let_ba : 'a t -> int * int * int Set.Poly.t * (int * 'a) list array
  val get_state_count : 'a t -> int
  val get_initial_state_id : 'a t -> int
  val get_final_state_ids : 'a t -> int Set.Poly.t
  val get_transition : 'a t -> (int * 'a) list array
  val string_of : printer:('a -> string) -> 'a t -> string
end = struct
  type 'a t = BA of int * int * int Set.Poly.t * (int * 'a) list array

  let mk_ba ~states ~initial_state ~final_states ~transition =
    BA (states, initial_state, final_states, transition)

  let init_ba ~states ~initial_state ~final_states ~transition =
    let final_states = Set.Poly.of_list final_states in
    let graph = Array.init states ~f:(fun _ -> []) in
    List.iter transition ~f:(fun (from_state_id, to_state_id, label_or_cond) ->
        graph.(from_state_id) <-
          (to_state_id, label_or_cond) :: graph.(from_state_id));
    mk_ba ~states ~initial_state ~final_states ~transition:graph

  let let_ba = function
    | BA (states, initial_state, final_states, transition) ->
        (states, initial_state, final_states, transition)

  let get_state_count = function BA (states, _, _, _) -> states

  let get_initial_state_id = function
    | BA (_, initial_state, _, _) -> initial_state

  let get_final_state_ids = function
    | BA (_, _, final_states, _) -> final_states

  let get_transition = function BA (_, _, _, transition) -> transition
  let string_of_node id = sprintf "Q%d" id

  let string_of ~printer = function
    | BA (states, initial_state, final_states, transition) ->
        sprintf
          "states: %d\ninitial state: %s\nfinal states: %s\ntransition:\n%s"
          states
          (string_of_node initial_state)
          (final_states |> String.concat_map_set ~sep:", " ~f:string_of_node)
          (Array.to_list transition
          |> String.concat_mapi_list ~sep:"\n" ~f:(fun from_id toes ->
                 sprintf " %s%s: %s"
                   (if from_id = initial_state then ">" else " ")
                   (if Set.mem final_states from_id then
                      String.paren (string_of_node from_id)
                    else sprintf " %s " (string_of_node from_id))
                   (String.concat_map_list ~sep:", " toes
                      ~f:(fun (to_id, label) ->
                        sprintf "%s(%s)" (string_of_node to_id) (printer label))))
          )
end

module HMESPriority = struct
  let atom = 8
  let atom_app = 6
  let binary_and = 4
  let binary_or = 2
end

module rec HMES : sig
  type func = Predicate.fixpoint * Ident.pvar * HMESFormula.t
  type t = Hmes of func list * Ident.pvar

  val mk_hmes : func list -> Ident.pvar -> t
  val mk_func : Predicate.fixpoint -> Ident.pvar -> HMESFormula.t -> func
  val let_hmes : t -> func list * Ident.pvar
  val string_of : t -> string
  val get_ftv : t -> Variables.t
end = struct
  type func = Predicate.fixpoint * Ident.pvar * HMESFormula.t
  type t = Hmes of func list * Ident.pvar

  let mk_hmes preds query_pvar = Hmes (preds, query_pvar)
  let mk_func fix pvar fml = (fix, pvar, fml)
  let let_hmes = function Hmes (preds, query_pvar) -> (preds, query_pvar)

  let string_of = function
    | Hmes (preds, query_pvar) ->
        sprintf "%s\ns.t.\n%s"
          (Ident.name_of_pvar query_pvar)
          (String.concat_map_list ~sep:";\n" preds ~f:(fun (fix, pvar, fml) ->
               sprintf "%s =%s %s" (Ident.name_of_pvar pvar)
                 (Predicate.str_of_fop fix)
                 (HMESFormula.string_of fml)))

  let get_ftv = function
    | Hmes (preds, _) ->
        List.fold_left ~init:Variables.empty preds ~f:(fun vars (_, _, fml) ->
            Variables.union vars (HMESFormula.get_ftv fml))
end

and HMESFormula : sig
  type t =
    | And of t * t
    | Or of t * t
    | Dia of t
    | Box of t
    | Atom of HMESAtom.t

  val mk_and : t -> t -> t
  val mk_or : t -> t -> t
  val mk_dia : t -> t
  val mk_box : t -> t
  val mk_atom : HMESAtom.t -> t
  val is_and : t -> bool
  val is_or : t -> bool
  val is_dia : t -> bool
  val is_box : t -> bool
  val is_atom : t -> bool
  val let_and : t -> t * t
  val let_or : t -> t * t
  val let_dia : t -> t
  val let_box : t -> t
  val let_atom : t -> HMESAtom.t
  val and_of : t list -> t
  val or_of : t list -> t
  val of_formula : Formula.t -> t
  val string_of : ?priority:int -> t -> string
  val get_ftv : t -> Variables.t
end = struct
  type t =
    | And of t * t
    | Or of t * t
    | Dia of t
    | Box of t
    | Atom of HMESAtom.t

  let mk_and fml1 fml2 = And (fml1, fml2)
  let mk_or fml1 fml2 = Or (fml1, fml2)
  let mk_dia fml = Dia fml
  let mk_box fml = Box fml
  let mk_atom atom = Atom atom
  let is_and = function And _ -> true | _ -> false
  let is_or = function Or _ -> true | _ -> false
  let is_dia = function Dia _ -> true | _ -> false
  let is_box = function Box _ -> true | _ -> false
  let is_atom = function Atom _ -> true | _ -> false
  let let_and = function And (fml1, fml2) -> (fml1, fml2) | _ -> assert false
  let let_or = function Or (fml1, fml2) -> (fml1, fml2) | _ -> assert false
  let let_dia = function Dia fml -> fml | _ -> assert false
  let let_box = function Box fml -> fml | _ -> assert false
  let let_atom = function Atom atom -> atom | _ -> assert false

  let rec and_of = function
    | [] -> Atom (True ())
    | [ fml ] -> fml
    | fml :: tail -> And (fml, and_of tail)

  let rec or_of = function
    | [] -> Atom (True ())
    | [ fml ] -> fml
    | fml :: tail -> Or (fml, or_of tail)

  let rec of_formula fml =
    if Formula.is_and fml then
      let fml1, fml2, _ = Formula.let_and fml in
      And (of_formula fml1, of_formula fml2)
    else if Formula.is_or fml then
      let fml1, fml2, _ = Formula.let_or fml in
      Or (of_formula fml1, of_formula fml2)
    else if Formula.is_atom fml then
      let atom, _ = Formula.let_atom fml in
      Atom (HMESAtom.of_atom atom)
    else failwith "HMESFormula.of_formula: not implemented or invalid formula"

  let rec string_of ?(priority = 0) = function
    | And (fml1, fml2) ->
        sprintf "%s /\\ %s"
          (string_of ~priority:HMESPriority.binary_and fml1)
          (string_of ~priority:HMESPriority.binary_and fml2)
        |> Priority.add_paren priority HMESPriority.binary_and
    | Or (fml1, fml2) ->
        sprintf "%s \\/ %s"
          (string_of ~priority:HMESPriority.binary_or fml1)
          (string_of ~priority:HMESPriority.binary_or fml2)
        |> Priority.add_paren priority HMESPriority.binary_or
    | Dia fml ->
        sprintf "<>%s" (string_of ~priority:HMESPriority.atom fml)
        |> Priority.add_paren priority HMESPriority.atom
    | Box fml ->
        sprintf "<>%s" (string_of ~priority:HMESPriority.atom fml)
        |> Priority.add_paren priority HMESPriority.atom
    | Atom atom -> HMESAtom.string_of ~priority atom

  let rec get_ftv = function
    | And (fml1, fml2) | Or (fml1, fml2) ->
        Variables.union (get_ftv fml1) (get_ftv fml2)
    | Dia fml | Box fml -> get_ftv fml
    | Atom atom -> HMESAtom.get_ftv atom
end

and HMESAtom : sig
  type t =
    | True of unit
    | False of unit
    | Pvar of Ident.pvar
    | PredApp of pred_sym * Term.t list

  val mk_true : unit -> t
  val mk_false : unit -> t
  val mk_pvar : Ident.pvar -> t
  val mk_predapp : pred_sym -> Term.t list -> t
  val is_true : t -> bool
  val is_false : t -> bool
  val is_pvar : t -> bool
  val is_predapp : t -> bool
  val let_pvar : t -> Ident.pvar
  val let_predapp : t -> pred_sym * Term.t list
  val of_atom : Atom.t -> t
  val string_of : ?priority:int -> t -> string
  val get_ftv : t -> Variables.t
  val atom_of : t -> Atom.t
end = struct
  type t =
    | True of unit
    | False of unit
    | Pvar of Ident.pvar
    | PredApp of pred_sym * Term.t list

  let mk_true () = True ()
  let mk_false () = False ()
  let mk_pvar pvar = Pvar pvar
  let mk_predapp sym args = PredApp (sym, args)
  let is_true = function True _ -> true | _ -> false
  let is_false = function False _ -> true | _ -> false
  let is_pvar = function Pvar _ -> true | _ -> false
  let is_predapp = function PredApp _ -> true | _ -> false
  let let_pvar = function Pvar pvar -> pvar | _ -> assert false

  let let_predapp = function
    | PredApp (sym, args) -> (sym, args)
    | _ -> assert false

  let of_atom atom =
    if Atom.is_true atom then True ()
    else if Atom.is_false atom then False ()
    else if Atom.is_psym_app atom then
      let sym, args, _ = Atom.let_psym_app atom in
      PredApp (sym, args)
    else if Atom.is_app atom then
      let pred, args, _ = Atom.let_app atom in
      if Predicate.is_var pred then
        let pvar, _ = Predicate.let_var pred in
        if List.is_empty args then Pvar pvar
        else failwith "HMESAtom.of_atom: pvar must have the type: () -> bool"
      else failwith "HMESAtom.of_atom: not implemented"
    else failwith "HMESAtom.of_atom: not implemented or invalid atom"

  let atom_of = function
    | True _ -> Atom.mk_true () ~info:Dummy
    | False _ -> Atom.mk_false () ~info:Dummy
    | Pvar pvar -> Atom.mk_pvar_app pvar [] [] ~info:Dummy
    | PredApp (sym, args) ->
        Atom.mk_app (Predicate.mk_psym sym) args ~info:Dummy

  let string_of ?(priority = 0) = function
    | True _ -> sprintf "true" |> Priority.add_paren priority HMESPriority.atom
    | False _ ->
        sprintf "false" |> Priority.add_paren priority HMESPriority.atom
    | Pvar pvar ->
        sprintf "%s" (Ident.name_of_pvar pvar)
        |> Priority.add_paren priority HMESPriority.atom
    | PredApp (sym, args) ->
        Atom.str_of (Atom.mk_app (Predicate.mk_psym sym) args ~info:Dummy)
        |> Priority.add_paren priority HMESPriority.atom

  let get_ftv = function
    | True _ | False _ | Pvar _ -> Variables.empty
    | PredApp (_, args) ->
        List.fold_left ~init:Variables.empty args ~f:(fun vars term ->
            Term.tvs_of term |> Set.to_list
            |> List.map ~f:Ident.name_of_tvar
            |> Variables.of_list |> Variables.union vars)
end

module rec Declare : sig
  type t = INT of string

  val is_int : t -> bool
  val mk_int : string -> t
  val let_int : t -> string
  val string_of : t -> string
end = struct
  type t = INT of string

  let is_int = function INT _ -> true
  let mk_int varname = INT varname
  let let_int = function INT varname -> varname
  let string_of = function INT varname -> sprintf "int %s;" varname
end

module rec Statement : sig
  type t =
    | IF of Formula.t * t * t
    | LOOP of t
    | ASSIGN of string * Term.t
    | NONDET_ASSIGN of string
    | UNREF_ASSIGN of string * Term.t
    | COMPOUND of t * t
    | NONDET of t * t
    | ASSUME of Formula.t
    | CALL_VOIDFUN of string * Term.t list
    | CALL_ASSIGN of string * string * Term.t list
    | VARDECL of string * Sort.t
    | LABEL of string
    | GOTO of string
    | RETURN_INT of Term.t
    | RETURN_NONDET
    | RETURN_VOID
    | BREAK
    | EXIT
    | NOP

  val is_if : t -> bool
  val is_loop : t -> bool
  val is_assign : t -> bool
  val is_nondet_assign : t -> bool
  val is_unref_assign : t -> bool
  val is_compound : t -> bool
  val is_nondet : t -> bool
  val is_assume : t -> bool
  val is_call_voidfun : t -> bool
  val is_call_assign : t -> bool
  val is_vardecl : t -> bool
  val is_label : t -> bool
  val is_goto : t -> bool
  val is_return_int : t -> bool
  val is_return_nondet : t -> bool
  val is_return_void : t -> bool
  val is_break : t -> bool
  val is_exit : t -> bool
  val is_nop : t -> bool
  val mk_if : Formula.t -> t -> t -> t
  val mk_loop : t -> t
  val mk_assign : string -> Term.t -> t
  val mk_nondet_assign : string -> t
  val mk_unref_assign : string -> Term.t -> t
  val mk_compound : t -> t -> t
  val mk_nondet : t -> t -> t
  val mk_assume : Formula.t -> t
  val mk_call_voidfun : string -> Term.t list -> t
  val mk_call_assign : string -> string -> Term.t list -> t
  val mk_vardecl : string -> Sort.t -> t
  val mk_label : string -> t
  val mk_goto : string -> t
  val mk_return_int : Term.t -> t
  val mk_return_nondet : unit -> t
  val mk_return_void : unit -> t
  val mk_break : unit -> t
  val mk_exit : unit -> t
  val mk_nop : unit -> t
  val let_if : t -> Formula.t * t * t
  val let_loop : t -> t
  val let_assign : t -> string * Term.t
  val let_nondet_assign : t -> string
  val let_unref_assign : t -> string * Term.t
  val let_compound : t -> t * t
  val let_nondet : t -> t * t
  val let_assume : t -> Formula.t
  val let_call_voidfun : t -> string * Term.t list
  val let_call_assign : t -> string * string * Term.t list
  val let_vardecl : t -> string * Sort.t
  val let_label : t -> string
  val let_goto : t -> string
  val let_return_int : t -> Term.t
  val varname_of_assign : t -> string
  val string_of : ?indent:int -> t -> string
  val subst : TermSubst.t -> t -> t
  val get_inner_statements : t -> t list
  val get_read_vars : t -> Variables.t

  (* val get_label_references: t -> (string, t) Hashtbl.t *)
  val get_all_labels : t -> string list
  val of_statements : t list -> t
end = struct
  type t =
    | IF of Formula.t * t * t
    | LOOP of t
    | ASSIGN of string * Term.t
    | NONDET_ASSIGN of string
    | UNREF_ASSIGN of string * Term.t
    | COMPOUND of t * t
    | NONDET of t * t
    | ASSUME of Formula.t
    | CALL_VOIDFUN of string * Term.t list
    | CALL_ASSIGN of string * string * Term.t list
    | VARDECL of string * Sort.t
    | LABEL of string
    | GOTO of string
    | RETURN_INT of Term.t
    | RETURN_NONDET
    | RETURN_VOID
    | BREAK
    | EXIT
    | NOP

  let is_if = function IF _ -> true | _ -> false
  let is_loop = function LOOP _ -> true | _ -> false
  let is_assign = function ASSIGN _ -> true | _ -> false
  let is_nondet_assign = function NONDET_ASSIGN _ -> true | _ -> false
  let is_unref_assign = function UNREF_ASSIGN _ -> true | _ -> false
  let is_compound = function COMPOUND _ -> true | _ -> false
  let is_nondet = function NONDET _ -> true | _ -> false
  let is_assume = function ASSUME _ -> true | _ -> false
  let is_call_voidfun = function CALL_VOIDFUN _ -> true | _ -> false
  let is_call_assign = function CALL_ASSIGN _ -> true | _ -> false
  let is_vardecl = function VARDECL _ -> true | _ -> false
  let is_label = function LABEL _ -> true | _ -> false
  let is_goto = function GOTO _ -> true | _ -> false
  let is_return_int = function RETURN_INT _ -> true | _ -> false
  let is_return_nondet = function RETURN_NONDET -> true | _ -> false
  let is_return_void = function RETURN_VOID -> true | _ -> false
  let is_break = function BREAK -> true | _ -> false
  let is_exit = function EXIT -> true | _ -> false
  let is_nop = function NOP -> true | _ -> false
  let mk_if cond_fml t_stmt f_stmt = IF (cond_fml, t_stmt, f_stmt)
  let mk_loop stmt = LOOP stmt
  let mk_assign varname term = ASSIGN (varname, term)
  let mk_nondet_assign varname = NONDET_ASSIGN varname
  let mk_unref_assign varname term = UNREF_ASSIGN (varname, term)
  let mk_compound stmt1 stmt2 = COMPOUND (stmt1, stmt2)
  let mk_nondet stmt1 stmt2 = NONDET (stmt1, stmt2)
  let mk_assume fml = ASSUME fml
  let mk_call_voidfun funname args = CALL_VOIDFUN (funname, args)
  let mk_call_assign varname funname args = CALL_ASSIGN (varname, funname, args)
  let mk_vardecl varname sort = VARDECL (varname, sort)
  let mk_label label_name = LABEL label_name
  let mk_goto label_name = GOTO label_name
  let mk_return_int term = RETURN_INT term
  let mk_return_nondet () = RETURN_NONDET
  let mk_return_void () = RETURN_VOID
  let mk_break () = BREAK
  let mk_exit () = EXIT
  let mk_nop () = NOP

  let let_if = function
    | IF (cond_fml, t_stmt, f_stmt) -> (cond_fml, t_stmt, f_stmt)
    | _ -> assert false

  let let_loop = function LOOP stmt -> stmt | _ -> assert false

  let let_assign = function
    | ASSIGN (varname, term) -> (varname, term)
    | _ -> assert false

  let let_nondet_assign = function
    | NONDET_ASSIGN varname -> varname
    | _ -> assert false

  let let_unref_assign = function
    | UNREF_ASSIGN (varname, term) -> (varname, term)
    | _ -> assert false

  let let_compound = function
    | COMPOUND (stmt1, stmt2) -> (stmt1, stmt2)
    | _ -> assert false

  let let_nondet = function
    | NONDET (stmt1, stmt2) -> (stmt1, stmt2)
    | _ -> assert false

  let let_assume = function ASSUME fml -> fml | _ -> assert false

  let let_call_voidfun = function
    | CALL_VOIDFUN (funname, args) -> (funname, args)
    | _ -> assert false

  let let_call_assign = function
    | CALL_ASSIGN (varname, funname, args) -> (varname, funname, args)
    | _ -> assert false

  let let_vardecl = function
    | VARDECL (varname, sort) -> (varname, sort)
    | _ -> assert false

  let let_label = function LABEL label_name -> label_name | _ -> assert false
  let let_goto = function GOTO label_name -> label_name | _ -> assert false
  let let_return_int = function RETURN_INT term -> term | _ -> assert false

  let varname_of_assign = function
    | ASSIGN (varname, _) | NONDET_ASSIGN varname -> varname
    | _ -> assert false

  let make_indent indent = String.make indent ' '
  let string_of_args = String.concat_map_list ~sep:", " ~f:Term.str_of

  let rec string_of ?(indent = 0) = function
    | IF (cond_fml, t_stmt, f_stmt) ->
        if is_nop f_stmt then
          sprintf "%sif (%s) {\n%s\n%s}" (make_indent indent)
            (Formula.str_of cond_fml)
            (string_of ~indent:(indent + 2) t_stmt)
            (make_indent indent)
        else
          sprintf "%sif (%s) {\n%s\n%s}\n%selse {\n%s\n%s}" (make_indent indent)
            (Formula.str_of cond_fml)
            (string_of ~indent:(indent + 2) t_stmt)
            (make_indent indent) (make_indent indent)
            (string_of ~indent:(indent + 2) f_stmt)
            (make_indent indent)
    | LOOP stmt ->
        sprintf "%swhile (1) {\n%s\n%s}" (make_indent indent)
          (string_of ~indent:(indent + 2) stmt)
          (make_indent indent)
    | ASSIGN (varname, term) ->
        sprintf "%s%s = %s;" (make_indent indent) varname (Term.str_of term)
    | NONDET_ASSIGN varname ->
        sprintf "%s%s = nondet();" (make_indent indent) varname
    | UNREF_ASSIGN (varname, term) ->
        sprintf "%s*%s = %s;" (make_indent indent) varname (Term.str_of term)
    | COMPOUND (stmt1, stmt2) ->
        sprintf "%s\n%s" (string_of ~indent stmt1) (string_of ~indent stmt2)
    | NONDET (stmt1, stmt2) ->
        sprintf "%snondet {\n%s\n%s}\n%selse {\n%s\n%s}" (make_indent indent)
          (string_of ~indent:(indent + 2) stmt1)
          (make_indent indent) (make_indent indent)
          (string_of ~indent:(indent + 2) stmt2)
          (make_indent indent)
    | ASSUME fml ->
        sprintf "%sassume(%s);" (make_indent indent) (Formula.str_of fml)
    | CALL_VOIDFUN (funname, args) ->
        sprintf "%s%s(%s);" (make_indent indent) funname (string_of_args args)
    | CALL_ASSIGN (varname, funname, args) ->
        sprintf "%s%s = %s(%s);" (make_indent indent) varname funname
          (string_of_args args)
    | VARDECL (varname, sort) ->
        sprintf "%s%s %s;" (make_indent indent) (Term.str_of_sort sort) varname
    | LABEL label_name -> sprintf "%s:" label_name
    | GOTO label_name -> sprintf "%sgoto %s;" (make_indent indent) label_name
    | BREAK -> sprintf "%sbreak;" (make_indent indent)
    | RETURN_INT term ->
        sprintf "%sreturn %s;" (make_indent indent) (Term.str_of term)
    | RETURN_VOID -> sprintf "%sreturn;" (make_indent indent)
    | RETURN_NONDET -> sprintf "%sreturn nondet();" (make_indent indent)
    | EXIT -> sprintf "%sexit 0;" (make_indent indent)
    | NOP -> sprintf "%snop;" (make_indent indent)

  let subst_args sub = List.map ~f:(Term.subst sub)

  let rec subst sub stmt =
    match stmt with
    | IF (cond_fml, t_stmt, f_stmt) ->
        let t_stmt = subst sub t_stmt in
        let f_stmt = subst sub f_stmt in
        mk_if (Formula.subst sub cond_fml) t_stmt f_stmt
    | LOOP stmt' ->
        let stmt' = subst sub stmt' in
        mk_loop stmt'
    | ASSIGN (varname, term) -> mk_assign varname (Term.subst sub term)
    | UNREF_ASSIGN (varname, term) ->
        mk_unref_assign varname (Term.subst sub term)
    | NONDET (stmt1, stmt2) ->
        let stmt1 = subst sub stmt1 in
        let stmt2 = subst sub stmt2 in
        mk_nondet stmt1 stmt2
    | COMPOUND (stmt1, stmt2) ->
        let stmt1 = subst sub stmt1 in
        let stmt2 = subst sub stmt2 in
        mk_compound stmt1 stmt2
    | ASSUME fml -> mk_assume (Formula.subst sub fml)
    | CALL_VOIDFUN (funname, args) ->
        mk_call_voidfun funname (subst_args sub args)
    | CALL_ASSIGN (varname, funname, args) ->
        mk_call_assign varname funname (subst_args sub args)
    | VARDECL _ -> assert false (* TODO *)
    | RETURN_INT term -> mk_return_int (Term.subst sub term)
    | LABEL _ | GOTO _ | RETURN_VOID | RETURN_NONDET | NONDET_ASSIGN _ | BREAK
    | EXIT | NOP ->
        stmt

  let get_inner_statements = function
    | IF (_, stmt1, stmt2) | NONDET (stmt1, stmt2) | COMPOUND (stmt1, stmt2) ->
        [ stmt1; stmt2 ]
    | LOOP stmt -> [ stmt ]
    | VARDECL _ | GOTO _ | RETURN_INT _ | RETURN_NONDET | RETURN_VOID | LABEL _
    | ASSIGN _ | UNREF_ASSIGN _ | ASSUME _ | CALL_VOIDFUN _ | CALL_ASSIGN _
    | NONDET_ASSIGN _ | BREAK | EXIT | NOP ->
        []

  let rec get_label_references_rep ?(nxt_stmt = Statement.mk_nop ())
      ?(res = Hashtbl.Poly.create ~size:10 ()) = function
    | IF (_, stmt1, stmt2) | NONDET (stmt1, stmt2) ->
        get_label_references_rep ~nxt_stmt ~res stmt1 |> ignore;
        get_label_references_rep ~nxt_stmt ~res stmt2 |> ignore;
        res
    | COMPOUND (stmt1, stmt2) ->
        get_label_references_rep ~nxt_stmt:stmt2 ~res stmt1 |> ignore;
        get_label_references_rep ~nxt_stmt ~res stmt2 |> ignore;
        res
    | LOOP stmt -> get_label_references_rep ~nxt_stmt:stmt ~res stmt
    | LABEL label_name ->
        Hashtbl.Poly.add_exn res ~key:label_name ~data:nxt_stmt;
        res
    | VARDECL _ | GOTO _ | RETURN_INT _ | RETURN_VOID | RETURN_NONDET | ASSIGN _
    | UNREF_ASSIGN _ | ASSUME _ | CALL_VOIDFUN _ | CALL_ASSIGN _
    | NONDET_ASSIGN _ | BREAK | EXIT | NOP ->
        res

  let get_label_references stmt = get_label_references_rep stmt

  let rec get_all_labels_rep res = function
    | LABEL label_name ->
        if Variables.is_mem res label_name then
          failwith @@ sprintf "there are labels with the same name"
        else Variables.add label_name res
    | stmt ->
        List.fold_left
          ~f:(fun res stmt' -> get_all_labels_rep res stmt')
          ~init:res
          (get_inner_statements stmt)

  let get_all_labels stmt =
    get_all_labels_rep Variables.empty stmt |> Variables.to_list

  let rec get_read_vars_rep label_refs used_labels = function
    | IF (cond_fml, t_stmt, f_stmt) ->
        let vars1, used_labels =
          get_read_vars_rep label_refs used_labels t_stmt
        in
        let vars2, used_labels =
          get_read_vars_rep label_refs used_labels f_stmt
        in
        ( Formula.tvs_of cond_fml |> Variables.of_tvarset
          |> Variables.union vars1 |> Variables.union vars2,
          used_labels )
    | LOOP stmt' -> get_read_vars_rep label_refs used_labels stmt'
    | ASSIGN (_, term) -> (Term.tvs_of term |> Variables.of_tvarset, used_labels)
    | UNREF_ASSIGN _ -> assert false
    | NONDET (stmt1, stmt2) | COMPOUND (stmt1, stmt2) ->
        let vars1, used_labels =
          get_read_vars_rep label_refs used_labels stmt1
        in
        let vars2, used_labels =
          get_read_vars_rep label_refs used_labels stmt2
        in
        (Variables.union vars1 vars2, used_labels)
    | ASSUME fml -> (Formula.tvs_of fml |> Variables.of_tvarset, used_labels)
    | CALL_VOIDFUN (_, args) | CALL_ASSIGN (_, _, args) ->
        ( List.fold_left ~init:Variables.empty args ~f:(fun vars arg ->
              Term.tvs_of arg |> Variables.of_tvarset |> Variables.union vars),
          used_labels )
    | VARDECL _ -> assert false (* TODO *)
    | GOTO label_name ->
        if Variables.is_mem used_labels label_name then
          (Variables.empty, used_labels)
        else
          Hashtbl.find_exn label_refs label_name
          |> get_read_vars_rep label_refs used_labels
    | RETURN_INT term -> (Term.tvs_of term |> Variables.of_tvarset, used_labels)
    | RETURN_VOID | RETURN_NONDET | LABEL _ | NONDET_ASSIGN _ | BREAK | EXIT
    | NOP ->
        (Variables.empty, used_labels)

  let get_read_vars stmt =
    let label_refs = get_label_references stmt in
    let vars, _ = get_read_vars_rep label_refs Variables.empty stmt in
    vars

  let rec of_statements = function
    | [] -> Statement.mk_nop ()
    | stmt :: [] -> stmt
    | stmt :: tail -> Statement.mk_compound stmt (of_statements tail)
end

module rec Init : sig
  type t =
    | ASSIGN of string * Term.t
    | ASSUME of Formula.t
    | NONDET_ASSIGN of string

  val is_assign : t -> bool
  val is_assume : t -> bool
  val is_nondet_assign : t -> bool
  val mk_assign : string -> Term.t -> t
  val mk_assume : Formula.t -> t
  val mk_nondet_assign : string -> t
  val let_assign : t -> string * Term.t
  val let_assume : t -> Formula.t
  val let_nondet_assign : t -> string
  val string_of : t -> string
  val update_state : State.t -> t -> State.t
  val update_formula_A : Formula.t -> t -> Formula.t
  val update_formula_E : Formula.t -> t -> Formula.t
  val subst : TermSubst.t -> t -> t
  val update_varname : string -> t -> t
  val of_stmt : t list -> Statement.t -> t list * Statement.t option
  val of_stmt_exn : t list -> Statement.t -> t list
end = struct
  type t =
    | ASSIGN of string * Term.t
    | ASSUME of Formula.t
    | NONDET_ASSIGN of string

  let is_assign = function ASSIGN _ -> true | _ -> false
  let is_assume = function ASSUME _ -> true | _ -> false
  let is_nondet_assign = function NONDET_ASSIGN _ -> true | _ -> false
  let mk_assign varname term = ASSIGN (varname, term)
  let mk_assume fml = ASSUME fml
  let mk_nondet_assign varname = NONDET_ASSIGN varname

  let let_assign = function
    | ASSIGN (varname, term) -> (varname, term)
    | _ -> assert false

  let let_assume = function ASSUME fml -> fml | _ -> assert false

  let let_nondet_assign = function
    | NONDET_ASSIGN varname -> varname
    | _ -> assert false

  let update_varname varname = function
    | ASSIGN (_, term) -> ASSIGN (varname, term)
    | NONDET_ASSIGN _ -> NONDET_ASSIGN varname
    | _ -> assert false

  let string_of = function
    | ASSIGN (varname, term) -> sprintf "%s = %s;" varname (Term.str_of term)
    | ASSUME fml -> sprintf "assume(%s);" (Formula.str_of fml)
    | NONDET_ASSIGN varname -> sprintf "%s = nondet();" varname

  let update_state state = function
    | ASSIGN (varname, term) -> State.update varname term state
    | ASSUME _ -> state
    | NONDET_ASSIGN varname ->
        let term = Term.mk_var (Ident.Tvar varname) T_int.SInt ~info:Dummy in
        State.update varname term state

  let update_formula_A fml = function
    | ASSIGN _ -> fml
    | NONDET_ASSIGN _ -> fml
    | ASSUME fml' -> Formula.mk_imply fml' fml

  let update_formula_E fml = function
    | ASSIGN _ -> fml
    | NONDET_ASSIGN _ -> fml
    | ASSUME fml' -> Formula.mk_and fml' fml ~info:Dummy

  let subst sub = function
    | ASSIGN (varname, term) -> mk_assign varname (Term.subst sub term)
    | ASSUME fml -> mk_assume (Formula.subst sub fml)
    | NONDET_ASSIGN varname -> mk_nondet_assign varname

  let is_already_assigned inits varname =
    List.exists inits ~f:(function
      | ASSIGN (varname', _) | NONDET_ASSIGN varname' ->
          String.equal varname' varname
      | ASSUME _ -> false)

  let rec of_stmt_rep stmt inits_rev =
    if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      let inits_rev, nxt_stmt = of_stmt_rep stmt1 inits_rev in
      match nxt_stmt with
      | None -> of_stmt_rep stmt2 inits_rev
      | Some nxt_stmt -> (inits_rev, Some (Statement.mk_compound nxt_stmt stmt2))
    else if Statement.is_assign stmt then
      let varname, term = Statement.let_assign stmt in
      if is_already_assigned inits_rev varname then (inits_rev, Some stmt)
      else (ASSIGN (varname, term) :: inits_rev, None)
    else if Statement.is_nondet_assign stmt then
      let varname = Statement.let_nondet_assign stmt in
      if is_already_assigned inits_rev varname then (inits_rev, Some stmt)
      else (NONDET_ASSIGN varname :: inits_rev, None)
    else if Statement.is_assume stmt then
      let fml = Statement.let_assume stmt in
      (ASSUME fml :: inits_rev, None)
    else (inits_rev, Some stmt)

  let of_stmt inits stmt =
    let inits_rev, stmt = of_stmt_rep stmt (List.rev inits) in
    (List.rev inits_rev, stmt)

  let of_stmt_exn inits stmt =
    let inits, stmt = of_stmt inits stmt in
    assert (Option.is_none stmt);
    inits
end

and State : sig
  type t = STATE of (string * Term.t ref) list

  val of_variables : Variables.t -> t
  val update : string -> Term.t -> t -> t
  val bounds_of : t -> sort_env_list
  val appformula_of : Ident.pvar -> t -> Formula.t
  val get : string -> t -> Term.t
  val mem : string -> t -> bool
  val of_inits : Init.t list -> t
end = struct
  type t = STATE of (string * Term.t ref) list

  let of_variables variables =
    let state =
      Variables.to_list variables
      |> List.map ~f:(fun varname ->
             (varname, ref (Term.mk_var (Ident.Tvar varname) T_int.SInt)))
    in
    STATE state

  (* let lookup varname = function STATE state ->
     (match List.assoc_opt varname state with
     | None -> raise (Error (sprintf "variable %s is not defined" varname))
     | Some term -> term) *)

  let update varname term = function
    | STATE state -> (
        try
          let r = List.Assoc.find_exn ~equal:String.equal state varname in
          r := term;
          STATE state
        with Not_found_s _ -> STATE state)

  let bounds_of = function
    | STATE state ->
        List.map ~f:(fun (varname, _) -> (Ident.Tvar varname, T_int.SInt)) state

  let appformula_of pvar = function
    | STATE state ->
        let sorts = List.map ~f:(fun _ -> T_int.SInt) state in
        let args = List.map ~f:(fun (_, term) -> !term) state in
        Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts args

  let get varname = function
    | STATE state -> !(List.Assoc.find_exn ~equal:String.equal state varname)

  let mem varname = function
    | STATE state ->
        List.exists
          ~f:(fun (varname', _) -> String.equal varname' varname)
          state

  let of_inits inits =
    List.fold_left ~f:Init.update_state ~init:(STATE []) inits
end

module FunDecl : sig
  type t =
    | FUN_NONDET of string * (string * Sort.t) list (* TODO *)
    | FUN_INT of string * (string * Sort.t) list * Statement.t
    | FUN_VOID of string * (string * Sort.t) list * Statement.t

  val is_fun_nondet : t -> bool
  val is_fun_int : t -> bool
  val is_fun_void : t -> bool
  val mk_fun_nondet : string -> (string * Sort.t) list -> t
  val mk_fun_int : string -> (string * Sort.t) list -> Statement.t -> t
  val mk_fun_void : string -> (string * Sort.t) list -> Statement.t -> t
  val let_fun_nondet : t -> string * (string * Sort.t) list
  val let_fun_int : t -> string * (string * Sort.t) list * Statement.t
  val let_fun_void : t -> string * (string * Sort.t) list * Statement.t
  val let_fun : t -> string * (string * Sort.t) list * Statement.t
  val get_funname : t -> string
  val get_params : t -> (string * Sort.t) list
  val find_fundecl : string -> t list -> t
  val is_non_recursive : t list -> t -> bool
  val string_of : t -> string
end = struct
  type t =
    | FUN_NONDET of string * (string * Sort.t) list
    | FUN_INT of string * (string * Sort.t) list * Statement.t
    | FUN_VOID of string * (string * Sort.t) list * Statement.t

  let is_fun_nondet = function FUN_NONDET _ -> true | _ -> false
  let is_fun_int = function FUN_INT _ -> true | _ -> false
  let is_fun_void = function FUN_VOID _ -> true | _ -> false
  let mk_fun_nondet funname params = FUN_NONDET (funname, params)
  let mk_fun_int funname params body = FUN_INT (funname, params, body)
  let mk_fun_void funname params body = FUN_VOID (funname, params, body)

  let let_fun_nondet = function
    | FUN_NONDET (funname, params) -> (funname, params)
    | _ -> assert false

  let let_fun_int = function
    | FUN_INT (funname, params, body) -> (funname, params, body)
    | _ -> assert false

  let let_fun_void = function
    | FUN_VOID (funname, params, body) -> (funname, params, body)
    | _ -> assert false

  let let_fun = function
    | FUN_INT (funname, params, body) | FUN_VOID (funname, params, body) ->
        (funname, params, body)
    | _ -> assert false

  let get_funbody = function
    | FUN_INT (_, _, body) | FUN_VOID (_, _, body) -> body
    | FUN_NONDET _ -> Statement.mk_return_nondet ()

  let get_funname = function
    | FUN_INT (funname, _, _)
    | FUN_NONDET (funname, _)
    | FUN_VOID (funname, _, _) ->
        funname

  let get_params = function
    | FUN_INT (_, params, _) | FUN_NONDET (_, params) | FUN_VOID (_, params, _)
      ->
        params

  let find_fundecl funname fundecls =
    match
      List.find
        ~f:(fun fundecl -> String.equal (get_funname fundecl) funname)
        fundecls
    with
    | Some fundecl -> fundecl
    | None ->
        failwith @@ sprintf "function %s was not declared in this scope" funname

  let rec get_next_funnames_rep stmt res =
    if Statement.is_call_assign stmt then
      let _, funname, _ = Statement.let_call_assign stmt in
      Variables.add funname res
    else if Statement.is_call_voidfun stmt then
      let funname, _ = Statement.let_call_voidfun stmt in
      Variables.add funname res
    else
      Statement.get_inner_statements stmt
      |> List.fold_left
           ~f:(fun res stmt' -> get_next_funnames_rep stmt' res)
           ~init:res

  let get_next_funnames fundecl =
    let body = get_funbody fundecl in
    get_next_funnames_rep body Variables.empty |> Variables.to_list

  let rec is_non_recursive_rep fundecls fundecl ancestors used =
    get_next_funnames fundecl
    |> List.fold_left
         ~f:(fun (res, used) funname' ->
           let fundecl' = find_fundecl funname' fundecls in
           if not res then (false, used)
           else if Variables.is_mem ancestors funname' then (true, used)
           else if Variables.is_mem used funname' then (true, used)
           else
             is_non_recursive_rep fundecls fundecl'
               (Variables.add funname' ancestors)
               (Variables.add funname' used))
         ~init:(true, used)

  let is_non_recursive fundecls fundecl =
    let funname = get_funname fundecl in
    let res, _ =
      is_non_recursive_rep fundecls fundecl
        (Variables.of_varname funname)
        (Variables.of_varname funname)
    in
    res

  let string_of_args =
    String.concat_map_list ~sep:", " ~f:(fun (varname, sort) ->
        sprintf "%s %s" (Term.str_of_sort sort) varname)

  let string_of = function
    | FUN_NONDET (funname, args) ->
        sprintf "int %s(%s) { return nondet(); }" funname (string_of_args args)
    | FUN_VOID (funname, args, stmt) ->
        sprintf "void %s(%s) {\n%s\n}" funname (string_of_args args)
          (Statement.string_of stmt)
    | FUN_INT (funname, args, stmt) ->
        sprintf "int %s(%s) {\n%s\n}" funname (string_of_args args)
          (Statement.string_of stmt)
end

type cctl = Ctl.t * Declare.t list * Init.t list * Statement.t
type cltl = Ltl.t * Declare.t list * Init.t list * Statement.t
type chmes = HMES.t * Declare.t list * Init.t list * Statement.t
