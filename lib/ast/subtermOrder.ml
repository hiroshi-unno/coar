(* The proper-subterm order on the values of inductive datatypes, as the
   decreasing relation of a structural recursion.

   In every model of the SMT-LIB theory an inductive datatype is interpreted
   as its algebra of finite constructor terms, so the proper-subterm relation
   on its values is well-founded (each step lowers the height of a finite
   tree).  A term [sel_1(.. sel_k(x) ..)] denotes a proper subterm of the value
   of [x] only where each selector is applied to a value built by its own
   constructor: a selector applied to another constructor ([tl nil]) denotes a
   value the theory leaves open, which may be [x] itself or larger.  So a
   decrease is stated together with the testers of every selector of the
   chain, and the caller asks whether its path condition implies them.

   The finiteness argument needs every datatype a value can contain to be
   inductive: a codatatype admits cyclic values ([x = cons(a, x)]), on which a
   selector chain can return to its start. *)

open Core
open Common.Ext
open LogicOld

(* [sort] is a datatype every datatype reachable from which (itself
   included) is inductive; its values are then finite trees. *)
let inductive_closure_sort = function
  | T_dt.SDT dt ->
      Datatype.is_dt dt
      && Set.for_all (fst (Datatype.used_dt_and_sorts_of dt)) ~f:Datatype.is_dt
  | _ -> false

let is_var_named x = function
  | Term.Var (y, _, _) -> Ident.tvar_equal x y
  | _ -> false

(* [c(sel_1(T), .., sel_n(T))] with the selectors of [c] in order, rewritten
   to [T], bottom-up.  Equal to its input wherever the testers of the
   selectors it removes hold. *)
let rec eta t =
  match t with
  | Term.FunApp ((T_dt.DTCons (cname, _, dt) as sym), args, info) -> (
      let args = List.map args ~f:eta in
      let rebuilt () = Term.mk_fsym_app ~info sym args in
      match Datatype.look_up_cons dt cname with
      | None -> rebuilt ()
      | Some cons -> (
          let sels = Datatype.sels_of_cons cons in
          if List.is_empty sels || List.length sels <> List.length args then
            rebuilt ()
          else
            let inner =
              List.map2_exn sels args ~f:(fun sel a ->
                  match a with
                  | Term.FunApp (T_dt.DTSel (sname, _, _), [ t' ], _)
                    when String.equal sname (Datatype.name_of_sel sel) ->
                      Some t'
                  | _ -> None)
            in
            match inner with
            | Some t0 :: rest
              when List.for_all rest ~f:(function
                     | Some t' -> Stdlib.( = ) t' t0
                     | None -> false) ->
                t0
            | _ -> rebuilt ()))
  | Term.FunApp (sym, args, info) ->
      Term.mk_fsym_app ~info sym (List.map args ~f:eta)
  | _ -> t

(* When [t] is a chain of selectors of inductive datatypes over the variable
   [x], of depth at least one, the testers that make each selector applied to
   its own constructor; [None] otherwise (a chain through a codatatype's
   selector included). *)
let selector_chain_testers x t =
  let rec go acc = function
    | Term.FunApp (T_dt.DTSel (sname, dt, _), [ inner ], _) -> (
        if not (Datatype.is_dt dt) then None
        else
          match Datatype.look_up_cons_of_sel dt sname with
          | None -> None
          | Some cons ->
              let tester =
                Formula.mk_atom
                @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons) inner
              in
              go (tester :: acc) inner)
    | t when is_var_named x t -> if List.is_empty acc then None else Some acc
    | _ -> None
  in
  go [] t

(* A formula that, where it holds, makes the value of [a] a proper subterm of
   the value of [x]: the testers of a selector chain over [x] that [a] equals
   after the eta rule, and that equality.  [false] when [a] is no such chain.
   Contract: the decrease is sound only when [x]'s sort satisfies
   [inductive_closure_sort]; the caller checks that. *)
let strict_decrease x a =
  let a' = eta a in
  match selector_chain_testers x a' with
  | Some testers -> Formula.and_of (testers @ [ Formula.eq a a' ])
  | None -> Formula.mk_false ()
