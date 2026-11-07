(* Guards ([p when g -> e]) of value cases, read as nested matches.

   The constraint generation reads a match case by its pattern alone, so a
   guard reaching it would be dropped and its case read as taken whenever the
   pattern matches: [match x with n when n > 0 -> 1 | _ -> 0] was read as
   always answering 1.  [desugar] rewrites, before the OCaml type checker
   runs, every [match] and [function] whose value cases carry a guard into
   guard-free matches with the same evaluation:

     match e with pre | p when g -> r | post
   becomes
     let s = e in
     let k () = <match s with post, rewritten again> in
     match s with pre | p -> (if g then r else k ()) | _ -> k ()

   where [pre] has no guard and [s], [k] are fresh names.  [k]'s body is
   outside the scope of [p]'s variables, so they cannot capture a name of
   [post]; [g] and [r] stay in [p]'s scope as before.  When [post] is empty,
   falling through the last guard is OCaml's [Match_failure], read as
   [assert false], a failure.  The scrutinee is evaluated once, before any
   case, as in OCaml.

   Left unchanged, for the constraint generation to refuse: a match with an
   exception or effect case (the rewrite above would move the exception
   cases' scope), and a [function] with a result type constraint.

   Assumes: no name of the form [__rcaml_guard_*] occurs in the program.
   Guarantees: the result has no guard on a value case of a [match] or
   [function] other than those left unchanged above; a structure with no guard
   is returned physically unchanged. *)

open Parsetree

let counter = ref 0

let fresh prefix =
  incr counter;
  Printf.sprintf "__rcaml_guard_%s%d" prefix !counter

let lid ~loc name = Location.mkloc (Longident.Lident name) loc
let evar ~loc name = Ast_helper.Exp.ident ~loc (lid ~loc name)
let pvar ~loc name = Ast_helper.Pat.var ~loc (Location.mkloc name loc)
let has_guard cases = List.exists (fun c -> Option.is_some c.pc_guard) cases

let is_value_case c =
  match c.pc_lhs.ppat_desc with
  | Ppat_exception _ | Ppat_effect _ -> false
  | _ -> true

let rewritable cases = has_guard cases && List.for_all is_value_case cases

let fun_of ~loc pat body =
  Ast_helper.Exp.function_ ~loc
    [ { pparam_loc = loc; pparam_desc = Pparam_val (Nolabel, None, pat) } ]
    None (Pfunction_body body)

(* the generated matches are partial ([post]) or end in a redundant [_]
   (after an irrefutable [p]) by construction: silence OCaml's warnings 8 and
   11 about them *)
let quiet =
  Ast_helper.Attr.mk (Location.mknoloc "warning")
    (PStr
       [
         Ast_helper.Str.eval
           (Ast_helper.Exp.constant (Ast_helper.Const.string "-8-11"));
       ])

(* the cases [cases] matched against the variable [s] *)
let rec match_on ~loc s cases =
  let rec split pre = function
    | [] -> None
    | c :: rest when Option.is_some c.pc_guard -> Some (List.rev pre, c, rest)
    | c :: rest -> split (c :: pre) rest
  in
  match split [] cases with
  | None -> Ast_helper.Exp.match_ ~loc ~attrs:[ quiet ] (evar ~loc s) cases
  | Some (pre, c, post) ->
      let guard = Option.get c.pc_guard in
      let k = fresh "rest" in
      let unit_e = Ast_helper.Exp.construct ~loc (lid ~loc "()") None in
      let unit_p = Ast_helper.Pat.construct ~loc (lid ~loc "()") None in
      let call_k = Ast_helper.Exp.apply ~loc (evar ~loc k) [ (Nolabel, unit_e) ] in
      let rest =
        if post = [] then
          Ast_helper.Exp.assert_ ~loc
            (Ast_helper.Exp.construct ~loc (lid ~loc "false") None)
        else match_on ~loc s post
      in
      Ast_helper.Exp.let_ ~loc Nonrecursive
        [ Ast_helper.Vb.mk ~loc (pvar ~loc k) (fun_of ~loc unit_p rest) ]
        (Ast_helper.Exp.match_ ~loc ~attrs:[ quiet ] (evar ~loc s)
           (pre
           @ [
               Ast_helper.Exp.case c.pc_lhs
                 (Ast_helper.Exp.ifthenelse ~loc guard c.pc_rhs (Some call_k));
               Ast_helper.Exp.case (Ast_helper.Pat.any ~loc ()) call_k;
             ]))

let mapper =
  let open Ast_mapper in
  {
    default_mapper with
    expr =
      (fun m e ->
        let e = default_mapper.expr m e in
        let loc = e.pexp_loc in
        match e.pexp_desc with
        | Pexp_match (scrut, cases) when rewritable cases ->
            let s = fresh "scrut" in
            {
              (Ast_helper.Exp.let_ ~loc Nonrecursive
                 [ Ast_helper.Vb.mk ~loc (pvar ~loc s) scrut ]
                 (match_on ~loc s cases))
              with
              pexp_attributes = e.pexp_attributes;
            }
        | Pexp_function (params, None, Pfunction_cases (cases, cloc, _))
          when rewritable cases ->
            let s = fresh "scrut" in
            {
              e with
              pexp_desc =
                Pexp_function
                  ( params
                    @ [
                        {
                          pparam_loc = cloc;
                          pparam_desc =
                            Pparam_val (Nolabel, None, pvar ~loc:cloc s);
                        };
                      ],
                    None,
                    Pfunction_body (match_on ~loc:cloc s cases) );
            }
        | _ -> e);
  }

let desugar (str : structure) =
  let found = ref false in
  let finder =
    let open Ast_mapper in
    {
      default_mapper with
      case =
        (fun m c ->
          if Option.is_some c.pc_guard then found := true;
          default_mapper.case m c);
    }
  in
  ignore (finder.structure finder str);
  if not !found then str else mapper.Ast_mapper.structure mapper str
