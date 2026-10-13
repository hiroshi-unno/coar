open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* ToDo *)
module Debug = Debug.Make ((val Debug.Config.disable))

type query = Formula.t
type t = { preds : Pred.t list; query : query }

(* the shared verdict, kept spellable here because callers have said
   [MuCLP.Problem.Valid] for years; the type equation makes the two the same
   type, so both spellings are interchangeable *)
type solution = Common.Verdict.t = Valid | Invalid | Unknown | Timeout

let make preds query = { preds; query }
let flip_solution = Common.Verdict.flip
let str_of_solution = Common.Verdict.str_of
let lts_str_of_solution = Common.Verdict.lts_str_of

let str_of muclp =
  sprintf "%s\ns.t.\n%s"
    (Formula.str_of muclp.query)
    (Pred.str_of_list muclp.preds)

let has_only_mu muclp =
  List.for_all ~f:(fun pred -> Stdlib.( = ) pred.kind Predicate.Mu) muclp.preds

let has_only_nu muclp =
  List.for_all ~f:(fun pred -> Stdlib.( = ) pred.kind Predicate.Nu) muclp.preds

let has_only_exists muclp =
  let rec check fml =
    if Formula.is_atom fml then true
    else if Formula.is_and fml || Formula.is_or fml then
      let _, fml_left, fml_right, _ = Formula.let_binop fml in
      check fml_left && check fml_right
    else if Formula.is_forall fml then false
    else if Formula.is_exists fml then check @@ snd3 @@ Formula.let_exists fml
    else failwith "not implemented"
    (*Debug.print @@ lazy (sprintf "not implemented for: %s" @@ Formula.str_of fml)*)
  in
  List.for_all
    ~f:(Evaluator.simplify >> check)
    (muclp.query :: List.map muclp.preds ~f:(fun pred -> pred.body))

let has_only_forall muclp =
  let rec check fml =
    if Formula.is_atom fml then true
    else if Formula.is_and fml || Formula.is_or fml then
      let _, fml_left, fml_right, _ = Formula.let_binop fml in
      check fml_left && check fml_right
    else if Formula.is_forall fml then check @@ snd3 @@ Formula.let_forall fml
    else if Formula.is_exists fml then false
    else failwith "not implemented"
  in
  List.for_all ~f:check
    (muclp.query :: List.map muclp.preds ~f:(fun pred -> pred.body))

let has_no_quantifier muclp = has_only_exists muclp && has_only_forall muclp

(* [elim_neg muclp] removes [=>], [<=>], xor and negation from the query and
   the bodies: the formulas are put in negation normal form and a negated
   predicate application [not (P ts)] becomes [P_neg ts], where [P_neg] is the
   dual of [P] (fixpoint operator flipped, body complemented), inserted right
   after [P].  Every backend assumes the atom / and / or / forall / exists
   fragment — [has_only_forall] fails on anything else, MuCyc and MuStrat
   mis-read [not]/[=>] — so this runs once, at parse time.  A problem without
   such constructs is returned
   unchanged. *)
let elim_neg muclp =
  let rec needs = function
    | Formula.Atom (_, _) -> false
    | Formula.UnaryOp (Formula.Not, Formula.Atom (atom, _), _) ->
        Atom.is_pvar_app atom
    | Formula.UnaryOp (Formula.Not, _, _) -> true
    | Formula.BinaryOp ((Formula.Imply | Formula.Iff | Formula.Xor), _, _, _) ->
        true
    | Formula.BinaryOp (_, phi1, phi2, _) -> needs phi1 || needs phi2
    | Formula.Bind (_, _, phi, _) -> needs phi
    | Formula.LetFormula (_, _, _, body, _) -> needs body
    | _ -> false
  in
  let formulas = muclp.query :: List.map muclp.preds ~f:(fun p -> p.body) in
  if not (List.exists formulas ~f:needs) then muclp
  else
    let pvars = Set.Poly.of_list @@ List.map muclp.preds ~f:(fun p -> p.name) in
    let dual_name (Ident.Pvar n) = Ident.Pvar (n ^ "_neg") in
    let rec elim_iff = function
      | Formula.BinaryOp (Formula.Iff, phi1, phi2, info) ->
          let phi1 = elim_iff phi1 and phi2 = elim_iff phi2 in
          Formula.mk_and ~info
            (Formula.mk_imply phi1 phi2)
            (Formula.mk_imply phi2 phi1)
      | Formula.BinaryOp (Formula.Xor, phi1, phi2, info) ->
          let phi1 = elim_iff phi1 and phi2 = elim_iff phi2 in
          Formula.mk_or ~info
            (Formula.mk_and phi1 (Formula.mk_neg phi2))
            (Formula.mk_and (Formula.mk_neg phi1) phi2)
      | Formula.BinaryOp (op, phi1, phi2, info) ->
          Formula.mk_binop ~info op (elim_iff phi1) (elim_iff phi2)
      | Formula.UnaryOp (op, phi, info) ->
          Formula.mk_unop ~info op (elim_iff phi)
      | Formula.Bind (b, bounds, phi, info) ->
          Formula.mk_bind ~info b bounds (elim_iff phi)
      | Formula.LetFormula (v, s, def, body, info) ->
          Formula.mk_let_formula ~info v s def (elim_iff body)
      | phi -> phi
    in
    (* negation normal form with [not (P ts)] turned into the dual atom;
       returns the set of predicates whose dual was used *)
    let rec dualize used = function
      | Formula.UnaryOp
          ( Formula.Not,
            Formula.Atom (Atom.App (Predicate.Var (pvar, sorts), ts, info), _),
            _ )
        when Set.mem pvars pvar ->
          ( Formula.mk_atom
              (Atom.mk_app ~info (Predicate.Var (dual_name pvar, sorts)) ts),
            Set.add used pvar )
      | Formula.BinaryOp (op, phi1, phi2, info) ->
          let phi1, used = dualize used phi1 in
          let phi2, used = dualize used phi2 in
          (Formula.mk_binop ~info op phi1 phi2, used)
      | Formula.Bind (b, bounds, phi, info) ->
          let phi, used = dualize used phi in
          (Formula.mk_bind ~info b bounds phi, used)
      | Formula.LetFormula (v, s, def, body, info) ->
          let body, used = dualize used body in
          (Formula.mk_let_formula ~info v s def body, used)
      | phi -> (phi, used)
    in
    let normalize used phi = dualize used @@ Formula.nnf_of @@ elim_iff phi in
    let query, used = normalize Set.Poly.empty muclp.query in
    let used, preds =
      List.fold_map muclp.preds ~init:used ~f:(fun used pred ->
          let body, used = normalize used pred.body in
          (used, { pred with body }))
    in
    (* duals of the predicates reached through negation, transitively: the
       body of a dual is the complement of the original body and may itself
       negate other predicates *)
    let dual_of (pred : Pred.t) used =
      let body, used = normalize used (Formula.mk_neg pred.body) in
      ( {
          pred with
          kind = Predicate.flip_fop pred.kind;
          name = dual_name pred.name;
          body;
        },
        used )
    in
    let rec close duals used =
      let missing = Set.diff used (Map.key_set duals) in
      if Set.is_empty missing then duals
      else
        let duals, used =
          Set.fold missing ~init:(duals, used) ~f:(fun (duals, used) pvar ->
              let pred =
                List.find_exn muclp.preds ~f:(fun p -> Stdlib.(p.name = pvar))
              in
              let dual, used = dual_of pred used in
              (Map.Poly.add_exn duals ~key:pvar ~data:dual, used))
        in
        close duals used
    in
    let duals = close Map.Poly.empty used in
    let preds =
      List.concat_map preds ~f:(fun pred ->
          match Map.Poly.find duals pred.name with
          | Some dual -> [ pred; dual ]
          | None -> [ pred ])
    in
    make preds query

let map_formula f muclp = make (Pred.map_list f muclp.preds) (f muclp.query)
let size_of muclp = List.length muclp.preds

let penv_of ?(init = Map.Poly.empty) muclp =
  Pred.pred_sort_env_map_of_list init muclp.preds

let get_depth_ht muclp =
  let res = Hashtbl.Poly.create ~size:(List.length muclp.preds) () in
  List.iteri muclp.preds ~f:(fun i pred ->
      Hashtbl.Poly.add_exn res ~key:pred.name ~data:i);
  res

let avoid_dup pvar pvars =
  if not @@ List.exists pvars ~f:(Ident.pvar_equal pvar) then pvar
  else
    let suffix = ref 2 in
    while
      List.exists pvars ~f:(fun pvar' ->
          Ident.pvar_equal pvar'
            (Ident.Pvar (Ident.name_of_pvar pvar ^ string_of_int !suffix)))
    do
      suffix := !suffix + 1
    done;
    Ident.Pvar (Ident.name_of_pvar pvar ^ string_of_int !suffix)

let aconv_tvar muclp =
  make
    (List.map muclp.preds ~f:(fun pred ->
         let map, args =
           List.unzip
           @@ List.map pred.args ~f:(fun (x, sort) ->
               let x' = Ident.mk_fresh_tvar () in
               ((x, Term.mk_var x' sort), (x', sort)))
         in
         {
           pred with
           args;
           body =
             Formula.(subst (Map.Poly.of_alist_exn map) @@ aconv_tvar pred.body);
         }))
    (Formula.aconv_tvar muclp.query)

(* [rename_binders_apart muclp] gives every binder of the query and of every
   body a name of its own: a quantified variable [x] becomes [x_k], [k] drawn
   from one counter for the whole problem, and any other binder (a [let], a
   recursive definition's argument, a binder inside a term) becomes [b_k].

   Contract.  Pre: none.  Post: the result is alpha-equivalent to [muclp]
   (predicate names, argument lists and free variables are kept; only
   binders are renamed, bottom-up, each body renaming going through
   [Formula.rename], which is safe because a new name is spelled nowhere in
   the problem and inner binders are already renamed when an outer one is);
   no two binders of the result share a name; and the result is a function of
   [muclp] alone (no global fresh-name counter is read), so two runs name
   alike.

   Why.  A reduction that names something after a bound variable, and
   disambiguates repeats by traversal order, assigns different names to the
   same block on two problems derived from one input when the derivation
   reorders operands -- negation-normalising simplification sorts the
   operands of [and]/[or] by a guard literal whose sign the negation flips.
   With the binders apart before either problem is derived, a block keeps
   its variables' names through such a derivation, and a name built from them
   denotes the same block on both problems. *)
let rename_binders_apart muclp =
  let taken =
    Hash_set.Poly.of_list
    @@ List.concat_map (muclp.query :: List.map muclp.preds ~f:(fun pred -> pred.Pred.body))
         ~f:(Formula.names_spelled_in >> Set.to_list)
    @ List.concat_map muclp.preds ~f:(fun pred -> List.map ~f:fst pred.args)
  in
  let counter = ref 0 in
  let fresh base =
    let rec draw () =
      incr counter;
      let x = Ident.Tvar (base ^ "_" ^ string_of_int !counter) in
      if Hash_set.mem taken x then draw ()
      else (
        Hash_set.add taken x;
        x)
    in
    draw ()
  in
  let next () = fresh "b" in
  let refresh senv =
    let senv' =
      List.map senv ~f:(fun (x, s) -> (fresh (Ident.name_of_tvar x), s))
    in
    (senv', ren_of_sort_env_list senv senv')
  in
  let apart =
    Formula.fold
      ~f:
        (object
           method fatom atom = Formula.mk_atom (Atom.aconv_tvar_norm next atom)
           method fnot phi1 = Formula.mk_neg phi1
           method fand phi1 phi2 = Formula.mk_and phi1 phi2
           method for_ phi1 phi2 = Formula.mk_or phi1 phi2
           method fimply phi1 phi2 = Formula.mk_imply phi1 phi2
           method fiff phi1 phi2 = Formula.mk_iff phi1 phi2
           method fxor phi1 phi2 = Formula.mk_xor phi1 phi2

           method fbind binder senv phi1 =
             let senv', map = refresh senv in
             Formula.mk_bind binder senv' (Formula.rename map phi1)

           method fletrec funcs phi1 =
             let funcs' =
               List.map funcs ~f:(fun def ->
                   let args, ren = refresh def.Formula.args in
                   { def with args; body = Formula.rename ren def.body })
             in
             Formula.mk_letrec funcs' phi1

           method flet x sort def body =
             let def = Term.aconv_tvar_norm next def in
             let x' = fresh (Ident.name_of_tvar x) in
             Formula.mk_let_formula x' sort def
               (Formula.rename (Map.Poly.singleton x x') body)
        end)
  in
  make
    (List.map muclp.preds ~f:(fun pred -> { pred with body = apart pred.body }))
    (apart muclp.query)

let move_quantifiers_to_front = map_formula Formula.move_quantifiers_to_front
let rm_forall = map_formula (Formula.rm_quant ~forall:true >> snd)
let simplify = map_formula Evaluator.simplify
let complete_tsort = map_formula (Formula.complete_tsort Map.Poly.empty)

(* TODO : this should be applied to hes Parser *)
let complete_psort uninterp_pvs muclp =
  let map = penv_of ~init:uninterp_pvs muclp in
  map_formula (Formula.complete_psort map) muclp

let bind_fvs_with_forall muclp =
  make muclp.preds @@ Formula.bind_fvs_with_forall muclp.query

let detect_arity0_preds muclp =
  if List.exists ~f:(fun pred -> List.length pred.args = 0) muclp.preds then
    failwith "arity0 predicates is not supported."
  else make muclp.preds muclp.query

let detect_undefined_preds muclp =
  let check map formula =
    let fpv = LogicOld.Formula.pvs_of formula in
    if false then
      Debug.print
      @@ lazy
           (sprintf "fpvs: %s"
           @@ String.concat_map_set ~sep:"," fpv ~f:Ident.name_of_pvar);
    match Set.find ~f:(Map.Poly.mem map >> not) fpv with
    | Some (Ident.Pvar pid) -> failwith @@ "undefined predicates: " ^ pid
    | None -> ()
  in
  let rec mk_env map = function
    | [] -> map
    | pred :: xs ->
        mk_env (Map.Poly.add_exn map ~key:pred.Pred.name ~data:pred.name) xs
  in
  let map = mk_env Map.Poly.empty muclp.preds in
  check map muclp.query;
  List.iter muclp.preds ~f:(fun pred -> check map pred.body);
  muclp

(* What a muCLP solver validates about its input when its config asks for it
   ([check_problem], set in every dbg_ config).  Only the undefined-predicate
   check runs: a predicate applied in the query or in a body with no definition
   in [preds] used to reach the reducer, which looks its arity up with
   [Hashtbl.find_exn] and died with [Not_found_s "Hashtbl.find_exn: not found"]
   -- an internal error that says nothing about the input being at fault.
   [detect_arity0_preds] stays off: the parser rejects a nullary predicate
   *application* before it can be reached (the atom rule requires at least one
   argument, so `A` alone in a query is a syntax error), which makes its
   message unreachable rather than wrong. *)
let check_problem muclp =
  muclp
  |> (if false then detect_arity0_preds else Fn.id)
  |> detect_undefined_preds
