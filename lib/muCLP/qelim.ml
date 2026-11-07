open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld

type mode =
  | Mu
  | Mu'
  | Mus
  | Nu (* sound but incomplete *) of int (* range *)
  | SkolemFun
  | SkolemPred
[@@deriving yojson]

(* Which existential occurrences of one formula share their Skolem witness
   predicates under [SkolemPred].  [No_witness_sharing]: one set of [FN]
   predicates per occurrence.  [Same_body]: occurrences under the same
   enclosing binders whose bodies are equal after their bound variables are
   renamed positionally share one set: a witness function for one is one for
   the other.  [Same_body_or_disjunct]: also occurrences under the same
   enclosing binders whose nearest common ancestor in the formula is a
   disjunction: at each valuation of the enclosing binders a minimal
   certificate of the formula's truth passes through at most one of them, so
   one function can take that one's witness.  [Same_choice_or_disjunct]: as
   [Same_body_or_disjunct], restricted to occurrences that bind the same
   variable names (the copies one choice gets when a body is copied onto
   several paths; a trailing [_<digits>] of a copy's renaming is ignored), so
   that two different choices of one sort keep separate witnesses.  Every
   rule preserves satisfiability; the classes are formed greedily, an
   occurrence joining the first class every member of which it may share
   with. *)
type witness_sharing =
  | No_witness_sharing
  | Same_body
  | Same_body_or_disjunct
  | Same_choice_or_disjunct
[@@deriving yojson]

module Config = struct
  type t = {
    elimination : mode; [@default SkolemPred]
        (** how an existential quantifier is eliminated *)
    share_witnesses : witness_sharing; [@default No_witness_sharing]
        (** read only under [SkolemPred]; off by default *)
    verbose : bool; [@default false]
  }
  [@@deriving yojson]

  let instantiate_ext_files cfg = Ok cfg

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Qelim"
    let instantiate = instantiate_ext_files
  end)

  module type ConfigType = sig
    val config : t
  end
end

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (* A scalar Bool may be represented by a nullary predicate occurrence.
     Positive-arity predicate heads are independent relations. Signature
     traversal masks local binders before these names are intersected with
     the candidate scalar bounds. *)
  let scalar_dependencies body =
    Set.union (Formula.tvs_of body)
      (Set.Poly.of_list
         (Set.to_list (Formula.predicate_signatures_of_term
                        (Term.mk_fsym_app (T_bool.Formula body) []))
          |> List.filter_map ~f:(fun (pvar, args) ->
                 if List.is_empty args then Some (Ident.pvar_to_tvar pvar)
                 else None)))

  (* Deterministic local names must also be fresh to the surrounding scalar
     parameters and every spelled body symbol, including Boolean aliases. *)
  let name_allocator body reserved =
    let taken = ref (Set.union (Formula.names_spelled_in body)
                       (Set.Poly.of_list reserved)) in
    fun base ->
      let rec pick suffix =
        let name = Ident.Tvar (if suffix = 0 then base
                              else base ^ "_" ^ Int.to_string suffix) in
        if Set.mem !taken name then pick (suffix + 1)
        else (taken := Set.add !taken name; name)
      in
      pick 0

  let add_prefix_to_tvars_reserved ~reserved prefix bounds fml =
    let fresh = name_allocator fml (reserved @ List.map bounds ~f:fst) in
    let subst, bounds_rev =
      List.fold ~init:(Map.Poly.empty, []) bounds
        ~f:(fun (subst, bounds_rev) (tvar, sort) ->
          let new_tvar = fresh (prefix ^ Ident.name_of_tvar tvar) in
          ( Map.Poly.add_exn subst ~key:tvar ~data:(Term.mk_var new_tvar sort),
            (new_tvar, sort) :: bounds_rev ))
    in
    (List.rev bounds_rev, Formula.subst subst fml)

  let add_prefix_to_tvars prefix bounds fml =
    add_prefix_to_tvars_reserved ~reserved:[] prefix bounds fml

  let mk_app pvar bounds0 bounds ?replacer () =
    Formula.mk_atom
    @@ Atom.mk_pvar_app pvar (List.map ~f:snd @@ bounds0 @ bounds)
    @@ Term.of_sort_env bounds0
    @ List.map bounds ~f:(fun (tvar, sort) ->
        Term.mk_var tvar sort
        |> match replacer with Some replacer -> replacer tvar | None -> Fn.id)

  let mk_replacer tvar op tvar' term_var =
    if Stdlib.(tvar' = tvar) then op term_var (T_int.one ()) else term_var

  let encode_exists_mu prefix bound_tvars bound_pvars unknowns exists_formula =
    (* avoid dup *)
    let pvar =
      Problem.avoid_dup (Ident.Pvar prefix)
        (bound_pvars @ Set.to_list @@ Kind.pvars_of unknowns)
    in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bound_tvars =
      let fv = scalar_dependencies body in
      List.filter bound_tvars ~f:(fst >> Set.mem fv)
    in
    let bounds, body = add_prefix_to_tvars_reserved ~reserved:(List.map bound_tvars ~f:fst) "#exists_" bounds body in
    (* Exists(x,y) =mu F(x,y) \/ Exists(x+1,y) \/ Exists(x-1,y) \/ Exists(x,y+1) \/ Exists(x,y-1) *)
    ( [
        Pred.make Predicate.Mu pvar (bound_tvars @ bounds)
        @@ Formula.or_of
        @@ body
           :: List.fold ~init:[] bounds ~f:(fun res (tvar, _) ->
               mk_app pvar bound_tvars bounds
                 ~replacer:(mk_replacer tvar T_int.mk_add)
                 ()
               :: mk_app pvar bound_tvars bounds
                    ~replacer:(mk_replacer tvar T_int.mk_sub)
                    ()
               :: res);
      ],
      mk_app pvar bound_tvars bounds ~replacer:(fun _ _ -> T_int.zero ()) (),
      unknowns )

  let encode_exists_mu' prefix bound_tvars bound_pvars unknowns exists_formula =
    (* avoid dup *)
    let pvar =
      Problem.avoid_dup (Ident.Pvar prefix)
        (bound_pvars @ Set.to_list @@ Kind.pvars_of unknowns)
    in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bound_tvars =
      let fv = scalar_dependencies body in
      List.filter bound_tvars ~f:(fst >> Set.mem fv)
    in
    let bounds, body = add_prefix_to_tvars_reserved ~reserved:(List.map bound_tvars ~f:fst) "#exists_" bounds body in
    let rec rep body subst res = function
      | [] -> Formula.subst subst body :: res
      | (tvar, sort) :: tail ->
          let subst' =
            Map.Poly.add_exn subst ~key:tvar
              ~data:(T_int.mk_neg (Term.mk_var tvar sort))
          in
          rep body subst (rep body subst' res tail) tail
    in
    (* Exists(x,y) =mu F(x,y) \/ F(-x,y) \/ F(x,-y) \/ F(-x,-y) \/ Exists(x+1,y) \/ Exists(x,y+1)*)
    ( [
        Pred.make Predicate.Mu pvar (bound_tvars @ bounds)
        @@ Formula.or_of
        @@ rep body Map.Poly.empty [] bounds
        @ List.map bounds ~f:(fun (tvar, _) ->
            mk_app pvar bound_tvars bounds
              ~replacer:(mk_replacer tvar T_int.mk_add)
              ());
      ],
      mk_app pvar bound_tvars bounds ~replacer:(fun _ _ -> T_int.zero ()) (),
      unknowns )

  let encode_exists_mus prefix bound_tvars bound_pvars unknowns exists_formula =
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bound_tvars =
      let fv = scalar_dependencies body in
      List.filter bound_tvars ~f:(fst >> Set.mem fv)
    in
    let bounds, body = add_prefix_to_tvars_reserved ~reserved:(List.map bound_tvars ~f:fst) "#exists_" bounds body in
    let rec encode_exists args bounds bound_pvars =
      match bounds with
      | [] -> ([], body)
      | (tvar, sort) :: tail ->
          (* avoid dup *)
          let tvar_name = Ident.name_of_tvar tvar in
          let pvar1, pvar2 =
            let bound_pvars' =
              bound_pvars @ Set.to_list @@ Kind.pvars_of unknowns
            in
            ( Problem.avoid_dup
                (Ident.Pvar (prefix ^ "_" ^ tvar_name ^ "_n"))
                bound_pvars',
              Problem.avoid_dup
                (Ident.Pvar (prefix ^ "_" ^ tvar_name ^ "_p"))
                bound_pvars' )
          in
          (* rec *)
          let args' = (tvar, sort) :: args in
          let add_preds, body =
            encode_exists args' tail (pvar1 :: pvar2 :: bound_pvars)
          in
          (* make exists body *)
          let mk_body pvar arg =
            Formula.mk_atom
            @@ Atom.mk_pvar_app pvar (List.map ~f:snd args')
                 (arg :: Term.of_sort_env args)
          in
          let def1 =
            (* tvar_exists - 1 *)
            Pred.make Predicate.Mu pvar1 args'
            @@ Formula.mk_or body
                 (mk_body pvar1
                 @@ T_int.mk_sub (Term.mk_var tvar sort) (T_int.one ()))
          in
          let def2 =
            (* tvar_exists + 1 *)
            Pred.make Predicate.Mu pvar2 args'
            @@ Formula.mk_or body
                 (mk_body pvar2
                 @@ T_int.mk_add (Term.mk_var tvar sort) (T_int.one ()))
          in
          (* ExistsLy(x,y) =mu F(x,y) \/ ExistsLy(x,y-1)
             ExistsRy(x,y) =mu F(x,y) \/ ExistsRy(x,y+1)
             ExistsLx(x) =mu ExistsLy(x,0) \/ ExistsRy(x,0) \/ ExistsLx(x-1)
             ExistsRx(x) =mu ExistsLy(x,0) \/ ExistsRy(x,0) \/ ExistsRx(x+1)
          *)
          ( def1 :: def2 :: add_preds,
            Formula.mk_or
              (mk_body pvar1 (T_int.zero ()))
              (mk_body pvar2 (T_int.zero ())) )
    in
    let preds, query = encode_exists bound_tvars bounds bound_pvars in
    (preds, query, unknowns)

  let encode_exists_nu range prefix bound_tvars bound_pvars unknowns
      exists_formula =
    (* avoid dup *)
    let pvar =
      Problem.avoid_dup (Ident.Pvar prefix)
        (bound_pvars @ Set.to_list @@ Kind.pvars_of unknowns)
    in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bound_tvars =
      let fv = scalar_dependencies body in
      List.filter bound_tvars ~f:(fst >> Set.mem fv)
    in
    let bounds, body = add_prefix_to_tvars_reserved ~reserved:(List.map bound_tvars ~f:fst) "#exists_" bounds body in
    let rec rep body subst res = function
      | [] -> Formula.subst subst body :: res
      | (tvar, sort) :: tail ->
          let subst' =
            Map.Poly.add_exn subst ~key:tvar
              ~data:(T_int.mk_neg (Term.mk_var tvar sort))
          in
          rep body subst (rep body subst' res tail) tail
    in
    (* Exists x =nu x >= 0 /\ (F(x) \/ F(-x) \/ Exists(x-1)) *)
    let body =
      Formula.and_of
      @@
      (* F(x) \/ F(-x) \/ Exists(x-1) *)
      Formula.or_of
        (* F(x) \/ F(-x) *)
        (rep body Map.Poly.empty [] bounds
        (* Exists(x-1) *)
        @ List.map bounds ~f:(fun (tvar, _) ->
            mk_app pvar bound_tvars bounds
              ~replacer:(mk_replacer tvar T_int.mk_sub)
              ()))
      (* x >= 0 *)
      :: List.map bounds ~f:(fun (tvar, sort) ->
          Formula.geq (Term.mk_var tvar sort) (T_int.zero ()))
    in
    ( [ Pred.make Predicate.Nu pvar (bound_tvars @ bounds) body ],
      (* forall x. x >= range => Exists(x) *)
      Evaluator.simplify @@ Formula.forall bounds
      @@ Formula.mk_imply
           (* x >= range *)
           (Formula.and_of
           @@ List.map bounds ~f:(fun (tvar, sort) ->
               Formula.geq (Term.mk_var tvar sort) (T_int.mk_int range)))
           (* Exists(x) *)
           (mk_app pvar bound_tvars bounds ()),
      unknowns )

  let encode_exists_skolem_fun_reserved ~reserved prefix bound_tvars bound_pvars unknowns
      exists_formula =
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bool_params, arith_params =
      let fv = scalar_dependencies body in
      List.filter bounds ~f:(fst >> Set.mem fv)
      |> List.partition_tf ~f:(snd >> Term.is_bool_sort)
    in
    let arith_params, body =
      let unknown_senv, _ = unknowns in
      let fresh = name_allocator body
          (reserved @ List.map (bounds @ bound_tvars) ~f:fst @ Map.keys unknown_senv
           @ List.map bound_pvars ~f:Ident.pvar_to_tvar @ Map.keys (get_fenv ())) in
      let subst, bounds_rev =
        List.fold ~init:(Map.Poly.empty, []) arith_params
          ~f:(fun (subst, bounds_rev) (tvar, sret) ->
            let new_tvar =
              fresh ("#skolem_" ^ prefix ^ Ident.name_of_tvar tvar)
            in
            let sargs = List.map ~f:snd bound_tvars in
            let fapp =
              Term.mk_fvar_app new_tvar sargs sret
                (Term.of_sort_env bound_tvars)
            in
            ( Map.Poly.add_exn subst ~key:tvar ~data:fapp,
              (new_tvar, sargs @ [ sret ]) :: bounds_rev ))
      in
      (List.rev bounds_rev, Formula.subst subst body)
    in
    (*assert (List.length pvars' = List.length arith_params);*)
    let body =
      (* expand existential quantification over boolean variables *)
      let rec aux body = function
        | [] -> body
        | (x, sort) :: xs ->
            assert (Term.is_bool_sort sort);
            let body = aux body xs in
            Formula.or_of
              [
                Formula.apply_pred (x, body) @@ T_bool.mk_true ();
                Formula.apply_pred (x, body) @@ T_bool.mk_false ();
              ]
      in
      aux body bool_params
    in
    ( [],
      Evaluator.simplify body,
      List.fold arith_params ~init:unknowns ~f:(fun unknowns (x, sorts) ->
          let sort =
            Logic.Sort.mk_fun @@ List.map ~f:Logic.ExtTerm.of_old_sort sorts
          in
          let kind =
            if Logic.ExtTerm.is_real_sort @@ Logic.Sort.ret_of sort then
              Kind.RealFun
            else Kind.IntFun
          in
          Kind.add_funs unknowns kind (Map.Poly.singleton x sort))
    )

  let encode_exists_skolem_fun prefix bound_tvars bound_pvars unknowns exists_formula =
    encode_exists_skolem_fun_reserved ~reserved:[] prefix bound_tvars bound_pvars
      unknowns exists_formula

  let disable_dependency = true

  (* [encode_exists_skolem_pred ?reuse ...]: with [reuse = Some pvs], the
     witness predicates are [pvs] (one per scalar bound variable the body uses,
     in order, already in [unknowns] with their kind) instead of fresh ones;
     requires [pvs] to have been made by an earlier call at the same enclosing
     binders [bound_tvars] for bound variables of the same sorts.  The last
     component of the result is the witness predicates used. *)
  let encode_exists_skolem_pred_with ?reuse prefix bound_tvars bound_pvars
      unknowns exists_formula =
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bool_params, arith_params =
      let fv = scalar_dependencies body in
      List.filter bounds ~f:(fst >> Set.mem fv)
      |> List.partition_tf ~f:(snd >> Term.is_bool_sort)
    in
    let other_pvars = bound_pvars @ Set.to_list @@ Kind.pvars_of unknowns in
    let _, pvars' =
      List.fold_left ~init:([], []) arith_params
        ~f:(fun (dep_params, pvars') (x, s) ->
          let pv =
            Ident.fnpred_pvar (Ident.Pvar (prefix ^ Ident.name_of_tvar x))
          in
          ( (if disable_dependency then []
             else
               dep_params
               @ [ (Ident.Tvar ("#exists_" ^ Ident.name_of_tvar x), s) ]),
            pvars'
            @ [
                ( Problem.avoid_dup pv (List.map ~f:fst pvars' @ other_pvars),
                  dep_params );
              ] ))
    in
    let pvars' =
      match reuse with
      | None -> pvars'
      | Some pvs -> List.map2_exn pvs pvars' ~f:(fun pv (_, dep) -> (pv, dep))
    in
    let arith_params, body = add_prefix_to_tvars_reserved ~reserved:(List.map bound_tvars ~f:fst) "#exists_" arith_params body in
    (*assert (List.length pvars' = List.length arith_params);*)
    let body =
      (* expand existential quantification over boolean variables *)
      let rec aux body = function
        | [] -> body
        | (x, sort) :: xs ->
            assert (Term.is_bool_sort sort);
            let body = aux body xs in
            Formula.or_of
              [
                Formula.apply_pred (x, body) @@ T_bool.mk_true ();
                Formula.apply_pred (x, body) @@ T_bool.mk_false ();
              ]
      in
      aux body bool_params
    in
    ( [],
      Evaluator.simplify
      @@ Formula.forall arith_params
      @@ Formula.mk_imply
           (Formula.and_of
              (List.map2_exn pvars' arith_params
                 ~f:(fun (pvar, dep_params) (tvar, sort) ->
                   mk_app pvar bound_tvars (dep_params @ [ (tvar, sort) ]) ())))
           body,
      (match reuse with
      | Some _ -> unknowns
      | None ->
          Kind.add_pred_env_set unknowns Kind.FN
          @@ Set.Poly.of_list
          @@ List.map2_exn pvars' arith_params
               ~f:(fun (pvar, dep_params) (_, sort) ->
                 (pvar, List.map ~f:snd (bound_tvars @ dep_params) @ [ sort ]))),
      List.map pvars' ~f:fst )

  let encode_exists_skolem_pred prefix bound_tvars bound_pvars unknowns
      exists_formula =
    let preds, fml, unknowns, _ =
      encode_exists_skolem_pred_with prefix bound_tvars bound_pvars unknowns
        exists_formula
    in
    (preds, fml, unknowns)

  (* The witness classes of one formula under [share_witnesses]: each class
     records the enclosing binders, the sorts of its bound variables, the
     witness predicates and, per member, its body with the bound variables
     renamed positionally and its path from the formula's root ([true] at a
     disjunction, [false] at a conjunction, with the side taken).  A new
     occurrence joins a class only when it may share with every member. *)
  type witness_class = {
    ctx : sort_env_list;
    sorts : Sort.t list;
    choice : string list;
    pvs : Ident.pvar list;
    mutable members : ((bool * int) list * Formula.t) list;
  }

  let canon_body bounds body =
    Formula.rename
      (Map.Poly.of_alist_exn
         (List.mapi bounds ~f:(fun i (x, _) ->
              (x, Ident.Tvar (sprintf "#share%d" i)))))
      body

  (* a structural equality that refuses, rather than raises, on a value
     polymorphic equality cannot compare *)
  let safe_equal a b =
    try Stdlib.( = ) a b with Invalid_argument _ -> false

  (* the nearest common ancestor of two paths is a disjunction *)
  let rec nca_is_or p q =
    match (p, q) with
    | (o1, s1) :: p', (_, s2) :: q' ->
        if s1 = s2 then nca_is_or p' q' else o1
    | _ -> false

  (* Rebinds each bit-vector variable of [exists bounds. body] as an integer
     variable of the same name read modulo the width:
     [exists (x:bv_k). F(x)] becomes [exists (x:Int). F(int_to_bv_k x)].
     The two are equivalent because [int_to_bv_k] is onto the bit-vectors of
     width [k].  Requires an existential formula; other bound sorts are kept.

     Only the enumerating encodings ([Mu], [Mu'], [Mus], [Nu]) may be given
     the rebound formula: they walk a bound variable by integer successor and
     predecessor and compare it with integer constants, so without this a
     bit-vector LTS reached Z3 with integer [>=] and [-] over a bit-vector
     variable and was refused with a sort-mismatch error.

     The Skolem encodings ([SkolemFun], [SkolemPred], with or without witness
     sharing) must keep the variable's own sort.  They do no arithmetic on the
     bound variable, and the sort of the variable becomes the sort of the
     witness unknown's last argument.  A caller may pair that unknown with
     one built elsewhere under the same name: MuStrat names a universal of
     one side ([conv_forall] below, which never rebinds) and the existential
     it becomes on the dual side with one key, and requires both declarations
     to have one sort.  Rebinding here gave the existential's key [Int] and
     the universal's [bv_k], and every bit-vector input stopped with a
     sort-mismatch failure. *)
  let bv_bounds_over_int exists_formula =
    let bounds, body, info = Formula.let_exists exists_formula in
    let subst, bounds =
      List.fold_map bounds ~init:Map.Poly.empty ~f:(fun subst (tvar, sort) ->
          match sort with
          | T_bv.SBV size ->
              ( Map.Poly.add_exn subst ~key:tvar
                  ~data:(T_irb.mk_int_to_bv ~size (Term.mk_var tvar T_int.SInt)),
                (tvar, T_int.SInt) )
          | _ -> (subst, (tvar, sort)))
    in
    if Map.is_empty subst then exists_formula
    else Formula.exists bounds (Formula.subst subst body) ~info

  let dispatched =
    match config.elimination with
    | Mu -> encode_exists_mu
    | Mu' -> encode_exists_mu'
    | Mus -> encode_exists_mus
    | Nu range -> encode_exists_nu (Z.of_int range)
    | SkolemFun -> encode_exists_skolem_fun
    | SkolemPred -> encode_exists_skolem_pred

  let rec encode_exists_reserved ~reserved ?(conv_forall = false)
      ?(classes = ref []) ?(path = []) prefix bound_tvars bound_pvars unknowns
      fml =
    (* the recursive calls share [classes] and extend [path] at a binary node *)
    let encode_exists_reserved ?(path = path) ~reserved ~conv_forall prefix =
      encode_exists_reserved ~reserved ~conv_forall ~classes ~path prefix
    in
    if Formula.is_quantifier_free fml then ([], fml, bound_pvars, unknowns)
    else if Formula.is_and fml || Formula.is_or fml then
      let binop, fml1, fml2, info = Formula.let_binop fml in
      let is_or = Formula.is_or fml in
      let preds1, fml1, bound_pvars, unknowns =
        encode_exists_reserved ~path:(path @ [ (is_or, 0) ]) ~reserved ~conv_forall prefix bound_tvars bound_pvars unknowns fml1
      in
      let preds2, fml2, bound_pvars, unknowns =
        encode_exists_reserved ~path:(path @ [ (is_or, 1) ]) ~reserved ~conv_forall prefix bound_tvars bound_pvars unknowns fml2
      in
      ( preds1 @ preds2,
        Formula.mk_binop binop fml1 fml2 ~info,
        bound_pvars,
        unknowns )
    else if Formula.is_forall fml then
      let bounds, fml, info = Formula.let_forall fml in
      let preds, fml, bound_pvars, unknowns =
        encode_exists_reserved ~reserved ~conv_forall prefix (bounds @ bound_tvars) bound_pvars
          unknowns fml
      in
      let fml' = Formula.forall bounds fml ~info in
      if conv_forall && Formula.is_forall fml' then
        let fml, unknowns =
          let body = fml in
          let bool_params, arith_params =
            let fv = scalar_dependencies body in
            List.filter bounds ~f:(fst >> Set.mem fv)
            |> List.partition_tf ~f:(snd >> Term.is_bool_sort)
          in
          let pvars' =
            List.fold_right arith_params ~init:[] ~f:(fun (x, _) pvars' ->
                let pv =
                  Ident.fnpred_pvar (Ident.Pvar (prefix ^ Ident.name_of_tvar x))
                in
                Problem.avoid_dup pv
                  (pvars' @ bound_pvars @ Set.to_list @@ Kind.pvars_of unknowns)
                :: pvars')
          in
          let arith_params, body =
            add_prefix_to_tvars_reserved ~reserved:(List.map bound_tvars ~f:fst) "#foralls_" arith_params body
          in
          (*assert (List.length pvars' = List.length arith_params);*)
          let body =
            (* expand universal quantification over boolean variables *)
            let rec aux body = function
              | [] -> body
              | (x, sort) :: xs ->
                  assert (Term.is_bool_sort sort);
                  let body = aux body xs in
                  Formula.and_of
                    [
                      Formula.apply_pred (x, body) @@ T_bool.mk_true ();
                      Formula.apply_pred (x, body) @@ T_bool.mk_false ();
                    ]
            in
            aux body bool_params
          in
          ( Evaluator.simplify
            @@ Formula.forall arith_params
            @@
            (* disjoin the dummy predicate variables for universal quantifiers *)
            Formula.or_of
              (List.map2_exn pvars' arith_params ~f:(fun pvar bind ->
                   mk_app pvar bound_tvars [ bind ] ())
              @ [ body ]),
            Kind.add_pred_env_set unknowns Kind.Ord
            @@ Set.Poly.of_list
            @@ List.map2_exn pvars' arith_params ~f:(fun pvar (_, sort) ->
                (pvar, List.map bound_tvars ~f:snd @ [ sort ])) )
        in
        (preds, fml, bound_pvars, unknowns)
      else (preds, fml', bound_pvars, unknowns)
    else if Formula.is_exists fml then
      let bounds, fml, info = Formula.let_exists fml in
      let preds, fml, bound_pvars, unknowns =
        encode_exists_reserved ~reserved ~conv_forall prefix (bounds @ bound_tvars) bound_pvars
          unknowns fml
      in
      let fml' = Formula.exists bounds fml ~info in
      if Formula.is_exists fml' then
        let add_preds, fml, unknowns =
          (match (config.elimination, config.share_witnesses) with
           | SkolemFun, _ -> encode_exists_skolem_fun_reserved ~reserved prefix
               bound_tvars bound_pvars unknowns fml'
           | SkolemPred, (Same_body | Same_body_or_disjunct | Same_choice_or_disjunct) ->
               let bounds, body, _ = Formula.let_exists fml' in
               (* Keying a class on the sorts of all bound variables meets
                  the positional precondition of [~reuse]: [Formula.exists]
                  has dropped every bound variable the body does not use, and
                  a Boolean one is expanded rather than witnessed, so equal
                  bound sorts give equal witnessed sorts in the same order. *)
               let sorts = List.map bounds ~f:snd in
               (* the bound variables' names, a copy's trailing [_<digits>]
                  dropped: which choice an occurrence makes *)
               let choice =
                 List.map bounds ~f:(fun (x, _) ->
                     let n = Ident.name_of_tvar x in
                     match String.rsplit2 n ~on:'_' with
                     | Some (stem, digits)
                       when (not (String.is_empty digits))
                            && String.for_all digits ~f:Char.is_digit ->
                         stem
                     | _ -> n)
               in
               let canon = canon_body bounds body in
               let fits c =
                 safe_equal c.ctx bound_tvars
                 && safe_equal c.sorts sorts
                 && (Stdlib.( <> ) config.share_witnesses Same_choice_or_disjunct
                    || List.equal String.equal c.choice choice)
                 && List.for_all c.members ~f:(fun (q, canon_q) ->
                        safe_equal canon_q canon
                        || (Stdlib.( <> ) config.share_witnesses Same_body
                           && nca_is_or path q))
               in
               (match List.find !classes ~f:fits with
               | Some c ->
                   let preds, fml, unknowns, _ =
                     encode_exists_skolem_pred_with ~reuse:c.pvs prefix
                       bound_tvars bound_pvars unknowns fml'
                   in
                   c.members <- (path, canon) :: c.members;
                   Debug.print
                   @@ lazy
                        (sprintf "witness shared: %s"
                           (String.concat_map_list ~sep:"," c.pvs
                              ~f:Ident.name_of_pvar));
                   (preds, fml, unknowns)
               | None ->
                   let preds, fml, unknowns, pvs =
                     encode_exists_skolem_pred_with prefix bound_tvars
                       bound_pvars unknowns fml'
                   in
                   classes :=
                     !classes
                     @ [ { ctx = bound_tvars; sorts; choice; pvs; members = [ (path, canon) ] } ];
                   (preds, fml, unknowns))
           | SkolemPred, No_witness_sharing ->
               encode_exists_skolem_pred prefix bound_tvars bound_pvars
                 unknowns fml'
           | (Mu | Mu' | Mus | Nu _), _ ->
               dispatched prefix bound_tvars bound_pvars unknowns
                 (bv_bounds_over_int fml'))
        in
        ( add_preds @ preds,
          fml,
          Pred.pvars_of_list add_preds @ bound_pvars,
          unknowns )
      else (preds, fml', bound_pvars, unknowns)
    else
      failwith (sprintf "[encode_exists] %s not supported" (Formula.str_of fml))

  let encode_exists ?(conv_forall = false) prefix bound_tvars bound_pvars unknowns fml =
    let reserved = Set.to_list (Formula.names_spelled_in fml) in
    encode_exists_reserved ~reserved ~conv_forall prefix bound_tvars bound_pvars unknowns fml

  let problem_names muclp =
    List.concat_map (muclp.Problem.query :: List.map muclp.Problem.preds
                      ~f:(fun pred -> pred.Pred.body))
      ~f:(fun phi -> Set.to_list (Formula.names_spelled_in phi))
    @ List.concat_map muclp.Problem.preds ~f:(fun pred -> Ident.pvar_to_tvar pred.Pred.name :: List.map pred.Pred.args ~f:fst)

  let elim_exists_in_query ?(conv_forall = false) (muclp, unknowns) =
    let bound_pvars = Pred.pvars_of_list muclp.Problem.preds in
    let add_preds, query', _pvars, unknowns =
      let prefix = "query_" in
      encode_exists_reserved ~reserved:(problem_names muclp) ~conv_forall prefix [] bound_pvars unknowns
        (Formula.nnf_of muclp.Problem.query)
    in
    (Problem.make (add_preds @ muclp.Problem.preds) query', unknowns)

  let elim_exists_in_preds ?(conv_forall = false) (muclp, unknowns) =
    let reserved = problem_names muclp in
    let bound_pvars = Pred.pvars_of_list muclp.Problem.preds in
    let preds', unknowns =
      List.fold ~init:([], unknowns) muclp.Problem.preds
        ~f:(fun (preds, unknowns) pred ->
          let add_preds, body, _pvars, unknowns =
            let prefix = Ident.name_of_pvar pred.name ^ Ident.divide_flag in
            encode_exists_reserved ~reserved ~conv_forall prefix pred.args bound_pvars unknowns
              (Formula.nnf_of pred.body)
          in
          (add_preds @ ({ pred with body } :: preds), unknowns))
    in
    (Problem.make (List.rev preds') muclp.Problem.query, unknowns)

  let elim_exists ?(conv_forall = false) =
    elim_exists_in_query ~conv_forall >> elim_exists_in_preds ~conv_forall
end
