(* The elaboration E: an OCaml program with algebraic effects and handlers,
   type-checked by the OCaml compiler, to the source calculus of [CpsLang],
   annotated with the solved MB effect typing.

   The traversal is [RCaml.MBcgen.fold_expr] in its CPS mode, the one EffCaml's
   generator uses, with an object whose methods build [CpsLang] terms instead
   of recursion-scheme rules; each structure item's constraints are solved by
   [RCaml.MBcsol] before its terms are built, so every node is annotated with
   its solved computation sort.  The item-level handling (datatype and
   external declarations, the [eff] datatype, the [check_toplevel]
   attribute) is the one of EffCaml's generator, so the two read the same
   programs and the same sorts.

   What the elaboration does to the program, construct by construct:
   A-normalisation -- an impure argument of an application, a tuple or an
   operation call is let-bound to a fresh scoped variable, left to right,
   before the call; an application [f a1 ... an] becomes
   [let p0 = f in let p1 = p0 a1 in ... p(n-1) an] with the [p_i] local
   binders; the condition of [if] and [assert] is let-bound to a fresh local
   binder; [e1; e2] binds [e1] to a fresh unscoped binder; [if c then e]
   gets the else-branch [return ()].

   Contract: on success, (i) every typed-tree node the traversal visits
   yields exactly one [CpsLang] node, whose [ty] is the solved sort of its
   position under the substitution of its item; (ii) the binders the
   elaboration draws are distinct from every variable of the program (checked
   at the end; a collision is a refusal, never a capture); (iii) the
   call-by-value meaning is preserved on the supported fragment (stated, not
   proved; the property test checks it on small closed programs).  A
   construct outside the fragment is a refusal naming the construct
   ([Error]), never a partial term: annotations, [unif], [match],
   [shift0]/[reset], recursive inner [let], simultaneous [let ... and ...],
   constructors with arguments, non-variable [let] patterns, exception
   clauses, constants other than Booleans, [()] and the Boolean primitives.

   The elaboration resets the process-global datatype and function
   environments of [Ast.LogicOld], as EffCaml's generator does, so it is not
   reentrant. *)

open Core
open Typedtree
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open Automata
open CpsLang

module Config = struct
  type t = { verbose : bool; mbcsol : RCaml.MBcsol.Config.t }

  module type ConfigType = sig
    val config : t
  end
end

exception Refused of string

let refuse fmt = ksprintf (fun s -> raise (Refused s)) fmt

let replace_any_tvar x =
  let name = Ident.name_of_tvar x in
  if String.is_prefix name ~prefix:"_" then
    Ident.mk_fresh_tvar ~prefix:(Some ("any" ^ name)) ()
  else x

(* An elaborated program with the tree automata of its [check_toplevel]
   attributes, each with the number of items it follows. *)
type elaborated = { program : program; checks : (TreeAutomaton.t * int) list }

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module MBcgen = RCaml.MBcgen.Make (struct
    let config =
      RCaml.MBcgen.Config.
        {
          verbose = config.verbose;
          for_cps_trans = true;
          (* as in EffCaml: each [perform_atp] call is read as ATP by the
             CPS reading itself *)
          atp_operations = Off;
        }
  end)

  module MBcsol = RCaml.MBcsol.Make (struct
    let config = { config.mbcsol with verbose = config.verbose }
  end)

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_module_name "CpsElab"

  type ctx = { maps : opsig_subst * sort_subst * eff_subst; ty : Sort.c }

  (* binders this elaboration drew, checked against the program at the end *)
  let drawn = ref Set.Poly.empty

  let draw prefix =
    let v = Ident.mk_fresh_tvar ~prefix:(Some prefix) () in
    drawn := Set.add !drawn v;
    v

  let value_of what (m : comp) =
    match m.desc with
    | Return v -> v
    | _ -> refuse "[elab] %s: a pure position holds a computation" what

  (* an argument of an application, a tuple or an operation call: a value, or
     a computation let-bound to a fresh scoped binder *)
  let elab_args ctx prefix nexts_either =
    List.map nexts_either ~f:(function
      | First (true, next, ty) -> (None, value_of prefix (next { ctx with ty }))
      | First (false, next, ty) ->
          let x = draw prefix in
          (Some ({ var = x; scoped = true }, next { ctx with ty }), var x)
      | Second (x, _sort) -> (None, var x))

  let wrap_lets ty binds body =
    List.fold_right binds ~init:body ~f:(fun bind body ->
        match bind with
        | None -> body
        | Some (b, m) -> mk_comp ty (Let (b, m, body)))

  let elab_expr eff_map senv0 dtenv0 (expr : expression) =
    ignore eff_map;
    MBcgen.fold_expr dtenv0 false senv0 expr
      ~f:
        (object
           method f_annot (_attrs, _next) (_ : ctx) : comp =
             refuse "[elab] annotations are not supported"

           method f_copy_label (_lbl : string) next = next

           (* effect schemes of top-level bindings are RCaml's: like EffCaml,
              the elaboration types every occurrence with the binding's stored
              sort, so no occurrence is an instance *)
           method has_scheme (_ : Path.t) = false

           method f_scheme_instance (p : Path.t) =
             refuse "[elab] no effect scheme for %s" (Path.name p)

           method f_unif (_next, _sort) (_ : ctx) : comp =
             refuse "[elab] unif is not supported"

           method f_var (is_handled, rec_vars) (x, _sort) ctx =
             let handled_rec = is_handled && Set.mem rec_vars x in
             mk_comp ctx.ty (Return (var ~handled_rec ~at:ctx.ty x))

           method f_const term ctx =
             let term = Term.subst_all ctx.maps term in
             let c =
               match
                 try Some (Ident.name_of_tvar @@ Term.tvar_of term)
                 with exn_ when not (Common.Timer.is_async exn_) -> None
               with
               | Some "Stdlib.=" -> Prim "Iff"
               | Some "Stdlib.<>" -> Prim "Xor"
               | Some "Stdlib.not" -> Prim "Not"
               | Some ("Stdlib.&&" | "Stdlib.&") -> Prim "And"
               | Some ("Stdlib.||" | "Stdlib.or") -> Prim "Or"
               | _ ->
                   if T_bool.is_true term then Bool true
                   else if T_bool.is_false term then Bool false
                   else
                     refuse "[elab] constant %s is not supported"
                       (Term.str_of term)
             in
             mk_comp ctx.ty (Return (Const c))

           method f_construct _dt cons_name nexts_either ctx =
             if List.is_empty nexts_either && String.equal cons_name "()" then
               mk_comp ctx.ty (Return (Const Unit))
             else refuse "[elab] constructor %s is not supported" cons_name

           method f_apply (_pure1, next1, opsig1s, opsig1, cont1s, cont1)
               next2s_either ctx =
             let opsig1s = List.map opsig1s ~f:(Term.subst_opsig ctx.maps) in
             let opsig1 = Term.subst_opsig ctx.maps opsig1 in
             let cont1s = List.map cont1s ~f:(Term.subst_cont ctx.maps) in
             let cont1 = Term.subst_cont ctx.maps cont1 in
             let next2s_either =
               List.map next2s_either ~f:(MBcgen.subst_all_either ctx.maps)
             in
             let args = elab_args ctx "arg" next2s_either in
             let ty1 =
               Sort.mk_eff_fun ~opsig:opsig1 ~opsigs:(Some opsig1s) ~cont:cont1
                 ~conts:(Some cont1s)
                 (List.map next2s_either ~f:(function
                   | First (_, _, c) -> c.Sort.val_type
                   | Second (_, s) -> s))
                 ctx.ty
             in
             let m_f = next1 { ctx with ty = ty1 } in
             (* the sort of the i-th partial application, read off the arrow
                chain the function is used at *)
             let rec stages s n =
               if n = 0 then []
               else
                 match s with
                 | Sort.SArrow (_, c) -> c :: stages c.val_type (n - 1)
                 | _ -> refuse "[elab] application of a non-function sort"
             in
             let tys = stages ty1.val_type (List.length args) in
             let p0 = draw "papp" in
             let rec chain p = function
               | [] -> assert false
               | [ (v, c) ] -> mk_comp c (App (var p, v))
               | (v, c) :: rest ->
                   let p' = draw "papp" in
                   mk_comp ctx.ty
                     (Let
                        ( { var = p'; scoped = false },
                          mk_comp c (App (var p, v)),
                          chain p' rest ))
             in
             let call =
               mk_comp ctx.ty
                 (Let
                    ( { var = p0; scoped = false },
                      m_f,
                      chain p0 (List.zip_exn (List.map args ~f:snd) tys) ))
             in
             wrap_lets ctx.ty (List.map args ~f:fst) call

           method f_tuple nexts_either ctx =
             let nexts_either =
               List.map nexts_either ~f:(MBcgen.subst_all_either ctx.maps)
             in
             let args = elab_args ctx "elem" nexts_either in
             wrap_lets ctx.ty (List.map args ~f:fst)
             @@ mk_comp ctx.ty (Return (Tuple (List.map args ~f:snd)))

           method f_function pats _t_annot_rty_opt (nexts, conts) ctx =
             let pats = List.map pats ~f:(Pattern.subst_sort ctx.maps) in
             let conts = List.map conts ~f:(Term.subst_cont ctx.maps) in
             match (ctx.ty.val_type, pats, nexts, conts) with
             | Sort.SArrow (_t, c), [ pat ], [ next ], [ cont ] ->
                 let x =
                   match pat with
                   | Pattern.PAny _ -> draw "any"
                   | PVar (x, _) -> replace_any_tvar x
                   | PCons (_, "()", []) -> draw "unit"
                   | _ ->
                       refuse "[elab] pattern %s is not supported"
                         (Pattern.str_of pat)
                 in
                 let body = next { ctx with ty = { c with cont_eff = cont } } in
                 mk_comp ctx.ty
                   (Return (Fun ({ var = x; scoped = true }, body)))
             | Sort.SArrow _, _, _, _ ->
                 refuse "[elab] pattern matching in a function is not supported"
             | _ -> refuse "[elab] a function at a non-arrow sort"

           method f_ite (next1, cont1) (next2, cont2) next3_opt ctx =
             let cont1 = Term.subst_cont ctx.maps cont1 in
             let cont2 = Term.subst_cont ctx.maps cont2 in
             let next3_opt = MBcgen.subst_all_opt ctx.maps next3_opt in
             let m1 =
               next1
                 {
                   ctx with
                   ty =
                     {
                       op_sig = ctx.ty.op_sig;
                       val_type = T_bool.SBool;
                       cont_eff = cont1;
                     };
                 }
             in
             let m2 =
               next2 { ctx with ty = { ctx.ty with cont_eff = cont2 } }
             in
             let m3 =
               match next3_opt with
               | None -> mk_comp ctx.ty (Return (Const Unit))
               | Some (next3, cont3) ->
                   next3 { ctx with ty = { ctx.ty with cont_eff = cont3 } }
             in
             let x = draw "cond" in
             mk_comp ctx.ty
               (Let
                  ( { var = x; scoped = false },
                    m1,
                    mk_comp ctx.ty (If (var x, m2, m3)) ))

           method f_match _ _ _ (_ : ctx) : comp =
             refuse "[elab] match expressions are not supported"

           method f_assert (next_opt, cont) ctx =
             let cont = Term.subst_cont ctx.maps cont in
             match next_opt with
             | None -> mk_comp ctx.ty Fail
             | Some next ->
                 let m =
                   next
                     {
                       ctx with
                       ty =
                         {
                           op_sig = ctx.ty.op_sig;
                           val_type = T_bool.SBool;
                           cont_eff = cont;
                         };
                     }
                 in
                 let x = draw "cond" in
                 mk_comp ctx.ty
                   (Let
                      ( { var = x; scoped = false },
                        m,
                        mk_comp ctx.ty (Assert (var x)) ))

           method f_let_and is_rec pats defs (next2, cont2) ctx =
             let pats = List.map pats ~f:(Pattern.subst_sort ctx.maps) in
             let cont2 = Term.subst_cont ctx.maps cont2 in
             let _is_pure1s, _is_fun1s, next1s, sort1s, cont1s = defs in
             match (is_rec, pats, next1s, sort1s, cont1s) with
             | true, _, _, _, _ ->
                 refuse "[elab] recursive inner functions are not supported"
             | false, [ pat ], [ next1 ], [ sort1 ], [ cont1 ] ->
                 let c1 =
                   Sort.
                     {
                       op_sig = ctx.ty.op_sig;
                       val_type = Term.subst_sort ctx.maps sort1;
                       cont_eff = Term.subst_cont ctx.maps cont1;
                     }
                 in
                 let m1 = next1 { ctx with ty = c1 } in
                 let b =
                   match pat with
                   | Pattern.PAny _ | Pattern.PCons (_, "()", []) ->
                       { var = draw "any"; scoped = false }
                   | Pattern.PVar (x, _) ->
                       if String.is_prefix (Ident.name_of_tvar x) ~prefix:"_"
                       then { var = replace_any_tvar x; scoped = false }
                       else { var = x; scoped = true }
                   | _ ->
                       refuse "[elab] pattern %s is not supported"
                         (Pattern.str_of pat)
                 in
                 let m2 =
                   next2 { ctx with ty = { ctx.ty with cont_eff = cont2 } }
                 in
                 mk_comp ctx.ty (Let (b, m1, m2))
             | _ -> refuse "[elab] simultaneous definitions are not supported"

           method f_sequence (next1, sort1, cont1) (next2, cont2) ctx =
             let sort1 = Term.subst_sort ctx.maps sort1 in
             let cont1 = Term.subst_cont ctx.maps cont1 in
             let cont2 = Term.subst_cont ctx.maps cont2 in
             let m1 =
               next1
                 {
                   ctx with
                   ty =
                     {
                       op_sig = ctx.ty.op_sig;
                       val_type = sort1;
                       cont_eff = cont1;
                     };
                 }
             in
             let m2 =
               next2 { ctx with ty = { ctx.ty with cont_eff = cont2 } }
             in
             mk_comp ctx.ty (Let ({ var = draw "seq"; scoped = false }, m1, m2))

           method f_shift0 _ _ (_ : ctx) : comp =
             refuse "[elab] shift0 is not supported"

           method f_reset _ (_ : ctx) : comp =
             refuse "[elab] reset is not supported"

           method f_perform is_atp _attrs (op_name, _op_sort, _op_cont)
               nexts_either ctx =
             let nexts_either =
               List.map nexts_either ~f:(MBcgen.subst_all_either ctx.maps)
             in
             let args = elab_args ctx "elem" nexts_either in
             wrap_lets ctx.ty (List.map args ~f:fst)
             @@ mk_comp ctx.ty
                  (Op
                     (op_name, List.map args ~f:snd, if is_atp then ATP else ATM))

           method f_handling (next_b, c_b) (next_r, x_r, c_r) op_handlers ctx =
             let c_b = Term.subst_triple ctx.maps c_b in
             let c_r = Term.subst_triple ctx.maps c_r in
             let x_r = replace_any_tvar x_r in
             let m_r = next_r { ctx with ty = c_r } in
             let clauses =
               List.map op_handlers
                 ~f:(fun
                     (name, kind, next, (x_args, _sort_args, k_opt, _sort_k, c))
                   ->
                   let c = Term.subst_triple ctx.maps c in
                   let kind =
                     match kind with
                     | MBcgen.ATMHandler -> Clause_ATM
                     | MBcgen.ATPHandler -> Clause_TR
                     | MBcgen.ExceptionHandler ->
                         refuse "[elab] exception clauses are not supported"
                   in
                   let params =
                     List.map x_args ~f:(fun x ->
                         { var = replace_any_tvar x; scoped = true })
                   in
                   let kont =
                     match k_opt with
                     | Some k -> { var = replace_any_tvar k; scoped = true }
                     | None -> { var = draw "k"; scoped = true }
                   in
                   {
                     op = name;
                     params;
                     kont;
                     body = next { ctx with ty = c };
                     kind;
                   })
             in
             let m_b = next_b { ctx with ty = c_b } in
             mk_comp ctx.ty
               (Handle
                  ({ ret = ({ var = x_r; scoped = true }, m_r); clauses }, m_b))
        end)

  let _ = Compmisc.init_path ()

  type envs = {
    items : item list;
    checks : (TreeAutomaton.t * int) list;
    dtenv : DTEnv.t;
    senv : sort_env_map;
    eff_ops : (string * Sort.t) list option;
    op_results : (string * Sort.t) list;
  }

  let eff_ops_of dtenv =
    match DTEnv.look_up_dt dtenv "eff" with
    | None -> None
    | Some dt ->
        Some
          (List.map (Datatype.conses_of dt) ~f:(fun cons ->
               match Datatype.params_of dt with
               | [ ret ] ->
                   ( Datatype.name_of_cons cons,
                     Sort.mk_fun
                     @@ Datatype.sorts_of_cons dt cons
                     @
                     let ans = Sort.mk_fresh_svar () in
                     [ Sort.mk_arrow ret ans; ans ] )
               | _ -> refuse "[elab] the eff datatype must have one parameter"))

  (* the attribute payload as a string, as EffCaml reads it *)
  let attr_content (attr : Parsetree.attribute) =
    match attr.attr_payload with
    | Parsetree.PStr ps -> (
        let ts, _, _, _, _ =
          Typemod.type_structure (Compmisc.initial_env ()) ps
        in
        match (List.hd_exn @@ List.rev ts.str_items).str_desc with
        | Tstr_eval
            ({ exp_desc = Texp_constant (Const_string (str, _, _)); _ }, _) ->
            str
        | _ ->
            refuse
              "[elab] an attribute payload must be a single string constant")
    | _ -> refuse "[elab] an attribute payload must be a structure"

  let of_struct_item (envs : envs) item =
    match item.str_desc with
    | Tstr_value (is_rec, vbs) ->
        let is_rec =
          match is_rec with Recursive -> true | Nonrecursive -> false
        in
        let is_pures, pats, defs =
          List.unzip3
          @@ List.map vbs ~f:(fun vb ->
              let pat = MBcgen.pattern_of envs.dtenv vb.vb_pat in
              let sort =
                match
                  ( MBcgen.find_val_attrs ~dtenv:envs.dtenv
                      ~attr_name:"annot_MB" vb.vb_attributes,
                    MBcgen.find_val_attrs ~dtenv:envs.dtenv ~attr_name:"annot"
                      vb.vb_attributes )
                with
                | Some t, _ | None, Some t -> Rtype.sort_of_val t
                | None, None ->
                    MBcgen.sort_of_expr ~lift:true envs.dtenv vb.vb_expr
              in
              ( MBcgen.is_pure vb.vb_expr.exp_desc,
                pat,
                ( Pattern.senv_of pat sort,
                  vb.vb_expr,
                  Sort.
                    {
                      op_sig = Sort.mk_fresh_empty_open_opsig ();
                      val_type = sort;
                      cont_eff = Sort.mk_fresh_evar ();
                    } ) ))
        in
        let eff_ops = eff_ops_of envs.dtenv in
        let senv_bounds =
          if is_rec then
            Map.update_with_list (envs.senv :: List.map defs ~f:fst3)
          else envs.senv
        in
        let eff_constrss, opsig_constrss, next1s =
          List.unzip3
          @@ List.map defs ~f:(fun (senv, expr, c) ->
              let old_rec_vars = !MBcgen.rec_vars in
              MBcgen.rec_vars :=
                if is_rec then Map.key_set senv else Set.Poly.empty;
              let res = elab_expr eff_ops senv_bounds envs.dtenv expr c in
              MBcgen.rec_vars := old_rec_vars;
              res)
        in
        let maps =
          let eff_constrs =
            Set.Poly.map (Set.Poly.union_list eff_constrss)
              ~f:(fun (effs, eff) ->
                ( List.map effs ~f:(Term.subst_sorts_cont !MBcgen.ref_id),
                  Term.subst_sorts_cont !MBcgen.ref_id eff ))
          in
          let opsig_constrs =
            Set.Poly.map (Set.Poly.union_list opsig_constrss)
              ~f:(fun (o1, o2) ->
                ( Term.subst_sorts_opsig !MBcgen.ref_id o1,
                  Term.subst_sorts_opsig !MBcgen.ref_id o2 ))
          in
          let sol =
            try MBcsol.solve eff_constrs opsig_constrs
            with MBcsol.Solve_failure msg ->
              refuse "[elab] no effect typing: %s" msg
          in
          let stheta =
            let stheta =
              Map.Poly.map sol.stheta ~f:(Term.subst_sorts_sort !MBcgen.ref_id)
            in
            let ref_id =
              Map.Poly.map !MBcgen.ref_id ~f:(Term.subst_sorts_sort stheta)
            in
            try Map.force_merge ref_id stheta
            with exn_ when not (Common.Timer.is_async exn_) ->
              refuse "[elab] the solution conflicts with the reference sorts"
          in
          let omap, smap, emap = (sol.otheta, stheta, sol.etheta) in
          let emap' =
            Map.Poly.map ~f:(Term.subst_conts_cont emap)
            @@ Map.Poly.map ~f:(Term.subst_sorts_cont smap)
            @@ Map.Poly.map ~f:(Term.subst_opsigs_cont omap) emap
          in
          let omap' =
            Map.Poly.map ~f:(Term.subst_conts_opsig emap')
            @@ Map.Poly.map ~f:(Term.subst_sorts_opsig smap)
            @@ Map.Poly.map ~f:(Term.subst_opsigs_opsig omap) omap
          in
          let smap' =
            Map.Poly.map ~f:(Term.subst_conts_sort emap')
            @@ Map.Poly.map ~f:(Term.subst_sorts_sort smap)
            @@ Map.Poly.map ~f:(Term.subst_opsigs_sort omap') smap
          in
          (omap', smap', emap')
        in
        let items =
          List.map3_exn is_pures pats (List.zip_exn next1s defs)
            ~f:(fun is_pure pat (next, (_, _, c)) ->
              let name =
                match pat with
                | Pattern.PVar (x, _) -> replace_any_tvar x
                | _ -> refuse "[elab] a top-level pattern must be a variable"
              in
              let ty = Term.subst_triple maps c in
              { name; is_pure; is_rec; body = next { maps; ty } })
        in
        let senv =
          (* the bound variables at their solved sorts, generalised when every
             binding is a pure function, as EffCaml's generator does *)
          let pat_senvs =
            List.map2_exn pats defs ~f:(fun pat (_, _, c) ->
                match pat with
                | Pattern.PVar (x, _) ->
                    Map.Poly.singleton x (Term.subst_triple maps c).val_type
                | _ -> Map.Poly.empty)
          in
          Map.update_with envs.senv @@ Map.force_merge_list
          @@ (if
                List.for_all is_pures ~f:Fn.id
                && List.for_all pats ~f:(Pattern.sort_of >> Sort.is_arrow)
              then List.map ~f:(Map.Poly.map ~f:(Typeinf.generalize envs.senv))
              else Fn.id)
               pat_senvs
        in
        { envs with items = envs.items @ items; senv; eff_ops }
    | Tstr_primitive vd ->
        let senv =
          Map.update_with envs.senv
          @@ Map.Poly.singleton (Ident.Tvar vd.val_name.txt)
          @@
          let sort =
            MBcgen.sort_of_type_expr envs.dtenv vd.val_desc.ctyp_type
          in
          Sort.mk_poly (Term.svs_of_sort sort) sort
        in
        { envs with senv }
    | Tstr_type (_, types) ->
        let dttypes, ustypes =
          List.partition_tf types ~f:(fun ty ->
              match ty.typ_kind with
              | Ttype_variant _ -> true
              | Ttype_abstract -> false
              | Ttype_open -> refuse "[elab] open types are not supported"
              | Ttype_record _ -> (
                  match ty.typ_name.txt with
                  | "effect_handler" | "handler" -> true
                  | _ -> refuse "[elab] record types are not supported"))
        in
        let dtenv =
          List.fold_left ustypes ~init:envs.dtenv ~f:(fun dtenv ty ->
              DTEnv.update_dt dtenv
              @@
              match ty.typ_manifest with
              | Some core_type ->
                  Datatype.mk_alias ty.typ_name.txt
                  @@ MBcgen.sort_of_core_type dtenv core_type
              | None -> Datatype.mk_uninterpreted_datatype ty.typ_name.txt)
        in
        let dts =
          let datatypes =
            List.map dttypes ~f:(fun t ->
                Datatype.mk_dt t.typ_name.txt
                @@ List.map t.typ_params
                     ~f:(fst >> MBcgen.sort_of_core_type dtenv))
          in
          let datatypes =
            List.map2_exn datatypes dttypes ~f:(fun dt ty ->
                match ty.typ_kind with
                | Ttype_variant tds ->
                    {
                      dt with
                      conses = List.map tds ~f:(MBcgen.cons_of dtenv datatypes);
                    }
                | _ -> dt)
          in
          List.map datatypes ~f:(fun dt ->
              Datatype.make (Datatype.name_of_dt dt) datatypes Datatype.FDt)
        in
        let dtenv = List.fold_left dts ~init:dtenv ~f:DTEnv.update_dt in
        update_dtenv dtenv;
        (* the declared result of each [eff] constructor, as EffCaml's
           generator records it ([Get : bool eff] gives [bool]) *)
        let op_results =
          List.fold dttypes ~init:envs.op_results ~f:(fun acc ty ->
              match (ty.typ_name.txt, ty.typ_kind) with
              | "eff", Ttype_variant tds ->
                  List.filter_map tds ~f:(fun cd ->
                      match cd.cd_res with
                      | Some { ctyp_desc = Ttyp_constr (_, _, [ index ]); _ } ->
                          Some
                            ( cd.cd_name.txt,
                              MBcgen.sort_of_core_type dtenv index )
                      | _ -> None)
              | _ -> acc)
        in
        { envs with dtenv; op_results }
    | Tstr_attribute attr -> (
        match attr.Parsetree.attr_name.txt with
        | "check_toplevel" ->
            let content = attr_content attr in
            let ta =
              let lb = Lexing.from_string content in
              HOMC.Parser.tree_automata HOMC.Lexer.token lb
            in
            {
              envs with
              checks = envs.checks @ [ (ta, List.length envs.items) ];
            }
        | "check" | "assert" -> refuse "[elab] [@@@check] is not implemented"
        | "automaton" -> refuse "[elab] [@@@automaton] is not supported"
        | _ -> envs)
    | Tstr_eval _ -> refuse "[elab] a top-level expression is not supported"
    | _ -> refuse "[elab] this structure item is not supported"

  (* [elaborate ps]: the elaborated program of a parsed structure, or the
     reason it is refused *)
  let elaborate (ps : Parsetree.structure) : (elaborated, string) Result.t =
    try
      let ts, _, _, _, _ =
        Typemod.type_structure (Compmisc.initial_env ()) ps
      in
      init_dtenv ();
      init_fenv ();
      init_dummy_term_senv ();
      MBcgen.ref_id := Map.Poly.empty;
      drawn := Set.Poly.empty;
      let envs =
        List.fold ts.str_items
          ~init:
            {
              items = [];
              checks = [];
              dtenv = get_dtenv ();
              senv = Map.Poly.empty;
              eff_ops = None;
              op_results = [];
            }
          ~f:of_struct_item
      in
      let program =
        {
          items = envs.items;
          eff_ops = envs.eff_ops;
          op_results = envs.op_results;
        }
      in
      (* (ii): a drawn binder must not be a binder the program wrote or a
         top-level name *)
      let program_binders =
        let rec c acc m =
          let bind acc (b : binder) =
            if Set.mem !drawn b.var then acc else Set.add acc b.var
          in
          let rec v acc = function
            | Fun (b, m) -> c (bind acc b) m
            | Tuple vs -> List.fold vs ~init:acc ~f:v
            | Var _ | Const _ -> acc
          in
          match m.desc with
          | Return x | Assert x -> v acc x
          | Let (b, m1, m2) -> c (c (bind acc b) m1) m2
          | App (f, a) -> v (v acc f) a
          | If (x, m1, m2) -> c (c (v acc x) m1) m2
          | Op (_, vs, _) -> List.fold vs ~init:acc ~f:v
          | Handle (h, m) ->
              let acc = c (c (bind acc (fst h.ret)) (snd h.ret)) m in
              List.fold h.clauses ~init:acc ~f:(fun acc cl ->
                  c (List.fold (cl.kont :: cl.params) ~init:acc ~f:bind) cl.body)
          | Fail | Rand _ | Event _ -> acc
        in
        List.fold program.items ~init:Set.Poly.empty ~f:(fun acc it ->
            c (Set.add acc it.name) it.body)
      in
      (match Set.find program_binders ~f:(Set.mem !drawn) with
      | Some x ->
          refuse "[elab] drawn binder %s collides with a program variable"
            (Ident.name_of_tvar x)
      | None -> ());
      Ok { program; checks = envs.checks }
    with
    | Refused msg -> Error msg
    | Failure msg -> Error ("[elab] " ^ msg)
    | Typemod.Error (loc, env, err) ->
        Error
          ("Typemod.Error:\n"
          ^ MBcgen.str_of_stdbuf ~f:Location.print_report
          @@ Typemod.report_error ~loc env err)
    | Typecore.Error (loc, env, err) ->
        Error
          ("Typecore.Error:\n"
          ^ MBcgen.str_of_stdbuf ~f:Location.print_report
          @@ Typecore.report_error ~loc env err)

  let parse_file filename =
    In_channel.with_file filename ~f:(fun ic ->
        let lexbuf = Lexing.from_channel ic in
        Lexing.set_filename lexbuf filename;
        Parse.implementation lexbuf)

  let parse_string str = Parse.implementation (Lexing.from_string str)

  let elaborate_file filename =
    elaborate
      (RCaml.EffectSyntax.desugar ~print:Debug.print (parse_file filename))

  let elaborate_string str =
    elaborate (RCaml.EffectSyntax.desugar ~print:Debug.print (parse_string str))
end
