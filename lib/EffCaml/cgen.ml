open Core
open Typedtree
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.Ident
open Ast.LogicOld
open HOMC
open Automata

let nt_of_tvar x = Ident.Tvar ("TL_" ^ Ident.name_of_tvar x)

let rec nt_of_pat = function
  | Pattern.PAny sort -> Pattern.PAny sort
  | Pattern.PVar (x, sort) -> Pattern.PVar (nt_of_tvar x, sort)
  | Pattern.PTuple pats -> Pattern.PTuple (List.map ~f:nt_of_pat pats)
  | Pattern.PCons (dt, n, pats) ->
      Pattern.PCons (dt (*ToDo*), n, List.map ~f:nt_of_pat pats)

let replace_any_tvar x =
  let name = Ident.name_of_tvar x in
  if String.is_prefix name ~prefix:"_" then
    Ident.mk_fresh_tvar ~prefix:(Some ("any" ^ name)) () (*ToDo*)
  else x

let rec replace_any_pat = function
  | Pattern.PAny sort -> Pattern.PAny sort
  | Pattern.PVar (x, sort) -> Pattern.PVar (replace_any_tvar x, sort)
  | Pattern.PTuple pats -> Pattern.PTuple (List.map ~f:replace_any_pat pats)
  | Pattern.PCons (dt, n, pats) ->
      Pattern.PCons (dt (*ToDo*), n, List.map ~f:replace_any_pat pats)

module Make (Config : Config.ConfigType) = struct
  let config = Config.config

  module MBcgen = RCaml.MBcgen.Make ((
    struct
      let config = RCaml.MBcgen.Config.{ verbose = config.verbose }
    end :
      RCaml.MBcgen.Config.ConfigType))

  module MBcsol = RCaml.MBcsol.Make ((
    struct
      let config =
        RCaml.MBcsol.Config.{ verbose = config.verbose; elim_pure = true }
    end :
      RCaml.MBcsol.Config.ConfigType))

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_module_name "Cgen"

  type item =
    | Skip
    | Check of (Ident.tvar * Ident.tvar RefType.t * TTA.pre_trs) list
    | CheckTopLevel of TreeAutomaton.t

  let rec env_of_pat = function
    | Pattern.PAny _, _sort -> Map.Poly.empty
    | Pattern.PVar (x, _sort1), sort2 ->
        (*print_endline (Term.str_of_sort sort1 ^ " vs " ^ Term.str_of_sort sort2);*)
        Map.Poly.singleton x sort2
    | Pattern.PTuple pats, T_tuple.STuple sorts ->
        Map.force_merge_list @@ List.map2_exn pats sorts ~f:(curry2 env_of_pat)
    | Pattern.PCons _, _ ->
        failwith
          "[env_of_pat] not reachable here because [let T x = ... in ...] is \
           parsed as [match ... with T x -> ...]"
    | _ -> failwith "[env_of_pat] unsupported pattern"

  let rec cps_type_of_dt dt =
    {
      dt with
      Datatype.conses =
        List.map (Datatype.conses_of_dt dt) ~f:(fun cons ->
            {
              cons with
              sels =
                List.map (Datatype.sels_of_cons cons) ~f:(function
                  | InSel (name, ret_name, params) ->
                      Datatype.InSel
                        (name, ret_name, List.map params ~f:cps_val_type_of)
                  | Sel (name, ret_sort) -> Sel (name, cps_val_type_of ret_sort));
            });
      params = List.map (Datatype.params_of_dt dt) ~f:cps_val_type_of;
    }

  and cps_opsig_of s = function
    | Sort.OpSig (map, _ (*ToDo*)) ->
        List.fold_right map ~init:s ~f:(fun (_, s1) s2 ->
            Sort.mk_arrow (cps_val_type_of s1) s2)
    | _ -> failwith "cps_opsig_of"

  and cps_cont_of s = function
    | Sort.EVar _ ->
        s
        (*ToDo*)
        (*failwith "evar not supported"*)
    | Sort.Pure -> (*ToDo*) s
    | Sort.Closed -> (*ToDo*) s
    | Sort.Eff (c1, c2) ->
        Sort.mk_arrow
          (Sort.mk_arrow s (cps_comp_type_of c1))
          (cps_comp_type_of c2)
    | _ -> failwith "unknown control effect"

  and cps_comp_type_of c =
    cps_opsig_of (cps_cont_of c.val_type c.cont_eff) c.op_sig

  and cps_val_type_of = function
    | ( Sort.SVar _ | T_bool.SBool | T_int.SInt | T_int.SRefInt | T_real.SReal
      | T_string.SString | T_sequence.SSequence _ | T_regex.SRegEx ) as s ->
        s
    | Sort.SArrow (s, c) ->
        Sort.mk_arrow (cps_val_type_of s) (cps_comp_type_of c)
    | Sort.SPoly (svs, s) -> Sort.SPoly (svs, cps_val_type_of s)
    | T_tuple.STuple sorts -> T_tuple.STuple (List.map ~f:cps_val_type_of sorts)
    | T_ref.SRef sort -> T_ref.SRef (cps_val_type_of sort)
    | T_dt.SDT t ->
        T_dt.SDT (Datatype.update_dt t (cps_type_of_dt (Datatype.dt_of t)))
    | T_dt.SUS (str, sorts) -> T_dt.SUS (str, List.map ~f:cps_val_type_of sorts)
    | T_array.SArray (s1, s2) ->
        T_array.SArray (cps_val_type_of s1, cps_val_type_of s2)
    | _ -> failwith "[cps_val_type_of] unknown sort"

  let term_unit = EHMTT.Term (Ident.Tvar "unit")
  let term_tt = EHMTT.Term (Ident.Tvar "tt")
  let term_ff = EHMTT.Term (Ident.Tvar "ff")
  let term_if = EHMTT.Term (Ident.Tvar "if")
  let term_fail = EHMTT.Term (Ident.Tvar "fail")
  let rterm_unit = RSFD.Term (Ident.Tvar "unit")
  let rterm_not = RSFD.Term (Ident.Tvar "not")
  let rterm_and = RSFD.Term (Ident.Tvar "and")
  let rterm_or = RSFD.Term (Ident.Tvar "or")
  let rterm_imply = RSFD.Term (Ident.Tvar "imply")
  let rterm_iff = RSFD.Term (Ident.Tvar "iff")

  let mk_tuple ts =
    EHMTT.apps
      (EHMTT.Term (Ident.Tvar ("tuple" ^ string_of_int @@ List.length ts)))
      ts

  let rec enum_values s =
    if Datatype.is_unit_sort s then [ term_unit ]
    else
      match s with
      | T_bool.SBool -> [ term_tt; term_ff ]
      | T_tuple.STuple sorts ->
          Vector.product mk_tuple @@ List.map sorts ~f:enum_values
      | _ -> [ term_unit ]
  (*ToDo*)

  let tl_handlers_of eff_map op_sig =
    let map =
      match op_sig with
      | Sort.OpSig (map, _) -> map
      | _ -> failwith "not supported"
    in
    List.unzip
    @@ List.map
         (match eff_map with Some eff_map -> eff_map | None -> map)
         ~f:(fun (op, sort) ->
           let sort = try ALMap.find_exn op map with _ -> sort in
           let nt = Ident.Tvar ("Top" ^ String.capitalize op) in
           let t = EHMTT.Term (Ident.Tvar ("op" ^ String.capitalize op)) in
           let k = Ident.Tvar "k" in
           ( (op, EHMTT.Nonterm nt),
             match Sort.args_of sort with
             | [ Sort.SArrow (sret, _) ] ->
                 ( nt,
                   ( [ k ],
                     EHMTT.apps t
                       (List.map (enum_values sret)
                          ~f:(EHMTT.app (EHMTT.mk_var k))) ) )
             | [ _sarg; Sort.SArrow (sret, _) ] ->
                 let x = Ident.Tvar "x" in
                 ( nt,
                   ( [ x; k ],
                     EHMTT.apps t
                       (EHMTT.mk_var x
                       :: List.map (enum_values sret)
                            ~f:(EHMTT.app (EHMTT.mk_var k))) ) )
             | _ ->
                 failwith
                   (sprintf "[tl_handlers_of] %s not supported"
                      (Term.str_of_sort sort)) ))

  type ctx = {
    maps : opsig_subst * sort_subst * eff_subst;
    args : tvar list;
    senv : (tvar, Sort.t) Core.Map.Poly.t;
    ntenv : (tvar, EHMTT.term) Core.Map.Poly.t;
    ty : Sort.c;
    conts_opt : ((string * EHMTT.term) list * EHMTT.term) option;
    num_conts : int;
  }

  let cgen_let eff_map tl_hs_nts (tl_nt, tl_args) _fenv _dtenv ntenv is_rec pats
      (is_pures, next1s, c1s) maps senv =
    let pats = List.map pats ~f:replace_any_pat in
    let pat_senvs, tl_pat_senvs, cs =
      List.unzip3
      @@ List.map3_exn is_pures pats c1s ~f:(fun is_pure pat c ->
             ( env_of_pat (pat, c.Sort.val_type),
               (if is_pure then Some (env_of_pat (nt_of_pat pat, c.val_type))
                else None),
               c ))
    in
    let ntenv_body =
      List.fold_left ~init:ntenv (List.zip_exn is_pures pats) ~f:(fun ntenv ->
        function
        | is_pure, PVar (x, _s) ->
            if is_pure then
              let data =
                EHMTT.apps
                  (EHMTT.Nonterm (nt_of_tvar x))
                  (List.map tl_args ~f:(fst >> EHMTT.mk_var))
              in
              Map.Poly.add_exn ntenv ~key:x ~data
            else ntenv
        | _ -> failwith "not supported")
    in
    let (tl_rules', tl_args', tl_nt'), rules, senv_aux =
      let senv_bound =
        if is_rec then
          Map.update_with senv
          @@ Map.force_merge_list
               (* assume distinct *)
               (pat_senvs
               @ List.map ~f:(Map.Poly.map ~f:cps_val_type_of)
               @@ List.filter_map ~f:Fn.id tl_pat_senvs)
        else senv
      in
      let ntenv_bound = if is_rec then ntenv_body else ntenv in
      List.fold_left
        ~init:(([], tl_args, tl_nt), [], Map.Poly.empty)
        (List.zip_exn pats (List.zip3_exn is_pures next1s cs))
        ~f:(fun
            ((tl_rules0, tl_args0, tl_nt0), rules0, senv0)
            (pat, (is_pure, next, c))
          ->
          match pat with
          | PVar (x, s) ->
              if is_pure then
                let term, rules =
                  next
                    {
                      maps;
                      args = List.map ~f:fst tl_args;
                      senv = senv_bound;
                      ntenv = ntenv_bound;
                      ty = c;
                      conts_opt = None;
                      num_conts = 0;
                    }
                in
                ( (tl_rules0, tl_args0, tl_nt0),
                  rules0
                  @ (nt_of_tvar x, (List.map ~f:fst tl_args, term))
                    :: List.map rules ~f:(fun ((nt, _sort), body) -> (nt, body)),
                  Map.force_merge senv0 @@ Map.Poly.of_alist_exn
                  @@ List.map rules ~f:fst )
              else
                let tl_nt = Ident.mk_fresh_tvar ~prefix:(Some "TL") () in
                Debug.print
                @@ lazy
                     ("generating a top level handler of "
                    ^ Ident.name_of_tvar x ^ " : " ^ Term.str_of_triple c);
                let hs, tl_hs_rules = tl_handlers_of eff_map c.op_sig in
                let term, rules =
                  next
                    {
                      maps;
                      args = List.map ~f:fst tl_args;
                      senv = senv_bound;
                      ntenv = ntenv_bound;
                      ty = c;
                      conts_opt =
                        Some
                          ( ALMap.of_alist_exn hs,
                            EHMTT.apps (EHMTT.Nonterm tl_nt)
                              (List.map ~f:(fst >> EHMTT.mk_var) tl_args0) );
                      num_conts = 1;
                    }
                in
                let tl_nt0_sort =
                  Sort.mk_fun
                    (List.map tl_args0 ~f:(snd >> cps_val_type_of)
                    @ [ Datatype.mk_unit_sort () ])
                in
                ( ( tl_rules0
                    @ [ (tl_nt0, (List.map ~f:fst tl_args0, term)) ]
                    @ List.map rules ~f:(fun ((nt, _sort), body) -> (nt, body))
                    @ (*ToDo*)
                    List.filter tl_hs_rules
                      ~f:
                        (fst
                        >> List.mem ~equal:Ident.tvar_equal tl_hs_nts
                        >> not),
                    tl_args0 @ [ (x, s) ],
                    tl_nt ),
                  rules0,
                  Map.force_merge senv0
                    (Map.Poly.of_alist_exn
                    @@ ((tl_nt0, tl_nt0_sort) :: List.map rules ~f:fst)) )
          | _ -> failwith "not supported")
    in
    let senv_body =
      Map.update_with senv (*shadowing*)
      @@ Map.force_merge senv_aux @@ Map.force_merge_list
      @@ (* assume the following are distinct *)
      (if
         (* generalizable? *)
         List.for_all is_pures ~f:Fn.id
         && List.for_all pats ~f:(Pattern.sort_of >> Sort.is_arrow)
       then List.map ~f:(Map.Poly.map ~f:(Typeinf.generalize senv))
       else Fn.id)
        (pat_senvs
        @ List.map ~f:(Map.Poly.map ~f:cps_val_type_of)
        @@ List.filter_map ~f:Fn.id tl_pat_senvs)
    in
    ((ntenv_body, tl_rules', tl_nt', tl_args'), rules, senv_body)

  let sort_of_either = function
    | First (_, _, c) -> c.Sort.val_type
    | Second (_, sort) -> sort

  let apply_cont_if_any conts_opt term =
    match conts_opt with None -> term | Some (_hs, k) -> EHMTT.app k term

  let lookup ntenv x =
    match Map.Poly.find ntenv x with None -> EHMTT.mk_var x | Some nt -> nt

  (*let cgen_either maps args senv ntenv ty conts_opt = function
    | First (_pure, next, _) -> next maps args senv ty conts_opt
    | Second (x, sort) -> (
        match Map.Poly.find senv x with
        | Some _ -> apply_cont_if_any conts_opt (lookup ntenv x)
        | None ->
            failwith
            @@ sprintf "[cgen_either] unbound variable: %s : %s\nsenv = %s"
                 (name_of_tvar x) (Term.str_of_sort sort) (*Env.str_of senv*) ""
        )*)

  let update_conts conts_opt k args =
    match conts_opt with
    | None -> failwith "continuations are not passed"
    | Some (hs, _) ->
        Some (hs, EHMTT.apps (EHMTT.Nonterm k) (List.map args ~f:EHMTT.mk_var))

  let cgen_expr eff_map _fenv0 dtenv0 senv0 (expr : expression) =
    let get_ops op_sig =
      match eff_map with
      | Some eff_map ->
          (*ToDo*)
          List.map eff_map ~f:fst
      | None -> (
          match op_sig with
          | Sort.OpSig (map, _) -> List.map map ~f:fst
          | _ -> assert false)
    in
    let from_opsig hs op_sig =
      let ops = get_ops op_sig in
      List.map ops ~f:(fun op ->
          try (op, ALMap.find_exn op hs)
          with Stdlib.Not_found -> failwith (op ^ " handler not passed"))
    in
    let get_map op_sig =
      match eff_map with
      | Some eff_map -> (*ToDo*) eff_map
      | None -> (
          match op_sig with Sort.OpSig (map, _) -> map | _ -> assert false)
    in
    let gen_hts op_sig =
      let map = get_map op_sig in
      List.unzip3
      @@ List.map map ~f:(fun (name, sort) ->
             let h = Ident.mk_fresh_tvar ~prefix:(Some "h") () in
             ((name, EHMTT.mk_var h), h, sort))
    in
    MBcgen.fold_expr dtenv0 senv0 expr
      ~f:
        (object
           method f_annot (attrs, next) ctx =
             ignore (attrs, next, ctx);
             failwith "[effcaml:annot] annotation not supported"

           method f_unif (next, sort) ctx =
             ignore (next, sort, ctx);
             failwith "[effcaml:unif] uniform distribution not supported"

           method f_var (x, sort) ctx =
             let xt = lookup ctx.ntenv x in
             let sort = Term.subst_sort ctx.maps sort in
             (* *)
             Debug.print
             @@ lazy
                  (sprintf "[effcaml:var] %s : %s <: %s\n" (name_of_tvar x)
                     (Term.str_of_sort sort)
                     (Term.str_of_triple ctx.ty));
             (apply_cont_if_any ctx.conts_opt @@ xt, [])

           method f_const term ctx =
             let term = Term.subst_all ctx.maps term in
             (* *)
             Debug.print
             @@ lazy
                  (sprintf "[effcaml:const] %s : %s\n" (Term.str_of term)
                     (Term.str_of_triple ctx.ty));
             let term =
               try
                 EHMTT.Nonterm
                   (Ident.Tvar
                      (match
                         Ident.name_of_tvar @@ fst @@ fst @@ Term.let_var term
                       with
                      | "Stdlib.=" -> "Iff"
                      | "Stdlib.<>" -> "Xor"
                      | "Stdlib.not" -> "Not"
                      | "Stdlib.&&" | "Stdlib.&" -> "And"
                      | "Stdlib.||" | "Stdlib.or" -> "Or"
                      | _ ->
                          failwith
                            (sprintf "[cgen_expr] %s not supported"
                               (Term.str_of term))))
               with _ ->
                 if T_bool.is_true term then term_tt
                 else if T_bool.is_false term then term_ff
                 else
                   failwith
                     (sprintf "[cgen_expr] %s not supported" (Term.str_of term))
             in
             (apply_cont_if_any ctx.conts_opt term, [])

           method f_construct dt cons_name nexts_either ctx =
             let dt = Datatype.subst ctx.maps dt in
             let nexts_either =
               List.map nexts_either ~f:(MBcgen.subst_all_either ctx.maps)
             in
             (* *)
             Debug.print
             @@ lazy
                  (sprintf "[effcaml:constructor] (%s : %s) (...) <: %s\n"
                     (Datatype.str_of dt) cons_name
                     (Term.str_of_triple ctx.ty));
             if List.is_empty nexts_either then
               let term =
                 match cons_name with
                 | "()" -> term_unit
                 | s ->
                     failwith
                       (sprintf "[cgen_expr] constructor %s not supported" s)
               in
               (apply_cont_if_any ctx.conts_opt term, [])
             else failwith "a constructor with arguments is not allowed"

           method f_apply (_pure1, next1, opsig1s, opsig1, cont1s, cont1)
               next2s_either ctx =
             let opsig1s = List.map opsig1s ~f:(Term.subst_opsig ctx.maps) in
             let opsig1 = Term.subst_opsig ctx.maps opsig1 in
             let cont1s = List.map cont1s ~f:(Term.subst_cont ctx.maps) in
             let cont1 = Term.subst_cont ctx.maps cont1 in
             let next2s_either =
               List.map next2s_either ~f:(MBcgen.subst_all_either ctx.maps)
             in
             (* *)
             Debug.print
             @@ lazy
                  (sprintf "[effcaml:apply] %s\n" (Term.str_of_triple ctx.ty));
             let xs2, ts2, ruless =
               List.unzip3
               @@ List.map next2s_either ~f:(function
                    | First (pure, next, ty) ->
                        if pure then
                          let t, rs = next { ctx with ty; conts_opt = None } in
                          (None, t, rs)
                        else
                          let x = Ident.mk_fresh_tvar ~prefix:(Some "arg") () in
                          (Some (x, ty.val_type), EHMTT.mk_var x, [])
                    | Second (x, _sort) -> (None, lookup ctx.ntenv x, []))
             in
             let term, rules =
               match ctx.conts_opt with
               | None -> failwith "continuations are not passed"
               | Some (hs, k_nt) ->
                   let ys = List.filter_map ~f:Fn.id xs2 in
                   let k_nt, rules =
                     List.mapi ts2 ~f:(fun i t ->
                         ( List.nth_exn opsig1s i,
                           Ident.mk_fresh_tvar ~prefix:(Some "Karg") (),
                           t ))
                     |> List.fold_right
                          ~init:(k_nt, List.concat ruless)
                          ~f:(fun (opsig, k, t2) (k_nt, rules) ->
                            let rule_papp =
                              let papp =
                                Ident.mk_fresh_tvar ~prefix:(Some "papp") ()
                              in
                              let f_sort = Sort.mk_fresh_svar () (*ToDo*) in
                              let k_sort =
                                Sort.mk_fun
                                  (List.map ctx.args
                                     ~f:(Map.Poly.find_exn ctx.senv)
                                  @ List.map ~f:snd ys
                                  @ [ f_sort; Datatype.mk_unit_sort () ])
                              in
                              let k_args =
                                ctx.args @ List.map ~f:fst ys @ [ papp ]
                              in
                              let k_body =
                                EHMTT.apps (EHMTT.mk_var papp)
                                  ((t2 :: (ALMap.data @@ from_opsig hs opsig))
                                  @ [ k_nt ])
                              in
                              ((k, k_sort), (k_args, k_body))
                            in
                            ( EHMTT.apps (EHMTT.Nonterm k)
                                (List.map ~f:EHMTT.mk_var
                                   (ctx.args @ List.map ~f:fst ys)),
                              rule_papp :: rules ))
                   in
                   let t1, rules1 =
                     next1
                       {
                         ctx with
                         args = ctx.args @ List.map ~f:fst ys;
                         senv =
                           Map.update_with ctx.senv (Map.Poly.of_alist_exn ys);
                         ty =
                           LogicOld.Sort.mk_eff_fun ~opsig:opsig1
                             ~opsigs:(Some opsig1s) ~cont:cont1
                             ~conts:(Some cont1s)
                             (List.map next2s_either ~f:sort_of_either) (*ToDo*)
                             ctx.ty;
                         conts_opt = Some (from_opsig hs opsig1, k_nt);
                       }
                   in
                   (t1, rules1 @ rules)
             in
             snd
             @@ List.fold_right2_exn xs2 next2s_either
                  ~init:(List.filter_map ~f:Fn.id xs2, (term, rules))
                  ~f:(fun x next (xs, (k_body, rules)) ->
                    match (x, next) with
                    | None, (First (true, _, _) | Second (_, _)) ->
                        (xs, (term, rules))
                    | Some _, First (false, next, c) ->
                        let k = Ident.mk_fresh_tvar ~prefix:(Some "Kapp") () in
                        let k_rule =
                          let k_sort =
                            Sort.mk_fun
                              (List.map ctx.args ~f:(Map.Poly.find_exn ctx.senv)
                              @ List.map ~f:snd xs
                              @ [ Datatype.mk_unit_sort () ])
                          in
                          let k_args = ctx.args @ List.map ~f:fst xs in
                          ((k, k_sort), (k_args, k_body))
                        in
                        let xs_ini = List.initial xs in
                        let term', rules' =
                          next
                            {
                              ctx with
                              args = ctx.args @ List.map ~f:fst xs_ini;
                              senv =
                                Map.update_with ctx.senv
                                  (Map.Poly.of_alist_exn xs_ini);
                              ty = c;
                              conts_opt =
                                (* ToDo: c.op_sig and ctx.conts_opt are consistent? *)
                                update_conts ctx.conts_opt k
                                  (ctx.args @ List.map ~f:fst xs_ini);
                            }
                        in
                        (xs_ini, (term', rules' @ (k_rule :: rules)))
                    | _ -> assert false)

           method f_tuple nexts_either ctx =
             let nexts_either =
               List.map nexts_either ~f:(MBcgen.subst_all_either ctx.maps)
             in
             (* *)
             Debug.print
             @@ lazy
                  (sprintf "[effcaml:tuple] (...) : %s\n"
                     (Term.str_of_triple ctx.ty));
             let xs, ts, ruless =
               List.unzip3
               @@ List.map nexts_either ~f:(function
                    | First (pure, next, ty) ->
                        if pure then
                          let t, rs = next { ctx with ty; conts_opt = None } in
                          (None, t, rs)
                        else
                          let x =
                            Ident.mk_fresh_tvar ~prefix:(Some "elem") ()
                          in
                          (Some (x, ty.Sort.val_type), EHMTT.mk_var x, [])
                    | Second (x, _sort) -> (None, lookup ctx.ntenv x, []))
             in
             let term = apply_cont_if_any ctx.conts_opt @@ mk_tuple ts in
             snd
             @@ List.fold_right2_exn xs nexts_either
                  ~init:(List.filter_map ~f:Fn.id xs, (term, List.concat ruless))
                  ~f:(fun x next (xs, (k_body, rules)) ->
                    match (x, next) with
                    | None, (First (true, _, _) | Second (_, _)) ->
                        (xs, (term, rules))
                    | Some _, First (false, next, c) ->
                        let k = Ident.mk_fresh_tvar ~prefix:(Some "Ktup") () in
                        let k_rule =
                          let k_sort =
                            Sort.mk_fun
                              (List.map ctx.args ~f:(Map.Poly.find_exn ctx.senv)
                              @ List.map ~f:snd xs
                              @ [ Datatype.mk_unit_sort () ])
                          in
                          let k_args = ctx.args @ List.map ~f:fst xs in
                          ((k, k_sort), (k_args, k_body))
                        in
                        let xs_ini = List.initial xs in
                        let term', rules' =
                          next
                            {
                              ctx with
                              args = ctx.args @ List.map ~f:fst xs_ini;
                              senv =
                                Map.update_with ctx.senv
                                  (Map.Poly.of_alist_exn xs_ini);
                              ty = c;
                              conts_opt =
                                (* ToDo: c.op_sig and ctx.conts_opt are consistent? *)
                                update_conts ctx.conts_opt k
                                  (ctx.args @ List.map ~f:fst xs_ini);
                            }
                        in
                        (xs_ini, (term', rules' @ (k_rule :: rules)))
                    | _ -> assert false)

           method f_function pats _t_annot_rty_opt (nexts, conts) ctx =
             let pats = List.map pats ~f:(Pattern.subst_sort ctx.maps) in
             let conts = List.map conts ~f:(Term.subst_cont ctx.maps) in
             (* *)
             Debug.print
             @@ lazy
                  (sprintf "[effcaml:function] %s\n"
                  @@ Term.str_of_triple ctx.ty);
             let nt = Ident.mk_fresh_tvar ~prefix:(Some "Lam") () in
             match ctx.ty.val_type with
             | Sort.SArrow (t, c) (*ToDo: should be Pure?*) -> (
                 match (pats, nexts, conts) with
                 | [ pat ], [ next ], [ cont ] ->
                     let x =
                       match pat with
                       | Pattern.PAny _ | Pattern.PCons (_, "()" (*ToDo*), [])
                         ->
                           Ident.mk_fresh_tvar ~prefix:(Some "any") () (*ToDo*)
                       | Pattern.PVar (x, _sort) -> replace_any_tvar x
                       | _ ->
                           failwith
                             (sprintf "[cgen_expr] %s not supported"
                                (Pattern.str_of pat))
                     in
                     let hts, hs, hsorts = gen_hts c.op_sig in
                     let ini_ans_type, fin_ans_type =
                       match cont with
                       | Sort.Eff (c1, c2) -> (c1, c2)
                       | _ ->
                           if true then failwith "not supported"
                           else
                             (*ToDo*)
                             let s =
                               Sort.mk_triple_from_sort (Sort.mk_fresh_svar ())
                             in
                             (s, s)
                     in
                     let ksort = Sort.SArrow (c.val_type, ini_ans_type) in
                     let k = Ident.mk_fresh_tvar ~prefix:(Some "k") () in
                     let body, rules =
                       next
                         {
                           ctx with
                           args = ctx.args @ (x :: hs) @ [ k ];
                           senv =
                             Map.update_with ctx.senv
                               (Map.Poly.of_alist_exn
                               @@ (x, t) :: (k, ksort) :: List.zip_exn hs hsorts
                               );
                           ty = { c with cont_eff = cont (*ToDo: c.cont_eff*) };
                           conts_opt =
                             Some (ALMap.of_alist_exn hts, EHMTT.mk_var k);
                           num_conts = Sort.num_conts c.cont_eff;
                         }
                     in
                     let sort =
                       Sort.mk_eff_fun
                         (List.map ctx.args ~f:(fun x ->
                              match Map.Poly.find ctx.senv x with
                              | Some r -> r
                              | None ->
                                  failwith (Ident.name_of_tvar x ^ " not found"))
                         @ [ t ] @ hsorts @ [ ksort ])
                         fin_ans_type
                     in
                     ( apply_cont_if_any ctx.conts_opt
                       @@ EHMTT.apps (EHMTT.Nonterm nt)
                            (List.map ctx.args ~f:EHMTT.mk_var),
                       ( (nt, (*ToDo*) sort.val_type),
                         (ctx.args @ [ x ] @ hs @ [ k ], body) )
                       :: rules )
                 | _ -> failwith "pattern matching not supported")
             | _ -> failwith "f_function"

           method f_ite (next1, cont1) (next2, cont2) next3_opt ctx =
             let cont1 = Term.subst_cont ctx.maps cont1 in
             let cont2 = Term.subst_cont ctx.maps cont2 in
             let next3_opt = MBcgen.subst_all_opt ctx.maps next3_opt in
             (* *)
             Debug.print
             @@ lazy
                  (sprintf "[effcaml:ite] %s [%d]\n"
                     (Term.str_of_triple ctx.ty)
                     ctx.num_conts);
             let k = Ident.mk_fresh_tvar ~prefix:(Some "Kite") () in
             let x = Ident.mk_fresh_tvar ~prefix:(Some "cond") () in
             let term, rules1 =
               next1
                 {
                   ctx with
                   ty =
                     Sort.
                       {
                         op_sig = ctx.ty.op_sig;
                         val_type = T_bool.SBool;
                         cont_eff = cont1;
                       };
                   conts_opt = update_conts ctx.conts_opt k ctx.args;
                 }
             in
             let args_eta_exp =
               let map =
                 List.map (get_map ctx.ty.op_sig) ~f:(fun (_, s) ->
                     (Ident.mk_fresh_tvar ~prefix:(Some "h") (), s))
               in
               List.concat
               @@ List.init (ctx.num_conts - 1) ~f:(fun _ ->
                      map
                      @ [
                          ( Ident.mk_fresh_tvar ~prefix:(Some "k") (),
                            Sort.mk_fresh_svar () );
                        ])
             in
             let then_t, rules2 =
               let t, rules =
                 next2 { ctx with ty = Sort.{ ctx.ty with cont_eff = cont2 } }
               in
               ( EHMTT.apps t (List.map args_eta_exp ~f:(fst >> EHMTT.mk_var)),
                 rules )
             in
             let else_t, rules3 =
               match next3_opt with
               | None -> (term_unit, [])
               | Some (next3, cont3) ->
                   let t, rules =
                     next3
                       { ctx with ty = Sort.{ ctx.ty with cont_eff = cont3 } }
                   in
                   ( EHMTT.apps t
                       (List.map args_eta_exp ~f:(fst >> EHMTT.mk_var)),
                     rules )
             in
             let k_rule =
               let k_sort =
                 Sort.mk_fun
                   (List.map ctx.args ~f:(Map.Poly.find_exn ctx.senv)
                   @ (T_bool.SBool :: List.map ~f:snd args_eta_exp)
                   @ [ Datatype.mk_unit_sort () ])
               in
               let k_args = ctx.args @ (x :: List.map ~f:fst args_eta_exp) in
               let k_body =
                 EHMTT.apps term_if [ EHMTT.mk_var x; then_t; else_t ]
               in
               ((k, k_sort), (k_args, k_body))
             in
             (term, rules1 @ (k_rule :: rules2) @ rules3)

           method f_match next1_either pats (nexts, effs) ctx =
             let pats = List.map pats ~f:(Pattern.subst_sort ctx.maps) in
             let effs = List.map effs ~f:(Term.subst_cont ctx.maps) in
             let next1_either = MBcgen.subst_all_either ctx.maps next1_either in
             (* *)
             ignore (next1_either, pats, nexts, effs, ctx);
             failwith "[effcaml:match] match expressions not supported"

           method f_assert (next_opt, cont) ctx =
             let cont = Term.subst_cont ctx.maps cont in
             (* *)
             let args_eta_exp =
               let map =
                 List.map (get_map ctx.ty.op_sig) ~f:(fun (_, s) ->
                     (Ident.mk_fresh_tvar ~prefix:(Some "h") (), s))
               in
               List.concat
               @@ List.init (ctx.num_conts - 1) ~f:(fun _ ->
                      map
                      @ [
                          ( Ident.mk_fresh_tvar ~prefix:(Some "k") (),
                            Sort.mk_fresh_svar () );
                        ])
             in
             match (next_opt, args_eta_exp) with
             | None, [] ->
                 Debug.print
                 @@ lazy
                      (sprintf "[effcaml:assert] assert false [%d] : %s\n"
                         ctx.num_conts
                         (Term.str_of_triple ctx.ty));
                 (term_fail, [])
             | None, _ ->
                 Debug.print
                 @@ lazy
                      (sprintf "[effcaml:assert] assert false [%d] : %s\n"
                         ctx.num_conts
                         (Term.str_of_triple ctx.ty));
                 let k = Ident.mk_fresh_tvar ~prefix:(Some "Kasr") () in
                 ( EHMTT.Nonterm k,
                   [
                     ( ( k,
                         Sort.mk_fun
                           (List.map ~f:snd args_eta_exp
                           @ [ Datatype.mk_unit_sort () ]) ),
                       (List.map ~f:fst args_eta_exp, term_fail) );
                   ] )
             | Some next, _ ->
                 Debug.print
                 @@ lazy
                      (sprintf "[effcaml:assert] assert ... [%d] : %s\n"
                         ctx.num_conts
                         (Term.str_of_triple ctx.ty));
                 let k = Ident.mk_fresh_tvar ~prefix:(Some "Kasr") () in
                 let x = Ident.mk_fresh_tvar ~prefix:(Some "cond") () in
                 let term, rules =
                   next
                     {
                       ctx with
                       ty =
                         Sort.
                           {
                             op_sig = ctx.ty.op_sig;
                             val_type = T_bool.SBool;
                             cont_eff = cont;
                           };
                       conts_opt = update_conts ctx.conts_opt k ctx.args;
                     }
                 in
                 ( term,
                   rules
                   @ [
                       ( ( k,
                           Sort.mk_fun
                             (List.map ctx.args ~f:(Map.Poly.find_exn ctx.senv)
                             @ (T_bool.SBool :: List.map ~f:snd args_eta_exp)
                             @ [ Datatype.mk_unit_sort () ]) ),
                         ( ctx.args @ (x :: List.map ~f:fst args_eta_exp),
                           EHMTT.apps term_if
                             [
                               EHMTT.mk_var x;
                               EHMTT.apps
                                 (apply_cont_if_any ctx.conts_opt term_unit)
                                 (List.map args_eta_exp ~f:(fst >> EHMTT.mk_var));
                               term_fail;
                             ] ) );
                     ] )

           method f_let_and is_rec pats defs (next2, cont2) ctx =
             let pats = List.map pats ~f:(Pattern.subst_sort ctx.maps) in
             let defs =
               let is_pure1s, is_fun1s, next1s, sort1s, cont1s = defs in
               ( is_pure1s,
                 is_fun1s,
                 next1s,
                 List.map2_exn sort1s cont1s ~f:(fun sort1 cont1 ->
                     Sort.
                       {
                         op_sig = ctx.ty.op_sig;
                         val_type = Term.subst_sort ctx.maps sort1;
                         cont_eff = Term.subst_cont ctx.maps cont1;
                       }) )
             in
             let cont2 = Term.subst_cont ctx.maps cont2 in
             (* *)
             match (is_rec, pats, defs) with
             | true, _, _ -> failwith "recursive inner functions not supported"
             | false, [ pat ], ([ _is_pure1 ], [ _is_fun1 ], [ next1 ], [ c1 ])
               ->
                 Debug.print
                 @@ lazy
                      (sprintf "[effcaml:let_and] %s\n"
                      @@ Term.str_of_triple ctx.ty);
                 let k = Ident.mk_fresh_tvar ~prefix:(Some "Klet") () in
                 let term1, rules1 =
                   next1
                     {
                       ctx with
                       ty = c1;
                       conts_opt = update_conts ctx.conts_opt k ctx.args;
                     }
                 in
                 let c2 = Sort.{ ctx.ty with cont_eff = cont2 } in
                 let (term2, rules2), x =
                   match pat with
                   | Pattern.PAny _ | Pattern.PCons (_, "()" (*ToDo*), []) ->
                       ( next2 { ctx with ty = c2 },
                         Ident.mk_fresh_tvar ~prefix:(Some "any") () )
                   | Pattern.PVar (x, s) ->
                       let args, senv =
                         let name = Ident.name_of_tvar x in
                         if String.is_prefix name ~prefix:"_" then
                           (ctx.args, ctx.senv)
                         else
                           ( ctx.args @ [ x ],
                             Map.update_with ctx.senv (Map.Poly.singleton x s)
                           )
                       in
                       ( next2 { ctx with args; senv; ty = c2 },
                         replace_any_tvar x )
                   | _ ->
                       failwith
                         (sprintf "[cgen_expr] %s not supported"
                            (Pattern.str_of pat))
                 in
                 ( term1,
                   rules1 @ rules2
                   @ [
                       ( ( k,
                           Sort.mk_fun
                             (List.map ctx.args ~f:(Map.Poly.find_exn ctx.senv)
                             @ [ c1.val_type; Datatype.mk_unit_sort () ]) ),
                         (ctx.args @ [ x ], term2) );
                     ] )
             | _, _, _ -> failwith "simultaneous definition not supported"

           method f_sequence (next1, sort1, cont1) (next2, cont2) ctx =
             let sort1 = Term.subst_sort ctx.maps sort1 in
             let cont1 = Term.subst_cont ctx.maps cont1 in
             let cont2 = Term.subst_cont ctx.maps cont2 in
             (* *)
             Debug.print
             @@ lazy
                  (sprintf "[effcaml:sequence] %s\n"
                  @@ Term.str_of_triple ctx.ty);
             let k = Ident.mk_fresh_tvar ~prefix:(Some "Kseq") () in
             let u = Ident.mk_fresh_tvar ~prefix:(Some "seq") () in
             let term1, rules1 =
               next1
                 {
                   ctx with
                   ty =
                     Sort.
                       {
                         op_sig = ctx.ty.op_sig;
                         val_type = sort1;
                         cont_eff = cont1;
                       };
                   conts_opt = update_conts ctx.conts_opt k ctx.args;
                 }
             in
             let term2, rules2 =
               next2 { ctx with ty = { ctx.ty with cont_eff = cont2 } }
             in
             ( term1,
               rules1
               @ ( ( k,
                     Sort.mk_fun
                       (List.map ctx.args ~f:(Map.Poly.find_exn ctx.senv)
                       @ [ Datatype.mk_unit_sort (); Datatype.mk_unit_sort () ]
                       ) ),
                   (ctx.args @ [ u ], term2) )
                 :: rules2 )

           method f_shift0 (x_opt, sort) (next2, c2) ctx =
             let sort = Term.subst_sort ctx.maps sort in
             let c2 = Term.subst_triple ctx.maps c2 in
             (* *)
             ignore (x_opt, sort, next2, c2, ctx);
             failwith "[effcaml:shift0] shift0 not supported"

           method f_reset (next1, sort1) ctx =
             let sort1 = Term.subst_sort ctx.maps sort1 in
             (* *)
             ignore (sort1, next1, ctx);
             failwith "[effcaml:reset] reset not supported"

           method f_perform _attrs name sort_op_applied nexts_either ctx =
             let sort_op_applied = Term.subst_sort ctx.maps sort_op_applied in
             let nexts_either =
               List.map nexts_either ~f:(MBcgen.subst_all_either ctx.maps)
             in
             (* *)
             Debug.print
             @@ lazy
                  (sprintf "[effcaml:peform] (%s : %s)(...) : %s\n"
                     (Term.str_of_sort sort_op_applied)
                     name
                     (Term.str_of_triple ctx.ty));
             let xs, ts, ruless =
               List.unzip3
               @@ List.map nexts_either ~f:(function
                    | First (pure, next, ty) ->
                        if pure then
                          let t, rs = next { ctx with ty; conts_opt = None } in
                          (None, t, rs)
                        else
                          let x =
                            Ident.mk_fresh_tvar ~prefix:(Some "elem") ()
                          in
                          (Some (x, ty.val_type), EHMTT.mk_var x, [])
                    | Second (x, _sort) -> (None, lookup ctx.ntenv x, []))
             in
             let term =
               match ctx.conts_opt with
               | None -> failwith "continuations are not passed"
               | Some (hs, k) -> (
                   try EHMTT.apps (ALMap.find_exn name hs) (ts @ [ k ])
                   with Stdlib.Not_found ->
                     failwith (name ^ " handler not passed"))
             in
             snd
             @@ List.fold_right2_exn xs nexts_either
                  ~init:(List.filter_map ~f:Fn.id xs, (term, List.concat ruless))
                  ~f:(fun x next (xs, (k_body, rules)) ->
                    match (x, next) with
                    | None, (First (true, _, _) | Second (_, _)) ->
                        (xs, (term, rules))
                    | Some _, First (false, next, c) ->
                        let k = Ident.mk_fresh_tvar ~prefix:(Some "Kpfm") () in
                        let k_rule =
                          let k_sort =
                            Sort.mk_fun
                              (List.map ctx.args ~f:(Map.Poly.find_exn ctx.senv)
                              @ List.map ~f:snd xs
                              @ [ Datatype.mk_unit_sort () ])
                          in
                          let k_args = ctx.args @ List.map ~f:fst xs in
                          ((k, k_sort), (k_args, k_body))
                        in
                        let xs_ini = List.initial xs in
                        let term', rules' =
                          next
                            {
                              ctx with
                              args = ctx.args @ List.map ~f:fst xs_ini;
                              senv =
                                Map.update_with ctx.senv
                                  (Map.Poly.of_alist_exn xs_ini);
                              ty = c;
                              conts_opt =
                                (* ToDo: c.op_sig and ctx.conts_opt are consistent? *)
                                update_conts ctx.conts_opt k
                                  (ctx.args @ List.map ~f:fst xs_ini);
                            }
                        in
                        (xs_ini, (term', rules' @ (k_rule :: rules)))
                    | _ -> assert false)

           method f_handling (next_b, c_b) (next_r, xr, c_r) op_names nexts
               clauses ctx =
             let c_b = Term.subst_triple ctx.maps c_b in
             let c_r = Term.subst_triple ctx.maps c_r in
             let clauses =
               List.map clauses ~f:(fun (x_args, sort_args, k_opt, sort_k, c) ->
                   ( x_args,
                     List.map ~f:(Term.subst_sort ctx.maps) sort_args,
                     k_opt,
                     Term.subst_sort ctx.maps sort_k,
                     Term.subst_triple ctx.maps c ))
             in
             (* *)
             let xr = replace_any_tvar xr in
             let clauses =
               List.map clauses ~f:(fun (x_args, sort_args, k_opt, sort_k, c) ->
                   ( List.map ~f:replace_any_tvar x_args,
                     sort_args,
                     Option.map ~f:replace_any_tvar k_opt,
                     sort_k,
                     c ))
             in
             (* *)
             Debug.print
             @@ lazy
                  (sprintf
                     "[effcaml:handling] handle %s with { ret : %s; ... } : %s\n"
                     (Term.str_of_triple c_b) (Term.str_of_triple c_r)
                     (Term.str_of_triple ctx.ty));
             let term_r, rules_r =
               let ksort = Sort.mk_fresh_svar () (*ToDo*) in
               let k = Ident.mk_fresh_tvar ~prefix:(Some "k") () in
               let hts, hs, hsorts = gen_hts c_r.op_sig in
               let term_r, rules_r =
                 next_r
                   {
                     ctx with
                     args = ctx.args @ (xr :: hs) @ [ k ];
                     senv =
                       Map.update_with ctx.senv
                         (Map.Poly.of_alist_exn
                         @@ (xr, c_b.val_type) :: (k, ksort)
                            :: List.zip_exn hs hsorts);
                     ty = c_r;
                     conts_opt = Some (hts, EHMTT.mk_var k);
                   }
               in
               let kret = Ident.mk_fresh_tvar ~prefix:(Some "Kret") () in
               let kret_rule =
                 let kret_sort =
                   Sort.mk_fun
                     (List.map ctx.args ~f:(Map.Poly.find_exn ctx.senv)
                     @ (c_b.val_type :: hsorts)
                     @ [ ksort; Datatype.mk_unit_sort () ])
                 in
                 let kret_args = ctx.args @ (xr :: hs) @ [ k ] in
                 ((kret, kret_sort), (kret_args, term_r))
               in
               ( EHMTT.apps (EHMTT.Nonterm kret)
                   (List.map ctx.args ~f:EHMTT.mk_var),
                 kret_rule :: rules_r )
             in
             let terms_h, ruless_h =
               let ops = get_ops c_b.op_sig in
               List.unzip
               @@ List.map ops ~f:(fun op ->
                      let i, _ =
                        try
                          List.findi_exn op_names ~f:(fun _ -> String.( = ) op)
                        with _ -> failwith @@ op ^ " not found"
                      in
                      let next = List.nth_exn nexts i in
                      let x_args, sort_args, k_opt, sort_k, c_h =
                        List.nth_exn clauses i
                      in
                      let senv'', k_arg =
                        let senv' =
                          List.fold2_exn x_args sort_args ~init:ctx.senv
                            ~f:(fun senv x s ->
                              try Map.Poly.add_exn senv ~key:x ~data:s
                              with _ ->
                                failwith @@ Ident.name_of_tvar x
                                ^ " already defined")
                        in
                        match k_opt with
                        | Some k ->
                            (Map.Poly.add_exn senv' ~key:k ~data:sort_k, k)
                        | None ->
                            ( senv',
                              mk_fresh_tvar ~prefix:(Some "k") () (*dummy*) )
                      in
                      let ksort = Sort.mk_fresh_svar () (*ToDo*) in
                      let k = Ident.mk_fresh_tvar ~prefix:(Some "k") () in
                      let hts, hs, hsorts = gen_hts c_h.op_sig in
                      let term_h, rules_h =
                        next
                          {
                            ctx with
                            args = ctx.args @ x_args @ (k_arg :: hs) @ [ k ];
                            senv =
                              Map.update_with senv''
                                (Map.Poly.of_alist_exn
                                @@ ((k, ksort) :: List.zip_exn hs hsorts));
                            ty = c_h;
                            conts_opt = Some (hts, EHMTT.mk_var k);
                          }
                      in
                      let khnd = Ident.mk_fresh_tvar ~prefix:(Some "Khnd") () in
                      let khnd_rule =
                        let khnd_sort =
                          Sort.mk_fun
                            (List.map ctx.args ~f:(Map.Poly.find_exn ctx.senv)
                            @ sort_args @ (sort_k :: hsorts)
                            @ [ ksort; Datatype.mk_unit_sort () ])
                        in
                        let khnd_args =
                          ctx.args @ x_args @ (k_arg :: hs) @ [ k ]
                        in
                        ((khnd, khnd_sort), (khnd_args, term_h))
                      in
                      ( ( op,
                          EHMTT.apps (EHMTT.Nonterm khnd)
                            (List.map ctx.args ~f:EHMTT.mk_var) ),
                        khnd_rule :: rules_h ))
             in
             let term_b, rules_b =
               next_b
                 {
                   ctx with
                   ty = c_b;
                   conts_opt = Some (ALMap.of_alist_exn terms_h, term_r);
                   num_conts = ctx.num_conts + 1;
                 }
             in
             match ctx.conts_opt with
             | None -> failwith "continuations are not passed"
             | Some (hs, k_nt) ->
                 ( EHMTT.apps term_b @@ ALMap.data hs
                   (*ToDo: consistent with type eff?*) @ [ k_nt ],
                   rules_b @ rules_r @ List.concat ruless_h )
        end)

  (** EHMTT Generation *)

  let _ = Compmisc.init_path ()

  let print_load_info str =
    Debug.print
    @@ lazy
         (sprintf "==================== processing %s ====================" str)

  type envs = {
    tl_rules : EHMTT.rule list;
    tl_nt : Ident.tvar;
    tl_args : (Ident.tvar * Sort.t) list;
    rules : EHMTT.rule list;
    trs : TTA.pre_trs;
    fenv : FunEnv.t;
    dtenv : DTEnv.t;
    ntenv : (Ident.tvar, EHMTT.term) Map.Poly.t;
    senv : sort_env_map;
  }

  let of_struct_item (envs : envs) item =
    match item.str_desc with
    | Tstr_eval (_expr, _) -> failwith "expression not supported"
    | Tstr_value (is_rec, vbs) ->
        let is_rec =
          let defs =
            String.concat_map_list ~sep:" and " vbs ~f:(fun vb ->
                Pattern.str_of @@ MBcgen.pattern_of envs.dtenv vb.vb_pat)
          in
          match is_rec with
          | Recursive ->
              print_load_info @@ "let rec " ^ defs;
              true
          | Nonrecursive ->
              print_load_info @@ "let " ^ defs;
              false
        in
        let is_pures, pats, defs =
          List.unzip3
          @@ List.map vbs ~f:(fun vb ->
                 let pat = MBcgen.pattern_of envs.dtenv vb.vb_pat in
                 (*ToDo*)
                 let sort =
                   match
                     ( MBcgen.find_val_attrs ~dtenv:envs.dtenv
                         ~attr_name:"annot_MB" vb.vb_attributes,
                       MBcgen.find_val_attrs ~dtenv:envs.dtenv
                         ~attr_name:"annot" vb.vb_attributes )
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
        let eff_map =
          match DTEnv.look_up_dt envs.dtenv "eff" with
          | None -> None
          | Some dt ->
              let conses = Datatype.conses_of dt in
              Option.some
              @@ List.map conses ~f:(fun cons ->
                     match Datatype.params_of dt with
                     | [ ret ] ->
                         let ans = Sort.mk_fresh_svar () in
                         ( Datatype.name_of_cons cons,
                           Sort.mk_fun
                           @@ Datatype.sorts_of_cons dt cons
                           @ [ Sort.mk_arrow ret ans; ans ] )
                     | _ -> assert false)
        in
        let maps, next1s =
          let senv_bounds =
            if is_rec then
              let pat_senvs = List.map defs (* assume distinct *) ~f:fst3 in
              Map.update_with_list (*shadowing*) @@ (envs.senv :: pat_senvs)
            else envs.senv
          in
          let eff_constrss, opsig_constrss, next1s =
            List.unzip3
            @@ List.map defs ~f:(fun (_, expr, c) ->
                   cgen_expr eff_map envs.fenv envs.dtenv senv_bounds expr c)
          in
          let omap, smap, emap =
            let eff_constrs = Set.Poly.union_list eff_constrss in
            let opsig_constrs = Set.Poly.union_list opsig_constrss in
            Debug.print (lazy "==== MB type template:");
            List.iter2_exn pats defs ~f:(fun pat (_, _, c) ->
                Debug.print
                @@ lazy (Pattern.str_of pat ^ ": " ^ Term.str_of_triple c));
            Map.Poly.iteri senv_bounds ~f:(fun ~key ~data ->
                Debug.print
                @@ lazy (Ident.name_of_tvar key ^ ": " ^ Term.str_of_sort data));
            Debug.print (lazy "==== constraints on control effects:");
            Set.iter eff_constrs ~f:(fun (effs, eff) ->
                Debug.print
                @@ lazy
                     (sprintf "%s <: %s"
                        (String.concat_map_list ~sep:" " effs
                           ~f:Term.str_of_cont)
                        (Term.str_of_cont eff)));
            Debug.print (lazy "==== constraints on operation signatures:");
            Set.iter opsig_constrs ~f:(fun (o1, o2) ->
                Debug.print
                @@ lazy (Term.str_of_opsig o1 ^ " <: " ^ Term.str_of_opsig o2));
            let sol = MBcsol.solve eff_constrs opsig_constrs in
            (sol.otheta, Map.force_merge !MBcgen.ref_id sol.stheta, sol.etheta)
          in
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
          ((omap', smap', emap'), next1s)
        in
        (* *)
        Debug.print @@ lazy "";
        let (ntenv, tl_rules, tl_nt, tl_args), rules, senv_body =
          cgen_let eff_map
            (List.map envs.tl_rules ~f:fst)
            (envs.tl_nt, envs.tl_args) envs.fenv envs.dtenv envs.ntenv is_rec
            pats
            (is_pures, next1s, List.map defs ~f:(trd3 >> Term.subst_triple maps))
            maps envs.senv
        in
        Debug.print
        @@ lazy
             (sprintf "updated senv:\n%s"
                (str_of_sort_env_map Term.str_of_sort senv_body));
        ( {
            envs with
            tl_rules = envs.tl_rules @ tl_rules;
            tl_nt;
            tl_args;
            rules = envs.rules @ (*EHMTT.eta_expand senv_body*) rules;
            ntenv;
            senv = senv_body;
          },
          Skip )
    | Tstr_primitive vd ->
        print_load_info "external";
        let senv' =
          Map.update_with envs.senv
          @@ Map.Poly.singleton (Tvar vd.val_name.txt)
          @@
          let sort =
            MBcgen.sort_of_type_expr envs.dtenv vd.val_desc.ctyp_type
          in
          Sort.mk_poly (Term.svs_of_sort sort) sort
        in
        Debug.print
        @@ lazy
             (sprintf "updated senv:\n%s"
                (str_of_sort_env_map Term.str_of_sort senv'));
        ({ envs with senv = senv' }, Skip)
    | Tstr_type (_rec_flag (*ToDo*), types) ->
        print_load_info "type";
        let dttypes, ustypes =
          List.partition_tf types ~f:(fun ty ->
              Debug.print
              @@ lazy
                   (sprintf "[of_struct_item] processing a type declaration: %s"
                      ty.typ_name.txt);
              match ty.typ_kind with
              | Ttype_variant _ ->
                  Debug.print @@ lazy "\t is a variant type";
                  true
              | Ttype_abstract ->
                  Debug.print @@ lazy "\t is an abstract type";
                  false
              | Ttype_open ->
                  failwith "unsupported type_declaration kind: Ttype_open"
              | Ttype_record _ -> (
                  match ty.typ_name.txt with
                  | "effect_handler" | "handler" ->
                      Debug.print @@ lazy "\t is a handler type";
                      true
                  | _ ->
                      failwith "unsupported type_declaration kind: Ttype_record"
                  ))
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
                | Ttype_abstract ->
                    failwith "unsupported type_declaration kind: Ttype_abstract"
                | Ttype_open ->
                    failwith "unsupported type_declaration kind: Ttype_open"
                | Ttype_record _ -> dt
                (*ToDo: empty definition*)
                (*failwith "unsupported type_declaration kind: Ttype_record"*))
          in
          List.map datatypes ~f:(fun dt ->
              Datatype.make (Datatype.name_of_dt dt) datatypes Datatype.FDt)
        in
        let dtenv' = List.fold_left dts ~init:dtenv ~f:DTEnv.update_dt in
        Debug.print
        @@ lazy
             (sprintf "[of_struct_item] datatype env:\n%s"
             @@ DTEnv.str_of dtenv');
        update_dtenv dtenv';
        ({ envs with dtenv = dtenv' }, Skip)
    | Tstr_typext _ -> failwith "type extension not supported"
    | Tstr_exception _ -> failwith "exception not supported"
    | Tstr_module _ -> failwith "module not supported"
    | Tstr_recmodule _ -> failwith "recursive module not supported"
    | Tstr_modtype _ -> failwith "module type not supported"
    | Tstr_open _ -> failwith "open not supported"
    | Tstr_class _ -> failwith "class not supported"
    | Tstr_class_type _ -> failwith "class type not supported"
    | Tstr_include _ -> failwith "include not supported"
    | Tstr_attribute attr -> (
        print_load_info "attribute";
        let content =
          match attr.Parsetree.attr_payload with
          | Parsetree.PStr ps -> (
              (*Debug.print @@ lazy
                 (sprintf "parse structure:\n%s" (str_of_parse_structure ps));*)
              let ts, _, _, _, _ =
                Typemod.type_structure (Compmisc.initial_env ()) ps
              in
              (*Debug.print @@ lazy
                 (sprintf "attr typedtree:%s" (MBcgen.str_of_typedtree_structure ts));*)
              match (List.hd_exn @@ List.rev ts.str_items).str_desc with
              | Tstr_eval (expr, _) -> (
                  match expr.exp_desc with
                  | Texp_constant (Const_string (str, _, _)) -> str
                  | Texp_constant (Const_int _) -> failwith "Const_int"
                  | Texp_constant (Const_char _) -> failwith "Const_char"
                  | Texp_constant (Const_float _) -> failwith "Const_float"
                  | Texp_constant (Const_int32 _) -> failwith "Const_int32"
                  | Texp_constant (Const_int64 _) -> failwith "Const_int64"
                  | Texp_constant (Const_nativeint _) ->
                      failwith "Const_nativeint"
                  | _ -> failwith "Tstr_eval")
              | _ -> failwith "unsupported")
          | _ -> failwith "unsupported"
        in
        match attr.Parsetree.attr_name.txt with
        | "automaton" ->
            Debug.print @@ lazy ("[automaton] " ^ content);
            let (trs : TTA.pre_trs) =
              let lb = Lexing.from_string content in
              lb.Lexing.lex_curr_p <-
                {
                  Lexing.pos_fname = "N/A";
                  Lexing.pos_lnum = 1;
                  Lexing.pos_cnum = 0;
                  Lexing.pos_bol = 0;
                };
              Parser.tta_transitions Lexer.token lb
            in
            ({ envs with trs = envs.trs @ trs (* assume distinct *) }, Skip)
        | "check" | "assert" ->
            Debug.print @@ lazy ("[check] " ^ content);
            let specs =
              let lb = Lexing.from_string content in
              lb.Lexing.lex_curr_p <-
                {
                  Lexing.pos_fname = "N/A";
                  Lexing.pos_lnum = 1;
                  Lexing.pos_cnum = 0;
                  Lexing.pos_bol = 0;
                };
              Parser.typedefs Lexer.token lb
            in
            ( envs,
              Check
                (List.map specs ~f:(fun (id_nt, main_typ) ->
                     (id_nt, main_typ, envs.trs))) )
        | "check_toplevel" ->
            Debug.print @@ lazy ("[check_toplevel] " ^ content);
            let (ta : TreeAutomaton.t) =
              let lb = Lexing.from_string content in
              lb.Lexing.lex_curr_p <-
                {
                  Lexing.pos_fname = "N/A";
                  Lexing.pos_lnum = 1;
                  Lexing.pos_cnum = 0;
                  Lexing.pos_bol = 0;
                };
              Parser.tree_automata Lexer.token lb
            in
            (envs, CheckTopLevel ta)
        | name ->
            Debug.print @@ lazy ("unknown annotation: " ^ name);
            (envs, Skip))

  let rec top_level_aux envs = function
    | [] ->
        Debug.print
        @@ lazy
             "======================== All HOMC Problems Generated \
              ========================";
        []
    | item :: tl -> (
        match of_struct_item envs item with
        | envs, Skip -> top_level_aux envs tl
        | _envs, Check _asserts ->
            failwith "not implemented"
            (*
            List.map asserts ~f:(function tvar, typ, trs ->
                Debug.print @@ lazy "\n*** EHMTT generated:\n";
                ( Format.asprintf "type_of(%s) <: %a" (name_of_tvar tvar)
                    RefType.pr typ,
                  Problem.EHMTT (envs.rules, trs, (nt_of_tvar tvar, typ)) ))
            @ top_level_aux envs tl
            *)
        | envs, CheckTopLevel ta ->
            Debug.print @@ lazy "\n*** HORS generated:\n";
            (*(Ident.Tvar "EffCamlMain", RefType.Base (Ident.Tvar "q0"));*)
            ( Format.asprintf "type_of(_) <: %s"
              @@ TreeAutomaton.init_state_of ta,
              let x = Ident.Tvar "x" in
              let xt = RSFD.Term x in
              let y = Ident.Tvar "y" in
              let yt = RSFD.Term y in
              let hs =
                match DTEnv.look_up_dt envs.dtenv "eff" with
                | None -> []
                | Some dt ->
                    List.mapi (Datatype.conses_of dt) ~f:(fun i _ ->
                        Ident.Tvar ("h" ^ string_of_int (i + 1)))
              in
              let k = Ident.Tvar "k" in
              let kt = RSFD.Term k in
              let nt_not = Ident.Tvar "Not" in
              let nt_and = Ident.Tvar "And" in
              let nt_andP = Ident.Tvar "AndP" in
              let nt_or = Ident.Tvar "Or" in
              let nt_orP = Ident.Tvar "OrP" in
              let nt_imply = Ident.Tvar "Imply" in
              let nt_implyP = Ident.Tvar "ImplyP" in
              let nt_iff = Ident.Tvar "Iff" in
              let nt_iffP = Ident.Tvar "IffP" in
              Problem.RSFD
                ( [],
                  EHMTT.rsfd_of [] envs.tl_rules
                  @ (envs.tl_nt, (List.map ~f:fst envs.tl_args, rterm_unit))
                    :: EHMTT.rsfd_of [] envs.rules
                  @ [
                      ( nt_not,
                        ( [ x ] @ hs @ [ k ],
                          RSFD.app kt (RSFD.apps rterm_not [ xt ]) ) );
                      ( nt_and,
                        ( [ x ] @ hs @ [ k ],
                          RSFD.app kt (RSFD.app (RSFD.Nonterm nt_andP) xt) ) );
                      ( nt_andP,
                        ( [ x; y ] @ hs @ [ k ],
                          RSFD.app kt (RSFD.apps rterm_and [ xt; yt ]) ) );
                      ( nt_or,
                        ( [ x ] @ hs @ [ k ],
                          RSFD.app kt (RSFD.app (RSFD.Nonterm nt_orP) xt) ) );
                      ( nt_orP,
                        ( [ x; y ] @ hs @ [ k ],
                          RSFD.app kt (RSFD.apps rterm_or [ xt; yt ]) ) );
                      ( nt_imply,
                        ( [ x ] @ hs @ [ k ],
                          RSFD.app kt (RSFD.app (RSFD.Nonterm nt_implyP) xt) )
                      );
                      ( nt_implyP,
                        ( [ x; y ] @ hs @ [ k ],
                          RSFD.app kt (RSFD.apps rterm_imply [ xt; yt ]) ) );
                      ( nt_iff,
                        ( [ x ] @ hs @ [ k ],
                          RSFD.app kt (RSFD.app (RSFD.Nonterm nt_iffP) xt) ) );
                      ( nt_iffP,
                        ( [ x; y ] @ hs @ [ k ],
                          RSFD.app kt (RSFD.apps rterm_iff [ xt; yt ]) ) );
                    ],
                  ta ) )
            :: top_level_aux envs tl)

  let top_level ps =
    try
      let ts, _, _, _, _ =
        Typemod.type_structure (Compmisc.initial_env ()) ps
      in
      (*Debug.print @@ lazy (sprintf "typedtree structure:\n%s"
                             (MBcgen.str_of_typedtree_structure ts));*)
      init_dtenv ();
      init_fenv ();
      init_dummy_term_senv ();
      MBcgen.ref_id := Map.Poly.empty;
      let envs =
        {
          tl_rules = [];
          tl_args = [];
          tl_nt = Ident.mk_fresh_tvar ~prefix:(Some "TL") ();
          rules = [];
          trs = [];
          fenv = get_fenv ();
          dtenv = get_dtenv ();
          ntenv = Map.Poly.empty;
          senv = Map.Poly.empty;
        }
      in
      Result.return @@ top_level_aux envs ts.str_items
    with
    | Typemod.Error (loc, env, err) ->
        failwith @@ "Typemod.Error:\n"
        ^ MBcgen.str_of_stdbuf ~f:Location.print_report
        @@ Typemod.report_error ~loc env err
    | Env.Error err ->
        failwith @@ "Env.Error:" ^ MBcgen.str_of_stdbuf ~f:Env.report_error err
    | Typecore.Error (loc, env, err) ->
        failwith @@ "Typecore.Error:\n"
        ^ MBcgen.str_of_stdbuf ~f:Location.print_report
        @@ Typecore.report_error ~loc env err

  let from_ml_file =
    In_channel.create >> Lexing.from_channel >> Parse.implementation
    >> top_level
end
