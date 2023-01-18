open Core
open Common
open Common.Ext
open Common.Combinator
open Ast.Ident
open Ast.LogicOld

module Make (Config : Config.ConfigType) = struct
  let config = Config.config
  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))
  let _ = Debug.set_module_name "MBcsol"

  let is_pure = function
    | Sort.Pure -> true
    | _ -> false

  let is_eff = function
    | Sort.Eff _ -> true
    | _ -> false

  let extract_ev = function
    | Sort.EVar ev -> Some ev
    | _ -> None

  exception Solve_failure of string

  module Constr = struct
    type t = {
      sub_sv_sv : (svar * svar) list;
      sub_ev_ev : (evar * evar) list;
      sub_pure_ev : evar list;
      sub_ev_eff : (evar * (Sort.o * Sort.t * Sort.e * Sort.o * Sort.t * Sort.e)) list;
      sub_evs_ev : (evar list * evar) list;
      ecomps : (Sort.e list * (Sort.o * Sort.t * Sort.e * Sort.o * Sort.t * Sort.e)) list;
    }

    let empty =  {
      sub_sv_sv = [];
      sub_ev_ev = [];
      sub_pure_ev = [];
      sub_ev_eff = [];
      sub_evs_ev = [];
      ecomps  = [];
    }

    let add_sub_sv_sv x c = { c with sub_sv_sv = x :: c.sub_sv_sv }
    let add_sub_ev_ev x c = { c with sub_ev_ev = x :: c.sub_ev_ev }
    let add_sub_pure_ev x c = { c with sub_pure_ev = x :: c.sub_pure_ev }
    let add_sub_ev_eff x c = { c with sub_ev_eff = x :: c.sub_ev_eff }
    let add_sub_evs_ev x c = { c with sub_evs_ev = x :: c.sub_evs_ev }
    let add_ecomp x c = { c with ecomps = x :: c.ecomps }
  end

  module SimplResult = struct
    type t = {
      constr : Constr.t;
      eeqls : (Sort.e * Sort.e) list;
      seqls : (Sort.t * Sort.t) list;
      oeqls : (Sort.o * Sort.o) list;
    }

    let empty =  {
      constr = Constr.empty;
      eeqls = [];
      seqls = [];
      oeqls = [];
    }

    let map_constr f res = { res with constr = f res.constr }
    let add_eeqls x res = { res with eeqls = x @ res.eeqls }
    let add_seqls x res = { res with seqls = x @ res.seqls }
    let add_oeqls x res = { res with oeqls = x @ res.oeqls }
  end

  module SimplState = struct
    type t = {
      res : SimplResult.t;
      esubs : (Sort.e * Sort.e) list;
      ssubs : (Sort.t * Sort.t) list;
      osubs : (Sort.o * Sort.o) list;
    }

    let map_res f state = { state with res = f state.res }
    let map_constr f state = map_res (SimplResult.map_constr f) state
    let add_esubs x state = { state with esubs = x @ state.esubs }
    let add_ssubs x state = { state with ssubs = x @ state.ssubs }
    let add_osubs x state = { state with osubs = x @ state.osubs }
  end

  let rec simplify_esubs (state : SimplState.t) =
    match state.esubs with
    | [] -> state
    | (e1, e2) :: esubs ->
      let state = { state with esubs } in
      match e1, e2 with
      | e, Sort.Pure ->
        let state = SimplState.map_res (SimplResult.add_eeqls [e, Sort.Pure]) state in
        simplify_esubs state
      | Sort.Eff (o1, t1, e1, o2, t2, e2), e ->
        let ov1 = Sort.mk_fresh_empty_open_opsig () in
        let sv1 = Sort.mk_fresh_svar () in
        let ev1 = Sort.mk_fresh_evar () in
        let ov2 = Sort.mk_fresh_empty_open_opsig () in
        let sv2 = Sort.mk_fresh_svar () in
        let ev2 = Sort.mk_fresh_evar () in
        let state = state
                    |> SimplState.map_res (SimplResult.add_eeqls [e, Sort.Eff (ov1, sv1, ev1, ov2, sv2, ev2)])
                    |> SimplState.add_osubs [o1, ov1; ov2, o2]
                    |> SimplState.add_ssubs [sv1, t1; t2, sv2]
                    |> SimplState.add_esubs [ev1, e1; e2, ev2] in
        simplify_esubs state
      | Sort.EVar ev1, Sort.EVar ev2 ->
        let state = SimplState.map_constr (Constr.add_sub_ev_ev (ev1, ev2)) state in
        simplify_esubs state
      | Sort.EVar ev, Sort.Eff (o1, t1, e1, o2, t2, e2) ->
        let state = SimplState.map_constr (Constr.add_sub_ev_eff (ev, (o1, t1, e1, o2, t2, e2))) state in
        simplify_esubs state
      | Sort.Pure, Sort.EVar ev ->
        let state = SimplState.map_constr (Constr.add_sub_pure_ev ev) state in
        simplify_esubs state
      | Sort.Pure, Sort.Eff (o1, t1, e1, o2, t2, e2) ->
        let state = state
                    |> SimplState.add_osubs [o2, o1]
                    |> SimplState.add_ssubs [t1, t2]
                    |> SimplState.add_esubs [e1, e2] in
        simplify_esubs state
      | _ -> failwith "unknown effect"

  let rec simplify_ssubs (state : SimplState.t) =
    match state.ssubs with
    | [] -> state
    | (t1, t2) :: ssubs ->
      let state = { state with ssubs } in
      match t1, t2 with
      | t, Sort.SArrow (t1, (o, t2, e)) ->
        let ev = Sort.mk_fresh_evar () in
        let ov = Sort.mk_fresh_empty_open_opsig () in
        let sv1 = Sort.mk_fresh_svar () in
        let sv2 = Sort.mk_fresh_svar () in
        let state = state
                    |> SimplState.map_res (SimplResult.add_seqls [t, Sort.SArrow (sv1, (ov, sv2, ev))])
                    |> SimplState.add_esubs [ev, e]
                    |> SimplState.add_osubs [o, ov]
                    |> SimplState.add_ssubs [t1, sv1; sv2, t2] in
        simplify_ssubs state
      | t, T_array.SArray (t1, t2) ->
        let sv1 = Sort.mk_fresh_svar () in
        let sv2 = Sort.mk_fresh_svar () in
        let state = state
                    |> SimplState.map_res (SimplResult.add_seqls [t, T_array.SArray (sv1, sv2)])
                    |> SimplState.add_ssubs [sv1, t1; sv2, t2] in
        simplify_ssubs state
      | t, T_dt.SDT dt when Fn.non List.is_empty (Datatype.args_of dt) ->
        let args = Datatype.args_of dt in
        let svs = List.init (List.length args) ~f:(fun _ -> Sort.mk_fresh_svar ()) in
        let state = state
                    |> SimplState.map_res (SimplResult.add_seqls [t, T_dt.SDT (Datatype.update_args dt svs)])
                    |> SimplState.add_ssubs (List.map2_exn svs args ~f:(fun sv s -> (sv, s))) in
        simplify_ssubs state
      | t, T_tuple.STuple ((_ :: _) as ss) ->
        let svs = List.init (List.length ss) ~f:(fun _ -> Sort.mk_fresh_svar ()) in
        let state = state
                    |> SimplState.map_res (SimplResult.add_seqls [t, T_tuple.STuple svs])
                    |> SimplState.add_ssubs (List.map2_exn svs ss ~f:(fun sv s -> sv, s)) in
        simplify_ssubs state
      | Sort.SArrow (t1, (o, t2, e)), t ->
        let ev = Sort.mk_fresh_evar () in
        let ov = Sort.mk_fresh_empty_open_opsig () in
        let sv1 = Sort.mk_fresh_svar () in
        let sv2 = Sort.mk_fresh_svar () in
        let state = state
                    |> SimplState.map_res (SimplResult.add_seqls [t, Sort.SArrow (sv1, (ov, sv2, ev))])
                    |> SimplState.add_esubs [e, ev]
                    |> SimplState.add_osubs [ov, o]
                    |> SimplState.add_ssubs [sv1, t1; t2, sv2] in
        simplify_ssubs state
      | T_array.SArray (t1, t2), t ->
        let sv1 = Sort.mk_fresh_svar () in
        let sv2 = Sort.mk_fresh_svar () in
        let state = state
                    |> SimplState.map_res (SimplResult.add_seqls [t, T_array.SArray (sv1, sv2)])
                    |> SimplState.add_ssubs [t1, sv1; t2, sv2] in
        simplify_ssubs state
      | T_dt.SDT dt, t when Fn.non List.is_empty (Datatype.args_of dt) ->
        let args = Datatype.args_of dt in
        let svs = List.init (List.length args) ~f:(fun _ -> Sort.mk_fresh_svar ()) in
        let state = state
                    |> SimplState.map_res (SimplResult.add_seqls [t, T_dt.SDT (Datatype.update_args dt svs)])
                    |> SimplState.add_ssubs (List.map2_exn args svs ~f:(fun s sv -> s, sv)) in
        simplify_ssubs state
      | T_tuple.STuple ((_ :: _) as ss), t ->
        let svs = List.init (List.length ss) ~f:(fun _ -> Sort.mk_fresh_svar ()) in
        let state = state
                    |> SimplState.map_res (SimplResult.add_seqls [t, T_tuple.STuple svs])
                    |> SimplState.add_ssubs (List.map2_exn ss svs ~f:(fun s sv -> s, sv)) in
        simplify_ssubs state
      | Sort.SVar sv1, Sort.SVar sv2 ->
        let state = SimplState.map_constr (Constr.add_sub_sv_sv (sv1, sv2)) state in
        simplify_ssubs state
      | _, T_dt.SDT _ | _, T_tuple.STuple []
      | _, T_bool.SBool | _, T_int.SInt | _, T_int.SRefInt | _, T_real.SReal
      | _, T_string.SString | _, T_sequence.SFinSequence | _, T_sequence.SInfSequence
      | T_dt.SDT _, _ | T_tuple.STuple [], _
      | T_bool.SBool, _ | T_int.SInt, _ | T_int.SRefInt, _ | T_real.SReal, _
      | T_string.SString, _ | T_sequence.SFinSequence, _ | T_sequence.SInfSequence, _ ->
        let state = SimplState.map_res (SimplResult.add_seqls [t1, t2]) state in
        simplify_ssubs state
      | _ -> failwith "unknown sort"

  let rec simplify_osubs (state : SimplState.t) =
    match state.osubs with
    | [] -> state
    | (o1, o2) :: osubs ->
      let state = { state with osubs } in
      match o1, o2 with
      | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, Some rv2) ->
        let lefts, boths, rights = Common.Util.ALMap.split_lbr opmap1 opmap2 in
        let rv = mk_fresh_rvar () in
        let opsigr = Sort.OpSig (Common.Util.ALMap.of_alist_exn rights, Some rv) in
        let opsigl = Sort.OpSig (Common.Util.ALMap.of_alist_exn lefts, Some rv) in
        let state = state
                    |> SimplState.map_res (SimplResult.add_oeqls [Sort.mk_empty_open_opsig_from_rvar rv1, opsigr])
                    |> SimplState.map_res (SimplResult.add_oeqls [Sort.mk_empty_open_opsig_from_rvar rv2, opsigl])
                    |> SimplState.add_ssubs (List.map boths ~f:snd) in
        simplify_osubs state
      | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, None) ->
        let _lefts, boths, rights = Common.Util.ALMap.split_lbr opmap1 opmap2 in
        let rv = mk_fresh_rvar () in
        let opsigr = Sort.OpSig (Common.Util.ALMap.of_alist_exn rights, Some rv) in
        let state = state
                    |> SimplState.map_res (SimplResult.add_oeqls [Sort.mk_empty_open_opsig_from_rvar rv1, opsigr])
                    |> SimplState.add_ssubs (List.map boths ~f:snd) in
        simplify_osubs state
      | Sort.OpSig (opmap1, None), Sort.OpSig (opmap2, Some rv2) ->
        let lefts, boths, rights = Common.Util.ALMap.split_lbr opmap1 opmap2 in
        let opsigr = Sort.OpSig (Common.Util.ALMap.of_alist_exn rights, None) in
        let opsigl = Sort.OpSig (Common.Util.ALMap.of_alist_exn lefts, None) in
        let state = state
                    |> SimplState.map_res (SimplResult.add_oeqls [Sort.empty_closed_opsig, opsigr])
                    |> SimplState.map_res (SimplResult.add_oeqls [Sort.mk_empty_open_opsig_from_rvar rv2, opsigl])
                    |> SimplState.add_ssubs (List.map boths ~f:snd) in
        simplify_osubs state
      | Sort.OpSig (opmap1, None), Sort.OpSig (opmap2, None) ->
        let _lefts, boths, rights = Common.Util.ALMap.split_lbr opmap1 opmap2 in
        let opsigr = Sort.OpSig (Common.Util.ALMap.of_alist_exn rights, None) in
        let state = state
                    |> SimplState.map_res (SimplResult.add_oeqls [Sort.empty_closed_opsig, opsigr])
                    |> SimplState.add_ssubs (List.map boths ~f:snd) in
        simplify_osubs state
      | _ -> failwith "unknown opsig"

  let rec fully_simplify_subs (state : SimplState.t) =
    if List.is_empty state.esubs && List.is_empty state.ssubs && List.is_empty state.osubs then state.res
    else
      let state = simplify_esubs state in
      let state = simplify_ssubs state in
      let state = simplify_osubs state in
      fully_simplify_subs state

  let simplify_ecompsubs (res : SimplResult.t) =
    let rec go (res : SimplResult.t) = function
      | [] -> res
      | (effs, eff) :: ecompsubs ->
        if is_pure eff then
          let res = SimplResult.add_eeqls (List.map effs ~f:(fun e -> e, Sort.Pure)) res in
          go res ecompsubs
        else if List.exists effs ~f:is_pure then
          let ecompsubs = (List.filter effs ~f:(not <<< is_pure), eff) :: ecompsubs in
          go res ecompsubs
        else if List.exists effs ~f:is_eff || is_eff eff then
          let ov0 = Sort.mk_fresh_empty_open_opsig () in
          let sv0 = Sort.mk_fresh_svar () in
          let ev0 = Sort.mk_fresh_evar () in
          let ovn = Sort.mk_fresh_empty_open_opsig () in
          let svn = Sort.mk_fresh_svar () in
          let evn = Sort.mk_fresh_evar () in
          let res = res
                    |> SimplResult.add_eeqls [eff, Sort.Eff (ovn, svn, evn, ov0, sv0, ev0)]
                    |> SimplResult.map_constr (Constr.add_ecomp (effs, (ovn, svn, evn, ov0, sv0, ev0))) in
          go res ecompsubs
        else
          let unwrap_ev e = Option.value_exn ~message:"unknown effect" (extract_ev e) in
          let evs = List.map effs ~f:unwrap_ev in
          let ev = unwrap_ev eff in
          let res = SimplResult.map_constr (Constr.add_sub_evs_ev (evs, ev)) res in
          go res ecompsubs in
    go res

  let map_eql eql ~f = List.map eql ~f:(fun (a1, a2) -> f a1, f a2)
  let subst_cont_cont (ev, e) = Term.subst_conts_cont (Map.Poly.singleton ev e)
  let subst_cont_sort (ev, e) = Term.subst_conts_sort (Map.Poly.singleton ev e)
  let subst_cont_opsig (ev, e) = Term.subst_conts_opsig (Map.Poly.singleton ev e)
  let subst_sort_cont (sv, s) = Term.subst_sorts_cont (Map.Poly.singleton sv s)
  let subst_sort_sort (sv, s) = Term.subst_sorts_sort (Map.Poly.singleton sv s)
  let subst_sort_opsig (sv, s) = Term.subst_sorts_opsig (Map.Poly.singleton sv s)
  let subst_opsig_cont (rv, o) = Term.subst_opsigs_cont (Map.Poly.singleton rv o)
  let subst_opsig_sort (rv, o) = Term.subst_opsigs_sort (Map.Poly.singleton rv o)
  let subst_opsig_opsig (rv, o) = Term.subst_opsigs_opsig (Map.Poly.singleton rv o)

  module Subst = struct
    type t = {
      etheta : (evar, Sort.e) Map.Poly.t;
      stheta : (svar, Sort.t) Map.Poly.t;
      otheta : (rvar, Sort.o) Map.Poly.t;
    }

    let empty = { etheta = Map.Poly.empty; stheta = Map.Poly.empty; otheta = Map.Poly.empty }

    let add_subst_cont (ev, e) sb = {
      etheta = sb.etheta
               |> Map.Poly.map ~f:(subst_cont_cont (ev, e))
               |> Map.Poly.add_exn ~key:ev ~data:e;
      stheta = Map.Poly.map sb.stheta ~f:(subst_cont_sort (ev, e));
      otheta = Map.Poly.map sb.otheta ~f:(subst_cont_opsig (ev, e));
    }

    let add_subst_sort (sv, s) sb = {
      etheta = Map.Poly.map sb.etheta ~f:(subst_sort_cont (sv, s));
      stheta = sb.stheta
               |> Map.Poly.map ~f:(subst_sort_sort (sv, s))
               |> Map.Poly.add_exn ~key:sv ~data:s;
      otheta = Map.Poly.map sb.otheta ~f:(subst_sort_opsig (sv, s));
    }

    let add_subst_opsig (rv, o) sb = {
      etheta = Map.Poly.map sb.etheta ~f:(subst_opsig_cont (rv, o));
      stheta = Map.Poly.map sb.stheta ~f:(subst_opsig_sort (rv, o));
      otheta = sb.otheta
               |> Map.Poly.map ~f:(subst_opsig_opsig (rv, o))
               |> Map.Poly.add_exn ~key:rv ~data:o;
    }

    let subst_to_sort sb =
      Term.subst_opsigs_sort sb.otheta <<< Term.subst_sorts_sort sb.stheta <<< Term.subst_conts_sort sb.etheta
    let subst_to_cont sb =
      Term.subst_opsigs_cont sb.otheta <<< Term.subst_sorts_cont sb.stheta <<< Term.subst_conts_cont sb.etheta
    let subst_to_opsig sb =
      Term.subst_opsigs_opsig sb.otheta <<< Term.subst_sorts_opsig sb.stheta <<< Term.subst_conts_opsig sb.etheta
  end

  module UniResult = struct
    type t = {
      subst : Subst.t;
    }
  end

  module UniState = struct
    type t = {
      res : UniResult.t;
      eeqls : (Sort.e * Sort.e) list;
      seqls : (Sort.t * Sort.t) list;
      oeqls : (Sort.o * Sort.o) list;
    }

    let add_eeqls x state = { state with eeqls = x @ state.eeqls }
    let add_seqls x state = { state with seqls = x @ state.seqls }
    let add_oeqls x state = { state with oeqls = x @ state.oeqls }

    let subst_cont (ev, e) state = {
      res = { subst = Subst.add_subst_cont (ev, e) state.res.subst };
      eeqls = map_eql state.eeqls ~f:(subst_cont_cont (ev, e));
      seqls = map_eql state.seqls ~f:(subst_cont_sort (ev, e));
      oeqls = map_eql state.oeqls ~f:(subst_cont_opsig (ev, e));
    }

    let subst_sort (sv, s) state = {
      res = { subst = Subst.add_subst_sort (sv, s) state.res.subst };
      eeqls = map_eql state.eeqls ~f:(subst_sort_cont (sv, s));
      seqls = map_eql state.seqls ~f:(subst_sort_sort (sv, s));
      oeqls = map_eql state.oeqls ~f:(subst_sort_opsig (sv, s));
    }

    let subst_opsig (rv, o) state = {
      res = { subst = Subst.add_subst_opsig (rv, o) state.res.subst };
      eeqls = map_eql state.eeqls ~f:(subst_opsig_cont (rv, o));
      seqls = map_eql state.seqls ~f:(subst_opsig_sort (rv, o));
      oeqls = map_eql state.oeqls ~f:(subst_opsig_opsig (rv, o));
    }
  end

  let rec unify_eeqls (state : UniState.t) =
    match state.eeqls with
    | [] -> state
    | (e1, e2) :: eeqls ->
      let state = { state with eeqls } in
      let fail () = raise @@ Solve_failure
          (sprintf "unification failed: %s = %s" (Term.str_of_cont e1) (Term.str_of_cont e2)) in
      if Stdlib.(e1 = e2) then unify_eeqls state
      else
        match e1, e2 with
        | Sort.Eff (o11, t11, e11, o12, t12, e12), Sort.Eff (o21, t21, e21, o22, t22, e22) ->
          let state = state
                      |> UniState.add_oeqls [o11, o21; o12, o22]
                      |> UniState.add_seqls [t11, t21; t12, t22]
                      |> UniState.add_eeqls [e11, e21; e12, e22] in
          unify_eeqls state
        | Sort.EVar ev, e | e, Sort.EVar ev ->
          if Set.Poly.mem (Term.evs_of_cont e) ev then fail ()
          else
            let state = UniState.subst_cont (ev, e) state in
            unify_eeqls state
        | _ -> fail ()

  let rec unify_seqls (state : UniState.t) =
    match state.seqls with
    | [] -> state
    | (s1, s2) :: seqls ->
      let state = { state with seqls } in
      let fail () = raise @@ Solve_failure
          (sprintf "unification failed: %s = %s" (Term.str_of_sort s1) (Term.str_of_sort s2)) in
      if Stdlib.(s1 = s2) then unify_seqls state
      else
        match s1, s2 with
        | T_array.SArray (t11, t12), T_array.SArray (t21, t22) ->
          let state = UniState.add_seqls [t11, t21; t12, t22] state in
          unify_seqls state
        | Sort.SArrow (t11, (o1, t12, e1)), Sort.SArrow (t21, (o2, t22, e2)) ->
          let state = state
                      |> UniState.add_eeqls [e1, e2]
                      |> UniState.add_oeqls [o1, o2]
                      |> UniState.add_seqls [t11, t21; t12, t22] in
          unify_seqls state
        | Sort.SVar sv, t | t, Sort.SVar sv ->
          if Set.Poly.mem (Term.svs_of_sort t) sv then fail ()
          else
            let state = UniState.subst_sort (sv, t) state in
            unify_seqls state
        | T_dt.SDT dt1, T_dt.SDT dt2 ->
          let args1 = Datatype.args_of dt1 in
          let args2 = Datatype.args_of dt2 in
          if List.length args1 = List.length args2 then
            let state = UniState.add_seqls (List.zip_exn args1 args2) state in
            unify_seqls state
          else fail ()
        | T_tuple.STuple ss1, T_tuple.STuple ss2 ->
          let state = UniState.add_seqls (List.zip_exn ss1 ss2) state in
          unify_seqls state
        | _ -> fail ()

  let rec unify_oeqls (state : UniState.t) =
    match state.oeqls with
    | [] -> state
    | (o1, o2) :: oeqls ->
      let state = { state with oeqls } in
      let fail () = raise @@ Solve_failure
          (sprintf "unification failed: %s = %s" (Term.str_of_opsig o1) (Term.str_of_opsig o2)) in
      if Stdlib.(o1 = o2) then unify_oeqls state
      else
        match o1, o2 with
        | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, Some rv2) when Stdlib.(rv1 <> rv2) ->
          let lefts, boths, rights = Common.Util.ALMap.split_lbr opmap1 opmap2 in
          let rv = mk_fresh_rvar () in
          let opsigl = Sort.OpSig (Common.Util.ALMap.of_alist_exn lefts, Some rv) in
          let opsigr = Sort.OpSig (Common.Util.ALMap.of_alist_exn rights, Some rv) in
          if Set.Poly.mem (Term.rvs_of_opsig opsigr) rv1 || Set.Poly.mem (Term.rvs_of_opsig opsigl) rv2 then fail ()
          else
            let state = state
                        |> UniState.subst_opsig (rv1, opsigr)
                        |> UniState.subst_opsig (rv2, opsigl)
                        |> UniState.add_seqls (List.map boths ~f:snd) in
            unify_oeqls state
        | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, Some rv2) when Stdlib.(rv1 = rv2) ->
          let lefts, boths, rights = Common.Util.ALMap.split_lbr opmap1 opmap2 in
          if Fn.non List.is_empty lefts || Fn.non List.is_empty rights then fail ()
          else
            let state = state
                        |> UniState.add_seqls (List.map boths ~f:snd) in
            unify_oeqls state
        | Sort.OpSig (opmap, Some rv), Sort.OpSig (opmap', None)
        | Sort.OpSig (opmap', None), Sort.OpSig (opmap, Some rv) ->
          let lefts, boths, rights = Common.Util.ALMap.split_lbr opmap opmap' in
          if Fn.non List.is_empty lefts then fail ()
          else
            let opsigr = Sort.OpSig (Common.Util.ALMap.of_alist_exn rights, None) in
            if Set.Poly.mem (Term.rvs_of_opsig opsigr) rv then fail ()
            else
              let state = state
                          |> UniState.subst_opsig (rv, opsigr)
                          |> UniState.add_seqls (List.map boths ~f:snd) in
              unify_oeqls state
        | Sort.OpSig (opmap1, None), Sort.OpSig (opmap2, None) ->
          let lefts, boths, rights = Common.Util.ALMap.split_lbr opmap1 opmap2 in
          if Fn.non List.is_empty lefts || Fn.non List.is_empty rights then fail ()
          else
            let state = UniState.add_seqls (List.map boths ~f:snd) state in
            unify_oeqls state
        | _ -> fail ()

  let rec fully_unify_eqls (state : UniState.t) =
    if List.is_empty state.eeqls && List.is_empty state.seqls && List.is_empty state.oeqls then state.res
    else
      let state = unify_eeqls state in
      let state = unify_seqls state in
      let state = unify_oeqls state in
      fully_unify_eqls state

  module PreprocResult = struct
    type t = {
      constr : Constr.t;
      subst : Subst.t;
    }

    let empty = {
      constr = Constr.empty;
      subst = Subst.empty;
    }
  end

  module PreprocState = struct
    type t = {
      res : PreprocResult.t;
      esubs : (Sort.e * Sort.e) list;
      ssubs : (Sort.t * Sort.t) list;
      osubs : (Sort.o * Sort.o) list;
      ecompsubs : (Sort.e list * Sort.e) list;
    }

    let init ecompsubs osubs = { res = PreprocResult.empty; esubs = []; ssubs = []; osubs; ecompsubs }
    let add_esubs x state = { state with esubs = x @ state.esubs }
    let add_ssubs x state = { state with ssubs = x @ state.ssubs }
    let add_osubs x state = { state with osubs = x @ state.osubs }

    let from_subst_constr (subst : Subst.t) (constr : Constr.t) : t =
      let subst_to_cont = Subst.subst_to_cont subst in
      let subst_to_sort = Subst.subst_to_sort subst in
      let subst_to_opsig = Subst.subst_to_opsig subst in
      let ssubs, sub_sv_sv =
        List.partition_map constr.sub_sv_sv ~f:(fun (sv1, sv2) ->
            match Map.Poly.find subst.stheta sv1, Map.Poly.find subst.stheta sv2 with
            | Some s1, Some s2 -> First (s1, s2)
            | Some s1, None -> First (s1, Sort.SVar sv2)
            | None, Some s2 -> First (Sort.SVar sv1, s2)
            | None, None -> Second (sv1, sv2)) in
      let esubs_from_ev_ev, sub_ev_ev =
        List.partition_map constr.sub_ev_ev ~f:(fun (ev1, ev2) ->
            match Map.Poly.find subst.etheta ev1, Map.Poly.find subst.etheta ev2 with
            | Some e1, Some e2 -> First (e1, e2)
            | Some e1, None -> First (e1, Sort.EVar ev2)
            | None, Some e2 -> First (Sort.EVar ev1, e2)
            | None, None -> Second (ev1, ev2)) in
      let esubs_from_pure_ev, sub_pure_ev =
        List.partition_map constr.sub_pure_ev ~f:(fun ev ->
            match Map.Poly.find subst.etheta ev with
            | Some e -> First (Sort.Pure, e)
            | None -> Second ev) in
      let esubs_from_ev_eff, sub_ev_eff =
        List.partition_map constr.sub_ev_eff ~f:(fun (ev, (o1, s1, e1, o2, s2, e2)) ->
            let o1 = subst_to_opsig o1 in
            let s1 = subst_to_sort s1 in
            let e1 = subst_to_cont e1 in
            let o2 = subst_to_opsig o2 in
            let s2 = subst_to_sort s2 in
            let e2 = subst_to_cont e2 in
            match Map.Poly.find subst.etheta ev with
            | Some e -> First (e, Sort.Eff (o1, s1, e1, o2, s2, e2))
            | None -> Second (ev, (o1, s1, e1, o2, s2, e2))) in
      let esubs = List.concat [esubs_from_ev_ev; esubs_from_pure_ev; esubs_from_ev_eff] in
      let ecompsubs, sub_evs_ev =
        List.partition_map constr.sub_evs_ev ~f:(fun (evs, ev) ->
            let es, e =
              let f ev =
                match Map.Poly.find subst.etheta ev with
                | Some e -> First e
                | None -> Second ev in
              List.map evs ~f, f ev in
            if List.exists es ~f:Either.is_first || Either.is_first e then
              let f = Either.value_map ~first:Fn.id ~second:(fun ev -> Sort.EVar ev) in
              First (List.map es ~f, f e)
            else Second (evs, ev)) in
      let ecomps =
        List.map constr.ecomps ~f:(fun (es, (o1, s1, e1, o2, s2, e2)) ->
            let o1 = subst_to_opsig o1 in
            let s1 = subst_to_sort s1 in
            let e1 = subst_to_cont e1 in
            let o2 = subst_to_opsig o2 in
            let s2 = subst_to_sort s2 in
            let e2 = subst_to_cont e2 in
            List.map es ~f:subst_to_cont, (o1, s1, e1, o2, s2, e2)) in
      { res =
          { constr = { sub_sv_sv; sub_ev_ev; sub_pure_ev; sub_ev_eff; sub_evs_ev; ecomps }; subst };
        esubs; ssubs; osubs = []; ecompsubs }
  end

  let rec preprocess (state : PreprocState.t) =
    if List.is_empty state.esubs && List.is_empty state.ssubs && List.is_empty state.osubs && List.is_empty state.ecompsubs then
      state.res
    else
      let simpl_res = simplify_ecompsubs
          { constr = state.res.constr; eeqls = []; seqls = []; oeqls = [] } state.ecompsubs in
      let simpl_res = fully_simplify_subs
          { res = simpl_res; esubs = state.esubs; ssubs = state.ssubs; osubs = state.osubs } in
      let uni_res = fully_unify_eqls
          { res = { subst = state.res.subst }; eeqls = simpl_res.eeqls; seqls = simpl_res.seqls; oeqls = simpl_res.oeqls } in
      let state = PreprocState.from_subst_constr uni_res.subst simpl_res.constr in
      preprocess state

  module SearchState = struct
    type t = {
      constr : Constr.t;
      subst : Subst.t;
      embedded : evar Set.Poly.t;
    }

    let init (res : PreprocResult.t) =
      { constr = res.constr; subst = res.subst; embedded = Set.Poly.empty }

    let add_subst_cont (ev, e) state =
      let subst = Subst.add_subst_cont (ev, e) state.subst in
      PreprocState.from_subst_constr subst state.constr
  end

  let rec search_subs ~embed (state : SearchState.t) =
    match state.constr.sub_ev_eff with
    | [] -> state
    | (ev, (o1, s1, e1, o2, s2, e2)) :: sub_ev_eff ->
      let state = { state with constr = { state.constr with sub_ev_eff } } in
      let assume_eff () =
        let ov1 = Sort.mk_fresh_empty_open_opsig () in
        let sv1 = Sort.mk_fresh_svar () in
        let ev1 = Sort.mk_fresh_evar () in
        let ov2 = Sort.mk_fresh_empty_open_opsig () in
        let sv2 = Sort.mk_fresh_svar () in
        let ev2 = Sort.mk_fresh_evar () in
        let preproc_res =
          SearchState.add_subst_cont (ev, Sort.Eff (ov1, sv1, ev1, ov2, sv2, ev2)) state
          |> PreprocState.add_esubs [e1, ev1; ev2, e2]
          |> PreprocState.add_ssubs [s1, sv1; sv2, s2]
          |> PreprocState.add_osubs [ov1, o1; o2, ov2]
          |> preprocess in
        let embedded = Set.Poly.add state.embedded ev in
        let state : SearchState.t =
          { constr = preproc_res.constr; subst = preproc_res.subst; embedded } in
        search_subs ~embed state in
      let assume_pure () =
        let preproc_res = preprocess (SearchState.add_subst_cont (ev, Sort.Pure) state) in
        let state = { state with constr = preproc_res.constr; subst = preproc_res.subst } in
        search_subs ~embed state in
      let assume1, assume2 =
        if embed then assume_eff, assume_pure else assume_pure, assume_eff in
      try assume1 () with
      | Solve_failure _ -> assume2 ()

  let rec search_comps ~embed (state : SearchState.t) =
    match state.constr.ecomps with
    | [] -> state
    | (es, (o_first, s_first, e_first, o_last, s_last, e_last)) :: ecomps ->
      let state = { state with constr = { state.constr with ecomps } } in
      match es with
      | [] ->
        let uni_res = fully_unify_eqls
            { res = { subst = state.subst };
              seqls = [s_first, s_last];
              eeqls = [e_first, e_last];
              oeqls = [o_first, o_last];
            } in
        let preproc_res =
          preprocess (PreprocState.from_subst_constr uni_res.subst state.constr) in
        let state = { state with constr = preproc_res.constr; subst = preproc_res.subst } in
        search_comps ~embed state
      | Sort.Pure :: es ->
        let ecomps = (es, (o_first, s_first, e_first, o_last, s_last, e_last)) :: ecomps in
        let state = { state with constr = { state.constr with ecomps } } in
        search_comps ~embed state
      | Sort.Eff (o1, s1, e1, o2, s2, e2) :: es ->
        let uni_res = fully_unify_eqls
            { res = { subst = state.subst }; seqls = [s_last, s2]; eeqls = [e_last, e2]; oeqls = [o_last, o2] } in
        let ecomps = (es, (o_first, s_first, e_first, o1, s1, e1)) :: ecomps in
        let state = { state with constr = { state.constr with ecomps } } in
        let preproc_res =
          preprocess (PreprocState.from_subst_constr uni_res.subst state.constr) in
        let state = { state with constr = preproc_res.constr; subst = preproc_res.subst } in
        search_comps ~embed state
      | Sort.EVar ev :: es ->
        let assume_eff () =
          let ov_new = Sort.mk_fresh_empty_open_opsig () in
          let sv_new = Sort.mk_fresh_svar () in
          let ev_new = Sort.mk_fresh_evar () in
          let ecomps = (es, (o_first, s_first, e_first, ov_new, sv_new, ev_new)) :: ecomps in
          let state = { state with constr = { state.constr with ecomps } } in
          let preproc_res =
            SearchState.add_subst_cont (ev, Sort.Eff (ov_new, sv_new, ev_new, o_last, s_last, e_last)) state
            |> preprocess in
          let embedded = Set.Poly.add state.embedded ev in
          let state : SearchState.t =
            { constr = preproc_res.constr; subst = preproc_res.subst; embedded } in
          search_comps ~embed state in
        let assume_pure () =
          let ecomps = (es, (o_first, s_first, e_first, o_last, s_last, e_last)) :: ecomps in
          let state = { state with constr = { state.constr with ecomps } } in
          let preproc_res = SearchState.add_subst_cont (ev, Sort.Pure) state |> preprocess in
          let state = { state with constr = preproc_res.constr; subst = preproc_res.subst } in
          search_comps ~embed state in
        let assume1, assume2 =
          if embed then assume_eff, assume_pure else assume_pure, assume_eff in
        begin try assume1 () with
          | Solve_failure _ -> assume2 () end
      | _ -> failwith "unknown effect"

  let uniform ~ev_equiv (state : SearchState.t) =
    Map.Poly.fold ev_equiv ~init:[] ~f:(fun ~key:_ ~data:evs eeqls ->
        let effs =
          List.filter_map evs ~f:(fun ev ->
              Option.filter (Map.Poly.find state.subst.etheta ev) ~f:(fun e ->
                  is_eff e && not (Set.Poly.mem state.embedded ev))) in
        Option.value_map (List.hd effs) ~default:[] ~f:(fun eff ->
            List.map evs ~f:(fun ev ->
                let e = Option.value (Map.Poly.find state.subst.etheta ev) ~default:(Sort.EVar ev) in
                e, eff))
        @ eeqls)

  let rec fully_search ~embed ~ev_equiv (state : SearchState.t) =
    if List.is_empty state.constr.sub_ev_eff && List.is_empty state.constr.ecomps then
      state
    else
      let state = search_subs ~embed state in
      let state = search_comps ~embed state in
      let preproc_res =
        let uni_res = fully_unify_eqls
            { res = { subst = state.subst };
              eeqls = uniform ~ev_equiv state;
              seqls = [];
              oeqls = [] } in
        preprocess (PreprocState.from_subst_constr uni_res.subst state.constr) in
      let state = { state with constr = preproc_res.constr; subst = preproc_res.subst } in
      fully_search ~embed ~ev_equiv state

  let resolve_evs (constr : Constr.t) =
    assert (List.is_empty constr.sub_ev_eff && List.is_empty constr.ecomps);
    List.concat
      [ List.concat_map constr.sub_ev_ev ~f:(fun (ev1, ev2) -> [ev1; ev2]);
        constr.sub_pure_ev;
        List.concat_map constr.sub_evs_ev ~f:(fun (evs, ev) -> ev :: evs) ]

  let resolve_svs (constr : Constr.t) =
    assert (List.is_empty constr.sub_ev_eff && List.is_empty constr.ecomps);
    match constr.sub_sv_sv with
    | [] -> []
    | (sv1, _) :: _ -> List.concat_map constr.sub_sv_sv ~f:(fun (sv2, sv3) -> [sv2, sv1; sv3, sv1])

  let squash_evs_cont e =
    let evs = Set.Poly.to_list (Term.evs_of_cont e) in
    let sbs = Map.Poly.of_alist_exn (List.map evs ~f:(fun ev -> ev, Sort.Pure)) in
    Term.subst_conts_cont sbs e

  let squash_evs_sort s =
    let evs = Set.Poly.to_list (Term.evs_of_sort s) in
    let sbs = Map.Poly.of_alist_exn (List.map evs ~f:(fun ev -> ev, Sort.Pure)) in
    Term.subst_conts_sort sbs s

  let squash_evs_opsig o =
    let evs = Set.Poly.to_list (Term.evs_of_opsig o) in
    let sbs = Map.Poly.of_alist_exn (List.map evs ~f:(fun ev -> ev, Sort.Pure)) in
    Term.subst_conts_opsig sbs o

  let squash_rvs_cont e =
    let rvs = Set.Poly.to_list (Term.rvs_of_cont e) in
    let sbs = Map.Poly.of_alist_exn (List.map rvs ~f:(fun rv -> rv, Sort.empty_closed_opsig)) in
    Term.subst_opsigs_cont sbs e

  let squash_rvs_sort s =
    let rvs = Set.Poly.to_list (Term.rvs_of_sort s) in
    let sbs = Map.Poly.of_alist_exn (List.map rvs ~f:(fun rv -> rv, Sort.empty_closed_opsig)) in
    Term.subst_opsigs_sort sbs s

  let squash_rvs_opsig o =
    let rvs = Set.Poly.to_list (Term.rvs_of_opsig o) in
    let sbs = Map.Poly.of_alist_exn (List.map rvs ~f:(fun rv -> rv, Sort.empty_closed_opsig)) in
    Term.subst_opsigs_opsig sbs o

  let resolve (state : SearchState.t) : Subst.t =
    let subst_ev_pure = resolve_evs state.constr in
    let subst_sv_sv = resolve_svs state.constr in
    let etheta = Map.Poly.map state.subst.etheta ~f:(fun e ->
        let e =
          List.fold subst_ev_pure ~init:e ~f:(fun e ev ->
              subst_cont_cont (ev, Sort.Pure) e) in
        List.fold subst_sv_sv ~init:e ~f:(fun e (sv1, sv2) ->
            subst_sort_cont (sv1, Sort.SVar sv2) e)) in
    let stheta = Map.Poly.map state.subst.stheta ~f:(fun s ->
        let s =
          List.fold subst_ev_pure ~init:s ~f:(fun s ev ->
              subst_cont_sort (ev, Sort.Pure) s) in
        List.fold subst_sv_sv ~init:s ~f:(fun s (sv1, sv2) ->
            subst_sort_sort (sv1, Sort.SVar sv2) s)) in
    let otheta = Map.Poly.map state.subst.otheta ~f:(fun o ->
        let o =
          List.fold subst_ev_pure ~init:o ~f:(fun o ev ->
              subst_cont_opsig (ev, Sort.Pure) o) in
        List.fold subst_sv_sv ~init:o ~f:(fun o (sv1, sv2) ->
            subst_sort_opsig (sv1, Sort.SVar sv2) o)) in
    { etheta; stheta; otheta }

  let eliminate ~init_evs ~init_svs ~init_rvs (subst : Subst.t) : Subst.t =
    let etheta = Map.Poly.filter_keys subst.etheta ~f:(Set.Poly.mem init_evs) in
    let stheta = Map.Poly.filter_keys subst.stheta ~f:(Set.Poly.mem init_svs) in
    let otheta = Map.Poly.filter_keys subst.otheta ~f:(Set.Poly.mem init_rvs) in
    { etheta; stheta; otheta }

  let squash ~init_evs ~init_rvs (subst : Subst.t) : Subst.t =
    let etheta = Map.Poly.map subst.etheta ~f:(squash_evs_cont <<< squash_rvs_cont) in
    let etheta = Set.Poly.fold init_evs ~init:etheta ~f:(fun etheta ev ->
        match Map.Poly.add etheta ~key:ev ~data:Sort.Pure with
        | `Ok etheta -> etheta
        | `Duplicate -> etheta) in
    let stheta = Map.Poly.map subst.stheta ~f:(squash_evs_sort <<< squash_rvs_sort) in
    let otheta = Map.Poly.map subst.otheta ~f:(squash_evs_opsig <<< squash_rvs_opsig) in
    let otheta = Set.Poly.fold init_rvs ~init:otheta ~f:(fun otheta rv ->
        match Map.Poly.add otheta ~key:rv ~data:Sort.empty_closed_opsig with
        | `Ok otheta -> otheta
        | `Duplicate -> otheta) in
    { etheta; stheta; otheta }

  let postprocess ~init_evs ~init_svs ~init_rvs = resolve >> eliminate ~init_evs ~init_svs ~init_rvs >> squash ~init_evs ~init_rvs

  let discriminate_evs_cont ecompsub =
    List.fold ecompsub ~init:(Map.Poly.empty, []) ~f:(fun (ev_map, ecompsub) (effs, eff) ->
        let evs = Set.Poly.union_list (List.map (eff :: effs) ~f:Term.evs_of_cont) in
        let ev_map, etheta =
          Set.Poly.fold evs ~init:(ev_map, Map.Poly.empty) ~f:(fun (ev_map, etheta) ev ->
              let new_ev = ev(*mk_fresh_evar ()*) in
              let ev_map =
                Map.Poly.update ev_map ev ~f:(fun new_evs ->
                    new_ev :: Option.value new_evs ~default:[]) in
              let etheta = Map.Poly.add_exn etheta ~key:ev ~data:(Sort.EVar new_ev) in
              ev_map, etheta) in
        let effs = List.map effs ~f:(Term.subst_conts_cont etheta) in
        let eff = Term.subst_conts_cont etheta eff in
        ev_map, (effs, eff) :: ecompsub)

  let discriminate_evs_opsig osub =
    List.fold osub ~init:(Map.Poly.empty, []) ~f:(fun (ev_map, osub) (o1, o2) ->
        let evs = Set.Poly.union_list (List.map [o1; o2] ~f:Term.evs_of_opsig) in
        let ev_map, etheta =
          Set.Poly.fold evs ~init:(ev_map, Map.Poly.empty) ~f:(fun (ev_map, etheta) ev ->
              let new_ev = ev(*mk_fresh_evar ()*) in
              let ev_map =
                Map.Poly.update ev_map ev ~f:(fun new_evs ->
                    new_ev :: Option.value new_evs ~default:[]) in
              let etheta = Map.Poly.add_exn etheta ~key:ev ~data:(Sort.EVar new_ev) in
              ev_map, etheta) in
        let o1 = Term.subst_conts_opsig etheta o1 in
        let o2 = Term.subst_conts_opsig etheta o2 in
        ev_map, (o1, o2) :: osub)

  type solution = {
    ev_equiv : (evar, evar list) Map.Poly.t;
    subst_purest : Subst.t
  }

  let solve eff_constrs opsig_constrs : solution =
    let ev_equiv, ecompsubs = discriminate_evs_cont (Set.Poly.to_list eff_constrs) in
    let ev_equiv', osubs = discriminate_evs_opsig (Set.Poly.to_list opsig_constrs) in
    let ev_equiv = Map.Poly.merge ev_equiv ev_equiv' ~f:(fun ~key:_ data ->
        match data with
        | `Left evs | `Right evs -> Some evs
        | `Both (evs, evs') -> Some (evs @ evs')
      ) in

    let init_evs = Set.Poly.union_list @@
      Set.Poly.of_list (List.concat_no_order (Map.Poly.data ev_equiv)) ::
      List.map osubs ~f:(fun (o1, o2) ->
          Set.Poly.union_list [Term.evs_of_opsig o1; Term.evs_of_opsig o2]) in
    let init_svs = Set.Poly.union_list @@
      List.map (Set.to_list eff_constrs) ~f:(fun (es, e) ->
          Set.Poly.union_list (Term.svs_of_cont e :: List.map es ~f:Term.svs_of_cont)) @
      List.map (Set.to_list opsig_constrs) ~f:(fun (o1, o2) ->
          Set.Poly.union_list [Term.svs_of_opsig o1; Term.svs_of_opsig o2]) in
    let init_rvs = Set.Poly.union_list @@
      List.map (Set.to_list eff_constrs) ~f:(fun (es, e) ->
          Set.Poly.union_list (Term.rvs_of_cont e :: List.map es ~f:Term.rvs_of_cont)) @
      List.map (Set.to_list opsig_constrs) ~f:(fun (o1, o2) ->
          Set.Poly.union_list [Term.rvs_of_opsig o1; Term.rvs_of_opsig o2]) in

    (*Debug.print (lazy "==== discriminated:");
    List.iter ecompsubs ~f:(fun (es, e) ->
        Debug.print @@ lazy ((String.concat_map_list ~sep:" " es ~f:Term.str_of_cont)
                             ^ " <: " ^ Term.str_of_cont e));
    List.iter osubs ~f:(fun (o1, o2) ->
        Debug.print @@ lazy (Term.str_of_opsig o1 ^ " <: " ^ Term.str_of_opsig o2));
    Map.Poly.iteri ev_equiv ~f:(fun ~key:ev ~data:evs ->
        Debug.print @@ lazy (name_of_evar ev ^ " :: {"
                             ^ String.concat_map_list ~sep:", " evs ~f:name_of_evar ^ "}"));*)

    let preproc_res = preprocess (PreprocState.init ecompsubs osubs) in
    let search_state = SearchState.init preproc_res in
    let search_res_purest = fully_search ~embed:false ~ev_equiv search_state in
    let subst_purest = postprocess ~init_evs ~init_svs ~init_rvs search_res_purest in

    Debug.print @@ lazy "==== found solution:";
    Map.Poly.iteri subst_purest.etheta ~f:(fun ~key:ev ~data:e ->
        Debug.print @@ lazy (sprintf "%s := %s" (name_of_evar ev) (Term.str_of_cont e)));
    Map.Poly.iteri subst_purest.stheta ~f:(fun ~key:sv ~data:s ->
        Debug.print @@ lazy (sprintf "%s := %s" (name_of_svar sv) (Term.str_of_sort s)));
    Map.Poly.iteri subst_purest.otheta ~f:(fun ~key:sv ~data:s ->
        Debug.print @@ lazy (sprintf "%s := %s" (name_of_rvar sv) (Term.str_of_opsig s)));

    { ev_equiv; subst_purest }
end
