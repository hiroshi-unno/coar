open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast.Ident
open Ast.LogicOld

module Config = struct
  type t = { verbose : bool; elim_pure : bool } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid MBcsol Configuration (%s): %s" filename msg)
end

module Make (Config : Config.ConfigType) = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_module_name "MBcsol"
  let print_log = false

  exception Solve_failure of string

  module Constr = struct
    type t = {
      sub_sv_sv : (svar * svar) list;
      sub_evs_eff : (evar list * Sort.e) list;
      sub_effs_eff : (Sort.e list * Sort.e) list;
      ecomps : ((Sort.c * Sort.c) list * (Sort.c * Sort.c)) list;
      sub_ov_ov : (rvar * rvar) list;
      sub_ov_opsig : (rvar * ((string, Sort.t) ALMap.t * rvar option)) list;
      sub_opsig_ov : (((string, Sort.t) ALMap.t * rvar option) * rvar) list;
    }

    let empty =
      {
        sub_sv_sv = [];
        sub_evs_eff = [];
        sub_effs_eff = [];
        ecomps = [];
        sub_ov_ov = [];
        sub_ov_opsig = [];
        sub_opsig_ov = [];
      }

    let add_sub_sv_sv x c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (Ast.Ident.name_of_svar (fst x))
                (Ast.Ident.name_of_svar (snd x)));
      { c with sub_sv_sv = x :: c.sub_sv_sv }

    let add_sub_evs_eff (evs, eff) c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (String.concat_map_list ~sep:" " evs ~f:Ast.Ident.name_of_evar)
                (Term.str_of_cont eff));
      { c with sub_evs_eff = (evs, eff) :: c.sub_evs_eff }

    let add_sub_effs_eff (effs, eff) c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (String.concat_map_list ~sep:" " effs ~f:Term.str_of_cont)
                (Term.str_of_cont eff));
      if List.for_all effs ~f:Sort.is_evar then
        {
          c with
          sub_evs_eff = (List.map effs ~f:Sort.let_evar, eff) :: c.sub_evs_eff;
        }
      else { c with sub_effs_eff = (effs, eff) :: c.sub_effs_eff }

    let add_ecomp (effs, (c1, c2)) c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s => %s"
                (String.concat_map_list ~sep:" " effs ~f:(fun (c1, c2) ->
                     Term.str_of_cont (Sort.mk_cont_eff c1 c2)))
                (Term.str_of_triple c1) (Term.str_of_triple c2));
      { c with ecomps = (effs, (c1, c2)) :: c.ecomps }

    let add_sub_ov_ov x c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (Ast.Ident.name_of_rvar (fst x))
                (Ast.Ident.name_of_rvar (snd x)));
      { c with sub_ov_ov = x :: c.sub_ov_ov }

    let add_sub_ov_opsig (ovar, (map, opt)) c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (Ast.Ident.name_of_rvar ovar)
                (Term.str_of_opsig (Sort.OpSig (map, opt))));
      match (map, opt) with
      | [], Some ovar' -> { c with sub_ov_ov = (ovar, ovar') :: c.sub_ov_ov }
      | _ -> { c with sub_ov_opsig = (ovar, (map, opt)) :: c.sub_ov_opsig }

    let add_sub_opsig_ov ((map, opt), ovar) c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (Term.str_of_opsig (Sort.OpSig (map, opt)))
                (Ast.Ident.name_of_rvar ovar));
      match (map, opt) with
      | [], Some ovar' -> { c with sub_ov_ov = (ovar', ovar) :: c.sub_ov_ov }
      | _ -> { c with sub_opsig_ov = ((map, opt), ovar) :: c.sub_opsig_ov }

    let ovars_of c =
      Set.Poly.union_list
      @@ List.map c.sub_evs_eff ~f:(snd >> Term.rvs_of_cont)
      @ List.map c.sub_effs_eff ~f:(fun (effs, eff) ->
            Set.Poly.union_list @@ List.map (eff :: effs) ~f:Term.rvs_of_cont)
      @ List.map c.ecomps ~f:(fun (effs, (c1, c2)) ->
            Set.Poly.union_list
            @@ List.map ((c1, c2) :: effs)
                 ~f:(uncurry2 Sort.mk_cont_eff >> Term.rvs_of_cont))
      @ List.map c.sub_ov_ov ~f:(fun (ovar1, ovar2) ->
            Set.Poly.of_list [ ovar1; ovar2 ])
      @ List.map c.sub_ov_opsig ~f:(fun (ovar, (map, opt)) ->
            Set.add (Term.rvs_of_opsig (Sort.OpSig (map, opt))) ovar)
      @ List.map c.sub_opsig_ov ~f:(fun ((map, opt), ovar) ->
            Set.add (Term.rvs_of_opsig (Sort.OpSig (map, opt))) ovar)

    let constrained_ovars_of c =
      Set.Poly.union_list
      @@ List.map c.sub_evs_eff ~f:(snd >> Term.polar_rvs_of_cont ~pos:false)
      @ List.map c.sub_effs_eff ~f:(fun (effs, eff) ->
            Set.Poly.union_list
            @@ Term.polar_rvs_of_cont ~pos:false eff
               :: List.map effs ~f:(Term.polar_rvs_of_cont ~pos:true))
      @ List.map c.ecomps ~f:(fun (effs, (c1, c2)) ->
            Set.Poly.union_list
            @@ Term.polar_rvs_of_cont ~pos:false (Sort.mk_cont_eff c1 c2)
               :: List.map effs
                    ~f:
                      (uncurry2 Sort.mk_cont_eff
                      >> Term.polar_rvs_of_cont ~pos:true))
      @ List.map c.sub_ov_ov ~f:(fst >> Set.Poly.singleton)
      @ List.map c.sub_ov_opsig ~f:(fun (ovar, (map, opt)) ->
            Set.add
              (Term.polar_rvs_of_opsig ~pos:false (Sort.OpSig (map, opt)))
              ovar)
      @ List.map c.sub_opsig_ov ~f:(fun ((map, opt), _) ->
            Term.polar_rvs_of_opsig ~pos:true (Sort.OpSig (map, opt)))

    let unconstrained_ovars_of c =
      Set.diff (ovars_of c) (constrained_ovars_of c)

    let evars_of c =
      Set.Poly.union_list
      @@ List.map c.sub_evs_eff ~f:(fun (effs, eff) ->
             Set.union (Set.Poly.of_list effs) (Term.evs_of_cont eff))
      @ List.map c.sub_effs_eff ~f:(fun (effs, eff) ->
            Set.Poly.union_list @@ List.map (eff :: effs) ~f:Term.evs_of_cont)
      @ List.map c.ecomps ~f:(fun (effs, (c1, c2)) ->
            Set.Poly.union_list
            @@ List.map ((c1, c2) :: effs)
                 ~f:(uncurry2 Sort.mk_cont_eff >> Term.evs_of_cont))
      @ List.map c.sub_ov_opsig ~f:(fun (_, (map, opt)) ->
            Term.evs_of_opsig (Sort.OpSig (map, opt)))
      @ List.map c.sub_opsig_ov ~f:(fun ((map, opt), _) ->
            Term.evs_of_opsig (Sort.OpSig (map, opt)))

    let constrained_evars_of c =
      Set.Poly.union_list
      @@ List.map c.sub_evs_eff ~f:(fun (evs, eff) ->
             if List.is_empty evs && Sort.is_evar eff then Set.Poly.empty
             else Term.polar_evs_of_cont ~pos:true eff)
      @ List.map c.sub_effs_eff ~f:(fun (effs, eff) ->
            Set.Poly.union_list
            @@ Term.polar_evs_of_cont ~pos:true eff
               :: List.map effs ~f:(Term.polar_evs_of_cont ~pos:false))
      @ List.map c.ecomps ~f:(fun (effs, (c1, c2)) ->
            Set.Poly.union_list
            @@ Term.polar_evs_of_cont ~pos:true (Sort.mk_cont_eff c1 c2)
               :: List.map effs
                    ~f:
                      (uncurry2 Sort.mk_cont_eff
                      >> Term.polar_evs_of_cont ~pos:false))
      @ List.map c.sub_ov_opsig ~f:(fun (_, (map, opt)) ->
            Term.polar_evs_of_opsig ~pos:true (Sort.OpSig (map, opt)))
      @ List.map c.sub_opsig_ov ~f:(fun ((map, opt), _) ->
            Term.polar_evs_of_opsig ~pos:false (Sort.OpSig (map, opt)))

    let unconstrained_evars_of c =
      Set.diff (evars_of c) (constrained_evars_of c)
  end

  module SimplResult = struct
    type t = {
      constr : Constr.t;
      eeqls : (Sort.e * Sort.e) list;
      seqls : (Sort.t * Sort.t) list;
      oeqls : (Sort.o * Sort.o) list;
    }

    let empty = { constr = Constr.empty; eeqls = []; seqls = []; oeqls = [] }
    let map_constr f res = { res with constr = f res.constr }

    let add_eeqls x res =
      if print_log then
        List.iter x ~f:(fun (e1, e2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_cont e1)
                    (Term.str_of_cont e2)));
      { res with eeqls = x @ res.eeqls }

    let add_seqls x res =
      if print_log then
        List.iter x ~f:(fun (s1, s2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_sort s1)
                    (Term.str_of_sort s2)));
      { res with seqls = x @ res.seqls }

    let add_oeqls x res =
      if print_log then
        List.iter x ~f:(fun (o1, o2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_opsig o1)
                    (Term.str_of_opsig o2)));
      { res with oeqls = x @ res.oeqls }
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

    let add_esubs x state =
      if print_log then
        List.iter x ~f:(fun (e1, e2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s <: %s" (Term.str_of_cont e1)
                    (Term.str_of_cont e2)));
      { state with esubs = x @ state.esubs }

    let add_ssubs x state =
      if print_log then
        List.iter x ~f:(fun (s1, s2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s <: %s" (Term.str_of_sort s1)
                    (Term.str_of_sort s2)));
      { state with ssubs = x @ state.ssubs }

    let add_osubs x state =
      if print_log then
        List.iter x ~f:(fun (o1, o2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s <: %s" (Term.str_of_opsig o1)
                    (Term.str_of_opsig o2)));
      { state with osubs = x @ state.osubs }

    let add_subs c1 c2 state =
      let open Sort in
      state
      |> add_osubs [ (c2.op_sig, c1.op_sig) ]
      |> add_ssubs [ (c1.val_type, c2.val_type) ]
      |> add_esubs [ (c1.cont_eff, c2.cont_eff) ]
  end

  let rec simplify_esubs (state : SimplState.t) =
    match state.esubs with
    | [] -> state
    | (e1, e2) :: esubs -> (
        let state = { state with esubs } in
        if Stdlib.(e1 = e2) then simplify_esubs state
        else
          match (e1, e2) with
          | _, (Sort.Pure | Sort.Closed) | Sort.Closed, Sort.EVar _ ->
              state
              |> SimplState.map_res (SimplResult.add_eeqls [ (e1, e2) ])
              |> simplify_esubs
          | Sort.EVar ev1, _ ->
              state
              |> SimplState.map_constr (Constr.add_sub_evs_eff ([ ev1 ], e2))
              |> simplify_esubs
          | Sort.Pure, Sort.EVar _ ->
              state
              |> SimplState.map_constr (Constr.add_sub_evs_eff ([], e2))
              |> simplify_esubs
          | Sort.Eff (c1, c2), Sort.EVar ev ->
              let cv1 = Sort.mk_fresh_triple () in
              let cv2 = Sort.mk_fresh_triple () in
              let cont = Sort.mk_cont_eff cv1 cv2 in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_cont cont);
              state
              |> SimplState.map_res
                   (SimplResult.add_eeqls [ (Sort.EVar ev, cont) ])
              |> SimplState.add_subs cv1 c1 |> SimplState.add_subs c2 cv2
              |> simplify_esubs
          | Sort.Pure, Sort.Eff (c1, c2) ->
              state |> SimplState.add_subs c1 c2 |> simplify_esubs
          | Sort.Closed, Sort.Eff (_, _) -> assert false
          | Sort.Eff (c11, c12), Sort.Eff (c21, c22) ->
              state
              |> SimplState.add_subs c21 c11
              |> SimplState.add_subs c12 c22
              |> simplify_esubs
          | _ -> failwith "unknown effect")

  let rec simplify_ssubs (state : SimplState.t) =
    match state.ssubs with
    | [] -> state
    | (t1, t2) :: ssubs -> (
        let state = { state with ssubs } in
        if Stdlib.(t1 = t2) then simplify_ssubs state
        else
          match (t1, t2) with
          | t, Sort.SArrow (t', c) ->
              let sv = Sort.mk_fresh_svar () in
              let cv = Sort.mk_fresh_triple () in
              let sort = Sort.SArrow (sv, cv) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res (SimplResult.add_seqls [ (t, sort) ])
              |> SimplState.add_subs cv c
              |> SimplState.add_ssubs [ (t', sv) ]
              |> simplify_ssubs
          | Sort.SArrow (t', c), t ->
              let sv = Sort.mk_fresh_svar () in
              let cv = Sort.mk_fresh_triple () in
              let sort = Sort.SArrow (sv, cv) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res (SimplResult.add_seqls [ (t, sort) ])
              |> SimplState.add_subs c cv
              |> SimplState.add_ssubs [ (sv, t') ]
              |> simplify_ssubs
          | t, T_array.SArray (t1, t2) ->
              let sv1 = Sort.mk_fresh_svar () in
              let sv2 = Sort.mk_fresh_svar () in
              let sort = T_array.SArray (sv1, sv2) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res (SimplResult.add_seqls [ (t, sort) ])
              |> SimplState.add_ssubs [ (sv1, t1); (sv2, t2) ]
              |> simplify_ssubs
          | T_array.SArray (t1, t2), t ->
              let sv1 = Sort.mk_fresh_svar () in
              let sv2 = Sort.mk_fresh_svar () in
              let sort = T_array.SArray (sv1, sv2) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res (SimplResult.add_seqls [ (t, sort) ])
              |> SimplState.add_ssubs [ (t1, sv1); (t2, sv2) ]
              |> simplify_ssubs
          | t, T_dt.SDT dt when Fn.non List.is_empty (Datatype.params_of dt) ->
              let args = Datatype.params_of dt in
              let svs =
                List.init (List.length args) ~f:(fun _ -> Sort.mk_fresh_svar ())
              in
              let sort = T_dt.SDT (Datatype.update_params dt svs) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res (SimplResult.add_seqls [ (t, sort) ])
              |> SimplState.add_ssubs (List.zip_exn svs args) (*ToDo*)
              |> simplify_ssubs
          | T_dt.SDT dt, t when Fn.non List.is_empty (Datatype.params_of dt) ->
              let args = Datatype.params_of dt in
              let svs =
                List.init (List.length args) ~f:(fun _ -> Sort.mk_fresh_svar ())
              in
              let sort = T_dt.SDT (Datatype.update_params dt svs) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res (SimplResult.add_seqls [ (t, sort) ])
              |> SimplState.add_ssubs (List.zip_exn args svs) (*ToDo*)
              |> simplify_ssubs
          | t, T_tuple.STuple (_ :: _ as ss) ->
              let svs =
                List.init (List.length ss) ~f:(fun _ -> Sort.mk_fresh_svar ())
              in
              let sort = T_tuple.STuple svs in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res (SimplResult.add_seqls [ (t, sort) ])
              |> SimplState.add_ssubs (List.zip_exn svs ss)
              |> simplify_ssubs
          | T_tuple.STuple (_ :: _ as ss), t ->
              let svs =
                List.init (List.length ss) ~f:(fun _ -> Sort.mk_fresh_svar ())
              in
              let sort = T_tuple.STuple svs in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res (SimplResult.add_seqls [ (t, sort) ])
              |> SimplState.add_ssubs (List.zip_exn ss svs)
              |> simplify_ssubs
          | Sort.SVar sv1, Sort.SVar sv2 ->
              state
              |> SimplState.map_constr (Constr.add_sub_sv_sv (sv1, sv2))
              |> simplify_ssubs
          | t, T_ref.SRef t' | T_ref.SRef t', t ->
              let sv = Sort.mk_fresh_svar () in
              let sort = T_ref.SRef sv in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res
                   (SimplResult.add_seqls [ (t, sort); (t', sv) ])
              |> simplify_ssubs
          | _, T_dt.SUS _
          | T_dt.SUS _, _
          | _, T_dt.SDT _
          | T_dt.SDT _, _
          | _, T_tuple.STuple []
          | T_tuple.STuple [], _
          | _, T_bool.SBool
          | T_bool.SBool, _
          | _, T_int.SInt
          | T_int.SInt, _
          | _, T_int.SRefInt
          | T_int.SRefInt, _
          | _, T_real.SReal
          | T_real.SReal, _
          | _, T_string.SString
          | T_string.SString, _
          | _, T_sequence.SSequence _
          | T_sequence.SSequence _, _
          | _, T_regex.SRegEx
          | T_regex.SRegEx, _ ->
              state
              |> SimplState.map_res (SimplResult.add_seqls [ (t1, t2) ])
              |> simplify_ssubs
          | _ -> failwith "unknown sort")

  let rec simplify_osubs (state : SimplState.t) =
    match state.osubs with
    | [] -> state
    | (o1, o2) :: osubs -> (
        let state = { state with osubs } in
        if Stdlib.(o1 = o2) then simplify_osubs state
        else
          match (o1, o2) with
          | Sort.OpSig (opmap1, None), Sort.OpSig (opmap2, None) ->
              let _lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              state
              |> SimplState.map_res
                   (SimplResult.add_oeqls
                      [
                        ( Sort.empty_closed_opsig,
                          Sort.OpSig (ALMap.of_alist_exn rights, None) );
                      ])
              |> SimplState.add_ssubs (List.map boths ~f:snd)
              |> simplify_osubs
          | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, None) ->
              let _lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              if List.is_empty rights then
                state
                |> SimplState.add_ssubs (List.map boths ~f:snd)
                |> simplify_osubs
              else
                let rv = mk_fresh_rvar () in
                if print_log then
                  Debug.print
                  @@ lazy ("introducing " ^ Ast.Ident.name_of_rvar rv);
                state
                |> SimplState.map_res
                     (SimplResult.map_constr
                        (Constr.add_sub_ov_opsig
                           (rv1, (ALMap.of_alist_exn rights, Some rv))))
                |> SimplState.add_ssubs (List.map boths ~f:snd)
                |> simplify_osubs
          | Sort.OpSig (opmap1, None), Sort.OpSig (opmap2, Some rv2) ->
              let lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              state
              |> SimplState.map_res
                   (SimplResult.add_oeqls
                      [
                        ( Sort.empty_closed_opsig,
                          Sort.OpSig (ALMap.of_alist_exn rights, None) );
                      ])
              |> SimplState.map_res
                   (SimplResult.map_constr
                      (Constr.add_sub_opsig_ov
                         ((ALMap.of_alist_exn lefts, None), rv2)))
              |> SimplState.add_ssubs (List.map boths ~f:snd)
              |> simplify_osubs
          | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, Some rv2) ->
              let lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              if List.is_empty rights then
                state
                |> SimplState.map_res
                     (SimplResult.map_constr
                        (Constr.add_sub_opsig_ov
                           ((ALMap.of_alist_exn lefts, Some rv1), rv2)))
                |> SimplState.add_ssubs (List.map boths ~f:snd)
                |> simplify_osubs
              else if List.is_empty lefts then
                state
                |> SimplState.add_ssubs (List.map boths ~f:snd)
                |> SimplState.map_res
                     (SimplResult.map_constr
                        (Constr.add_sub_ov_opsig
                           (rv1, (ALMap.of_alist_exn rights, Some rv2))))
                |> simplify_osubs
              else
                let rv = mk_fresh_rvar () in
                if print_log then
                  Debug.print
                  @@ lazy ("introducing " ^ Ast.Ident.name_of_rvar rv);
                state
                |> SimplState.map_res
                     (SimplResult.map_constr
                        (Constr.add_sub_ov_opsig
                           (rv1, (ALMap.of_alist_exn rights, Some rv))))
                |> SimplState.map_res
                     (SimplResult.map_constr
                        (Constr.add_sub_opsig_ov
                           ((ALMap.of_alist_exn lefts, Some rv), rv2)))
                |> SimplState.add_ssubs (List.map boths ~f:snd)
                |> simplify_osubs
          | _ -> failwith "unknown opsig")

  let rec fully_simplify_subs (state : SimplState.t) =
    if
      List.is_empty state.esubs && List.is_empty state.ssubs
      && List.is_empty state.osubs
    then state.res
    else (
      if print_log then (
        Debug.print @@ lazy "==== esubs:";
        List.iter state.esubs ~f:(fun (e1, e2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s <: %s" (Term.str_of_cont e1) (Term.str_of_cont e2)));
        Debug.print @@ lazy "==== ssubs:";
        List.iter state.ssubs ~f:(fun (s1, s2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s <: %s" (Term.str_of_sort s1) (Term.str_of_sort s2)));
        Debug.print @@ lazy "==== osubs:";
        List.iter state.osubs ~f:(fun (o1, o2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s <: %s" (Term.str_of_opsig o1)
                    (Term.str_of_opsig o2))));
      let state = state |> simplify_esubs |> simplify_ssubs |> simplify_osubs in
      fully_simplify_subs state)

  let simplify_ecompsubs (res : SimplResult.t) =
    let rec go (res : SimplResult.t) = function
      | [] -> res
      | ([], Sort.Closed) :: ecompsubs -> go res ecompsubs
      | ([ Sort.Closed ], eff | [ eff ], Sort.Closed) :: ecompsubs ->
          let res = SimplResult.add_eeqls [ (Sort.Closed, eff) ] res in
          go res ecompsubs
      | (effs, eff) :: ecompsubs ->
          assert (List.for_all (eff :: effs) ~f:(Sort.is_closed >> not));
          let effs = List.filter effs ~f:(Sort.is_pure >> not) in
          if Sort.is_pure eff then
            let res =
              SimplResult.add_eeqls (List.map effs ~f:(fun e -> (e, eff))) res
            in
            go res ecompsubs
          else if Sort.is_evar eff && List.exists effs ~f:Sort.is_eff then (
            let eff' =
              Sort.mk_cont_eff (Sort.mk_fresh_triple ())
                (Sort.mk_fresh_triple ())
            in
            if print_log then
              Debug.print @@ lazy ("introducing " ^ Term.str_of_cont eff');
            let res = SimplResult.add_eeqls [ (eff, eff') ] res in
            go res @@ ((effs, eff') :: ecompsubs))
          else if List.for_all (eff :: effs) ~f:Sort.is_eff then
            let res =
              SimplResult.map_constr
                (Constr.add_ecomp
                   (List.map effs ~f:Sort.let_eff, Sort.let_eff eff))
                res
            in
            go res ecompsubs
          else
            let res =
              SimplResult.map_constr (Constr.add_sub_effs_eff (effs, eff)) res
            in
            go res ecompsubs
    in
    go res

  let map_eql eql ~f = List.map eql ~f:(fun (a1, a2) -> (f a1, f a2))
  let subst_cont_cont (ev, e) = Term.subst_conts_cont (Map.Poly.singleton ev e)
  let subst_cont_sort (ev, e) = Term.subst_conts_sort (Map.Poly.singleton ev e)

  let subst_cont_opsig (ev, e) =
    Term.subst_conts_opsig (Map.Poly.singleton ev e)

  let subst_sort_cont (sv, s) = Term.subst_sorts_cont (Map.Poly.singleton sv s)
  let subst_sort_sort (sv, s) = Term.subst_sorts_sort (Map.Poly.singleton sv s)

  let subst_sort_opsig (sv, s) =
    Term.subst_sorts_opsig (Map.Poly.singleton sv s)

  let subst_opsig_cont (rv, o) =
    Term.subst_opsigs_cont (Map.Poly.singleton rv o)

  let subst_opsig_sort (rv, o) =
    Term.subst_opsigs_sort (Map.Poly.singleton rv o)

  let subst_opsig_opsig (rv, o) =
    Term.subst_opsigs_opsig (Map.Poly.singleton rv o)

  module Subst = struct
    type t = {
      etheta : (evar, Sort.e) Map.Poly.t;
      stheta : (svar, Sort.t) Map.Poly.t;
      otheta : (rvar, Sort.o) Map.Poly.t;
    }

    let empty =
      {
        etheta = Map.Poly.empty;
        stheta = Map.Poly.empty;
        otheta = Map.Poly.empty;
      }

    let add_subst_cont (ev, e) sb =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s |-> %s"
                (Ast.Ident.name_of_evar ev)
                (Term.str_of_cont e));
      {
        etheta =
          sb.etheta
          |> Map.Poly.map ~f:(subst_cont_cont (ev, e))
          |> Map.Poly.add_exn ~key:ev ~data:e;
        stheta = Map.Poly.map sb.stheta ~f:(subst_cont_sort (ev, e));
        otheta = Map.Poly.map sb.otheta ~f:(subst_cont_opsig (ev, e));
      }

    let add_subst_sort (sv, s) sb =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s |-> %s"
                (Ast.Ident.name_of_svar sv)
                (Term.str_of_sort s));
      {
        etheta = Map.Poly.map sb.etheta ~f:(subst_sort_cont (sv, s));
        stheta =
          sb.stheta
          |> Map.Poly.map ~f:(subst_sort_sort (sv, s))
          |> Map.Poly.add_exn ~key:sv ~data:s;
        otheta = Map.Poly.map sb.otheta ~f:(subst_sort_opsig (sv, s));
      }

    let add_subst_opsig (rv, o) sb =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s |-> %s"
                (Ast.Ident.name_of_rvar rv)
                (Term.str_of_opsig o));
      {
        etheta = Map.Poly.map sb.etheta ~f:(subst_opsig_cont (rv, o));
        stheta = Map.Poly.map sb.stheta ~f:(subst_opsig_sort (rv, o));
        otheta =
          sb.otheta
          |> Map.Poly.map ~f:(subst_opsig_opsig (rv, o))
          |> Map.Poly.add_exn ~key:rv ~data:o;
      }

    let subst_to_sort sb =
      Term.subst_opsigs_sort sb.otheta
      <<< Term.subst_sorts_sort sb.stheta
      <<< Term.subst_conts_sort sb.etheta

    let subst_to_cont sb =
      Term.subst_opsigs_cont sb.otheta
      <<< Term.subst_sorts_cont sb.stheta
      <<< Term.subst_conts_cont sb.etheta

    let subst_to_opsig sb =
      Term.subst_opsigs_opsig sb.otheta
      <<< Term.subst_sorts_opsig sb.stheta
      <<< Term.subst_conts_opsig sb.etheta

    let ovars_of sb =
      Set.Poly.union_list
        (Map.key_set sb.otheta
         :: List.map (Map.data sb.otheta) ~f:Term.rvs_of_opsig
        @ List.map (Map.data sb.stheta) ~f:Term.rvs_of_sort
        @ List.map (Map.data sb.etheta) ~f:Term.rvs_of_cont)

    let evars_of sb =
      Set.Poly.union_list
        (Map.key_set sb.etheta
         :: List.map (Map.data sb.otheta) ~f:Term.evs_of_opsig
        @ List.map (Map.data sb.stheta) ~f:Term.evs_of_sort
        @ List.map (Map.data sb.etheta) ~f:Term.evs_of_cont)
  end

  module UniResult = struct
    type t = { subst : Subst.t }
  end

  module UniState = struct
    type t = {
      res : UniResult.t;
      eeqls : (Sort.e * Sort.e) list;
      seqls : (Sort.t * Sort.t) list;
      oeqls : (Sort.o * Sort.o) list;
    }

    let add_eeqls x state =
      if print_log then
        List.iter x ~f:(fun (e1, e2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_cont e1)
                    (Term.str_of_cont e2)));
      { state with eeqls = x @ state.eeqls }

    let add_seqls x state =
      if print_log then
        List.iter x ~f:(fun (s1, s2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_sort s1)
                    (Term.str_of_sort s2)));
      { state with seqls = x @ state.seqls }

    let add_oeqls x state =
      if print_log then
        List.iter x ~f:(fun (o1, o2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_opsig o1)
                    (Term.str_of_opsig o2)));
      { state with oeqls = x @ state.oeqls }

    let add_eqls c1 c2 state =
      let open Sort in
      state
      |> add_oeqls [ (c2.op_sig, c1.op_sig) ]
      |> add_seqls [ (c1.val_type, c2.val_type) ]
      |> add_eeqls [ (c1.cont_eff, c2.cont_eff) ]

    let subst_cont (ev, e) state =
      {
        res = { subst = Subst.add_subst_cont (ev, e) state.res.subst };
        eeqls = map_eql state.eeqls ~f:(subst_cont_cont (ev, e));
        seqls = map_eql state.seqls ~f:(subst_cont_sort (ev, e));
        oeqls = map_eql state.oeqls ~f:(subst_cont_opsig (ev, e));
      }

    let subst_sort (sv, s) state =
      {
        res = { subst = Subst.add_subst_sort (sv, s) state.res.subst };
        eeqls = map_eql state.eeqls ~f:(subst_sort_cont (sv, s));
        seqls = map_eql state.seqls ~f:(subst_sort_sort (sv, s));
        oeqls = map_eql state.oeqls ~f:(subst_sort_opsig (sv, s));
      }

    let subst_opsig (rv, o) state =
      {
        res = { subst = Subst.add_subst_opsig (rv, o) state.res.subst };
        eeqls = map_eql state.eeqls ~f:(subst_opsig_cont (rv, o));
        seqls = map_eql state.seqls ~f:(subst_opsig_sort (rv, o));
        oeqls = map_eql state.oeqls ~f:(subst_opsig_opsig (rv, o));
      }
  end

  let rec unify_eeqls (state : UniState.t) =
    match state.eeqls with
    | [] -> state
    | (e1, e2) :: eeqls -> (
        let state = { state with eeqls } in
        let fail () =
          raise
          @@ Solve_failure
               (sprintf "unification failed: %s = %s" (Term.str_of_cont e1)
                  (Term.str_of_cont e2))
        in
        if Stdlib.(e1 = e2) then unify_eeqls state
        else
          match (e1, e2) with
          | Sort.Pure, Sort.Closed | Sort.Closed, Sort.Pure -> unify_eeqls state
          | Sort.Eff (c11, c12), Sort.Eff (c21, c22) ->
              state |> UniState.add_eqls c11 c21 |> UniState.add_eqls c12 c22
              |> unify_eeqls
          | Sort.EVar ev, e | e, Sort.EVar ev ->
              if Set.mem (Term.evs_of_cont e) ev then fail ()
              else state |> UniState.subst_cont (ev, e) |> unify_eeqls
          | _ -> fail ())

  let rec unify_seqls (state : UniState.t) =
    match state.seqls with
    | [] -> state
    | (s1, s2) :: seqls -> (
        let state = { state with seqls } in
        let fail () =
          raise
          @@ Solve_failure
               (sprintf "unification failed: %s = %s" (Term.str_of_sort s1)
                  (Term.str_of_sort s2))
        in
        if Stdlib.(s1 = s2) then unify_seqls state
        else
          match (s1, s2) with
          | T_array.SArray (t11, t12), T_array.SArray (t21, t22) ->
              state
              |> UniState.add_seqls [ (t11, t21); (t12, t22) ]
              |> unify_seqls
          | Sort.SArrow (t1, c1), Sort.SArrow (t2, c2) ->
              state |> UniState.add_eqls c1 c2
              |> UniState.add_seqls [ (t1, t2) ]
              |> unify_seqls
          | Sort.SVar sv, t | t, Sort.SVar sv ->
              if Set.mem (Term.svs_of_sort t) sv then fail ()
              else state |> UniState.subst_sort (sv, t) |> unify_seqls
          | T_dt.SDT dt1, T_dt.SDT dt2 ->
              let args1 = Datatype.params_of dt1 in
              let args2 = Datatype.params_of dt2 in
              if List.length args1 = List.length args2 then
                state
                |> UniState.add_seqls (List.zip_exn args1 args2)
                |> unify_seqls
              else fail ()
          | T_tuple.STuple ss1, T_tuple.STuple ss2 ->
              state |> UniState.add_seqls (List.zip_exn ss1 ss2) |> unify_seqls
          | _ -> fail ())

  let rec unify_oeqls (state : UniState.t) =
    match state.oeqls with
    | [] -> state
    | (o1, o2) :: oeqls -> (
        let state = { state with oeqls } in
        let fail () =
          raise
          @@ Solve_failure
               (sprintf "unification failed: %s = %s" (Term.str_of_opsig o1)
                  (Term.str_of_opsig o2))
        in
        if Stdlib.(o1 = o2) then unify_oeqls state
        else
          match (o1, o2) with
          | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, Some rv2)
            when Stdlib.(rv1 <> rv2) ->
              (*if List.is_empty opmap1 && List.is_empty opmap2 then
                          state
                          |> UniState.subst_opsig (rv1, Sort.OpSig ([], Some rv2))
                          |> unify_oeqls
                        else*)
              let lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              let rv = mk_fresh_rvar () in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Ast.Ident.name_of_rvar rv);
              let opsigl = Sort.OpSig (ALMap.of_alist_exn lefts, Some rv) in
              let opsigr = Sort.OpSig (ALMap.of_alist_exn rights, Some rv) in
              if
                Set.mem (Term.rvs_of_opsig opsigr) rv1
                || Set.mem (Term.rvs_of_opsig opsigl) rv2
              then fail ()
              else
                state
                |> UniState.subst_opsig (rv1, opsigr)
                |> UniState.subst_opsig (rv2, opsigl)
                |> UniState.add_seqls (List.map boths ~f:snd)
                |> unify_oeqls
          | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, Some rv2)
            when Stdlib.(rv1 = rv2) ->
              let lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              if Fn.non List.is_empty lefts || Fn.non List.is_empty rights then
                fail ()
              else
                state
                |> UniState.add_seqls (List.map boths ~f:snd)
                |> unify_oeqls
          | Sort.OpSig (opmap, Some rv), Sort.OpSig (opmap', None)
          | Sort.OpSig (opmap', None), Sort.OpSig (opmap, Some rv) ->
              let lefts, boths, rights = ALMap.split_lbr opmap opmap' in
              if Fn.non List.is_empty lefts then fail ()
              else
                let opsigr = Sort.OpSig (ALMap.of_alist_exn rights, None) in
                if Set.mem (Term.rvs_of_opsig opsigr) rv then fail ()
                else
                  state
                  |> UniState.subst_opsig (rv, opsigr)
                  |> UniState.add_seqls (List.map boths ~f:snd)
                  |> unify_oeqls
          | Sort.OpSig (opmap1, None), Sort.OpSig (opmap2, None) ->
              let lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              if Fn.non List.is_empty lefts || Fn.non List.is_empty rights then
                fail ()
              else
                state
                |> UniState.add_seqls (List.map boths ~f:snd)
                |> unify_oeqls
          | _ -> fail ())

  let rec fully_unify_eqls (state : UniState.t) =
    if
      List.is_empty state.eeqls && List.is_empty state.seqls
      && List.is_empty state.oeqls
    then state.res
    else (
      if print_log then (
        Debug.print @@ lazy "==== eeqls:";
        List.iter state.eeqls ~f:(fun (e1, e2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s = %s" (Term.str_of_cont e1) (Term.str_of_cont e2)));
        Debug.print @@ lazy "==== seqls:";
        List.iter state.seqls ~f:(fun (s1, s2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s = %s" (Term.str_of_sort s1) (Term.str_of_sort s2)));
        Debug.print @@ lazy "==== oeqls:";
        List.iter state.oeqls ~f:(fun (o1, o2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s = %s" (Term.str_of_opsig o1)
                    (Term.str_of_opsig o2))));
      state |> unify_oeqls |> unify_eeqls |> unify_seqls |> fully_unify_eqls)

  module PreprocResult = struct
    type t = { constr : Constr.t; subst : Subst.t }

    let empty = { constr = Constr.empty; subst = Subst.empty }
  end

  module PreprocState = struct
    type t = {
      res : PreprocResult.t;
      esubs : (Sort.e * Sort.e) list;
      ssubs : (Sort.t * Sort.t) list;
      osubs : (Sort.o * Sort.o) list;
      ecompsubs : (Sort.e list * Sort.e) list;
    }

    let init ecompsubs osubs =
      { res = PreprocResult.empty; esubs = []; ssubs = []; osubs; ecompsubs }

    let add_esubs x state = { state with esubs = x @ state.esubs }
    let add_ssubs x state = { state with ssubs = x @ state.ssubs }
    let add_osubs x state = { state with osubs = x @ state.osubs }

    let add_subs c1 c2 state =
      let open Sort in
      add_esubs [ (c1.cont_eff, c2.cont_eff) ]
      @@ add_ssubs [ (c1.val_type, c2.val_type) ]
      @@ add_osubs [ (c2.op_sig, c1.op_sig) ] state

    (*let add_ecompsubs x state = { state with ecompsubs = x @ state.ecompsubs }*)

    let from_subst_constr (subst : Subst.t) (constr : Constr.t) : t =
      let subst_to_cont = Subst.subst_to_cont subst in
      (*let subst_to_sort = Subst.subst_to_sort subst in*)
      let subst_to_opsig = Subst.subst_to_opsig subst in
      let ssubs, sub_sv_sv =
        List.partition_map constr.sub_sv_sv ~f:(fun (sv1, sv2) ->
            match
              (Map.Poly.find subst.stheta sv1, Map.Poly.find subst.stheta sv2)
            with
            | Some s1, Some s2 -> First (s1, s2)
            | Some s1, None -> First (s1, Sort.SVar sv2)
            | None, Some s2 -> First (Sort.SVar sv1, s2)
            | None, None -> Second (sv1, sv2))
      in
      let sub_effs_eff =
        List.unique
        @@ List.map
             (List.map constr.sub_evs_eff ~f:(fun (evs, eff) ->
                  (List.map evs ~f:(fun evar -> Sort.EVar evar), eff))
             @ constr.sub_effs_eff)
             ~f:(fun (effs, eff) ->
               ( List.filter ~f:(Sort.is_pure >> not)
                 @@ List.map effs ~f:subst_to_cont,
                 subst_to_cont eff ))
      in
      (*let esubs, sub_effs_eff =
          List.partition_map sub_effs_eff ~f:(fun (effs, eff) ->
              match effs with
              | [ eff' ] -> First (eff', eff)
              | _ -> Second (effs, eff))
        in*)
      let ecomps, ecompsubs, sub_effs_eff =
        List.partition3_map sub_effs_eff ~f:(fun (effs, eff) ->
            if List.for_all (eff :: effs) ~f:Sort.is_eff then
              `Fst (List.map effs ~f:Sort.let_eff, Sort.let_eff eff)
            else if
              Sort.is_pure eff
              || List.exists (eff :: effs) ~f:Sort.is_closed
              || (Sort.is_evar eff && List.exists effs ~f:Sort.is_eff)
            then `Snd (effs, eff)
            else `Trd (effs, eff))
      in
      let _, sub_evs_eff, sub_effs_eff =
        List.partition3_map sub_effs_eff ~f:(fun (effs, eff) ->
            match (effs, eff) with
            | [ eff' ], eff when Stdlib.(eff = eff') -> `Fst ()
            | _ ->
                if List.for_all effs ~f:Sort.is_evar then
                  `Snd (List.map effs ~f:Sort.let_evar, eff)
                else `Trd (effs, eff))
      in
      let ecomps =
        List.unique
          (ecomps
          @ List.map constr.ecomps ~f:(fun (es, (c1, c2)) ->
                match subst_to_cont (Sort.mk_cont_eff c1 c2) with
                | Sort.Eff (c1, c2) ->
                    ( List.map es ~f:(fun (c1, c2) ->
                          match subst_to_cont (Sort.mk_cont_eff c1 c2) with
                          | Sort.Eff (c1, c2) -> (c1, c2)
                          | _ -> assert false),
                      (c1, c2) )
                | _ -> assert false))
      in
      let osubs_from_ov_ov, sub_ov_ov =
        List.partition_map constr.sub_ov_ov ~f:(fun (ovar1, ovar2) ->
            match
              ( Map.Poly.find subst.otheta ovar1,
                Map.Poly.find subst.otheta ovar2 )
            with
            | Some opsig1, Some opsig2 -> First (opsig1, opsig2)
            | Some opsig1, None -> First (opsig1, Sort.OpSig ([], Some ovar2))
            | None, Some opsig2 -> First (Sort.OpSig ([], Some ovar1), opsig2)
            | None, None -> Second (ovar1, ovar2))
      in
      let osubs_from_ov_opsig, sub_ov_opsig =
        List.partition_map constr.sub_ov_opsig ~f:(fun (ov, (map, opt)) ->
            match
              ( subst_to_opsig (Sort.OpSig (map, opt)),
                Map.Poly.find subst.otheta ov )
            with
            | opsig, Some opsig' -> First (opsig', opsig)
            | Sort.OpSig (map, opt), None -> Second (ov, (map, opt))
            | _ -> failwith "")
      in
      let osubs_from_opsig_ov, sub_opsig_ov =
        List.partition_map constr.sub_opsig_ov ~f:(fun ((map, opt), ov) ->
            match
              ( subst_to_opsig (Sort.OpSig (map, opt)),
                Map.Poly.find subst.otheta ov )
            with
            | opsig, Some opsig' -> First (opsig, opsig')
            | Sort.OpSig (map, opt), None -> Second ((map, opt), ov)
            | _ -> failwith "")
      in
      let osubs =
        List.concat
          [ osubs_from_ov_ov; osubs_from_ov_opsig; osubs_from_opsig_ov ]
      in
      {
        res =
          {
            constr =
              {
                sub_sv_sv;
                sub_evs_eff;
                sub_effs_eff;
                ecomps;
                sub_ov_ov;
                sub_ov_opsig;
                sub_opsig_ov;
              };
            subst;
          };
        esubs = [];
        ssubs;
        osubs;
        ecompsubs;
      }
  end

  let rec preprocess (state : PreprocState.t) =
    if
      List.is_empty state.esubs && List.is_empty state.ssubs
      && List.is_empty state.osubs
      && List.is_empty state.ecompsubs
    then state.res
    else (
      if print_log then (
        Debug.print @@ lazy "==== esubs:";
        List.iter state.esubs ~f:(fun (e1, e2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s <: %s" (Term.str_of_cont e1) (Term.str_of_cont e2)));
        Debug.print @@ lazy "==== ssubs:";
        List.iter state.ssubs ~f:(fun (s1, s2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s <: %s" (Term.str_of_sort s1) (Term.str_of_sort s2)));
        Debug.print @@ lazy "==== osubs:";
        List.iter state.osubs ~f:(fun (o1, o2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s <: %s" (Term.str_of_opsig o1)
                    (Term.str_of_opsig o2)));
        Debug.print @@ lazy "==== ecompsubs:";
        List.iter state.ecompsubs ~f:(fun (effs, eff) ->
            Debug.print
            @@ lazy
                 (sprintf "%s <: %s"
                    (String.concat_map_list ~sep:" " effs ~f:Term.str_of_cont)
                    (Term.str_of_cont eff))));
      let simpl_res =
        fully_simplify_subs
          {
            res =
              simplify_ecompsubs
                {
                  constr = state.res.constr;
                  eeqls = [];
                  seqls = [];
                  oeqls = [];
                }
                state.ecompsubs;
            esubs = state.esubs;
            ssubs = state.ssubs;
            osubs = state.osubs;
          }
      in
      let uni_res =
        fully_unify_eqls
          {
            res = { subst = state.res.subst };
            eeqls = simpl_res.eeqls;
            seqls = simpl_res.seqls;
            oeqls = simpl_res.oeqls;
          }
      in
      preprocess (PreprocState.from_subst_constr uni_res.subst simpl_res.constr))

  module SearchState = struct
    type t = { constr : Constr.t; subst : Subst.t; embedded : evar Set.Poly.t }

    let init (res : PreprocResult.t) =
      { constr = res.constr; subst = res.subst; embedded = Set.Poly.empty }

    let add_subst_conts sub state =
      let subst =
        Set.fold sub ~init:state.subst ~f:(fun subst (ev, e) ->
            Subst.add_subst_cont (ev, e) subst)
      in
      PreprocState.from_subst_constr subst state.constr

    let add_subst_opsigs sub state =
      let subst =
        Set.fold sub ~init:state.subst ~f:(fun subst (rv, o) ->
            Subst.add_subst_opsig (rv, o) subst)
      in
      PreprocState.from_subst_constr subst state.constr
  end

  let rec search_ecomps ~embed (state : SearchState.t) =
    match state.constr.ecomps with
    | [] -> state
    | (es, (c_first, c_last)) :: ecomps -> (
        let state = { state with constr = { state.constr with ecomps } } in
        match es with
        | [] ->
            (*let uni_res =
                fully_unify_eqls
                  {
                    res = { subst = state.subst };
                    seqls = [ (s_first, s_last) ];
                    eeqls = [ (e_first, e_last) ];
                    oeqls = [ (o_first, o_last) ];
                  }
              in*)
            let preproc_res =
              preprocess
              @@ PreprocState.add_subs c_first c_last
              @@ PreprocState.from_subst_constr (*uni_res.subst*) state.subst
                   state.constr
            in
            search_ecomps ~embed
              {
                state with
                constr = preproc_res.constr;
                subst = preproc_res.subst;
              }
        | (c1, c2) :: es ->
            (*let uni_res =
                fully_unify_eqls
                  {
                    res = { subst = state.subst };
                    seqls = [ (s_last, s2) ];
                    eeqls = [ (e_last, e2) ];
                    oeqls = [ (o_last, o2) ];
                  }
              in*)
            let state =
              {
                state with
                constr =
                  { state.constr with ecomps = (es, (c_first, c1)) :: ecomps };
              }
            in
            let preproc_res =
              preprocess
              @@ PreprocState.add_subs c2 c_last
              @@ PreprocState.from_subst_constr (*uni_res.subst*) state.subst
                   state.constr
            in
            search_ecomps ~embed
              {
                state with
                constr = preproc_res.constr;
                subst = preproc_res.subst;
              })

  let rec search_effs_eff ~embed acc (state : SearchState.t) =
    match state.constr.sub_effs_eff with
    | [] ->
        assert (List.is_empty acc);
        state
    (*| ([ Sort.EVar ev1 ], Sort.EVar ev2) :: sub_effs_eff
      when Ast.Ident.evar_equal ev1 ev2 ->
        let state =
          { state with constr = { state.constr with sub_effs_eff } }
        in
        search_effs_eff ~embed acc state*)
    | (es, (Sort.EVar _ as e)) :: sub_effs_eff
      when List.for_all es ~f:Sort.is_evar ->
        let state =
          {
            state with
            constr =
              Constr.add_sub_evs_eff
                (List.map es ~f:Sort.let_evar, e)
                { state.constr with sub_effs_eff };
          }
        in
        search_effs_eff ~embed acc state
    | (es, (Sort.Eff (c_first, c_last) as e)) :: sub_effs_eff -> (
        let state =
          { state with constr = { state.constr with sub_effs_eff } }
        in
        match es with
        | [] ->
            (*let uni_res =
                fully_unify_eqls
                  {
                    res = { subst = state.subst };
                    seqls = [ (s_first, s_last) ];
                    eeqls = [ (e_first, e_last) ];
                    oeqls = [ (o_first, o_last) ];
                  }
              in*)
            let preproc_res =
              preprocess
              @@ PreprocState.add_subs c_first c_last
              @@ PreprocState.from_subst_constr (*uni_res.subst*) state.subst
                   state.constr
            in
            search_effs_eff ~embed acc
              {
                state with
                constr = preproc_res.constr;
                subst = preproc_res.subst;
              }
        | Sort.Eff (c1, c2) :: es ->
            (*let uni_res =
                fully_unify_eqls
                  {
                    res = { subst = state.subst };
                    seqls = [ (s_last, s2) ];
                    eeqls = [ (e_last, e2) ];
                    oeqls = [ (o_last, o2) ];
                  }
              in*)
            let state =
              {
                state with
                constr =
                  {
                    state.constr with
                    sub_effs_eff =
                      (es, Sort.mk_cont_eff c_first c1) :: sub_effs_eff;
                  };
              }
            in
            let preproc_res =
              preprocess
              @@ PreprocState.add_subs c2 c_last
              @@ PreprocState.from_subst_constr (*uni_res.subst*) state.subst
                   state.constr
            in
            search_effs_eff ~embed acc
              {
                state with
                constr = preproc_res.constr;
                subst = preproc_res.subst;
              }
        | Sort.EVar _ :: _ ->
            let es1, es2 = List.split_while es ~f:Sort.is_evar in
            if List.is_empty es2 then
              let state =
                {
                  state with
                  constr =
                    {
                      state.constr with
                      sub_evs_eff =
                        (List.map es1 ~f:Sort.let_evar, e)
                        :: state.constr.sub_evs_eff;
                    };
                }
              in
              let preproc_res =
                preprocess
                @@ PreprocState.from_subst_constr state.subst state.constr
              in
              search_effs_eff ~embed acc
                {
                  state with
                  constr = preproc_res.constr;
                  subst = preproc_res.subst;
                }
            else
              let c = Sort.mk_fresh_triple () in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_triple c);
              let cont1 = Sort.mk_cont_eff c c_last in
              let cont2 = Sort.mk_cont_eff c_first c in
              let state =
                {
                  state with
                  constr =
                    {
                      state.constr with
                      sub_evs_eff =
                        (List.map es1 ~f:Sort.let_evar, cont1)
                        :: state.constr.sub_evs_eff;
                      sub_effs_eff = (es2, cont2) :: sub_effs_eff;
                    };
                }
              in
              let preproc_res =
                preprocess
                @@ PreprocState.from_subst_constr state.subst state.constr
              in
              search_effs_eff ~embed acc
                {
                  state with
                  constr = preproc_res.constr;
                  subst = preproc_res.subst;
                }
            (*let assume_eff () =
                let ov1, sv1, ev1 = Sort.mk_fresh_triple () in
                let ov2, sv2, ev2 = Sort.mk_fresh_triple () in
                let cont = Sort.mk_cont_eff (ov1, sv1, ev1) (ov2, sv2, ev2) in
                if print_log then
                  Debug.print @@ lazy ("introducing " ^ Term.str_of_cont cont);
                let cont' =
                  Sort.mk_cont_eff (o_first, s_first, e_first) (ov1, sv1, ev1)
                in
                let sub_effs_eff = (es, cont') :: sub_effs_eff in
                let preproc_res =
                  preprocess
                  @@ PreprocState.add_esubs [ (ev2, e_last) ]
                  @@ PreprocState.add_ssubs [ (sv2, s_last) ]
                  @@ PreprocState.add_osubs [ (o_last, ov2) ]
                  @@ SearchState.add_subst_conts [ (ev, cont) ]
                  @@ { state with constr = { state.constr with sub_effs_eff } }
                in
                search_effs_eff ~embed acc
                  {
                    constr = preproc_res.constr;
                    subst = preproc_res.subst;
                    embedded = Set.add state.embedded ev;
                  }
              in
              let assume_pure () =
                let sub_effs_eff =
                  ( es,
                    Sort.Eff (o_first, s_first, e_first, o_last, s_last, e_last)
                  )
                  :: sub_effs_eff
                in
                let preproc_res =
                  preprocess
                  @@ SearchState.add_subst_conts [ (ev, Sort.Pure) ]
                  @@ { state with constr = { state.constr with sub_effs_eff } }
                in
                search_effs_eff ~embed acc
                @@ {
                     constr = preproc_res.constr;
                     subst = preproc_res.subst;
                     embedded = state.embedded;
                   }
              in

              let assume1, assume2 =
                if embed then (assume_eff, assume_pure)
                else (assume_pure, assume_eff)
              in
              try assume1 () with Solve_failure _ -> assume2 ()*)
        | _ -> failwith "unknown effect")
    | _ -> assert false

  let rec fully_search ~embed (state : SearchState.t) =
    if Fn.non List.is_empty state.constr.ecomps then (
      if print_log then (
        Debug.print @@ lazy "==== ecomps:";
        List.iter state.constr.ecomps ~f:(fun (effs, (c1, c2)) ->
            Debug.print
            @@ lazy
                 (sprintf "%s <: %s => %s"
                    (String.concat_map_list ~sep:" " effs ~f:(fun (c1, c2) ->
                         Term.str_of_cont (Sort.mk_cont_eff c1 c2)))
                    (Term.str_of_triple c1) (Term.str_of_triple c2))));
      let state = search_ecomps ~embed state in
      let preproc_res =
        preprocess (PreprocState.from_subst_constr state.subst state.constr)
      in
      fully_search ~embed
        { state with constr = preproc_res.constr; subst = preproc_res.subst })
    else
      let uovars =
        (*Set.diff*)
        Constr.unconstrained_ovars_of state.constr
        (*(Subst.ovars_of state.subst)*)
      in
      if Fn.non Set.is_empty uovars then (
        if print_log then (
          Debug.print @@ lazy "==== unconstrained ovars:";
          Debug.print
          @@ lazy
               (String.concat_map_set ~sep:"," ~f:Ast.Ident.name_of_rvar uovars));
        let preproc_res =
          preprocess
          @@ SearchState.add_subst_opsigs
               (Set.Poly.map uovars ~f:(fun ovar ->
                    (ovar, Sort.empty_closed_opsig)))
               state
        in
        fully_search ~embed
          { state with constr = preproc_res.constr; subst = preproc_res.subst })
      else
        let oeqs =
          let tc =
            PartOrd.transitive_closure_of
              (Set.Poly.of_list state.constr.sub_ov_ov)
          in
          let nodes =
            List.unique @@ uncurry2 ( @ ) (List.unzip state.constr.sub_ov_ov)
          in
          let dict =
            Map.Poly.of_alist_exn @@ List.mapi nodes ~f:(fun i n -> (n, i))
          in
          let uf = UnionFind.mk_size_uf ~size:(List.length nodes) in
          List.iter state.constr.sub_ov_ov ~f:(fun (ovar1, ovar2) ->
              if Set.mem tc (ovar1, ovar2) && Set.mem tc (ovar2, ovar1) then
                UnionFind.unite
                  (Map.Poly.find_exn dict ovar1)
                  (Map.Poly.find_exn dict ovar2)
                  uf);
          let groups = UnionFind.get_groups uf in
          Set.Poly.of_list
          @@ List.concat_map groups ~f:(fun ids ->
                 let id, ids = List.hd_tl ids in
                 List.map ids ~f:(fun id' ->
                     ( List.nth_exn nodes id',
                       Sort.mk_empty_open_opsig_from_rvar
                       @@ List.nth_exn nodes id )))
        in
        if Fn.non Set.is_empty oeqs then (
          if print_log then (
            Debug.print @@ lazy "==== sub_ov_ov:";
            List.iter state.constr.sub_ov_ov ~f:(fun (ovar1, ovar2) ->
                Debug.print
                @@ lazy
                     (sprintf "%s <: %s"
                        (Ast.Ident.name_of_rvar ovar1)
                        (Ast.Ident.name_of_rvar ovar2))));
          let preproc_res =
            preprocess @@ SearchState.add_subst_opsigs oeqs state
          in
          fully_search ~embed
            {
              state with
              constr = preproc_res.constr;
              subst = preproc_res.subst;
            })
        else
          let covars =
            Set.Poly.union_list
            @@ List.map state.constr.sub_ov_ov ~f:(fun (ovar1, _ovar2) ->
                   Set.Poly.singleton ovar1)
            @ List.map state.constr.sub_opsig_ov ~f:(fun ((map, opt), _ovar) ->
                  Term.rvs_of_opsig (Sort.OpSig (map (*ToDo*), opt)))
          in
          let oeqs =
            Set.Poly.of_list
            @@ List.map ~f:(fun ov_opsigs ->
                   let ov_opsigs = List.unique ov_opsigs in
                   let ov = fst @@ List.hd_exn ov_opsigs in
                   let ops =
                     List.unique
                     @@ List.concat_map ov_opsigs
                          ~f:(snd >> fst >> List.map ~f:fst)
                   in
                   let opsig =
                     Sort.OpSig
                       ( ALMap.of_alist_exn
                         @@ List.map ops ~f:(fun op ->
                                (op, Sort.mk_fresh_svar ())),
                         None )
                   in
                   if print_log then
                     Debug.print
                     @@ lazy ("introducing " ^ Term.str_of_opsig opsig);
                   (ov, opsig)
                   (*match List.unique ov_opsigs with
                     | [ (ov, (map, opt)) ] -> (ov, Sort.OpSig (map, opt))
                     | _ -> failwith (string_of_int @@ List.length ov_opsigs)*))
            @@ List.classify (fun (ov1, _) (ov2, _) ->
                   Ast.Ident.rvar_equal ov1 ov2)
            @@ List.filter state.constr.sub_ov_opsig
                 ~f:(fst >> Set.mem covars >> not)
          in
          if Fn.non Set.is_empty oeqs then (
            if print_log then (
              Debug.print @@ lazy "==== sub_ov_ov:";
              List.iter state.constr.sub_ov_ov ~f:(fun (ovar1, ovar2) ->
                  Debug.print
                  @@ lazy
                       (sprintf "%s <: %s"
                          (Ast.Ident.name_of_rvar ovar1)
                          (Ast.Ident.name_of_rvar ovar2)));
              Debug.print @@ lazy "==== sub_ov_opsig:";
              List.iter state.constr.sub_ov_opsig ~f:(fun (ovar, (map, opt)) ->
                  Debug.print
                  @@ lazy
                       (sprintf "%s <: %s"
                          (Ast.Ident.name_of_rvar ovar)
                          (Term.str_of_opsig (Sort.OpSig (map, opt)))));
              Debug.print @@ lazy "==== sub_opsig_ov:";
              List.iter state.constr.sub_opsig_ov ~f:(fun ((map, opt), ovar) ->
                  Debug.print
                  @@ lazy
                       (sprintf "%s <: %s"
                          (Term.str_of_opsig (Sort.OpSig (map, opt)))
                          (Ast.Ident.name_of_rvar ovar))));
            let preproc_res =
              preprocess @@ SearchState.add_subst_opsigs oeqs state
            in
            fully_search ~embed
              {
                state with
                constr = preproc_res.constr;
                subst = preproc_res.subst;
              })
          else
            let uevars =
              (*Set.diff*)
              Constr.unconstrained_evars_of state.constr
              (*(Subst.evars_of state.subst)*)
            in
            if Fn.non Set.is_empty uevars then (
              if print_log then (
                Debug.print @@ lazy "==== unconstrained evars:";
                Debug.print
                @@ lazy
                     (String.concat_map_set ~sep:"," ~f:Ast.Ident.name_of_evar
                        uevars));
              let preproc_res =
                preprocess
                @@ SearchState.add_subst_conts
                     (Set.Poly.map uevars ~f:(fun ev -> (ev, Sort.Pure)))
                     state
              in
              fully_search ~embed
                {
                  state with
                  constr = preproc_res.constr;
                  subst = preproc_res.subst;
                })
            else
              let sub_ev_ev =
                List.filter_map state.constr.sub_evs_eff ~f:(function
                  | [ ev ], eff when Sort.is_evar eff ->
                      Some (ev, Sort.let_evar eff)
                  | _ -> None)
              in
              let eeqs =
                let tc =
                  PartOrd.transitive_closure_of (Set.Poly.of_list sub_ev_ev)
                in
                let nodes =
                  List.unique @@ uncurry2 ( @ ) (List.unzip sub_ev_ev)
                in
                let dict =
                  Map.Poly.of_alist_exn
                  @@ List.mapi nodes ~f:(fun i n -> (n, i))
                in
                let uf = UnionFind.mk_size_uf ~size:(List.length nodes) in
                List.iter sub_ev_ev ~f:(fun (evar1, evar2) ->
                    if Set.mem tc (evar1, evar2) && Set.mem tc (evar2, evar1)
                    then
                      UnionFind.unite
                        (Map.Poly.find_exn dict evar1)
                        (Map.Poly.find_exn dict evar2)
                        uf);
                let groups = UnionFind.get_groups uf in
                Set.Poly.of_list
                @@ List.concat_map groups ~f:(fun ids ->
                       let id, ids = List.hd_tl ids in
                       List.map ids ~f:(fun id' ->
                           ( List.nth_exn nodes id',
                             Sort.EVar (List.nth_exn nodes id) )))
              in
              if Fn.non Set.is_empty eeqs then (
                if print_log then (
                  Debug.print @@ lazy "==== sub_ev_ev:";
                  List.iter sub_ev_ev ~f:(fun (evar1, evar2) ->
                      Debug.print
                      @@ lazy
                           (sprintf "%s <: %s"
                              (Ast.Ident.name_of_evar evar1)
                              (Ast.Ident.name_of_evar evar2))));
                let preproc_res =
                  preprocess @@ SearchState.add_subst_conts eeqs state
                in
                fully_search ~embed
                  {
                    state with
                    constr = preproc_res.constr;
                    subst = preproc_res.subst;
                  })
              else if
                List.is_empty state.constr.sub_ov_ov
                && List.is_empty state.constr.sub_ov_opsig
                && List.is_empty state.constr.sub_opsig_ov
                && List.for_all state.constr.sub_effs_eff ~f:(fun (effs, eff) ->
                       List.for_all (eff :: effs) ~f:Sort.is_evar)
              then state
              else (
                if print_log then (
                  Debug.print @@ lazy "==== sub_ov_ov:";
                  List.iter state.constr.sub_ov_ov ~f:(fun (ovar1, ovar2) ->
                      Debug.print
                      @@ lazy
                           (sprintf "%s <: %s"
                              (Ast.Ident.name_of_rvar ovar1)
                              (Ast.Ident.name_of_rvar ovar2)));
                  Debug.print @@ lazy "==== sub_ov_opsig:";
                  List.iter state.constr.sub_ov_opsig
                    ~f:(fun (ovar, (map, opt)) ->
                      Debug.print
                      @@ lazy
                           (sprintf "%s <: %s"
                              (Ast.Ident.name_of_rvar ovar)
                              (Term.str_of_opsig (Sort.OpSig (map, opt)))));
                  Debug.print @@ lazy "==== sub_opsig_ov:";
                  List.iter state.constr.sub_opsig_ov
                    ~f:(fun ((map, opt), ovar) ->
                      Debug.print
                      @@ lazy
                           (sprintf "%s <: %s"
                              (Term.str_of_opsig (Sort.OpSig (map, opt)))
                              (Ast.Ident.name_of_rvar ovar)));
                  Debug.print @@ lazy "==== sub_evs_eff:";
                  List.iter state.constr.sub_evs_eff ~f:(fun (evs, eff) ->
                      Debug.print
                      @@ lazy
                           (sprintf "%s <: %s"
                              (String.concat_map_list ~sep:" " evs
                                 ~f:Ast.Ident.name_of_evar)
                              (Term.str_of_cont eff)));
                  Debug.print @@ lazy "==== sub_effs_eff:";
                  List.iter state.constr.sub_effs_eff ~f:(fun (effs, eff) ->
                      Debug.print
                      @@ lazy
                           (sprintf "%s <: %s"
                              (String.concat_map_list ~sep:" " effs
                                 ~f:Term.str_of_cont)
                              (Term.str_of_cont eff))));
                let state = search_effs_eff ~embed [] state in
                let preproc_res =
                  preprocess
                  @@ PreprocState.from_subst_constr state.subst state.constr
                in
                fully_search ~embed
                  {
                    state with
                    constr = preproc_res.constr;
                    subst = preproc_res.subst;
                  })

  let resolve_evs (constr : Constr.t) =
    if print_log then (
      Debug.print @@ lazy "==== sub_evs_eff:";
      List.iter constr.sub_evs_eff ~f:(fun (evs, eff) ->
          Debug.print
          @@ lazy
               (sprintf "%s <: %s"
                  (String.concat_map_list ~sep:" " evs ~f:Ast.Ident.name_of_evar)
                  (Term.str_of_cont eff)));
      Debug.print @@ lazy "==== sub_effs_eff:";
      List.iter constr.sub_effs_eff ~f:(fun (effs, eff) ->
          Debug.print
          @@ lazy
               (sprintf "%s <: %s"
                  (String.concat_map_list ~sep:" " effs ~f:Term.str_of_cont)
                  (Term.str_of_cont eff))));
    assert (
      List.for_all constr.sub_evs_eff ~f:(snd >> Sort.is_evar)
      && List.for_all constr.sub_effs_eff ~f:(fun (effs, eff) ->
             List.for_all (eff :: effs) ~f:Sort.is_evar));
    List.concat
      [
        List.concat_map constr.sub_evs_eff ~f:(fun (evs, eff) ->
            Sort.let_evar eff :: evs);
        List.concat_map constr.sub_effs_eff ~f:(fun (effs, eff) ->
            List.map (eff :: effs) ~f:Sort.let_evar);
      ]

  let resolve_svs ~init_svs (constr : Constr.t) =
    let rec go subst = function
      | [] ->
          Map.Poly.fold subst ~init:[] ~f:(fun ~key ~data s ->
              List.map data ~f:(fun sv -> (sv, key)) @ s)
      | (sv1, sv2) :: sub_sv_sv ->
          let sv, sv' =
            if Set.mem init_svs sv1 then
              if Set.mem init_svs sv2 && Stdlib.(sv2 < sv1) then (sv2, sv1)
              else (sv1, sv2)
            else if Set.mem init_svs sv2 || Stdlib.(sv2 < sv1) then (sv2, sv1)
            else (sv1, sv2)
          in
          go
            (Map.Poly.update subst sv ~f:(fun svs ->
                 sv' :: Option.value svs ~default:[]))
            sub_sv_sv
    in
    go Map.Poly.empty constr.sub_sv_sv

  let squash_evs_cont e =
    let evs = Set.to_list (Term.evs_of_cont e) in
    let sbs =
      Map.Poly.of_alist_exn (List.map evs ~f:(fun ev -> (ev, Sort.Pure)))
    in
    Term.subst_conts_cont sbs e

  let squash_evs_sort s =
    let evs = Set.to_list (Term.evs_of_sort s) in
    let sbs =
      Map.Poly.of_alist_exn (List.map evs ~f:(fun ev -> (ev, Sort.Pure)))
    in
    Term.subst_conts_sort sbs s

  let squash_evs_opsig o =
    let evs = Set.to_list (Term.evs_of_opsig o) in
    let sbs =
      Map.Poly.of_alist_exn (List.map evs ~f:(fun ev -> (ev, Sort.Pure)))
    in
    Term.subst_conts_opsig sbs o

  let squash_rvs_cont e =
    let rvs = Set.to_list (Term.rvs_of_cont e) in
    let sbs =
      Map.Poly.of_alist_exn
        (List.map rvs ~f:(fun rv -> (rv, Sort.empty_closed_opsig)))
    in
    Term.subst_opsigs_cont sbs e

  let squash_rvs_sort s =
    let rvs = Set.to_list (Term.rvs_of_sort s) in
    let sbs =
      Map.Poly.of_alist_exn
        (List.map rvs ~f:(fun rv -> (rv, Sort.empty_closed_opsig)))
    in
    Term.subst_opsigs_sort sbs s

  let squash_rvs_opsig o =
    let rvs = Set.to_list (Term.rvs_of_opsig o) in
    let sbs =
      Map.Poly.of_alist_exn
        (List.map rvs ~f:(fun rv -> (rv, Sort.empty_closed_opsig)))
    in
    Term.subst_opsigs_opsig sbs o

  let resolve ~init_svs (state : SearchState.t) : Subst.t =
    let subst_ev_pure = List.unique @@ resolve_evs state.constr in
    let subst_sv_svs =
      resolve_svs ~init_svs state.constr
      |> List.classify (fun (sv1, _) (sv2, _) -> Stdlib.(sv1 = sv2))
      |> List.map ~f:(fun svsvs ->
             ( fst @@ List.hd_exn svsvs,
               Set.Poly.of_list @@ List.map ~f:snd svsvs ))
      |> Map.Poly.of_alist_exn
    in
    let subst_sv_sv =
      let fp =
        fix
          ~f:(fun map ->
            Map.Poly.map map ~f:(fun svs ->
                Set.concat_map svs ~f:(fun sv ->
                    match Map.Poly.find map sv with
                    | None -> Set.Poly.singleton sv
                    | Some s -> s)))
          ~equal:(Map.Poly.equal Set.equal) subst_sv_svs
      in
      Map.Poly.iteri fp ~f:(fun ~key:sv ~data:svs ->
          if false then
            print_endline
              (sprintf "%s |-> %s"
                 (Ast.Ident.name_of_svar sv)
                 (String.concat_map_set svs ~sep:"\\/" ~f:Ast.Ident.name_of_svar)));
      let fp1, fp2 = Map.Poly.partition_tf fp ~f:(Set.length >> ( = ) 1) in
      let ran = Set.Poly.union_list @@ Map.Poly.data fp1 in
      let r = ref Map.Poly.empty in
      let fp2 =
        Map.Poly.map fp2 ~f:(fun svs ->
            assert (
              true
              (*ToDo: unsound if Set.Poly.length svs <> 1 *)
              || Set.length svs = 1);
            let d =
              try Set.min_elt_exn (Set.inter svs ran) (*ToDo*)
              with _ -> Set.choose_exn svs
            in
            r :=
              Set.fold (Set.diff svs ran) ~init:!r ~f:(fun m x ->
                  Map.Poly.set m ~key:x ~data:d);
            d)
      in
      Map.to_alist
      @@ Map.force_merge_list [ Map.Poly.map fp1 ~f:Set.choose_exn; fp2; !r ]
    in
    let etheta =
      Map.force_merge
        ~catch_dup:(fun (ev, e1, e2) ->
          failwith
          @@ sprintf "%s |-> %s != %s"
               (Ast.Ident.name_of_evar ev)
               (Term.str_of_cont e1) (Term.str_of_cont e2))
        (Map.Poly.of_alist_exn
        @@ List.map subst_ev_pure ~f:(fun ev -> (ev, Sort.Pure)))
      @@ Map.Poly.map state.subst.etheta ~f:(fun e ->
             let e =
               List.fold subst_ev_pure ~init:e ~f:(fun e ev ->
                   subst_cont_cont (ev, Sort.Pure) e)
             in
             List.fold subst_sv_sv ~init:e ~f:(fun e (sv1, sv2) ->
                 subst_sort_cont (sv1, Sort.SVar sv2) e))
    in
    let stheta =
      Map.force_merge
        (Map.Poly.of_alist_exn
        @@ List.map subst_sv_sv ~f:(fun (sv1, sv2) -> (sv1, Sort.SVar sv2)))
      @@ Map.Poly.map state.subst.stheta ~f:(fun s ->
             let s =
               List.fold subst_ev_pure ~init:s ~f:(fun s ev ->
                   subst_cont_sort (ev, Sort.Pure) s)
             in
             List.fold subst_sv_sv ~init:s ~f:(fun s (sv1, sv2) ->
                 subst_sort_sort (sv1, Sort.SVar sv2) s))
    in
    let otheta =
      Map.Poly.map state.subst.otheta ~f:(fun o ->
          let o =
            List.fold subst_ev_pure ~init:o ~f:(fun o ev ->
                subst_cont_opsig (ev, Sort.Pure) o)
          in
          List.fold subst_sv_sv ~init:o ~f:(fun o (sv1, sv2) ->
              subst_sort_opsig (sv1, Sort.SVar sv2) o))
    in
    { etheta; stheta; otheta }

  let eliminate ~init_evs ~init_svs ~init_rvs (subst : Subst.t) : Subst.t =
    let etheta = Map.Poly.filter_keys subst.etheta ~f:(Set.mem init_evs) in
    let stheta = Map.Poly.filter_keys subst.stheta ~f:(Set.mem init_svs) in
    let otheta = Map.Poly.filter_keys subst.otheta ~f:(Set.mem init_rvs) in
    { etheta; stheta; otheta }

  let squash ~init_evs ~init_rvs (subst : Subst.t) : Subst.t =
    let etheta =
      Map.Poly.map subst.etheta ~f:(squash_evs_cont <<< squash_rvs_cont)
    in
    let etheta =
      Set.fold init_evs ~init:etheta ~f:(fun etheta ev ->
          match Map.Poly.add etheta ~key:ev ~data:Sort.Pure with
          | `Ok etheta -> etheta
          | `Duplicate -> etheta)
    in
    let stheta =
      Map.Poly.map subst.stheta ~f:(squash_evs_sort <<< squash_rvs_sort)
    in
    let otheta =
      Map.Poly.map subst.otheta ~f:(squash_evs_opsig <<< squash_rvs_opsig)
    in
    let otheta =
      Set.fold init_rvs ~init:otheta ~f:(fun otheta rv ->
          match Map.Poly.add otheta ~key:rv ~data:Sort.empty_closed_opsig with
          | `Ok otheta -> otheta
          | `Duplicate -> otheta)
    in
    { etheta; stheta; otheta }

  let elim_pure th =
    Subst.
      {
        etheta = Map.Poly.map ~f:Term.elim_pure_cont th.etheta;
        (*ToDo*)
        stheta = Map.Poly.map ~f:Term.elim_pure_val_type th.stheta;
        otheta = Map.Poly.map ~f:Term.elim_pure_opsig th.otheta;
        (*ToDo*)
      }

  let postprocess ~init_evs ~init_svs ~init_rvs =
    resolve ~init_svs
    >> eliminate ~init_evs ~init_svs ~init_rvs
    >> squash ~init_evs ~init_rvs
    >> if config.elim_pure then elim_pure else Fn.id

  let solve eff_constrs opsig_constrs =
    let ecompsubs = Set.to_list eff_constrs in
    let osubs = Set.to_list opsig_constrs in
    let init_evs =
      Set.Poly.union_list
      @@ List.map ecompsubs ~f:(fun (effs, eff) ->
             Set.Poly.union_list (List.map (eff :: effs) ~f:Term.evs_of_cont))
      @ List.map osubs ~f:(fun (o1, o2) ->
            Set.Poly.union_list [ Term.evs_of_opsig o1; Term.evs_of_opsig o2 ])
    in
    let init_svs =
      Set.Poly.union_list
      @@ List.map ecompsubs ~f:(fun (effs, eff) ->
             Set.Poly.union_list (List.map (eff :: effs) ~f:Term.svs_of_cont))
      @ List.map osubs ~f:(fun (o1, o2) ->
            Set.Poly.union_list [ Term.svs_of_opsig o1; Term.svs_of_opsig o2 ])
    in
    let init_rvs =
      Set.Poly.union_list
      @@ List.map ecompsubs ~f:(fun (effs, eff) ->
             Set.Poly.union_list (List.map (eff :: effs) ~f:Term.rvs_of_cont))
      @ List.map osubs ~f:(fun (o1, o2) ->
            Set.Poly.union_list [ Term.rvs_of_opsig o1; Term.rvs_of_opsig o2 ])
    in
    let sol =
      PreprocState.init ecompsubs osubs
      |> preprocess |> SearchState.init |> fully_search ~embed:false
      |> postprocess ~init_evs ~init_svs ~init_rvs
    in
    Debug.print @@ lazy "==== found solution:";
    Map.Poly.iteri sol.etheta ~f:(fun ~key:ev ~data:e ->
        Debug.print
        @@ lazy (sprintf "%s := %s" (name_of_evar ev) (Term.str_of_cont e)));
    Map.Poly.iteri sol.stheta ~f:(fun ~key:sv ~data:s ->
        Debug.print
        @@ lazy (sprintf "%s := %s" (name_of_svar sv) (Term.str_of_sort s)));
    Map.Poly.iteri sol.otheta ~f:(fun ~key:sv ~data:s ->
        Debug.print
        @@ lazy (sprintf "%s := %s" (name_of_rvar sv) (Term.str_of_opsig s)));
    sol
end
