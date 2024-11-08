open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

module Make (Verbose : Debug.Config.ConfigType) = struct
  module Debug = Debug.Make (Verbose)

  type clause =
    Atom.t Set.Poly.t
    * Atom.t Set.Poly.t
    * Formula.t
    * (Ident.tvar, int) Hashtbl.Poly.t (* ns * ps * phi * tvar_occur_times *)

  type erasure = (Ident.pvar, (int * int) Set.Poly.t) Map.Poly.t
  type direct = RAF | FAR

  let enable = true
  let is_raf = function RAF -> true | _ -> false
  let is_far = function FAR -> true | _ -> false
  let str_of_atoms = String.concat_map_set ~sep:", " ~f:Atom.str_of

  let str_of_clause ((ns, ps, phi, _) : clause) =
    sprintf "%s <- %s, %s" (str_of_atoms ps) (str_of_atoms ns)
      (Formula.str_of phi)

  let str_of_pcsp_clause (ps, ns, _) =
    sprintf "%s <- %s"
      (String.concat_set ~sep:", " @@ Set.Poly.map ns ~f:Atom.str_of)
      (String.concat_set ~sep:", " @@ Set.Poly.map ps ~f:Atom.str_of)

  let str_of_erasure (e : erasure) =
    String.concat ~sep:"\n"
    @@ List.filter_map (Map.Poly.to_alist e) ~f:(fun (pvar, is) ->
           if Set.is_empty is then None
           else
             Option.return @@ sprintf "{%s}"
             @@ String.concat_map_set ~sep:", " is
                  ~f:(uncurry @@ sprintf "(%s,%d(%d))" (Ident.name_of_pvar pvar)))

  let str_of_times times =
    sprintf "{%s}"
    @@ String.concat_map_list ~sep:";  " ~f:(fun (tvar, time) ->
           sprintf "%s: %d" (Ident.name_of_tvar tvar) time)
    @@ Hashtbl.Poly.to_alist times

  let is_empty = Map.for_all ~f:Set.is_empty

  let size_of =
    Map.Poly.fold ~init:0 ~f:(fun ~key:_ ~data -> ( + ) (Set.length data))

  let look_up_occur_time ~f his a x : int =
    match Hashtbl.Poly.find his (a, x) with
    | Some times -> times
    | None ->
        let times = f x a in
        Hashtbl.Poly.set his ~key:(a, x) ~data:times;
        times

  let occur_times_in_atoms =
    let check_history = Hashtbl.Poly.create () in
    fun (x : Ident.tvar) (atoms : Atom.t Set.Poly.t) ->
      let ret =
        Set.fold atoms ~init:0 ~f:(fun ret atom ->
            ret + look_up_occur_time check_history atom x ~f:Atom.occur_times)
      in
      (* Debug.print @@ lazy (sprintf "[occur_times_in_atoms] %s : %d" (Ident.name_of_tvar x) ret); *)
      ret

  let occur_times_in_formula =
    let check_history = Hashtbl.Poly.create () in
    fun x phi ->
      let ret = look_up_occur_time check_history phi x ~f:Formula.occur_times in
      (* Debug.print @@ lazy (sprintf "[occur_times_in_formula] %s : %d" (Ident.name_of_tvar x) ret); *)
      ret

  let src_id_of id (param_log : bool array) =
    let len = Array.length param_log in
    (* Debug.print @@ lazy (sprintf "src_id_of: %d" id); *)
    assert (id < len);
    let rec inner step i =
      (* Debug.print @@ lazy (sprintf "step:%d i:%d" step i); *)
      assert (i < len);
      if Array.get param_log i then
        if step = id then i else inner (step + 1) (i + 1)
      else inner step (i + 1)
    in
    inner 0 0

  let init_param_logs_of =
    Map.Poly.to_alist
    >> List.map ~f:(fun (tvar, sort) ->
           let args = Logic.Sort.args_of sort in
           let arr = Array.init (List.length args) ~f:(fun _ -> true) in
           (Ident.tvar_to_pvar tvar, (arr, args)))
    >> Map.Poly.of_alist_exn

  let update_param_logs_with_erasure param_logs =
    Map.Poly.iteri ~f:(fun ~key:pvar ~data:is ->
        let arr, _args = Map.Poly.find_exn param_logs pvar in
        Set.iter is ~f:(fun (_, src_id) -> Array.set arr src_id false))

  let str_of_param_logs param_logs senv =
    Map.Poly.to_alist param_logs
    |> List.filter ~f:(fst >> Ident.pvar_to_tvar >> Map.Poly.mem senv)
    |> String.concat_map_list ~sep:"\n" ~f:(fun (pvar, (arr, _args)) ->
           sprintf "%s(%s)" (Ident.name_of_pvar pvar)
           @@ String.concat_mapi_list (Array.to_list arr) ~sep:","
                ~f:(fun i tf -> if tf then sprintf "x%d" i else "_"))

  (*let deleted_sort = Sort.SVar (Ident.Svar "##deleted_sort##")
    let deleted_term = Term.mk_var (Ident.Tvar "##deleted_term##") deleted_sort
    let show_and_update_time st_time str =
      Debug.print @@ lazy
        (sprintf "%s : %s" str
           (Time_float.Span.to_short_string @@
            Time_float.abs_diff !st_time (Time_float.now ())));
      st_time := Time_float.now ()*)

  let sub_list list is = List.filteri list ~f:(fun i _ -> not @@ Set.mem is i)

  let erase_senv (e : erasure) =
    Map.Poly.mapi ~f:(fun ~key:tvar ~data:sort ->
        (* Debug.print @@ lazy (sprintf "[erase senv] erase %s : %s" (Ident.name_of_tvar tvar) (Logic.ExtTerm.str_of_sort sort)); *)
        match Map.Poly.find e (Ident.tvar_to_pvar tvar) with
        | None -> sort
        | Some is ->
            let sorts' =
              sub_list (Logic.Sort.args_of sort) @@ Set.Poly.map ~f:fst is
            in
            Logic.Sort.mk_fun @@ sorts' @ [ Logic.ExtTerm.SBool ])

  let erase_atom ?(times = None) (e : erasure) = function
    | Atom.App (Predicate.Var (pvar1, sorts), ts, info) ->
        let is =
          match Map.Poly.find e pvar1 with
          | Some is -> Set.Poly.map is ~f:fst
          | None -> Set.Poly.empty
        in
        let sub_times ts is = function
          | None -> ()
          | Some times ->
              List.iteri ts ~f:(fun i t ->
                  if Term.is_var t && Set.mem is i then
                    let (tvar, _), _ = Term.let_var t in
                    Hashtbl.Poly.set times ~key:tvar
                      ~data:(Hashtbl.Poly.find_exn times tvar - 1))
        in
        sub_times ts is times;
        Atom.App (Predicate.Var (pvar1, sub_list sorts is), sub_list ts is, info)
    | atm -> atm

  let erase_atoms ?(times = None) e = Set.Poly.map ~f:(erase_atom ~times e)

  let erase_clause e ((ns, ps, phi, times) : clause) =
    (erase_atoms ~times:(Some times) e ns, erase_atoms e ps, phi, times)

  let find_tks atoms pvar i =
    Set.Poly.filter_map atoms ~f:(function
      | Atom.App (Predicate.Var (pvar1, _), ts, _) when Stdlib.(pvar = pvar1) ->
          Some (List.nth_exn ts i)
      | _ -> None)

  let find_unsafe_raf clauses (e : erasure) (pvar, (is : (int * int) Set.Poly.t))
      =
    let check_tk atoms times t =
      if Term.is_var t then
        let (x, _), _ = Term.let_var t in
        if Hashtbl.Poly.find_exn times x > 1 then true
        else occur_times_in_atoms x (erase_atoms e atoms) <> 0
      else true
    in
    Set.find_map clauses ~f:(fun (ns, ps, _, times) ->
        Set.filter is
          ~f:(fst >> find_tks ns pvar >> Set.exists ~f:(check_tk ps times))
        |> fun uis -> if Set.is_empty uis then None else Some uis)
    |> function
    | Some uis -> Some (pvar, uis, is)
    | _ -> None

  let find_unsafe_far clauses (e : erasure) (pvar, (is : (int * int) Set.Poly.t))
      =
    let check_tk ps ns phi e t =
      if Term.is_var t then
        let (x, _), _ = Term.let_var t in
        if occur_times_in_atoms x ps > 1 then true
        else
          occur_times_in_atoms x (erase_atoms e ns)
          + occur_times_in_formula x phi
          <> 0
      else true
    in
    Set.find_map clauses ~f:(fun (ns, ps, phi, _times) ->
        Set.filter is
          ~f:(fst >> find_tks ps pvar >> Set.exists ~f:(check_tk ps ns phi e))
        |> fun uis -> if Set.is_empty uis then None else Some uis)
    |> function
    | Some i -> Some (pvar, i, is)
    | _ -> None

  let is_special_pvar pvs pvar = Set.mem pvs @@ Ident.pvar_to_tvar pvar

  let full_erasure_of_atom param_logs direct bpvs fnpvs = function
    | Atom.App (Predicate.Var (pvar1, sorts), _, _) ->
        if
          is_special_pvar bpvs pvar1
          || (is_far direct && is_special_pvar fnpvs pvar1)
        then None
        else
          let bounds =
            if is_special_pvar fnpvs pvar1 then List.length sorts - 1
            else List.length sorts
          in
          let param_log, _ = Map.Poly.find_exn param_logs pvar1 in
          (* Debug.print @@ lazy
             (sprintf "[full_erasure_of_atom] %s:(%s)"
             (Ident.name_of_pvar pvar1)
             (String.concat_mapi_list ~sep:"," sorts ~f:(fun i sort -> sprintf "x%d:%s" i @@ Term.str_of_sort sort))); *)
          Some
            ( pvar1,
              List.foldi sorts ~init:Set.Poly.empty ~f:(fun i ret _ ->
                  if i < bounds then Set.add ret (i, src_id_of i param_log)
                  else ret) )
    | _ -> None

  let full_erasure_of param_logs direct bpvs fnpvs =
    Set.fold ~init:Map.Poly.empty ~f:(fun ret (ns, ps, _, _) ->
        Set.fold (Set.union ns ps) ~init:ret ~f:(fun ret atom ->
            match full_erasure_of_atom param_logs direct bpvs fnpvs atom with
            | None -> ret
            | Some (pvar, is) -> Map.Poly.set ~key:pvar ~data:is ret))

  let raf param_logs bpvs fnpvs clauses : erasure =
    let _st_time = ref (Time_float.now ()) in
    let rec inner (e : erasure) =
      Debug.print @@ lazy (sprintf "[raf] erase (%d)" (size_of e));
      match
        List.filter_map (Map.Poly.to_alist e) ~f:(find_unsafe_raf clauses e)
      with
      | [] -> e
      | a ->
          inner
            (List.fold_left a ~init:e ~f:(fun e (pvar, uis, is) ->
                 Map.Poly.set e ~key:pvar ~data:(Set.diff is uis)))
    in
    inner @@ full_erasure_of param_logs RAF bpvs fnpvs clauses

  let far param_logs bpvs fnpvs clauses : erasure =
    let _st_time = ref (Time_float.now ()) in
    let rec inner (e : erasure) =
      Debug.print @@ lazy (sprintf "[far] erase (%d)" (size_of e));
      match
        List.filter_map (Map.Poly.to_alist e) ~f:(find_unsafe_far clauses e)
      with
      | [] -> e
      | a ->
          inner
            (List.fold_left a ~init:e ~f:(fun e (pvar, uis, is) ->
                 Map.Poly.set e ~key:pvar ~data:(Set.diff is uis)))
    in
    inner @@ full_erasure_of param_logs FAR bpvs fnpvs clauses

  let rec elim_args param_logs bpvs fnpvs senv (clauses : clause Set.Poly.t) =
    Debug.print @@ lazy "[elim arg] start raf";
    let e_raf = raf param_logs bpvs fnpvs clauses in
    update_param_logs_with_erasure param_logs e_raf;
    Debug.print @@ lazy "[elim arg] raf end";
    Debug.print
    @@ lazy
         (sprintf "[elim arg] new raf erasure (%d): \n%s" (size_of e_raf)
            (str_of_erasure e_raf));
    Debug.print
    @@ lazy
         (sprintf "[elim arg] param_logs after raf:\n%s"
            (str_of_param_logs param_logs senv));
    let senv' = erase_senv e_raf senv in
    let clauses' = Set.Poly.map clauses ~f:(erase_clause e_raf) in
    Debug.print @@ lazy "[elim arg] start far";
    let e_far = far param_logs bpvs fnpvs clauses' in
    update_param_logs_with_erasure param_logs e_far;
    Debug.print @@ lazy "[elim arg] far end";
    Debug.print
    @@ lazy
         (sprintf "[elim arg] new far erasure (%d): \n%s" (size_of e_far)
            (str_of_erasure e_far));
    Debug.print
    @@ lazy
         (sprintf "[elim arg] param_logs after far:\n%s"
            (str_of_param_logs param_logs senv));
    if is_empty e_raf && is_empty e_far then (senv', clauses')
    else
      let senv'' = erase_senv e_far senv' in
      let clauses'' = Set.Poly.map clauses' ~f:(erase_clause e_far) in
      elim_args param_logs bpvs fnpvs senv'' clauses''

  let init_time_with_atoms times atoms =
    Set.iter (Set.concat_map atoms ~f:Atom.tvs_of) ~f:(fun tvar ->
        let time = occur_times_in_atoms tvar atoms in
        match Hashtbl.Poly.find times tvar with
        | Some i -> Hashtbl.Poly.set times ~key:tvar ~data:(i + time)
        | _ -> Hashtbl.Poly.add_exn times ~key:tvar ~data:time)

  let init_time_with_formula times phi =
    Set.iter (Formula.tvs_of phi) ~f:(fun tvar ->
        let time = occur_times_in_formula tvar phi in
        match Hashtbl.Poly.find times tvar with
        | Some i -> Hashtbl.Poly.set times ~key:tvar ~data:(i + time)
        | _ -> Hashtbl.Poly.add_exn times ~key:tvar ~data:time)

  let elim_args param_logs bpvs fnpvs senv clauses =
    Set.Poly.map clauses ~f:(fun cl ->
        let times = Hashtbl.Poly.create () in
        let ps, ns, phi = cl in
        init_time_with_atoms times ns;
        init_time_with_formula times phi;
        let cl' = (ns, ps, phi, times) in
        Debug.print @@ lazy ("[clause] " ^ str_of_clause cl');
        Debug.print
        @@ lazy
             ("[#occurrences of each unknown in the clause] "
            ^ str_of_times times);
        cl')
    |> elim_args param_logs bpvs fnpvs senv
    |> fun (senv, cls) ->
    Debug.print @@ lazy "*** args eliminated clauses:";
    ( senv,
      Set.Poly.map cls ~f:(fun ((ns, ps, phi, _) as cl) ->
          Debug.print @@ lazy (str_of_clause cl);
          (ps, ns, phi)) )

  let elim_pcsp_args ?(bpvs = Set.Poly.empty) param_logs pcsp =
    if not enable then pcsp
    else
      let penv = ref (PCSP.Problem.params_of pcsp).senv in
      let bpvs =
        PCSP.Problem.pvs_of pcsp
        |> Set.filter ~f:(fun t ->
               Set.mem bpvs t
               || PCSP.Problem.is_wf_pred pcsp t
               || PCSP.Problem.is_nwf_pred pcsp t
               || PCSP.Problem.is_ne_pred (*ToDo*) pcsp t
               || PCSP.Problem.is_adm_pred (*ToDo*) pcsp t
               || PCSP.Problem.is_integ_pred (*ToDo*) pcsp t
               (*|| PCSP.Problem.is_int_fun pcsp t
                 || PCSP.Problem.is_regex pcsp t*))
      in
      let fnpvs = PCSP.Problem.fnpvs_of pcsp in
      Debug.print
      @@ lazy
           (sprintf "[elim_pcsp_args] init param_logs:\n%s"
              (str_of_param_logs param_logs (PCSP.Problem.senv_of pcsp)));
      let pcsp =
        PCSP.Problem.map_if_raw_old pcsp ~f:(fun inp ->
            (* note that phis may contain variables with the same name but different types *)
            let senvs, phis = Set.unzip inp in
            let senv =
              Map.of_set_exn @@ Logic.of_old_sort_env_set
              @@ Set.concat_map ~f:Set.of_map senvs
            in
            (* Debug.print @@ lazy (sprintf "[before elim pcsp args] senv: %s" (Logic.str_of_sort_env_list Logic.ExtTerm.str_of_sort (Map.Poly.to_alist senv))); *)
            Set.concat_map phis
              ~f:
                (Formula.cnf_of (*ToDo*)
                   Logic.(to_old_sort_env_map @@ PCSP.Problem.senv_of pcsp))
            |> elim_args param_logs bpvs fnpvs !penv
            |> (fun (penv', cls) ->
                 penv := penv';
                 cls)
            |> Set.Poly.map ~f:(fun (ps, ns, phi) ->
                   let senv, phi = ClauseOld.to_formula (senv, ps, ns, phi) in
                   (* Debug.print @@ lazy (sprintf "[after elim pcsp args] senv: %s" (Logic.str_of_sort_env_list Logic.ExtTerm.str_of_sort (Map.Poly.to_alist senv))); *)
                   (Logic.to_old_sort_env_map senv, phi)))
      in
      PCSP.Problem.update_params pcsp
        { (PCSP.Problem.params_of pcsp) with senv = !penv }

  let elim_pcsp_args ?(bpvs = Set.Poly.empty) param_logs pcsp =
    Debug.set_id @@ PCSP.Problem.id_of pcsp;
    try elim_pcsp_args ~bpvs param_logs pcsp
    with exn ->
      Debug.print @@ lazy (Exn.to_string exn);
      pcsp
end
