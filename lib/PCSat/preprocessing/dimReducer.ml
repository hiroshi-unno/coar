open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* [Term.occur_times x t], [Atom.occur_times] and [Formula.occur_times] for
   every variable [x] at once, in one traversal: the table maps each variable
   that occurs to the count those functions give it.  A use of a let-bound
   variable [v] counts once for [v] and contributes the counts of [v]'s
   definition for every other variable, as there.  Asking the one-variable
   functions once per variable of a clause costs the variables times the
   clause's size, which on a resolvent of tens of thousands of nodes and
   thousands of variables was most of the time of argument reduction.
   Like them it assumes let-bound names are distinct, and refuses [LetRec]. *)
module OccurCounts = struct
  let bump tbl x c =
    Hashtbl.Poly.update tbl x ~f:(function None -> c | Some c' -> c' + c)

  let rec term lets tbl = function
    | Term.Var (tvar, _, _) -> (
        bump tbl tvar 1;
        match Map.Poly.find lets tvar with
        | Some m ->
            Map.Poly.iteri m ~f:(fun ~key ~data ->
                if not (Ident.tvar_equal key tvar) then bump tbl key data)
        | None -> ())
    | Term.FunApp (T_bool.Formula phi, _, _) -> formula lets tbl phi
    | Term.FunApp (_, ts, _) -> List.iter ts ~f:(term lets tbl)
    | Term.LetTerm (var, _, def, body, _) ->
        term (Map.Poly.add_exn lets ~key:var ~data:(of_term lets def)) tbl body

  and of_term lets t =
    let tbl = Hashtbl.Poly.create () in
    term lets tbl t;
    Map.Poly.of_alist_exn (Hashtbl.Poly.to_alist tbl)

  and atom lets tbl = function
    | Atom.True _ | Atom.False _ -> ()
    | Atom.App (_, ts, _) -> List.iter ts ~f:(term lets tbl)

  and formula lets tbl = function
    | Formula.Atom (a, _) -> atom lets tbl a
    | Formula.BinaryOp (_, phi1, phi2, _) ->
        formula lets tbl phi1;
        formula lets tbl phi2
    | Formula.UnaryOp (_, phi1, _) | Formula.Bind (_, _, phi1, _) ->
        formula lets tbl phi1
    | Formula.LetRec _ -> failwith "[occur_times_in_formula]unsupported letrec"
    | Formula.LetFormula (var, _, def, body, _) ->
        formula
          (Map.Poly.add_exn lets ~key:var ~data:(of_term lets def))
          tbl body

  let of_atoms atoms =
    let tbl = Hashtbl.Poly.create () in
    Set.iter atoms ~f:(atom Map.Poly.empty tbl);
    tbl

  let of_formula phi =
    let tbl = Hashtbl.Poly.create () in
    formula Map.Poly.empty tbl phi;
    tbl

  let find tbl x = Option.value ~default:0 (Hashtbl.Poly.find tbl x)
end

(* the reduction's clausal form, read in one pass where a formula is one
   clause already, with the union sort environment converted back once and
   each clause's free variables remembered across clauses by physical
   identity; [false] restores the per-formula [cnf_of], the per-clause
   [reduce_sort_map] and the per-clause conversion, which give the same
   clauses (kept for the differential test of the two) *)
let one_pass_clauses : bool Atomic.t = Atomic.make true

(* what the last run of [drop_constant_args] in this process dropped: each
   reduced unknown's name with the dropped positions, by position in its
   signature before the pass.  An instrument for a census that runs the
   preprocessor and asks afterwards what the pass did; nothing in the solver
   reads it *)
let constant_args_log : (string * int list) list Atomic.t = Atomic.make []

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
      (String.concat_map_set ~sep:", " ns ~f:Atom.str_of)
      (String.concat_map_set ~sep:", " ps ~f:Atom.str_of)

  let str_of_erasure (e : erasure) =
    String.concat ~sep:"\n"
    @@ List.filter_map (Map.Poly.to_alist e) ~f:(fun (pvar, is) ->
        if Set.is_empty is then None
        else
          Option.return @@ sprintf "{%s}"
          @@ String.concat_map_set ~sep:", " is
               ~f:
                 (Tuple2.uncurry
                 @@ sprintf "(%s,%d(%d))" (Ident.name_of_pvar pvar)))

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
    let check_history = Hashtbl.PolyDeep.create () in
    fun (x : Ident.tvar) (atoms : Atom.t Set.Poly.t) ->
      let ret =
        Set.fold atoms ~init:0 ~f:(fun ret atom ->
            ret + look_up_occur_time check_history atom x ~f:Atom.occur_times)
      in
      (* Debug.print @@ lazy (sprintf "[occur_times_in_atoms] %s : %d" (Ident.name_of_tvar x) ret); *)
      ret

  let occur_times_in_formula =
    let check_history = Hashtbl.PolyDeep.create () in
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
        @@ String.concat_mapi_list (Array.to_list arr) ~sep:"," ~f:(fun i tf ->
            if tf then sprintf "x%d" i else "_"))

  (*let deleted_sort = Sort.SVar (Ident.Svar "##deleted_sort##")
    let deleted_term = Term.mk_var (Ident.Tvar "##deleted_term##") deleted_sort
    let show_and_update_time st_time str =
      Debug.print @@ lazy
        (sprintf "%s : %s" str
           (Time_float.Span.to_short_string @@
            Time_float.abs_diff !st_time (Common.Clock.now_float ())));
      st_time := Common.Clock.now_float ()*)

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
        Atom.mk_app ~info
          (Predicate.Var (pvar1, sub_list sorts is))
          (sub_list ts is)
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
      if (not @@ Sort.is_arrow (Term.sort_of t)) (*ToDo*) && Term.is_var t then
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
      if (not @@ Sort.is_arrow (Term.sort_of t)) (*ToDo*) && Term.is_var t then
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

  let full_erasure_of_atom param_logs _direct bpvs fnpvs = function
    | Atom.App (Predicate.Var (pvar1, sorts), _, _) ->
        if is_special_pvar bpvs pvar1 || is_special_pvar fnpvs pvar1 then
          (* FN predicates take part in neither FAR nor RAF: erasing an
             input by RAF stands for [FN_f'(rest) := exists x. FN_f(x, rest)],
             which is not functional once the head clauses fix different
             outputs for different inputs *)
          None
        else
          let bounds = List.length sorts in
          let param_log, _ = Map.Poly.find_exn param_logs pvar1 in
          (* Debug.print @@ lazy
             (sprintf "[full_erasure_of_atom] %s:(%s)"
             (Ident.name_of_pvar pvar1)
             (String.concat_mapi_list ~sep:"," sorts ~f:(fun i sort -> sprintf "x%d:%s" i @@ Term.str_of_sort sort))); *)
          Some
            ( pvar1,
              List.foldi sorts ~init:Set.Poly.empty ~f:(fun i ret _s ->
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
    let _st_time = ref (Common.Clock.now_float ()) in
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
    let _st_time = ref (Common.Clock.now_float ()) in
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

  (* the committed erasures, per predicate in order, by original position *)
  let trail : (Ident.pvar, ([ `RAF | `FAR ] * int list) list) Map.Poly.t ref =
    ref Map.Poly.empty

  let record_erasure kind (e : erasure) =
    Map.Poly.iteri e ~f:(fun ~key:pvar ~data:is ->
        if not (Set.is_empty is) then
          let src_ids =
            List.sort ~compare:Int.compare @@ List.map (Set.to_list is) ~f:snd
          in
          trail :=
            Map.Poly.update !trail pvar ~f:(function
              | None -> [ (kind, src_ids) ]
              | Some l -> l @ [ (kind, src_ids) ]))

  let rec elim_args param_logs bpvs fnpvs senv (clauses : clause Set.Poly.t) =
    Debug.print @@ lazy "[elim arg] start raf";
    let e_raf = raf param_logs bpvs fnpvs clauses in
    record_erasure `RAF e_raf;
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
    record_erasure `FAR e_far;
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
    let tvs = Set.concat_map atoms ~f:Atom.tvs_of in
    let counts = lazy (OccurCounts.of_atoms atoms) in
    Set.iter tvs ~f:(fun tvar ->
        let time = OccurCounts.find (Lazy.force counts) tvar in
        match Hashtbl.Poly.find times tvar with
        | Some i -> Hashtbl.Poly.set times ~key:tvar ~data:(i + time)
        | _ -> Hashtbl.Poly.add_exn times ~key:tvar ~data:time)

  let init_time_with_formula times phi =
    let counts = lazy (OccurCounts.of_formula phi) in
    Set.iter (Formula.tvs_of phi) ~f:(fun tvar ->
        let time = OccurCounts.find (Lazy.force counts) tvar in
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
      trail := (PCSP.Problem.params_of pcsp).erasure_trail;
      let bpvs =
        Set.filter (PCSP.Problem.pvs_of pcsp) ~f:(fun t ->
            Set.mem bpvs t
            || PCSP.Problem.is_wf_pred pcsp t
            || PCSP.Problem.is_dwf_pred pcsp t
            || PCSP.Problem.is_nwf_pred pcsp t
            || PCSP.Problem.is_parity_pred pcsp t
            || PCSP.Problem.is_tot_pred (*ToDo*) pcsp t
            || PCSP.Problem.is_adm_pred (*ToDo*) pcsp t
            || PCSP.Problem.is_integ_pred (*ToDo*) pcsp t
            (*|| PCSP.Problem.is_int_fun pcsp t
                 || PCSP.Problem.is_regex pcsp t*))
      in
      (* a single-valued ([Uniq]) predicate is excluded with the functional
         ones and for the same reason: erasing another argument by RAF stands
         for an existential over it, which is not single-valued at the kind's
         position once different values of the erased argument fix different
         values there *)
      let fnpvs =
        Set.union (PCSP.Problem.fnpvs_of pcsp) (PCSP.Problem.uniqpvs_of pcsp)
      in
      Debug.print
      @@ lazy
           (sprintf "[elim_pcsp_args] init param_logs:\n%s"
              (str_of_param_logs param_logs (PCSP.Problem.senv_of pcsp)));
      let pcsp =
        PCSP.Problem.map_raw_old_exn pcsp ~f:(fun inp ->
            (* note that phis may contain variables with the same name but different types *)
            let senvs, phis = Set.unzip inp in
            let senv =
              Map.of_set_exn @@ Logic.of_old_sort_env_set
              @@ Set.concat_map ~f:Set.of_map senvs
            in
            (* Debug.print @@ lazy (sprintf "[before elim pcsp args] senv: %s" (Logic.str_of_sort_env_list Logic.ExtTerm.str_of_sort (Map.Poly.to_alist senv))); *)
            (* each input formula is most often one clause already (the
               output of an elimination round), and [cnf_of] tests every
               disjunction node of such a clause for an unknown by walking the
               node's whole subtree, so a clause of k disjuncts was walked k
               times; [cnf_of_clause_tree] returns the same clauses in one
               pass and hands anything else to [cnf_of] *)
            let exi_senv =
              Logic.(to_old_sort_env_map @@ PCSP.Problem.senv_of pcsp)
            in
            let one_pass = Atomic.get one_pass_clauses in
            Set.concat_map phis
              ~f:
                (if one_pass then Formula.cnf_of_clause_tree exi_senv
                 else Formula.cnf_of exi_senv)
            |> elim_args param_logs bpvs fnpvs !penv
            |> (fun (penv', cls) ->
            penv := penv';
            cls)
            |> (let senv_old = lazy (Logic.to_old_sort_env_map senv) in
                let reduce = ClauseOld.reduce_sort_map_shared () in
                Set.Poly.map ~f:(fun (ps, ns, phi) ->
                (* [senv] is the union over every input formula, so each
                   clause is cut back to the variables it mentions: handed
                   the union, every clause of a 450-clause problem carried
                   1,040 sort entries for 31 used variables, and every later
                   phase paid for the 1,009 others -- each conversion to the
                   other term representation, each canonical rebuild of a
                   resolvent's environment (half of the resolution phase's
                   time on that problem), each quantifier sent to Z3 *)
                (* the union is converted back once, not once per clause:
                   the conversion is a function of each sort, so restricting
                   the converted map gives what converting each restriction
                   gave, and a clause's free variables are read through
                   [reduce_sort_map_shared], which remembers those of the
                   large pure disjuncts the clauses share physically *)
                if one_pass then
                  let senv, phi =
                    ClauseOld.to_formula @@ reduce (senv, ps, ns, phi)
                  in
                  ( Map.Poly.mapi senv ~f:(fun ~key ~data:_ ->
                        Map.Poly.find_exn (Lazy.force senv_old) key),
                    phi )
                else
                  let senv, phi =
                    ClauseOld.to_formula
                    @@ ClauseOld.reduce_sort_map (senv, ps, ns, phi)
                  in
                  (Logic.to_old_sort_env_map senv, phi))))
      in
      PCSP.Problem.update_params pcsp
        {
          (PCSP.Problem.params_of pcsp) with
          senv = !penv;
          erasure_trail = !trail;
        }

  let elim_pcsp_args ?(bpvs = Set.Poly.empty) param_logs pcsp =
    Debug.set_id @@ PCSP.Problem.id_of pcsp;
    if PCSP.Problem.is_cnf pcsp then (
      (* The reduction rewrites the problem's formulas, and a clausal problem
         has none left to rewrite.  Saying so here is not a new decision: the
         mapping helper used below raises on a clausal problem instead of
         passing it through, and the handler underneath then returned the
         unreduced problem with the reason buried inside a caught exception.
         Measured over 1,296 benchmarks in four input languages (1,391 calls of
         this function), that exception is the only way the reduction was ever
         skipped -- once, on the fourth of four calls on an optimisation
         problem -- and the clash of one variable name at two sorts that the
         comment inside the function warns about never happened once. *)
      Debug.print
      @@ lazy "[elim_pcsp_args] skipped: the problem is already clausal";
      pcsp)
    else
      try elim_pcsp_args ~bpvs param_logs pcsp
      with exn when not (Common.Timer.is_async exn) ->
        (* a timeout raised inside the reduction must keep propagating; caught
           here it would continue the solve on the unreduced problem as if the
           budget had not run out *)
        Debug.print @@ lazy (Exn.to_string exn);
        pcsp

  (* Dropping the copied arguments of a functional predicate.

     The reduction above leaves functional ([FN]) and single-valued
     predicates alone, because its erasures stand for a quantifier over the
     erased argument, and neither quantifier preserves single-valuedness.  A
     witness predicate made by skolemising a universal in a clause body takes
     every variable of that clause as an argument, and a clause from a program
     verifier carries many variables that the clause's own equations make
     copies of one another; on one input 985 of the 1,402 arguments of 36 such
     predicates were copies or constants, and building the hypothesis spaces
     over them took most of a two-minute budget.

     The erasure here is of another kind and stands for a substitution, not a
     quantifier.  Argument [i] (never the last, which is the result) of [P] is
     dropped when, at EVERY occurrence of [P] in every clause, it is after the
     clause's own definitions either

     - the same term as one FIXED earlier argument [j] (the same [j] at every
       occurrence), or
     - the same closed term [c] (the same [c] at every occurrence).

     A definition is a premise [x = t] of the clause with [x] a variable not
     free in [t] (a disjunct [x != t] of the clause's pure part); the
     definitions are applied until none applies, so the test is syntactic
     equality of the two arguments in the clause's premise-normal form, and it
     never asks a solver.

     Equisatisfiable, for every kind that constrains only the relation's
     shape in its last argument ([FN], [Uniq]): given a solution [f] of [P],
     [f'(rest) := f(rest with x_i := x_j)] (or [:= c]) solves the reduced
     problem, because inside each clause the premise makes [a_i = a_j] (or
     [a_i = c]) hold wherever [P] is applied, so [f(a) = f'(a without a_i)];
     conversely a solution [f'] of the reduced problem extends to
     [f(all) := f'(all without x_i)], which keeps totality and
     single-valuedness and agrees with [f'] at every occurrence.  The second
     direction is the one the answer is read through: the argument record
     marks the position as erased, so the printed solution ignores it, which
     is exactly that extension.  Both directions hold model by model, so the
     reduction is sound for [sat] and for [unsat] alike.

     An occurrence the test cannot see -- [P] inside the pure part of a
     clause, under a binder or inside a term -- disqualifies [P] entirely.
     Nothing is recorded in the erasure trail, whose two kinds are
     quantifiers; a refutation certificate that needs the reduced predicate's
     definition then finds the trail and the record disagreeing and reports
     the step unchecked rather than guessing. *)
  let fn_copy_erasure param_logs fnpvs
      (clauses : (Atom.t Set.Poly.t * Atom.t Set.Poly.t * Formula.t) list) :
      erasure =
    (* the clause's definitions [x = t], idempotent and acyclic *)
    let definitions = ClauseCone.definitions in
    let same t1 t2 = try Stdlib.(t1 = t2) with Invalid_argument _ -> false in
    (* per predicate: [None] when disqualified, else the normalised argument
       lists of its occurrences *)
    let occs = Hashtbl.Poly.create () in
    List.iter clauses ~f:(fun (ps, ns, phi) ->
        Set.iter (Formula.pvs_of phi) ~f:(fun pv ->
            if Set.mem fnpvs pv then Hashtbl.Poly.set occs ~key:pv ~data:None);
        let m = lazy (definitions phi) in
        Set.iter (Set.union ps ns) ~f:(function
          | Atom.App (Predicate.Var (pv, _), ts, _) when Set.mem fnpvs pv -> (
              match Hashtbl.Poly.find occs pv with
              | Some None -> ()
              | prev ->
                  let ts =
                    Array.of_list @@ List.map ts ~f:(Term.subst (Lazy.force m))
                  in
                  let l = match prev with Some (Some l) -> l | _ -> [] in
                  Hashtbl.Poly.set occs ~key:pv ~data:(Some (ts :: l)))
          | _ -> ()));
    Hashtbl.Poly.fold occs ~init:Map.Poly.empty ~f:(fun ~key:pv ~data acc ->
        match (data, Map.Poly.find param_logs pv) with
        | Some (o :: os), Some (param_log, _) ->
            let os = o :: os in
            let n = Array.length o in
            if List.exists os ~f:(fun a -> Array.length a <> n) then acc
            else
              let constant i =
                Set.is_empty (Term.tvs_of o.(i))
                && List.for_all os ~f:(fun a -> same a.(i) o.(i))
              in
              let copy i =
                List.exists (List.range 0 i) ~f:(fun j ->
                    List.for_all os ~f:(fun a -> same a.(i) a.(j)))
              in
              let is =
                List.filter
                  (List.range 0 (n - 1))
                  ~f:(fun i -> constant i || copy i)
              in
              if List.is_empty is then acc
              else
                Map.Poly.set acc ~key:pv
                  ~data:
                    (Set.Poly.of_list
                    @@ List.map is ~f:(fun i -> (i, src_id_of i param_log)))
        | _ -> acc)

  let drop_fn_copy_args ?(bpvs = Set.Poly.empty) param_logs pcsp =
    if PCSP.Problem.is_cnf pcsp then pcsp
    else
      let fnpvs =
        Set.Poly.filter_map
          (Set.union
             (PCSP.Problem.fnpvs_of pcsp)
             (PCSP.Problem.uniqpvs_of pcsp))
          ~f:(fun t ->
            if Set.mem bpvs t then None else Some (Ident.tvar_to_pvar t))
      in
      if Set.is_empty fnpvs then pcsp
      else
        let exi_senv = Logic.to_old_sort_env_map (PCSP.Problem.senv_of pcsp) in
        let erasure = ref Map.Poly.empty in
        try
          let pcsp' =
            PCSP.Problem.map_raw_old_exn pcsp ~f:(fun inp ->
                let cls =
                  Set.to_list inp
                  |> List.concat_map ~f:(fun (uni_senv, phi) ->
                      Set.to_list (Formula.cnf_of exi_senv phi)
                      |> List.map ~f:(fun cl -> (uni_senv, cl)))
                in
                let e =
                  fn_copy_erasure param_logs fnpvs (List.map cls ~f:snd)
                in
                erasure := e;
                if is_empty e then inp
                else
                  Set.Poly.of_list
                  @@ List.map cls ~f:(fun (uni_senv, (ps, ns, phi)) ->
                      let senv, phi =
                        ClauseOld.to_formula
                        @@ ClauseOld.reduce_sort_map
                             ( Logic.of_old_sort_env_map uni_senv,
                               erase_atoms e ps,
                               erase_atoms e ns,
                               phi )
                      in
                      (Logic.to_old_sort_env_map senv, phi)))
          in
          if is_empty !erasure then pcsp
          else (
            update_param_logs_with_erasure param_logs !erasure;
            Debug.print
            @@ lazy
                 (sprintf "[drop_fn_copy_args] dropped (%d):\n%s"
                    (size_of !erasure) (str_of_erasure !erasure));
            PCSP.Problem.update_params pcsp'
              {
                (PCSP.Problem.params_of pcsp') with
                senv = erase_senv !erasure (PCSP.Problem.senv_of pcsp);
              })
        with exn when not (Common.Timer.is_async exn) ->
          Debug.print @@ lazy (Exn.to_string exn);
          pcsp
  (* Dropping the arguments of an ordinary unknown that every derivation fixes
     to one constant.

     An argument [k] of an ordinary unknown [P] is dropped when every clause
     with [P] in its head has [P] as its only head atom and, after the clause's
     own definitions [x = t] (the premises [ClauseCone.definitions] reads,
     and a premise fixing a variable to a closed value in arithmetic normal
     form, [constant_pins]; the test is syntactic and asks no solver), the
     head's argument [k] is either

     - a closed term, the same closed term [c] at every such head (a fact, or
       any clause resetting the argument to [c]), or
     - the same term as argument [k] of some occurrence of [P] in that
       clause's body (a step passing the argument on unchanged),

     with at least one head of the first kind.  Any other head occurrence, an
     occurrence of [P] in a clause's pure part, and an unknown of another kind
     leave [P] alone.

     The reduced problem has a fresh ordinary unknown [P'] over the other
     arguments: a head [P(r, h)] becomes [P'(r)], and a body occurrence
     [P(r, t)] becomes [P'(r)] with the premise [t = c] added to its clause
     (an occurrence at another value is not a state any derivation reaches, so
     the clause demands nothing there).

     Equisatisfiable, model by model.  (1) A solution [S] of the original gives
     [P'(r) := S(r, c)].  A reduced clause holding [P'(r)] and [t = c] in its
     body holds [S(r, t)], so the original clause's instance applies and gives
     its head; a head [P'(r')] is [S(r', c)], and the original head [S(r', h)]
     has [h = c], being [c] after the definitions or a copy of a body argument
     the added premise sets to [c].  Clauses whose head is another unknown or
     [false] only gained premises.  (2) A solution of the reduced problem
     gives [P(r, x) := P'(r) /\ x = c], which solves the original: in a body
     the original occurrence is the reduced one together with its premise
     [t = c]; a head [P(r', h)] needs [P'(r')], which the reduced clause gives,
     and [h = c], which holds by the definitions or because [h] copies a body
     argument that is [c] wherever the body holds.  Both directions hold for
     several positions and several unknowns at once, since each clause is
     argued on its own instances.  Direction (2) is how the answer is read
     back: [P]'s definition is recorded among the eliminated unknowns' and
     closed under the solution of [P']. *)
  (* the variables a premise of the clause [phi] fixes to a closed value: a
     disjunct [t1 != t2] (or [not (t1 = t2)]) whose only variable is [x],
     occurring once under [+], [-] and unary [-], so that the premise is
     [x = c] for the closed term [c] ([Evaluator.isolate_target], exact),
     which is returned simplified.  This reads a definition the arithmetic
     normal form has written as [0 != 10 - x]. *)
  let constant_pins phi =
    List.fold (Formula.disjuncts_list_of phi) ~init:Map.Poly.empty
      ~f:(fun m d ->
        match d with
        | Formula.UnaryOp
            ( Formula.Not,
              Formula.Atom
                (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
              _ )
        | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _)
          -> (
            match
              Set.to_list (Set.union (Term.tvs_of t1) (Term.tvs_of t2))
            with
            | [ x ] when not (Map.Poly.mem m x) -> (
                let is_target = function
                  | Term.Var (y, _, _) -> Ident.tvar_equal x y
                  | _ -> false
                in
                let occurs t = Set.mem (Term.tvs_of t) x in
                match Evaluator.isolate_target ~is_target ~occurs t1 t2 with
                | Some c when Set.is_empty (Term.tvs_of c) ->
                    Map.Poly.set m ~key:x ~data:(Evaluator.simplify_term c)
                | _ -> m)
            | _ -> m)
        | _ -> m)

  let constant_args (ordpvs : Ident.pvar Set.Poly.t)
      (clauses : (Atom.t Set.Poly.t * Atom.t Set.Poly.t * Formula.t) list) :
      (Ident.pvar, (int * Term.t) list) Map.Poly.t =
    let definitions = ClauseCone.definitions in
    let same = ClauseCone.same in
    let disq = Hash_set.Poly.create () in
    let arity = Hashtbl.Poly.create () in
    (* per unknown: each head occurrence's normalised arguments, with the
       normalised arguments of the unknown's occurrences in the same body *)
    let heads = Hashtbl.Poly.create () in
    let note_arity pv n =
      match Hashtbl.Poly.find arity pv with
      | Some n' when n' <> n -> Hash_set.add disq pv
      | Some _ -> ()
      | None -> Hashtbl.Poly.set arity ~key:pv ~data:n
    in
    List.iter clauses ~f:(fun (ps, ns, phi) ->
        Set.iter (Formula.pvs_of phi) ~f:(fun pv ->
            if Set.mem ordpvs pv then Hash_set.add disq pv);
        let m = lazy (definitions phi) in
        let pins = lazy (constant_pins phi) in
        (* a head argument after the definitions, read as its closed value
           where the clause fixes one: a closed term simplified, or a variable
           a premise pins *)
        let norm ts =
          Array.of_list
          @@ List.map ts ~f:(fun t ->
              let t = Term.subst (Lazy.force m) t in
              if Set.is_empty (Term.tvs_of t) then Evaluator.simplify_term t
              else
                match t with
                | Term.Var (x, _, _) -> (
                    match Map.Poly.find (Lazy.force pins) x with
                    | Some c -> c
                    | None -> t)
                | _ -> t)
        in
        let occs pv atoms =
          List.filter_map (Set.to_list atoms) ~f:(function
            | Atom.App (Predicate.Var (pv', _), ts, _) when Stdlib.(pv = pv') ->
                Some ts
            | _ -> None)
        in
        Set.iter ns ~f:(function
          | Atom.App (Predicate.Var (pv, _), ts, _) when Set.mem ordpvs pv ->
              note_arity pv (List.length ts)
          | _ -> ());
        Set.iter ps ~f:(function
          | Atom.App (Predicate.Var (pv, _), ts, _) when Set.mem ordpvs pv ->
              note_arity pv (List.length ts);
              if Set.length ps <> 1 then Hash_set.add disq pv
              else
                Hashtbl.Poly.add_multi heads ~key:pv
                  ~data:(norm ts, List.map (occs pv ns) ~f:norm)
          | _ -> ()));
    Hashtbl.Poly.fold heads ~init:Map.Poly.empty ~f:(fun ~key:pv ~data acc ->
        if Hash_set.mem disq pv then acc
        else
          let n = Hashtbl.Poly.find_exn arity pv in
          let constant_at k =
            let rec go c = function
              | [] -> c
              | (h, bs) :: rest ->
                  if Set.is_empty (Term.tvs_of h.(k)) then
                    match c with
                    | `None -> go (`Const h.(k)) rest
                    | `Const c' when same c' h.(k) -> go c rest
                    | _ -> `Bad
                  else if List.exists bs ~f:(fun b -> same b.(k) h.(k)) then
                    go c rest
                  else `Bad
            in
            match go `None data with `Const c -> Some (k, c) | _ -> None
          in
          match List.filter_map (List.range 0 n) ~f:constant_at with
          | [] -> acc
          | ks -> Map.Poly.set acc ~key:pv ~data:ks)

  (* one clause of the reduced problem: [dropped] maps a reduced unknown to
     its replacement and the dropped positions with their constants *)
  let rewrite_constant_args
      (dropped : (Ident.pvar, Ident.pvar * (int * Term.t) list) Map.Poly.t)
      ((ps, ns, phi) : Atom.t Set.Poly.t * Atom.t Set.Poly.t * Formula.t) =
    let reduce = function
      | Atom.App (Predicate.Var (pv, sorts), ts, info) as a -> (
          match Map.Poly.find dropped pv with
          | None -> (a, [])
          | Some (q, ks) ->
              let is = Set.Poly.of_list @@ List.map ks ~f:fst in
              ( Atom.mk_app ~info
                  (Predicate.Var (q, sub_list sorts is))
                  (sub_list ts is),
                List.map ks ~f:(fun (k, c) -> Formula.neq (List.nth_exn ts k) c)
              ))
      | a -> (a, [])
    in
    let ns, premises = List.unzip @@ List.map (Set.to_list ns) ~f:reduce in
    ( Set.Poly.map ps ~f:(reduce >> fst),
      Set.Poly.of_list ns,
      match List.concat premises with
      | [] -> phi
      | ds -> Formula.or_of (phi :: ds) )

  (* the original unknown's definition read back from the reduced one's:
     [P(xs) := P'(xs without the dropped) /\ x_k = c for each dropped k] *)
  let constant_args_definition (sort : Logic.Sort.t) (q : Ident.tvar)
      (ks : (int * Term.t) list) : Logic.term =
    let xs =
      List.map (Logic.Sort.args_of sort) ~f:(fun s ->
          (Ident.mk_fresh_tvar (), s))
    in
    let is = Set.Poly.of_list @@ List.map ks ~f:fst in
    Logic.Term.mk_lambda xs
    @@ Logic.BoolTerm.and_of
         (Logic.ExtTerm.mk_var_app q
            (List.map (sub_list xs is) ~f:(fst >> Logic.ExtTerm.mk_var))
         :: List.map ks ~f:(fun (k, c) ->
             let x, s = List.nth_exn xs k in
             Logic.ExtTerm.of_old_formula
             @@ Formula.eq (Term.mk_var x (Logic.ExtTerm.to_old_sort s)) c))

  (* the pass over a problem: the reduced problem and the unknowns it adds,
     with their sorts.  [bpvs] are never reduced. *)
  let drop_constant_args ?(bpvs = Set.Poly.empty) pcsp =
    Atomic.set constant_args_log [];
    if PCSP.Problem.is_cnf pcsp then (pcsp, [])
    else
      let senv = PCSP.Problem.senv_of pcsp in
      let kinds = PCSP.Problem.kind_map_of pcsp in
      let stable = ClauseSet.pvs_of (PCSP.Problem.stable_clauses_of pcsp) in
      let ordpvs =
        Set.Poly.filter_map (Map.key_set senv) ~f:(fun t ->
            match Map.Poly.find kinds t with
            | Some k
              when Kind.is_ord k
                   && (not (Set.mem bpvs t))
                   && not (Set.mem stable t) ->
                Some (Ident.tvar_to_pvar t)
            | _ -> None)
      in
      if Set.is_empty ordpvs then (pcsp, [])
      else
        let exi_senv = Logic.to_old_sort_env_map senv in
        let found = ref Map.Poly.empty in
        try
          let pcsp' =
            PCSP.Problem.map_raw_old_exn pcsp ~f:(fun inp ->
                let cls =
                  Set.to_list inp
                  |> List.concat_map ~f:(fun (uni_senv, phi) ->
                      Set.to_list (Formula.cnf_of exi_senv phi)
                      |> List.map ~f:(fun cl -> (uni_senv, cl)))
                in
                let consts = constant_args ordpvs (List.map cls ~f:snd) in
                if Map.Poly.is_empty consts then inp
                else
                  let dropped =
                    Map.Poly.mapi consts ~f:(fun ~key:pv ~data:ks ->
                        ( Ident.tvar_to_pvar
                          @@ Ident.mk_fresh_tvar
                               ~prefix:(Some (Ident.name_of_pvar pv ^ "_const"))
                               (),
                          ks ))
                  in
                  found := dropped;
                  Set.Poly.of_list
                  @@ List.map cls ~f:(fun (uni_senv, cl) ->
                      let ps, ns, phi = rewrite_constant_args dropped cl in
                      let senv, phi =
                        ClauseOld.to_formula
                        @@ ClauseOld.reduce_sort_map
                             (Logic.of_old_sort_env_map uni_senv, ps, ns, phi)
                      in
                      (Logic.to_old_sort_env_map senv, phi)))
          in
          if Map.Poly.is_empty !found then (pcsp, [])
          else
            let entries =
              Map.Poly.to_alist !found
              |> List.map ~f:(fun (pv, (q, ks)) ->
                  let p = Ident.pvar_to_tvar pv in
                  let q = Ident.pvar_to_tvar q in
                  let sort = Map.Poly.find_exn senv p in
                  let is = Set.Poly.of_list @@ List.map ks ~f:fst in
                  let qsort =
                    Logic.Sort.mk_fun
                      (sub_list (Logic.Sort.args_of sort) is
                      @ [ Logic.ExtTerm.SBool ])
                  in
                  (p, sort, q, qsort, ks))
            in
            Atomic.set constant_args_log
              (List.map entries ~f:(fun (p, _, _, _, ks) ->
                   (Ident.name_of_tvar p, List.map ks ~f:fst)));
            Debug.print
            @@ lazy
                 (sprintf "[drop_constant_args] %s"
                    (String.concat_map_list ~sep:"; " entries
                       ~f:(fun (p, _, q, _, ks) ->
                         sprintf "%s := %s(..) with %s" (Ident.name_of_tvar p)
                           (Ident.name_of_tvar q)
                           (String.concat_map_list ~sep:", " ks
                              ~f:(fun (k, c) ->
                                sprintf "x%d = %s" k (Term.str_of c))))));
            let params = PCSP.Problem.params_of pcsp' in
            let params =
              List.fold entries ~init:params ~f:(fun params (p, sort, q, _, ks) ->
                  let is = Set.Poly.of_list @@ List.map ks ~f:fst in
                  PCSP.Params.move_candidate_atoms params ~from:p
                    ~sorts:
                      (List.map (Logic.Sort.args_of sort)
                         ~f:Logic.ExtTerm.to_old_sort)
                    ~to_:q
                    ~keep:(fun i -> not (Set.mem is i)))
            in
            let remove m =
              List.fold entries ~init:m ~f:(fun m (p, _, _, _, _) ->
                  Map.Poly.remove m p)
            in
            let added = List.map entries ~f:(fun (_, _, q, qsort, _) -> (q, qsort)) in
            ( PCSP.Problem.update_params pcsp'
                {
                  params with
                  PCSP.Params.senv =
                    Map.force_merge (remove params.PCSP.Params.senv)
                      (Map.Poly.of_alist_exn added);
                  kind_map =
                    Map.force_merge
                      (remove params.PCSP.Params.kind_map)
                      (Map.Poly.of_alist_exn
                      @@ List.map added ~f:(fun (q, _) -> (q, Kind.Ord)));
                  sol_for_eliminated =
                    Map.force_merge params.PCSP.Params.sol_for_eliminated
                      (Map.Poly.of_alist_exn
                      @@ List.map entries ~f:(fun (p, sort, q, _, ks) ->
                          (p, constant_args_definition sort q ks)));
                },
              added )
        with exn when not (Common.Timer.is_async exn) ->
          Debug.print @@ lazy (Exn.to_string exn);
          (pcsp, [])
end
