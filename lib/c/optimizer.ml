open Core
open Common.Ext
open CSyntax
open Linked
open Linked.LinkedStatement
open Ast
open Ast.LogicOld

type target = Variables.t * Declare.t list * Init.t list * LinkedStatement.t

module StatementEnv = struct
  type 'a t = ENV of ('a * (LinkedStatement.t * 'a ref) list)

  let mk_empty init = ENV (init, [])

  let init init items =
    ENV (init, List.map ~f:(fun (key, value) -> (key, ref value)) items)

  let exists stmt = function
    | ENV (_, env) ->
        List.exists ~f:(fun (stmt', _) -> phys_equal stmt' stmt) env

  let add stmt = function
    | ENV (init, env) -> ENV (init, (stmt, ref init) :: env)

  let remove stmt = function
    | ENV (init, env) ->
        ENV
          ( init,
            env
            |> List.filter ~f:(fun (stmt', _) -> not @@ phys_equal stmt' stmt)
          )

  let get stmt = function
    | ENV (init, env) -> (
        match List.find ~f:(fun (stmt', _) -> phys_equal stmt' stmt) env with
        | Some (_, item) -> !item
        | None -> init)

  (* let get_exn stmt = function
      ENV (_, env) ->
      match List.find_opt (fun (stmt', _) -> phys_equal stmt' stmt) env with
      | Some (_, item) -> !item
      | None -> assert false *)

  let update stmt newvalue = function
    | ENV (init, env) -> (
        match List.find ~f:(fun (stmt', _) -> phys_equal stmt' stmt) env with
        | Some (_, item) ->
            item := newvalue;
            ENV (init, env)
        | None -> ENV (init, (stmt, ref newvalue) :: env))

  let length = function ENV (_, env) -> List.length env
  let keys = function ENV (_, env) -> List.map ~f:(fun (key, _) -> key) env

  let values = function
    | ENV (_, env) -> List.map ~f:(fun (_, value) -> !value) env

  (* let entries = function
      ENV (_, env) ->
      List.map (fun (key, value) -> key, !value) env *)

  let merge env1 env2 : unit t =
    List.fold ~init:env1 (keys env2) ~f:(fun env stmt -> update stmt () env)
end

module Util : sig
  val get_prev_env : LinkedStatement.t -> LinkedStatement.t list StatementEnv.t

  val remove_nobranch :
    query:LinkedStatement.t ->
    LinkedStatement.t ->
    LinkedStatement.t list ->
    LinkedStatement.t
  (** remove stmt from stmts and returns new query_stmt *)

  val replace_stmt : query:t -> t StatementEnv.t -> t
  (** returns new query_stmt *)

  val mk_replacer : t list -> t StatementEnv.t
end = struct
  (* get_prev_env *)
  let add_to_prev_env stmt prev_stmt env =
    StatementEnv.update stmt (prev_stmt :: StatementEnv.get stmt env) env

  let rec get_prev_env_rep stmt (used, env) =
    if StatementEnv.exists stmt used then (used, env)
    else
      let used = StatementEnv.add stmt used in
      get_next_statements stmt
      |> List.fold ~init:(used, env) ~f:(fun (used, env) nxt_stmt ->
             (used, add_to_prev_env nxt_stmt stmt env)
             |> get_prev_env_rep nxt_stmt)

  let get_prev_env stmt =
    let _, env =
      get_prev_env_rep stmt (StatementEnv.mk_empty (), StatementEnv.mk_empty [])
    in
    env

  (* TODO: self loop *)
  let remove_nobranch ~query stmt stmts =
    match get_next_statements stmt with
    | [ nxt_stmt ] ->
        List.iter stmts ~f:(fun stmt' ->
            get_next_statements_ref stmt'
            |> List.iter ~f:(fun stmt_ref ->
                   if phys_equal !stmt_ref stmt then stmt_ref := nxt_stmt));
        if phys_equal query stmt then nxt_stmt else query
    | _ -> failwith "not a nobranch stmt"

  let mk_replacer stmts =
    let dummy_stmt = mk_exit () in
    stmts
    |> List.map ~f:(fun stmt -> (stmt, stmt))
    |> StatementEnv.init dummy_stmt

  let replace_stmt ~query new_stmts =
    StatementEnv.values new_stmts
    |> List.fold ~init:[] ~f:(fun used stmt ->
           get_next_statements_ref stmt
           |> List.fold ~init:used ~f:(fun used nxt_stmt ->
                  if List.exists ~f:(fun r -> phys_equal r nxt_stmt) used then
                    used
                  else if StatementEnv.exists !nxt_stmt new_stmts then (
                    nxt_stmt := StatementEnv.get !nxt_stmt new_stmts;
                    nxt_stmt :: used)
                  else
                    failwith
                    @@ sprintf "internal error: replace failed:\n%s\n\n"
                         (string_of stmt)))
    |> ignore;
    StatementEnv.get query new_stmts
end

module ReadGraph = struct
  type rs_t =
    | Never
    | Once of unit StatementEnv.t
    | TwiceOrMore of unit StatementEnv.t

  type rg_t = RG of rs_t StatementEnv.t
  type rgenv_t = RGENV of (Ident.tvar, rg_t) List.Assoc.t

  let empty = Never
  let rg_empty = RG (StatementEnv.mk_empty Never)
  (* let rgenv_empty = RGENV [] *)

  let length = function
    | Never -> 0
    | Once env | TwiceOrMore env -> StatementEnv.length env
  (* let rg_length = function RG rg -> StatementEnv.length rg *)
  (* let rgenv_length = function RGENV rgenv -> List.length rgenv *)

  let rg_update stmt rs = function
    | RG rg -> RG (StatementEnv.update stmt rs rg)

  let is_once = function Once _ -> true | _ -> false

  let mem stmt = function
    | Never -> false
    | Once env | TwiceOrMore env -> StatementEnv.exists stmt env

  (* let rg_mem stmt = function RG rg -> StatementEnv.exists stmt rg *)
  let rgenv_mem tvar = function
    | RGENV rgenv -> List.Assoc.mem ~equal:Stdlib.( = ) rgenv tvar

  let rg_get stmt = function RG rg -> StatementEnv.get stmt rg

  let rgenv_get tvar = function
    | RGENV rgenv ->
        assert (rgenv_mem tvar (RGENV rgenv));
        List.Assoc.find_exn ~equal:Stdlib.( = ) rgenv tvar

  let get_reading_stmts = function
    | Never -> StatementEnv.mk_empty ()
    | Once env | TwiceOrMore env -> env

  let rgenv_entries = function RGENV rgenv -> rgenv
  let rg_is_empty = function RG rg -> StatementEnv.length rg = 0

  (* let rg_rev = function RG rg ->
     StatementEnv.entries rg
     |> List.fold
      ~f:(fun res (stmt, rs) ->
         get_reading_stmts rs
         |> StatementEnv.keys
         |> List.fold
           ~f:(fun res nxt_stmt ->
              StatementEnv.update nxt_stmt
                (stmt :: StatementEnv.get nxt_stmt res)
                res
           )
           ~init:res
      )
      ~init:(StatementEnv.mk_empty [])

     let rgenv_rev = function RGENV rgenv ->
     let rgdata =
      rgenv
      |> List.map
        ~f:(fun (tvar, rg) -> tvar, rg_rev rg)
     in
     rgdata *)

  let string_of_rgenv query_stmt = function
    | RGENV rgenv ->
        string_of
          ~info:(fun stmt ->
            List.map ~f:fst rgenv
            |> String.concat_map_list ~sep:" " ~f:(fun tvar ->
                   let r = rgenv_get tvar (RGENV rgenv) |> rg_get stmt in
                   sprintf "%s:%d" (Ident.name_of_tvar tvar) (length r))
            |> sprintf "[%s]")
          query_stmt

  (* max rs1 rs2 *)
  let merge rs1 rs2 =
    let merged =
      StatementEnv.merge (get_reading_stmts rs1) (get_reading_stmts rs2)
    in
    match (rs1, rs2) with
    | TwiceOrMore _, _ | _, TwiceOrMore _ -> TwiceOrMore merged
    | Once _, Once _ | Once _, Never | Never, Once _ -> Once merged
    | Never, Never -> Never

  (* rs1 + rs2 *)
  let add rs1 rs2 =
    let merged =
      StatementEnv.merge (get_reading_stmts rs1) (get_reading_stmts rs2)
    in
    match (rs1, rs2) with
    | TwiceOrMore _, _ | _, TwiceOrMore _ | Once _, Once _ -> TwiceOrMore merged
    | Once _, Never | Never, Once _ -> Once merged
    | Never, Never -> Never

  let is_updated old_rs new_rs =
    match (old_rs, new_rs) with
    | Never, Never -> false
    | Once _, Once _ | TwiceOrMore _, TwiceOrMore _ ->
        length old_rs <> length new_rs
    | _ -> true

  let rec rc_of_term_rep varname term res =
    if Term.is_var term then
      let (tvar, _), _ = Term.let_var term in
      if String.equal (Ident.name_of_tvar tvar) varname then res + 1 else res
    else if Term.is_app term then
      let _, args, _ = Term.let_app term in
      List.fold
        ~f:(fun res term -> rc_of_term_rep varname term res)
        ~init:res args
    else failwith "rc_of_term_rep: not implemented"

  let rc_of_atom_rep varname atom res =
    if Atom.is_app atom then
      let _, args, _ = Atom.let_app atom in
      List.fold
        ~f:(fun res term -> rc_of_term_rep varname term res)
        ~init:res args
    else if Atom.is_true atom || Atom.is_false atom then res
    else
      failwith
      @@ sprintf "rc_of_atom_rep: not implemented for: %s" (Atom.str_of atom)

  let rec rc_of_formula_rep varname fml res =
    match fml with
    | Formula.Atom (atom, _) -> rc_of_atom_rep varname atom res
    | Formula.UnaryOp (_, phi, _) -> rc_of_formula_rep varname phi res
    | Formula.BinaryOp (_, phi1, phi2, _) ->
        rc_of_formula_rep varname phi1 res |> rc_of_formula_rep varname phi2
    | Formula.Bind (_, bounds, phi', _) ->
        (* <varname> is in <bounds> *)
        if
          List.exists
            ~f:(fun (tvar, _) -> String.equal (Ident.name_of_tvar tvar) varname)
            bounds
        then 0 (* <varname> is not in <bounds> *)
        else rc_of_formula_rep varname phi' res
    | LetRec (_funcs, _phi, _info) ->
        failwith "rc_of_formula_rep: not implemented"
    | LetFormula (_var, _sort, def, body, _info) ->
        rc_of_term_rep varname def res |> rc_of_formula_rep varname body

  let of_rc stmt cnt =
    if cnt = 0 then Never
    else if cnt = 1 then Once (StatementEnv.init () [ (stmt, ()) ])
    else TwiceOrMore (StatementEnv.init () [ (stmt, ()) ])

  let of_formula varname stmt fml =
    of_rc stmt @@ rc_of_formula_rep varname fml 0

  let of_term varname stmt term = of_rc stmt @@ rc_of_term_rep varname term 0

  let rec get_rg_dfs varname prev_env stmt res : rg_t =
    let rs =
      List.fold ~init:empty (get_next_statements stmt) ~f:(fun rs nxt_stmt ->
          rg_get nxt_stmt res |> merge rs)
    in
    let update = get_rg_dfs_update varname prev_env stmt in
    if is_assign stmt then
      let varname', term, _ = let_assign stmt in
      if String.equal varname' varname then
        of_term varname stmt term |> update res
      else of_term varname stmt term |> add rs |> update res
    else if is_nondet_assign stmt then
      let varname', _ = let_nondet_assign stmt in
      if String.equal varname' varname then res else update res rs
    else if is_if stmt then
      let fml, _, _ = let_if stmt in
      of_formula varname stmt fml |> add rs |> update res
    else if is_nondet stmt then update res rs
    else if is_assume stmt then
      let fml, _ = let_assume stmt in
      of_formula varname stmt fml |> add rs |> update res
    else if is_nop stmt then update res rs
    else if is_exit stmt then (* Never is the default *) res
    else failwith "not implemented"

  and get_rg_dfs_update varname prev_env stmt res rs =
    let rs0 = rg_get stmt res in
    if is_updated rs0 rs then
      let res = rg_update stmt rs res in
      List.fold ~init:res (StatementEnv.get stmt prev_env)
        ~f:(fun res prev_stmt -> get_rg_dfs varname prev_env prev_stmt res)
    else res

  let get_rg varname prev_env stmts : rg_t =
    List.fold ~init:rg_empty stmts ~f:(fun rg stmt ->
        get_rg_dfs varname prev_env stmt rg)

  let get_rgenv spec_fv prev_env stmt : rgenv_t =
    let stmts = get_all_statements stmt in
    let rgdata =
      LinkedStatement.get_used_vars_from stmt
      |> Variables.to_list
      |> List.fold_left ~init:[] ~f:(fun rgdata varname ->
             if Variables.is_mem spec_fv varname then rgdata
             else (Ident.Tvar varname, get_rg varname prev_env stmts) :: rgdata)
      |> List.rev
    in
    RGENV rgdata
end

module RemoveAssign : sig
  val optimize : print:(string lazy_t -> unit) -> target -> target
end = struct
  let remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts) =
    match get_next_statements stmt_key with
    | [ next_stmt_key ] ->
        if not @@ phys_equal stmt_key next_stmt_key then
          let query_stmt_key =
            Util.remove_nobranch ~query:query_stmt_key stmt_key stmt_keys
          in
          let new_stmts = StatementEnv.remove stmt_key new_stmts in
          (query_stmt_key, new_stmts)
        else
          (* case: self loop -> replace with nop loop *)
          let new_stmt = mk_nop (ref stmt_key) in
          (* replace and return *)
          (query_stmt_key, StatementEnv.update stmt_key new_stmt new_stmts)
    | _ -> assert false

  let sub_stmt using_stmt_key tvar term new_stmts =
    if StatementEnv.exists using_stmt_key new_stmts then
      let using_stmt =
        StatementEnv.get using_stmt_key new_stmts |> sub tvar term
      in
      StatementEnv.update using_stmt_key using_stmt new_stmts
    else new_stmts

  let is_nondet_term _nondet_tvar _term = (* TODO *) true

  let rec is_nondet_formula nondet_tvar = function
    | Formula.Atom (atom, _) -> (*ToDo*) Set.mem (Atom.tvs_of atom) nondet_tvar
    | UnaryOp (_, phi, _) -> is_nondet_formula nondet_tvar phi
    | BinaryOp (_, phi1, phi2, _) ->
        is_nondet_formula nondet_tvar phi1 && is_nondet_formula nondet_tvar phi2
    | Bind (_, _bounds, _phi, _) -> (* ToDo *) false
    | LetRec (_funcs, _phi, _) -> (* ToDo *) false
    | LetFormula (_tvar, _sort, _def, _body, _info) -> (* ToDo *) false

  let check_nondet_if nondet_tvar stmt =
    if is_if stmt then
      let cond_fml, _, _ = let_if stmt in
      is_nondet_formula nondet_tvar cond_fml
    else false

  let check_nondet_assign nondet_tvar stmt =
    if is_assign stmt then
      let _, term, _ = let_assign stmt in
      is_nondet_term nondet_tvar term
    else false

  (* let rec remove_assign_one rgenv stmt_key stmt_keys (query_stmt_key, new_stmts) =
     if StatementEnv.exists stmt_key new_stmts then
      let stmt = StatementEnv.get stmt_key new_stmts in
      (* remove assign stmt *)
      if is_assign stmt then
        let varname, term, nxt_stmt_key = let_assign stmt in
        let tvar = Ident.Tvar varname in
        if ReadGraph.rgenv_mem tvar rgenv then
          let rs = ReadGraph.rgenv_get tvar rgenv |> ReadGraph.rg_get !nxt_stmt_key in
          match rs with
          | ReadGraph.Never ->
            (* remove *)
            remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts)
          | ReadGraph.Once using_stmt_keys | ReadGraph.TwiceOrMore using_stmt_keys ->
            (*
              substitution
              1. assignment value is const
              2. before execute substituted statement (reading the assigned variable) the assignment statement is always called
                 and other assignment statements for the variable are never callsed
            *)
            (* cond 1 *)
            let can_subst =
              Term.tvs_of term
              |> Set.is_empty
            in
            if can_subst then
              let using_stmt_keys = StatementEnv.keys using_stmt_keys in
              (* sub, cond 2 *)
              let rev_rgenv =
                ReadGraph.rgenv_rev rgenv
                |> Fn.Fn.flip (List.Assoc.find_exn ~equal:Stdlib.(=)) tvar
              in
              let new_stmts, can_remove =
                List.fold
                  (fun (new_stmts, can_remove) using_stmt_key ->
                     let can_subst =
                       StatementEnv.get_exn using_stmt_key rev_rgenv
                       |> List.length
                       |> (fun len -> len = 1)
                     in
                     if can_subst then
                       sub_stmt using_stmt_key tvar term new_stmts, can_remove
                     else
                       new_stmts, false
                  )
                  (new_stmts, true)
                  using_stmt_keys
              in
              (* remove *)
              let query_stmt_key, new_stmts =
                if can_remove then
                  remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts)
                else
                  query_stmt_key, new_stmts
              in
              (* check *)
              List.fold
                (fun (query_stmt_key, new_stmts) using_stmt_key ->
                   remove_assign_one rgenv using_stmt_key stmt_keys (query_stmt_key, new_stmts)
                )
                (query_stmt_key, new_stmts)
                using_stmt_keys
            else
              query_stmt_key, new_stmts
        else
          (* case: <tvar> \in <phi> *)
          query_stmt_key, new_stmts
      else if is_nondet_assign stmt then
        let varname, nxt_stmt_key = let_nondet_assign stmt in
        let tvar = Ident.Tvar varname in
        if ReadGraph.rgenv_mem tvar rgenv then
          let rs = ReadGraph.rgenv_get tvar rgenv |> ReadGraph.rg_get !nxt_stmt_key in
          match rs with
          | Never ->
            remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts)
          | Once using_stmt_keys ->
            let using_stmt_keys = StatementEnv.keys using_stmt_keys in
            (* TODO: add a LinkedStatement type where we can use a temporary nondet var *)
            (* TODO: truthy / falthy *)
            (* TODO(bug): check whether any path from assign stmt to stmt using the assigned var don't pass an assignment *)
            let rev_rgenv =
              ReadGraph.rgenv_rev rgenv
              |> flip (List.Assoc.find_exn ~equal:Stdlib.(=)) tvar
            in
            let can_remove =
              List.for_all
                (fun using_stmt_key ->
                   let using_stmt = StatementEnv.get using_stmt_key new_stmts in
                   is_nondet_if tvar using_stmt
                   &&
                   StatementEnv.get_exn using_stmt_key rev_rgenv
                   |> List.length
                   |> (fun len -> len = 1)
                )
                using_stmt_keys
            in
            if can_remove then
              (* remove *)
              let query_stmt_key, new_stmts = remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts) in
              (* sub *)
              let new_stmts =
                List.fold
                  (fun new_stmts using_stmt_key ->
                     let using_stmt = StatementEnv.get using_stmt_key new_stmts in
                     let _, t_stmt, f_stmt = let_if using_stmt in
                     let using_stmt = mk_nondet t_stmt f_stmt in
                     if StatementEnv.exists using_stmt_key new_stmts then
                       StatementEnv.update using_stmt_key using_stmt new_stmts
                     else
                       new_stmts
                  )
                  new_stmts
                  using_stmt_keys
              in
              query_stmt_key, new_stmts
            else
              query_stmt_key, new_stmts
          | TwiceOrMore _ ->
            query_stmt_key, new_stmts
        else
          (* case: <tvar> \in <phi> *)
          query_stmt_key, new_stmts
      else
        (* case: other stmts *)
        query_stmt_key, new_stmts
     else
      (* already deleted *)
      query_stmt_key, new_stmts *)

  type sub_value_t = T_VALID | T_INVALID | T_NONDET | T_LIT of Term.t

  let check_nondet rc = ReadGraph.is_once rc

  let sub_assign_one init_state rgenv stmt_key stmt_keys
      (query_stmt_key, new_stmts) =
    if StatementEnv.exists stmt_key new_stmts then
      let stmt = StatementEnv.get stmt_key new_stmts in
      get_read_vars stmt |> Variables.to_list
      |> List.fold ~init:(query_stmt_key, new_stmts)
           ~f:(fun (query_stmt_key, new_stmts) varname ->
             let tvar = Ident.Tvar varname in
             if ReadGraph.rgenv_mem tvar rgenv then
               (* TODO: simplify terms *)
               (* TODO: improve performance *)
               let rg = ReadGraph.rgenv_get tvar rgenv in
               let init_value =
                 let rc = ReadGraph.rg_get query_stmt_key rg in
                 if ReadGraph.mem stmt_key rc then
                   if State.mem varname init_state then (
                     let term = State.get varname init_state in
                     assert (Term.tvs_of term |> Set.is_empty);
                     T_LIT term)
                   else if check_nondet rc then T_NONDET
                   else T_INVALID
                 else T_VALID
               in
               let value =
                 List.fold ~init:init_value stmt_keys ~f:(fun value stmt_key' ->
                     if Stdlib.(value = T_INVALID) then T_INVALID
                     else if StatementEnv.exists stmt_key' new_stmts then
                       let stmt' = StatementEnv.get stmt_key' new_stmts in
                       let update new_value =
                         if
                           Stdlib.(value = T_VALID)
                           || Stdlib.(new_value = value)
                         then new_value
                         else T_INVALID
                       in
                       if is_assign stmt' then
                         let varname', term, nxt_stmt_key = let_assign stmt' in
                         if
                           String.equal varname' varname
                           && ReadGraph.rg_get !nxt_stmt_key rg
                              |> ReadGraph.mem stmt_key
                         then
                           if Set.is_empty @@ Term.tvs_of term then
                             update (T_LIT term)
                           else T_INVALID
                         else value
                       else if is_nondet_assign stmt' then
                         let varname', nxt_stmt_key = let_nondet_assign stmt' in
                         let rc = ReadGraph.rg_get !nxt_stmt_key rg in
                         if
                           String.equal varname' varname
                           && ReadGraph.mem stmt_key rc
                         then
                           if check_nondet rc then update T_NONDET
                           else T_INVALID
                         else value
                       else value
                     else value)
               in
               match value with
               | T_VALID ->
                   failwith
                   @@ sprintf
                        "internal error: can't reach the statement:\n\
                         %s\n\n\
                         original:\n\
                         %s\n\n\
                         varname: %s\n"
                        (string_of stmt) (string_of stmt_key) varname
               | T_NONDET ->
                   if check_nondet_if tvar stmt then
                     let _, t_stmt, f_stmt = let_if stmt in
                     let stmt = mk_nondet t_stmt f_stmt in
                     ( query_stmt_key,
                       StatementEnv.update stmt_key stmt new_stmts )
                   else if check_nondet_assign tvar stmt then
                     let varname, _, nxt_stmt = let_assign stmt in
                     let stmt = mk_nondet_assign varname nxt_stmt in
                     ( query_stmt_key,
                       StatementEnv.update stmt_key stmt new_stmts )
                   else (query_stmt_key, new_stmts)
               | T_LIT term ->
                   (query_stmt_key, sub_stmt stmt_key tvar term new_stmts)
               | T_INVALID -> (query_stmt_key, new_stmts)
             else (* case: <tvar> \in <phi> *)
               (query_stmt_key, new_stmts))
    else (* already deleted *)
      (query_stmt_key, new_stmts)

  let remove_unused_assign_one rgenv stmt_key stmt_keys
      (query_stmt_key, new_stmts) =
    if StatementEnv.exists stmt_key new_stmts then
      let stmt = StatementEnv.get stmt_key new_stmts in
      if is_assign stmt || is_nondet_assign stmt then
        let varname, nxt_stmt_key =
          if is_assign stmt then
            let varname, _, nxt_stmt_key = let_assign stmt in
            (varname, nxt_stmt_key)
          else let_nondet_assign stmt
        in
        let tvar = Ident.Tvar varname in
        if
          ReadGraph.rgenv_mem tvar rgenv
          && (*ToDo*)
          Stdlib.(
            ReadGraph.rgenv_get tvar rgenv
            |> ReadGraph.rg_get !nxt_stmt_key
            = Never)
        then remove_stmt stmt_key stmt_keys (query_stmt_key, new_stmts)
        else (* case: <tvar> \in <phi> *)
          (query_stmt_key, new_stmts)
      else (query_stmt_key, new_stmts)
    else (* already deleted *)
      (query_stmt_key, new_stmts)

  let sub_assign ~print is_print_for_debug stmts inits spec_fv query_stmt =
    let new_stmts = Util.mk_replacer stmts in
    let prev_env = Util.get_prev_env query_stmt in
    let rgenv = ReadGraph.get_rgenv spec_fv prev_env query_stmt in
    if is_print_for_debug then
      print
      @@ lazy
           (sprintf "rgenv:\n%s\n\n"
              (ReadGraph.string_of_rgenv query_stmt rgenv));
    let init_state = State.of_inits inits in
    List.fold ~init:(query_stmt, new_stmts) stmts
      ~f:(fun (query_stmt, new_stmts) stmt ->
        sub_assign_one init_state rgenv stmt stmts (query_stmt, new_stmts))
    |> fun (query_stmt, new_stmts) ->
    Util.replace_stmt ~query:query_stmt new_stmts

  let remove_unused_assign stmts spec_fv query_stmt =
    let new_stmts = Util.mk_replacer stmts in
    let prev_env = Util.get_prev_env query_stmt in
    let rgenv = ReadGraph.get_rgenv spec_fv prev_env query_stmt in
    let query_stmt, _ =
      List.fold ~init:(query_stmt, new_stmts) stmts
        ~f:(fun (query_stmt, new_stmts) stmt ->
          remove_unused_assign_one rgenv stmt stmts (query_stmt, new_stmts))
    in
    Util.replace_stmt ~query:query_stmt new_stmts

  let optimize_stmt ~print inits spec_fv stmt =
    let rec rep is_first n stmt =
      if n = 0 then stmt
      else
        let stmts = get_all_statements stmt in
        let stmt = sub_assign ~print is_first stmts inits spec_fv stmt in
        let stmts = get_all_statements stmt in
        remove_unused_assign stmts spec_fv stmt |> rep false (n - 1)
    in
    rep false 10 stmt
  (* rep true 10 stmt *)

  let optimize ~print (spec_fv, decls, inits, stmt) =
    (spec_fv, decls, inits, optimize_stmt ~print inits spec_fv stmt)
end

module RemoveNop : sig
  val optimize : target -> target
end = struct
  let optimize_stmt query_stmt =
    let stmts = get_all_statements query_stmt in
    List.fold ~init:query_stmt stmts ~f:(fun query_stmt stmt ->
        if is_nop stmt then Util.remove_nobranch ~query:query_stmt stmt stmts
        else query_stmt)

  let optimize (spec_fv, decls, inits, stmt) =
    (spec_fv, decls, inits, optimize_stmt stmt)
end

(*
  if there doesn't exists an assign stmt for phivars or an assume stmt after some stmt, remove the stmt
*)
module RemoveTrailingNoValueChanged : sig
  val optimize : target -> target
end = struct
  let rec dfs prev_env stmt used =
    if StatementEnv.exists stmt used then used
    else
      let used = StatementEnv.add stmt used in
      StatementEnv.get stmt prev_env
      |> List.fold ~init:used ~f:(fun used prev_stmt ->
             dfs prev_env prev_stmt used)

  let optimize_stmt spec_fv query_stmt =
    let stmts = get_all_statements query_stmt in
    let prev_env = Util.get_prev_env query_stmt in
    let noreplace_stmts =
      List.fold ~init:(StatementEnv.mk_empty ()) stmts ~f:(fun used stmt ->
          if
            is_assume stmt
            || Fn.non Variables.is_empty
                 (Variables.inter (get_written_vars stmt) spec_fv)
          then dfs prev_env stmt used
          else used)
    in
    let new_stmts = Util.mk_replacer stmts in
    List.fold ~init:new_stmts stmts ~f:(fun new_stmts stmt ->
        if StatementEnv.exists stmt noreplace_stmts then new_stmts
        else StatementEnv.update stmt (mk_exit ()) new_stmts)
    |> Util.replace_stmt ~query:query_stmt

  let optimize (spec_fv, decls, inits, stmt) =
    (spec_fv, decls, inits, optimize_stmt spec_fv stmt)
end

let optimize ~print spec_fv decls inits stmt =
  (spec_fv, decls, inits, stmt)
  |> RemoveAssign.optimize ~print
  |> RemoveNop.optimize |> RemoveTrailingNoValueChanged.optimize
(* TODO: for assumes *)
