open Core
open Common.Ext
open Common.Combinator
open Ast
open EHMTT
open Automata

let rsfd_of is_main (rules0 : t) (trs : TTA.trs) (trs_out : TTA.trs)
    (id_nt, typs, id) =
  let trs_in =
    let ids = RefType.attr_of @@ RefType.make_type typs (RefType.Base id) in
    let fds = List.unique @@ List.concat_map ~f:(snd >> snd >> trees) rules0 in
    TreeAutomaton.remove_unreachable ~next_ids_body:TTA.next_ids_body
      (List.map ~f:Ident.name_of_tvar (ids @ fds))
      trs
  in
  let trs_out =
    TreeAutomaton.reachable ~next_ids_body:TTA.next_ids_body
      (Ident.name_of_tvar id) trs_out
  in
  let ts =
    fst @@ List.unzip @@ List.map ~f:of_type
    @@
    let rec f = function
      | RefType.Base id -> RefType.Base (id, true)
      | RefType.Func (typ1, RefType.Base id) ->
          RefType.Func (f typ1, RefType.Base (id, false))
      | RefType.Func (typ1, typ2) -> RefType.Func (f typ1, f typ2)
    in
    List.map ~f typs
  in
  let rules =
    RSFD.optimize_case
    (* reduce case_ statements with constant arg. *)
    @@ List.map ~f:(fun (id, (ids, t)) -> (id, (ids, RSFD.reduce trs_in t)))
    @@ RSFD.reachable (Ident.Tvar "RSFDStart")
    @@ List.map ~f:(fun (id, (ids, t)) -> (id, (ids, rsfd_term_of trs_in t)))
    @@ ( Ident.Tvar "RSFDStart",
         ([], apps (Nonterm (if is_main then copy1 id_nt else id_nt)) ts) )
       :: rules0
  in
  Problem.RSFD (trs_in, rules, TreeAutomaton.TTA trs_out)

let rsfds_of_ehmtt ~print rules trs (id_nt, main_typ) =
  match RefType.args_and_ret main_typ with
  | main_type_args, RefType.Base main_type_ret ->
      let terminals =
        List.unique
        @@ List.map trs ~f:(fun (_q, (a, qs)) -> (Ident.Tvar a, List.length qs))
      in
      (* create "Copy" function *)
      let rules = rules @ [ make_tree_copier terminals ] in
      (* type inference *)
      let type_env = TypeSystem.f rules in
      (* print @@ lazy
         (Format.asprintf "Typing: [%a]" (List.pr TypeSystem.pr_bn ", ") type_env); *)
      print
      @@ lazy
           (sprintf "Order of original EHMTT: %d"
           @@ List.last_exn
           @@ List.sort ~compare:Stdlib.compare
           @@ List.map ~f:(snd >> order_of_type) type_env);
      (* replace each (copy t) with (Copy t) *)
      let rules = expandCopy rules in
      print
      @@ lazy
           (sprintf "Size of original EHMTT: %d (%d rules)" (size_of_prog rules)
              (List.length rules));
      (* *)
      print @@ lazy (Format.asprintf "@[<v>%a@]" pr_rules rules);
      print @@ lazy "---------------------------------------------------";
      (* *)
      (* main transformation *)
      print @@ lazy "";
      print @@ lazy "Transformation from EHMTT to Recursion Schemes:";
      let begin_t = Core_unix.time () in
      let table = TTA.make trs in
      let trs_out = TTA.add_br_transitions trs in
      (* RSFD for verification of the whole program *)
      let rsfd =
        let table_out = TTA.make trs_out in
        let rules0 = alphaRules rules in
        print
        @@ lazy
             (sprintf "Size of the input EHMTT: %d (%d rules)"
                (size_of_prog rules0) (List.length rules0));
        (* print
           @@ lazy (Format.asprintf "@[<v>%a@]" pr_rules rules0); *)
        ( "main",
          rsfd_of true rules0 table table_out
            (id_nt, main_type_args, main_type_ret) )
      in
      (* RSFDs for verification of each coercion *)
      let rsfds =
        let terminals =
          if List.mem ~equal:Ident.tvar_equal (EHMTT.terminals rules) tbr then
            (tbr, 2) :: terminals
          else terminals
        in
        let trs_out = TTA.add_success_transitions trs_out in
        if true then
          let table_out = TTA.make trs_out in
          let cs = List.concat_map rules ~f:(snd >> snd >> coercions) in
          List.mapi cs ~f:(fun i (q, t, idx) ->
              let rules' = beta_rules (q, t, idx) rules id_nt terminals in
              ( "coerce" ^ string_of_int (i + 1),
                rsfd_of false rules' table table_out (id_nt, main_type_args, q)
              ))
        else
          (* let rulesX, coerce_states, ncoerces =
               beta rules terminals type_env
             in
             let trs_out =
               TTA.add_check_transitions trs_out coerce_states
             in
             print @@ lazy (sprintf "# of coercions: %d" ncoerces);*)
          assert false
      in
      let elapsed_t = Core_unix.time () -. begin_t in
      print @@ lazy (sprintf "Total time for transformation: %f sec" elapsed_t);
      rsfd :: rsfds
  | _, ret ->
      failwith @@ Format.asprintf "return type %a not supported" RefType.pr ret

(*
  let debug_print_sub sub =
    let prsub ppf (x, y) = Format.fprintf ppf "%s:%s" x y in
    Format.eprintf "[%a]" (List.pr prsub ", ") sub

  let transform_rule (f, (xs, t)) =
    let f_ty = 
      try List.assoc f typeenv
      with Not_found -> failwith (Format.sprintf "No type info for %s@\n" f)
    in
    let (ty_args,_) = TypeSystem.args_and_ret f_ty in
    let make_subst i =
      let ty_i = 
        try List.nth ty_args (i-1)  
        with List.Invalid_index(k) -> failwith (Format.sprintf "Failed to pick %dth type of %s" k f)
      in
      let x_i = List.nth xs (i-1) in
      if (is_intype ty_i) then
        (x_i, copy1 x_i)
      else
        (x_i, x_i)
    in
    let idx = List.from_to 1 (List.length xs) in
    let sub = List.map make_subst idx in
    let rule_a = (copy1 f, (List.map copy1 xs, Term.subst sub (alpha t))) in
    let xs1 = List.map copy1 xs in
    let xs2 = List.map copy2 xs in
    let xs12 = unzip (List.combine xs1 xs2) in
    let bt = beta_term t coerce_states in
    let rule_b = (copy2 f, (xs12, Term.subst sub bt)) in
    (rule_a, rule_b)
  in
  let rules = (unzip (List.map transform_rule rules)) @ (List.map make_terminal_fun terminals) in
  (start_rules@rules, !coerce_states, n)
*)

(*
let rec beta_term t stref =
  let rec coerces = function
    | Term(a) -> []
    | Var(x,t) -> []
    | Nonterm(f) -> []
    | App(t1, t2) -> List.unique ((coerces t1) @  (coerces t2))
    | Case(x, pats) -> []
    | Tree(q) -> []
    | CaseState(q, pats) -> []
    | Coerce(q, t) ->
      stref := List.unique (q::!stref); 
      [(q,t)]
    | CaseCoerce(q, t, pats) -> 
      stref := List.unique (q::!stref); 
      [(q,t)]
    | Copy(_) | VarOrTerm(_) -> failwith "coerces"
  in
  let chi cs t =
    let check_term (q,t) = 
      let chk = Term("check__" ^ q) in
      let at = alpha t in
      App(chk, at)
    in
    let checked_terms = List.map check_term cs in
    let bts = List.map (fun (_, t) -> beta_term t stref) cs in
    let branch = 
      Util.nondet_branch (Term(TTA.br_symbol)) (fun (x,y) -> App(x,y)) (checked_terms@bts@[t])
    in
    branch
  in
  let rec beta1 = function
    | Term(a) -> Nonterm(term a)
    | Var(x,t) as v when (is_intype !t) -> v
    | Var(x,t) -> Var(copy2 x, t)
    | Nonterm(f) -> Nonterm(copy2 f)
    | App(t1, t2) -> 
      App(App(beta1 t1, alpha t2), beta1 t2)
    | Case(x, pats) -> 
      let f (a, (xs, t)) = (a, (xs, beta_term t stref)) in
      Case(x, List.map f pats)
    | Tree(q) as t -> t
    | CaseState(q, pats) -> 
      let f (a, (xs, t)) = (a, (xs, beta_term t stref)) in
      CaseState(q, List.map f pats)
    | Coerce(_) | CaseCoerce(_) | Copy(_) | VarOrTerm(_) -> failwith "beta1"
  in
  let rec beta0 = function
    | Term(a) as t-> t
    | Var(x,t) as v -> v
    | Nonterm(f) as n -> n
    | App(t1, t2) -> App(beta0 t1, beta0 t2)
    | Case(x, pats) as c -> c
    | Tree(q) as t -> t
    | CaseState(q, pats) as c -> c
    | Coerce(q,t) -> Tree(q)
    | CaseCoerce(q,t,pats) -> CaseState(q, pats)
    | Copy(_) | VarOrTerm(_) -> failwith "beta1"
  in
  chi (coerces t) (beta1(beta0 t))
;;

let beta rules terminals typeenv =
  let make_terminal_fun (a, n) =
    let vs = List.from_to 1 n in
    let vs = List.map (fun v -> "x" ^ (string_of_int v)) vs in
    let vs1 = List.map copy1 vs in
    let vs2 = List.map copy2 vs in
    let vs12 = unzip (List.combine vs1 vs2) in
    let vs2' = List.map (fun v -> Var(v, ref Out)) vs2 in
    let t = 
      if n = 0 then
        Term(TTA.success_symbol)
      else
        Util.nondet_branch (Term(TTA.br_symbol)) (fun (x,y) -> App(x,y)) vs2' 
    in
    let rule = (term a, (vs12, t)) in
    rule
  in
  let coerce_states = ref [] in
  let transform_rule (f, (xs, t)) =
    let f_ty = 
      try List.assoc f typeenv
      with Not_found -> failwith (Format.sprintf "No type info for %s@\n" f)
    in
    let (ty_args,_) = TypeSystem.args_and_ret f_ty in
    let make_subst i =
      let ty_i = 
        try List.nth ty_args (i-1)  
        with List.Invalid_index(k) -> failwith (Format.sprintf "Failed to pick %dth type of %s" k f)
      in
      let x_i = List.nth xs (i-1) in
      if (is_intype ty_i) then
        (x_i, copy1 x_i)
      else
        (x_i, x_i)
    in
    let idx = List.from_to 1 (List.length xs) in
    let sub = List.map make_subst idx in
(*    debug_print_sub sub; *)
    let rule_a = (copy1 f, (List.map copy1 xs, Term.subst sub (alpha t))) in
    let xs1 = List.map copy1 xs in
    let xs2 = List.map copy2 xs in
    let xs12 = unzip (List.combine xs1 xs2) in
    let bt = beta_term t coerce_states in
    let rule_b = (copy2 f, (xs12, Term.subst sub bt)) in
    (rule_a, rule_b)
  in
  let start_rule (f, (xs, t)) = 
    let start_from_f = 
      let xsxs = unzip (List.combine xs xs) in
      let dummy_type = ref (TVar({contents=None})) in
      let xsxs = List.map (fun x -> Var(x,dummy_type)) xsxs in
      let f2 = Nonterm(copy2 f) in
      Term.apps f2 xsxs
    in
    (f, (xs, start_from_f))
  in
  let cs = List.map (fun (_, (_, t)) -> Term.count_coerce t) rules in
  let n = List.fold_left (fun x y -> x + y) 0 cs in
  if n = 0 then
    (rules, [], 0)
  else
    let start_rules = List.map start_rule rules in
    let rules = (unzip (List.map transform_rule rules)) @ (List.map make_terminal_fun terminals) in
    (start_rules@rules, !coerce_states, n)
;;
*)

(*
let rsfd_of trs =
  fold
    (object
       method nonterm id = RSFD.Nonterm id
       method var id = RSFD.Var id
       method term id = RSFD.Term id
       method app t1 t2 = RSFD.App (t1, t2)

       method case id1 pats =
         let ts =
           List.map trs ~f:(fun (_, ys) ->
               nondet_branch
                 (List.map ys ~f:(fun (id2, ids1) ->
                      try
                        let ids2, t =
                          List.Assoc.find_exn ~equal:Ident.tvar_equal pats id2
                        in
                        let sub =
                          List.map2_exn ids1 ids2 ~f:(fun id1 id2 ->
                              ( id2,
                                RSFD.Nonterm
                                  (Ident.Tvar
                                     (String.capitalize
                                    @@ Ident.name_of_tvar id1)) ))
                        in
                        RSFD.subst sub t
                      with Not_found_s _ -> RSFD.Term (Ident.Tvar "fail"))))
         in
         RSFD.apps (RSFD.Var id1) ts

       method coerce id t _ =
         RSFD.App
           ( RSFD.Nonterm
               (Ident.Tvar
                  ("Coerce" ^ String.capitalize @@ Ident.name_of_tvar id)),
             t )

       method copy t = RSFD.App (RSFD.Nonterm (Ident.Tvar "Copy"), t)

       method tree id =
         RSFD.Nonterm (Ident.Tvar (String.capitalize @@ Ident.name_of_tvar id))

       method varorterm _id = failwith "rsfd_of"
    end)
*)
