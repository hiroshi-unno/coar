(* Reduction of an EHMTT verification problem to higher-order model checking
   (Unno, Tabuchi and Kobayashi, "Verification of tree-processing programs via
   higher-order model checking", APLAS 2010).  [rsfds_of_ehmtt] returns a list
   of named RSFD problems: one ("main") for the whole program against the
   output automaton, and one per coercion in the rules, each checking that the
   coerced term meets the state it is coerced to.  Satisfaction of every
   returned problem establishes the EHMTT safety property. The converse
   does not hold in general: abstracting input trees by automaton states
   loses correlations between repeated inspections of the same input.
   A rejected obligation can therefore be a false alarm for the source
   program, even when the HORS checker decides that obligation exactly. *)
open Core
open Common.Ext
open Common.Combinator
open Ast
open EHMTT
open Automata

(* The figures the reduction reports for one generated problem, as the
   original EHMTT verifier printed them: the size and rule count of the
   transformed EHMTT the problem is made from, of the RSFD it becomes, and
   the state counts of its input and output automata (each restricted to the
   states the problem can reach). *)
type stats = {
  ehmtt_size : int;
  ehmtt_rules : int;
  rsfd_size : int;
  rsfd_rules : int;
  input_states : int;
  output_states : int;
}

(* [rsfd_of ~names ~fresh_case rules0 trs trs_out (typs, id) start] is the
   RSFD problem whose rules are [rules0] and a start rule
   [names.start -> start], checked against
   [trs_out] from state [id], with [trs] restricted to the states the input
   can be in: those of the main type's parameters [typs] and of the trees the
   rules mention.  [trs] must list each of those states ([input_table]); one
   with no transition makes [names.success] an accepted leaf of [trs_out].
   [start] must apply the problem's copy of the main
   non-terminal to the most general arguments, and every non-terminal it and
   [rules0] mention must have a rule in [rules0].  [fresh_case] names the
   non-terminals a large case is moved into. *)
let rsfd_of ~names ~fresh_case (rules0 : t) (trs : TTA.trs) (trs_out : TTA.trs)
    (typs, id) start =
  let trs_in =
    let ids = RefType.attr_of @@ RefType.make_type typs (RefType.Base id) in
    let fds =
      List.dedup_keep_last @@ List.concat_map ~f:(snd >> snd >> trees) rules0
    in
    TreeAutomaton.remove_unreachable ~next_ids_body:TTA.next_ids_body
      (List.map ~f:Ident.name_of_tvar (ids @ fds))
      trs
  in
  let trs_out =
    TreeAutomaton.reachable ~next_ids_body:TTA.next_ids_body
      (Ident.name_of_tvar id) trs_out
  in
  (* a case on a state with no transition (one accepting no input tree)
     is the leaf [names.success] ([rsfd_term_of]); no run reaches it, so
     every output state accepts it.  Only added when such a state is
     present, and never twice for one state, which would make the automaton
     nondeterministic *)
  let trs_out =
    if List.exists trs_in ~f:(snd >> List.is_empty) then
      let success = Ident.name_of_tvar names.success in
      List.map trs_out ~f:(fun (q, body) ->
          if List.Assoc.mem body ~equal:String.equal success then (q, body)
          else (q, body @ [ (success, []) ]))
    else trs_out
  in
  let rules =
    RSFD.optimize_case ~fresh:fresh_case
    (* reduce case_ statements with constant arg. *)
    @@ List.map ~f:(fun (id, (ids, t)) -> (id, (ids, RSFD.reduce trs_in t)))
    @@ RSFD.reachable names.start
    @@ List.map ~f:(fun (id, (ids, t)) ->
        (id, (ids, rsfd_term_of ~names trs_in t)))
    @@ ((names.start, ([], start)) :: rules0)
  in
  ( Problem.RSFD (trs_in, rules, TreeAutomaton.TTA trs_out),
    {
      ehmtt_size = size_of_prog rules0;
      ehmtt_rules = List.length rules0;
      rsfd_size = RSFD.sizeof rules;
      rsfd_rules = List.length rules;
      input_states = TreeAutomaton.number_of_states_trs trs_in;
      output_states = TreeAutomaton.number_of_states_trs trs_out;
    } )

(* The program the generated problems are made from: [rules] are the
   input's, then the tree copier, then the rules of the most general
   arguments of the main type's function-typed parameters, with [copy t]
   not yet expanded; [start] applies the main non-terminal to those
   arguments; [copier] is the tree copier's name and [fail] the terminal of
   a case with no branch for its node, both drawn fresh. *)
type program = { rules : t; start : term; copier : Ident.tvar; fail : string }

(* An input the reduction refuses: a non-terminal defined twice (a program
   is a set of definitions, one per name; reading only the first of two would
   check a program other than the one written), an integer literal (the
   reduction's own notation for a data value, which the input language does
   not have), or an automaton that gives the reserved choice terminal [br] a
   transition. *)
exception Ill_formed of string

(* Returns the generated problems, and the [program] they were made from.
   An input is a tree, finite or infinite, that the input automaton accepts
   (APLAS 2010, Definitions 2 and 3): the input automaton is read with only
   the transitions some such tree uses ([input_table]), and when a base
   parameter of the main type is over a state accepting no tree at all the
   property holds vacuously and no problem is returned.

   [print] receives the statistics of the original EHMTT verifier, in its
   wording: the order and size of the input, then for every generated problem
   a [BEGIN <name>.hors...] ... [END <name>.hors...] block with its [stats],
   then the totals over all problems and the time the reduction took. *)
let rsfds_of_ehmtt ~print rules trs (id_nt, main_typ) =
  (match
     List.find_a_dup (List.map rules ~f:fst) ~compare:Ident.tvar_compare
   with
  | Some f ->
      raise
        (Ill_formed
           (sprintf "the non-terminal %s is defined more than once"
              (Ident.name_of_tvar f)))
  | None -> ());
  (* An integer literal is the reduction's own syntax for a data value, the
     index of an input state in the list the reduction restricts to the
     states a problem reaches; the input language gives it no meaning, and
     the index would name a different state in a different problem *)
  (let rec has_fd = function
     | Fd _ -> true
     | App (t1, t2) -> has_fd t1 || has_fd t2
     | Case (_, pats) -> List.exists pats ~f:(snd >> snd >> has_fd)
     | Coerce (_, t, _) | Copy t -> has_fd t
     | Nonterm _ | Var _ | Term _ | Tree _ | VarOrTerm _ -> false
   in
   match List.find rules ~f:(snd >> snd >> has_fd) with
   | Some (f, _) ->
       raise
         (Ill_formed
            (sprintf
               "the rule of %s has an integer literal, which the EHMTT \
                language does not have"
               (Ident.name_of_tvar f)))
   | None -> ());
  (* [br] is the input language's nondeterministic choice, which every
     state reads into itself on both children; an automaton that gives it
     transitions of its own would make the output automaton
     nondeterministic and give [br] a second meaning, so it is refused *)
  (match List.find trs ~f:(fun (_q, (a, _qs)) -> String.equal a "br") with
  | Some (q, (_, qs)) ->
      raise
        (Ill_formed
           (sprintf
              "the automaton gives br a transition (%s br -> %s); br is \
               reserved for nondeterministic choice, which every state reads \
               into itself on both children"
              q (String.concat ~sep:" " qs)))
  | None -> ());
  (* A rule parameter named [br] is renamed.  The reduction joins the
     branches of a case with the choice terminal [br] inside the rule's
     body, and the model checkers tell a variable from a terminal by the
     rule's parameter list, so the printed choice would read the parameter
     instead: one branch picked by an input's data value where every branch
     must be accepted.  The renaming keeps the meaning, since the body's
     variable occurrences of [br] are the parameter's (a pattern-bound [br]
     is replaced by a data value and never printed). *)
  let rules =
    let taken = String.Set.of_list (names_of_program rules trs main_typ) in
    let rec fresh i =
      let x = "brv" ^ if i = 0 then "" else string_of_int i in
      if Set.mem taken x then fresh (i + 1) else Ident.Tvar x
    in
    let br = Ident.Tvar "br" in
    List.map rules ~f:(fun (f, (xs, t)) ->
        if List.mem xs br ~equal:Ident.tvar_equal then
          let x' = fresh 0 in
          ( f,
            ( List.map xs ~f:(fun x ->
                  if Ident.tvar_equal x br then x' else x),
              subst [ (br, x') ] t ) )
        else (f, (xs, t)))
  in
  (* the names the reduction adds avoid every name of the program *)
  let program_names = names_of_program rules trs main_typ in
  let names = names_for program_names in
  let copy1 = copy1 ~names and copy2 = copy2 ~names in
  (* the non-terminals a large case is moved into: [CASE<k>], which has no
     underscore and so ends like no copy, skipping the program's names *)
  let fresh_case =
    let cnt = ref 0 in
    let taken = String.Set.of_list program_names in
    let rec fresh () =
      incr cnt;
      let x = "CASE" ^ string_of_int !cnt in
      if Set.mem taken x || String.equal x (Ident.name_of_tvar names.start)
      then fresh ()
      else x
    in
    fresh
  in
  match RefType.args_and_ret main_typ with
  | main_type_args, RefType.Base main_type_ret ->
      let terminals =
        List.dedup_keep_last
        @@ List.map trs ~f:(fun (_q, (a, qs)) -> (Ident.Tvar a, List.length qs))
      in
      (* the most general arguments of the main non-terminal, with the rules
         of the non-terminals that stand for its function-typed parameters;
         their names avoid every name of the program and of its copies *)
      let copier, start_args, arg_rules =
        let taken =
          List.map program_names ~f:(fun x -> Ident.Tvar x)
          @ [ names.br; names.success; names.start ]
        in
        let taken x =
          List.exists
            [ x; copy1 x; copy2 x ]
            ~f:(fun y -> List.mem ~equal:Ident.tvar_equal taken y)
          || String.is_prefix (Ident.name_of_tvar x)
               ~prefix:names.terminal_prefix
          || String.is_prefix (Ident.name_of_tvar x)
               ~prefix:names.arg_check_prefix
        in
        (* the tree copier's name: [Copy] unless the program uses it (an
           input may define its own [Copy], which need not be a copier) *)
        let copier =
          let rec go i =
            let x =
              Ident.Tvar (if i = 0 then "Copy" else "Copy" ^ string_of_int i)
            in
            if taken x then go (i + 1) else x
          in
          go 0
        in
        let cnt = ref 0 in
        let rec fresh () =
          incr cnt;
          let x = Ident.Tvar ("N" ^ string_of_int !cnt) in
          if taken x then fresh () else x
        in
        let ts, rss =
          List.unzip @@ List.map main_type_args ~f:(of_type ~names ~fresh ~copier)
        in
        (copier, ts, List.concat rss)
      in
      (* the states the generated rules check an argument against *)
      let arg_check_states =
        List.filter_map (EHMTT.terminals arg_rules) ~f:(fun a ->
            String.chop_prefix ~prefix:names.arg_check_prefix
              (Ident.name_of_tvar a))
      in
      (* create "Copy" function; the generated rules are typed and transformed
         with the program's, since they apply its [Copy] and are applied by it
         *)
      let rules = rules @ [ make_tree_copier ~copier terminals ] @ arg_rules in
      let program =
        {
          rules;
          start = apps (Nonterm id_nt) start_args;
          copier;
          fail = names.fail;
        }
      in
      (* type inference *)
      let type_env = TypeSystem.f ~print ~start:program.start rules in
      (* print @@ lazy
         (Format.asprintf "Typing: [%a]" (List.pr TypeSystem.pr_bn ", ") type_env); *)
      print
      @@ lazy
           (sprintf "Order of original EHMTT: %d"
           @@ List.last_exn
           @@ List.sort ~compare:Stdlib.compare
           @@ List.map ~f:(snd >> order_of_type) type_env);
      (* replace each (copy t) with (Copy t) *)
      let rules = expandCopy ~copier rules in
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
      let begin_t = Common.Clock.time_s () in
      (* the input automaton read over its trees, finite or infinite, with
         the transitions no input uses dropped, listing every state an
         input or a [gen] can name *)
      let table =
        input_table trs
          (List.map ~f:Ident.name_of_tvar
             (RefType.attr_of main_typ
             @ List.concat_map rules ~f:(snd >> snd >> trees)))
      in
      let trs_out =
        TTA.add_arg_check_transitions ~prefix:names.arg_check_prefix
          (TTA.add_br_transitions ~br:(Ident.name_of_tvar names.br) trs)
          arg_check_states
      in
      let start = apps (Nonterm id_nt) start_args in
      (* RSFD for verification of the whole program *)
      let rsfd =
        let table_out = TTA.make trs_out in
        let rules0 = alphaRules ~names rules in
        ( "main",
          rsfd_of ~names ~fresh_case rules0 table table_out
            (main_type_args, main_type_ret)
            (alpha ~names start) )
      in
      (* RSFDs for verification of each coercion *)
      let rsfds =
        (* every terminal the rules use is an output constructor, whether
           or not the input automaton reads it: the beta copy of each is a
           rule that explores its children, so a terminal the input
           automaton does not know (one only the program builds, [br], or
           an argument check) needs a rule as much as one it does.  The
           arity is the one the type inference gave it. *)
        let terminals =
          let rec arity = function
            | TVar { contents = Some typ } -> arity typ
            | Func (_, typ) -> 1 + arity typ
            | TVar { contents = None } | In | Out -> 0
          in
          let known = List.map terminals ~f:fst in
          terminals
          @ List.filter_map (EHMTT.terminals rules) ~f:(fun a ->
              if List.mem ~equal:Ident.tvar_equal known a then None
              else
                Option.map ~f:(fun typ -> (a, arity typ))
                @@ List.Assoc.find ~equal:Ident.tvar_equal (List.rev type_env) a)
        in
        let trs_out =
          TTA.add_success_transitions
            ~success:(Ident.name_of_tvar names.success)
            trs_out
        in
        if true then
          let table_out = TTA.make trs_out in
          let cs = List.concat_map rules ~f:(snd >> snd >> coercions) in
          List.mapi cs ~f:(fun i (q, t, idx) ->
              let rules' = beta_rules ~names (q, t, idx) rules terminals in
              ( "coerce" ^ string_of_int (i + 1),
                rsfd_of ~names ~fresh_case rules' table table_out
                  (main_type_args, q)
                  (beta_term ~names (q, t, idx) start) ))
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
      let elapsed_t = Common.Clock.time_s () -. begin_t in
      (* the property quantifies over the inputs of the main type's base
         parameters; when one of their states accepts no tree, finite or
         infinite, there is no input, the property holds vacuously, and there is nothing to
         check (the problems above would explore inputs that do not exist) *)
      let problems =
        match
          List.find_map main_type_args ~f:(function
            | RefType.Base q
              when List.Assoc.find table ~equal:String.equal
                     (Ident.name_of_tvar q)
                   |> Option.for_all ~f:List.is_empty ->
                Some q
            | _ -> None)
        with
        | Some q ->
            print
            @@ lazy
                 (sprintf
                    "The state %s of a parameter of the main type accepts no \
                     tree, finite or infinite: the property holds vacuously"
                    (Ident.name_of_tvar q));
            []
        | None -> rsfd :: rsfds
      in
      List.iter problems ~f:(fun (name, (_, s)) ->
          print @@ lazy (sprintf "BEGIN %s.hors..." name);
          print
          @@ lazy
               (sprintf "Size of transformed EHMTT: %d (%d rules)" s.ehmtt_size
                  s.ehmtt_rules);
          print
          @@ lazy (sprintf "Size of RSFD: %d (%d rules)" s.rsfd_size s.rsfd_rules);
          print
          @@ lazy
               (sprintf "Number of states of input automaton: %d" s.input_states);
          print
          @@ lazy
               (sprintf "Number of states of output automaton: %d"
                  s.output_states);
          print @@ lazy (sprintf "END %s.hors..." name));
      let total f = List.sum (module Int) problems ~f:(snd >> snd >> f) in
      print
      @@ lazy
           (sprintf "Total size of transformed EHMTT: %d (%d rules)"
              (total (fun s -> s.ehmtt_size))
              (total (fun s -> s.ehmtt_rules)));
      print
      @@ lazy (sprintf "Total size of RSFD: %d" (total (fun s -> s.rsfd_size)));
      print
      @@ lazy
           (sprintf "Total number of states of input automaton: %d"
              (total (fun s -> s.input_states)));
      print
      @@ lazy
           (sprintf "Total number of states of output automaton: %d"
              (total (fun s -> s.output_states)));
      print @@ lazy (sprintf "Total time for transformation: %f sec" elapsed_t);
      ( List.map problems ~f:(fun (name, (problem, _)) -> (name, problem)),
        program )
  | _, ret ->
      failwith @@ Format.asprintf "return type %a not supported" RefType.pr ret

(* Write the text of every problem of [problems] into [dir] (created when
   missing) as [<name>.hors], in the format the external model checkers
   read.  An existing file of that name is overwritten. *)
let write_hors_files dir problems =
  Core_unix.mkdir_p dir;
  List.iter problems ~f:(fun (name, problem) ->
      Out_channel.with_file
        (Filename.concat dir (name ^ ".hors"))
        ~f:(fun oc -> Problem.pr (Format.formatter_of_out_channel oc) problem))

(* Decide an EHMTT problem with a HORS model checker [solve], which answers
   a verdict together with the checker's counterexample when it printed one.
   The problem is reduced with [rsfds_of_ehmtt], and the resulting problems
   are decided in order.

   The verdict is decided by the first problem, in order, that is not
   satisfied: [Sat] when there is none; when it is refuted, [Unsat] if
   [Completeness.check] establishes that the reduction is complete for the
   program or [Confirmation.search] finds concrete inputs on which the
   program violates the specification (both written to standard error),
   and otherwise [Unknown], with the counterexample written to standard
   error marked as possibly spurious; and an [Error] naming it when
   [solve] could not decide it ([Unknown] or an [Error]), since a problem not
   yet decided could still refute.  Rules that
   do not type under [TypeSystem.f] are refused with an [Error], never a
   verdict.

   [options.check_all_problems] decides only how many problems are checked,
   never the verdict: when it is [false], checking stops at that first
   problem; when [true], every problem is checked (an undecided one does not
   stop the rest) and one line per problem, its name and its outcome with the
   counterexample if any, goes to standard error as soon as it is known.  A
   timeout or another asynchronous exception still ends the whole check.
   [options.hors_dir] receives the text of every problem before the first is
   checked.  [print] receives the diagnostics: the reduction's statistics, the
   time each check took and the name of the problem that decided the verdict.
   *)
let solve_ehmtt ~print ~(options : EhmttOptions.t)
    ~(solve : Problem.t -> (Problem.solution * string option) Or_error.t)
    ehmtt trs (main, typ) =
  let start_t = Common.Clock.time_s () in
  match rsfds_of_ehmtt ~print ehmtt trs (main, typ) with
  | exception TypeSystem.Type_error msg ->
      Or_error.error_string ("the EHMTT rules are not well typed: " ^ msg)
  | exception Ill_formed msg -> Or_error.error_string ("the EHMTT program: " ^ msg)
  | rsfds, program ->
      Option.iter options.hors_dir ~f:(fun dir -> write_hors_files dir rsfds);
      print @@ lazy "\nHigher-Order Model Checking:";
      let report name msg =
        if options.check_all_problems then
          eprintf "EHMTT problem %s: %s\n%!" name msg
      in
      let mc_time = ref 0.0 in
      let check (name, rsfd) =
        print @@ lazy (sprintf "BEGIN %s.hors..." name);
        let begin_t = Common.Clock.time_s () in
        let res = solve rsfd in
        let t = Common.Clock.time_s () -. begin_t in
        mc_time := !mc_time +. t;
        print @@ lazy (sprintf "Time for model checking: %f sec" t);
        print @@ lazy (sprintf "END %s.hors..." name);
        (match res with
        | Ok (Problem.Sat, _) -> report name "verified"
        | Ok (Problem.Unsat, Some cex) ->
            report name
              ("refuted with a counterexample: " ^ String.strip cex)
        | Ok (Problem.Unsat, None) -> report name "refuted"
        | Ok (Problem.Unknown, _) -> report name "not decided"
        | Error err -> report name ("error: " ^ Error.to_string_hum err));
        (name, res)
      in
      (* every problem when asked, otherwise up to the first one that is not
         satisfied *)
      let rec go = function
        | [] -> []
        | p :: rest -> (
            let ((_, res) as r) = check p in
            match res with
            | Ok (Problem.Sat, _) -> r :: go rest
            | _ -> if options.check_all_problems then r :: go rest else [ r ])
      in
      let results = go rsfds in
      print
      @@ lazy (sprintf "Total time for model checking: %f sec" !mc_time);
      let res =
        match
          List.find results ~f:(function
            | _, Ok (Problem.Sat, _) -> false
            | _ -> true)
        with
        | None -> Ok Problem.Sat
        | Some (name, Ok (Problem.Unsat, cex)) -> (
            print @@ lazy (sprintf "refuted by the HORS problem %s" name);
            (* the reduction is sound for every program but complete only
               for a linear program without coercions and a deterministic
               output automaton; outside that, the refutation may be
               spurious, and it is [Unsat] only when a search over concrete
               inputs finds a run of the program that violates the
               specification; otherwise the verdict is [Unknown] and the
               counterexample is still reported, marked as such *)
            match
              Completeness.check ~program:program.rules ~start:program.start
                ~user_rules:ehmtt trs typ
            with
            | Ok () -> Ok Problem.Unsat
            | Error reasons -> (
                let cex_text =
                  match cex with
                  | Some c -> ":\n" ^ String.strip c
                  | None -> " (the checker printed none)"
                in
                let reasons = String.concat ~sep:"; " reasons in
                match
                  Confirmation.search ~rules:program.rules ~copier:program.copier
                    ~fail:program.fail trs
                    (main, typ)
                with
                | Ok (Some w) ->
                    eprintf
                      "EHMTT: the HORS problem %s is refuted; the reduction \
                       is not complete for this program (%s), and the \
                       refutation is confirmed by running it: %s\n%!"
                      name reasons
                      (Format.asprintf "%a" Confirmation.pr_witness w);
                    Ok Problem.Unsat
                | (Ok None | Error _) as found ->
                    eprintf
                      "EHMTT: the HORS problem %s is refuted, but the \
                       reduction is complete only for a linear program \
                       without coercions and with a deterministic output \
                       automaton, and here %s; %s. The answer is unknown; \
                       this counterexample may be spurious (it need not \
                       correspond to a run of the program)%s\n%!"
                      name reasons
                      (match found with
                      | Ok _ ->
                          "running the program on the input trees up to the \
                           search's bounds found no violation"
                      | Error msg ->
                          "the refutation could not be confirmed by running \
                           the program: " ^ msg)
                      cex_text;
                    Ok Problem.Unknown))
        | Some (name, Ok ((Problem.Unknown | Problem.Sat), _)) ->
            Or_error.error_string
              (sprintf
                 "EHMTT verification failed: the HORS problem %s was not \
                  decided"
                 name)
        | Some (name, Error err) ->
            Or_error.error_string
              (sprintf "the HORS problem %s: %s" name (Error.to_string_hum err))
      in
      let elapsed_t = Common.Clock.time_s () -. start_t in
      print @@ lazy (sprintf "\nElapsed Time: %f sec" elapsed_t);
      res


(*
let debug_print_sub sub =
  let prsub ppf (x, y) = Format.fprintf ppf "%s:%s" x y in
  Format.eprintf "[%a]" (List.pr prsub ", ") sub

let transform_rule (f, (xs, t)) =
  let f_ty =
    try List.assoc f typeenv
    with Not_found -> failwith (Format.sprintf "No type info for %s@\n" f)
  in
  let ty_args, _ = TypeSystem.args_and_ret f_ty in
  let make_subst i =
    let ty_i =
      try List.nth ty_args (i - 1)
      with List.Invalid_index k ->
        failwith (Format.sprintf "Failed to pick %dth type of %s" k f)
    in
    let x_i = List.nth xs (i - 1) in
    if is_intype ty_i then (x_i, copy1 x_i) else (x_i, x_i)
  in
  let idx = List.range ~stop:`inclusive 1 (List.length xs) in
  let sub = List.map make_subst idx in
  let rule_a = (copy1 f, (List.map copy1 xs, Term.subst sub (alpha t))) in
  let xs1 = List.map copy1 xs in
  let xs2 = List.map copy2 xs in
  let xs12 = flatten_pairs (List.combine xs1 xs2) in
  let bt = beta_term t coerce_states in
  let rule_b = (copy2 f, (xs12, Term.subst sub bt)) in
  (rule_a, rule_b)

let _ =
  let rules =
    flatten_pairs (List.map transform_rule rules)
    @ List.map make_terminal_fun terminals
  in
  (start_rules @ rules, !coerce_states, n)
*)

(*
let rec beta_term t stref =
  let rec coerces = function
    | Term a -> []
    | Var (x, t) -> []
    | Nonterm f -> []
    | App (t1, t2) -> List.dedup_keep_last (coerces t1 @ coerces t2)
    | Case (x, pats) -> []
    | Tree q -> []
    | CaseState (q, pats) -> []
    | Coerce (q, t) ->
        stref := List.dedup_keep_last (q :: !stref);
        [ (q, t) ]
    | CaseCoerce (q, t, pats) ->
        stref := List.dedup_keep_last (q :: !stref);
        [ (q, t) ]
    | Copy _ | VarOrTerm _ -> failwith "coerces"
  in
  let chi cs t =
    let check_term (q, t) =
      let chk = Term ("check__" ^ q) in
      let at = alpha t in
      App (chk, at)
    in
    let checked_terms = List.map check_term cs in
    let bts = List.map (fun (_, t) -> beta_term t stref) cs in
    let branch =
      Util.nondet_branch (Term TTA.br_symbol)
        (fun (x, y) -> App (x, y))
        (checked_terms @ bts @ [ t ])
    in
    branch
  in
  let rec beta1 = function
    | Term a -> Nonterm (term a)
    | Var (x, t) as v when is_intype !t -> v
    | Var (x, t) -> Var (copy2 x, t)
    | Nonterm f -> Nonterm (copy2 f)
    | App (t1, t2) -> App (App (beta1 t1, alpha t2), beta1 t2)
    | Case (x, pats) ->
        let f (a, (xs, t)) = (a, (xs, beta_term t stref)) in
        Case (x, List.map f pats)
    | Tree q as t -> t
    | CaseState (q, pats) ->
        let f (a, (xs, t)) = (a, (xs, beta_term t stref)) in
        CaseState (q, List.map f pats)
    | Coerce _ | CaseCoerce _ | Copy _ | VarOrTerm _ -> failwith "beta1"
  in
  let rec beta0 = function
    | Term a as t -> t
    | Var (x, t) as v -> v
    | Nonterm f as n -> n
    | App (t1, t2) -> App (beta0 t1, beta0 t2)
    | Case (x, pats) as c -> c
    | Tree q as t -> t
    | CaseState (q, pats) as c -> c
    | Coerce (q, t) -> Tree q
    | CaseCoerce (q, t, pats) -> CaseState (q, pats)
    | Copy _ | VarOrTerm _ -> failwith "beta1"
  in
  chi (coerces t) (beta1 (beta0 t))

let beta rules terminals typeenv =
  let make_terminal_fun (a, n) =
    let vs = List.range ~stop:`inclusive 1 n in
    let vs = List.map (fun v -> "x" ^ string_of_int v) vs in
    let vs1 = List.map copy1 vs in
    let vs2 = List.map copy2 vs in
    let vs12 = flatten_pairs (List.combine vs1 vs2) in
    let vs2' = List.map (fun v -> Var (v, ref Out)) vs2 in
    let t =
      if n = 0 then Term TTA.success_symbol
      else
        Util.nondet_branch (Term TTA.br_symbol) (fun (x, y) -> App (x, y)) vs2'
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
    let ty_args, _ = TypeSystem.args_and_ret f_ty in
    let make_subst i =
      let ty_i =
        try List.nth ty_args (i - 1)
        with List.Invalid_index k ->
          failwith (Format.sprintf "Failed to pick %dth type of %s" k f)
      in
      let x_i = List.nth xs (i - 1) in
      if is_intype ty_i then (x_i, copy1 x_i) else (x_i, x_i)
    in
    let idx = List.range ~stop:`inclusive 1 (List.length xs) in
    let sub = List.map make_subst idx in
    (*    debug_print_sub sub; *)
    let rule_a = (copy1 f, (List.map copy1 xs, Term.subst sub (alpha t))) in
    let xs1 = List.map copy1 xs in
    let xs2 = List.map copy2 xs in
    let xs12 = flatten_pairs (List.combine xs1 xs2) in
    let bt = beta_term t coerce_states in
    let rule_b = (copy2 f, (xs12, Term.subst sub bt)) in
    (rule_a, rule_b)
  in
  let start_rule (f, (xs, t)) =
    let start_from_f =
      let xsxs = flatten_pairs (List.combine xs xs) in
      let dummy_type = ref (TVar { contents = None }) in
      let xsxs = List.map (fun x -> Var (x, dummy_type)) xsxs in
      let f2 = Nonterm (copy2 f) in
      Term.apps f2 xsxs
    in
    (f, (xs, start_from_f))
  in
  let cs = List.map (fun (_, (_, t)) -> Term.count_coerce t) rules in
  let n = List.fold_left (fun x y -> x + y) 0 cs in
  if n = 0 then (rules, [], 0)
  else
    let start_rules = List.map start_rule rules in
    let rules =
      flatten_pairs (List.map transform_rule rules)
      @ List.map make_terminal_fun terminals
    in
    (start_rules @ rules, !coerce_states, n)
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
