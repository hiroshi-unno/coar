(* Backend that hands a system of polynomial quantified entailments to the
   external PolyQEnt tool.  Its unknowns must be real-valued constants
   (template coefficients); a problem with any other unknown, such as a
   predicate, is refused with an [Error] before anything is written.  The
   entailments are printed as SMT-LIB assertions to a file in a per-call
   scratch directory under the system temporary directory, and
   PolyQEnt is run on it as a separate process (under [timeout] when a budget
   is given); a [sat] answer's model is parsed back into real values.
   PolyQEnt's [unsat] and [unknown] both become the [Unknown] verdict, since
   neither shows that no real assignment exists; a non-zero exit or empty
   output becomes an [Error]. *)
open Core
open Common
open Common.Ext
open Ast
open Ast.Logic

module type SolverType = sig
  val solve :
    ?timeout:int option ->
    ?print_sol:bool ->
    PCSP.Problem.t ->
    PCSP.Problem.solution Or_error.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (* PolyQEnt decides polynomial quantified entailments: its unknowns are
     real-valued template coefficients, declared as constants, and it has no
     notion of an unknown predicate (the translation below declares every
     unknown that some constraint mentions as a [Real] constant).  A problem with one -- any CHC or pCSP
     input given to this backend directly -- used to fail inside the
     translation below with a message about SMT printing or the clausal form,
     reported as a crash; it is a pairing this backend declines. *)
  let non_real_unknowns pqes =
    Map.Poly.fold
      (PCSP.Problem.senv_of @@ PCSP.Problem.remove_unused_params pqes)
      ~init:[]
      ~f:(fun ~key ~data acc ->
        if ExtTerm.is_real_sort data then acc else key :: acc)

  (* [polyqent_names names] is the renaming under which the query is printed:
     it maps every name in [names] that PolyQEnt cannot read to a fresh one it
     can, and leaves out the others (they are printed as they are).

     PolyQEnt's SMT-LIB reader takes a variable only as a run of the
     characters [a-zA-Z0-9_]: it has no rule for a quoted symbol [|...|], nor
     for SMT-LIB's other simple-symbol characters ([~ ! @ $ % ^ & * - + = < > .
     ? /] and the [#] and ['] the tool's own fresh names carry, as in
     [#tvar6]).  A query naming such a variable is refused by PolyQEnt's
     parser and the problem loses its answer.  Quoting the name would be legal
     SMT-LIB and still unreadable to PolyQEnt, so the name is replaced instead.

     Guarantees: every name in the image matches [[a-zA-Z_][a-zA-Z0-9_]*], is
     a legal SMT-LIB simple symbol, is not a word PolyQEnt's grammar reserves
     ([and], [or], [Int], [Real]), is not in [names], and is the image of
     exactly one name, so the map is injective, its inverse reads PolyQEnt's
     model back, and applying it to a formula captures nothing.  A name that is
     already readable, and not reserved, is not in the map. *)
  let polyqent_names names =
    let readable name =
      (not (String.is_empty name))
      && (Char.is_alpha name.[0] || Char.equal name.[0] '_')
      && String.for_all name ~f:(fun c -> Char.is_alphanum c || Char.equal c '_')
      && not (List.mem [ "and"; "or"; "Int"; "Real" ] name ~equal:String.equal)
    in
    let taken =
      ref (Set.Poly.map names ~f:Ident.name_of_tvar)
    in
    Set.fold names ~init:Map.Poly.empty ~f:(fun renaming x ->
        let name = Ident.name_of_tvar x in
        if readable name then renaming
        else
          let stem =
            "pq_"
            ^ String.filter name ~f:(fun c ->
                  Char.is_alphanum c || Char.equal c '_')
          in
          let rec fresh i =
            let candidate = sprintf "%s_%d" stem i in
            if Set.mem !taken candidate then fresh (i + 1) else candidate
          in
          let name' = fresh 0 in
          taken := Set.add !taken name';
          Map.Poly.add_exn renaming ~key:x ~data:(Ident.Tvar name'))

  (* The three files of one call -- the query, PolyQEnt's derived system and
     the configuration copy -- live in a directory of their own under the
     system's temporary directory ([TMPDIR], else [/tmp]), named
     [coar_polyqent_p<pid>_<random>].  A directory per call keeps two calls
     apart even inside one process (two solver domains), and puts whatever a
     killed run leaves behind outside the directory the tool runs from. *)
  let scratch_prefix = "coar_polyqent_p"
  let scratch_files = [ "query.smt2"; "system.smt2"; "config.json" ]

  (* Remove [dir] if it holds nothing but this wrapper's files; anything else
     in it is left alone, and so is a directory already gone. *)
  let remove_scratch dir =
    List.iter scratch_files ~f:(fun name ->
        try Core_unix.unlink (Filename.concat dir name)
        with Core_unix.Unix_error _ -> ());
    try Core_unix.rmdir dir with Core_unix.Unix_error _ -> ()

  (* Collect the directories of runs that no longer exist: a run killed by
     SIGKILL, or by a termination signal while no handler was installed,
     cannot remove its own.  A directory is removed only when the process id
     in its name names no live process (signal 0 finds no such process) and it
     holds nothing but this wrapper's files. *)
  let collect_dead_scratch () =
    let tmp = Stdlib.Filename.get_temp_dir_name () in
    let dead pid =
      match Signal_unix.send Signal.zero (`Pid (Pid.of_int pid)) with
      | `No_such_process -> true
      | `Ok -> false
      | exception Core_unix.Unix_error _ -> false
    in
    match Stdlib.Sys.readdir tmp with
    | exception Sys_error _ -> ()
    | entries ->
        Array.iter entries ~f:(fun entry ->
            match String.chop_prefix entry ~prefix:scratch_prefix with
            | None -> ()
            | Some rest -> (
                match
                  Option.bind (List.hd (String.split rest ~on:'_'))
                    ~f:Int.of_string_opt
                with
                | Some pid when pid > 0 && dead pid ->
                    remove_scratch (Filename.concat tmp entry)
                | _ -> ()))

  (* the scratch directories of calls in flight, each with the process that
     made it, removed by the hooks below.  A forked copy inherits the list and
     the hooks, and must not remove the directory of a call its parent is
     still inside, so a hook removes only its own process's directories. *)
  let live_scratch : (int * string) list Atomic.t = Atomic.make []

  let rec update_live f =
    let old = Atomic.get live_scratch in
    if not (Atomic.compare_and_set live_scratch old (f old)) then update_live f

  let remove_live () =
    let self = Pid.to_int @@ Core_unix.getpid () in
    List.iter (Atomic.get live_scratch) ~f:(fun (pid, dir) ->
        if pid = self then remove_scratch dir)

  (* Register before this module is shared by solver domains: concurrent
     forcing of a lazy first-use initializer can raise Lazy.Undefined. *)
  let () =
    PhaseTime.at_signal remove_live;
    Stdlib.at_exit remove_live

  (* Run [f dir] with a fresh scratch directory [dir] and remove it afterwards,
     whether [f] returns or raises; the exception, an alarm's timeout included,
     is re-raised unchanged.  While [f] runs, the directory is also removed by
     the termination-signal hook ([PhaseTime.at_signal], run when the phase
     account is on) and at exit, so a run stopped by SIGTERM under the account,
     or one that exits while a solver domain is still inside this call, leaves
     nothing.  SIGKILL, and SIGTERM with no handler installed, can leave the
     directory; [collect_dead_scratch] removes it on a later call. *)
  let with_scratch f =
    collect_dead_scratch ();
    let pid = Pid.to_int @@ Core_unix.getpid () in
    let dir =
      Stdlib.Filename.temp_dir (sprintf "%s%d_" scratch_prefix pid) ""
    in
    update_live (List.cons (pid, dir));
    let finish () =
      remove_scratch dir;
      update_live (List.filter ~f:(fun (_, d) -> not (String.equal d dir)))
    in
    match f dir with
    | v ->
        finish ();
        v
    | exception exn ->
        finish ();
        raise exn

  (* the number of queries copied so far by this process *)
  let query_copies = Atomic.make 0

  let solve ?(timeout = None) ?(print_sol = false) pqes =
    match non_real_unknowns pqes with
    | _ :: _ as unknowns ->
        Or_error.error_string
        @@ sprintf
             "PolyQEnt solves polynomial quantified entailments whose \
              unknowns are real-valued template coefficients, but this \
              problem has %d unknown(s) of another sort, such as a predicate: \
              %s.  Use PCSat."
             (List.length unknowns)
             (String.concat ~sep:", " (List.rev_map unknowns ~f:Ident.name_of_tvar))
    | [] ->
    (* the fields of PolyQEnt's own configuration, copied into each call's
       configuration below; an unreadable one is refused before anything runs *)
    match
      match config.config_path with
      | None -> Ok []
      | Some config_path -> (
        match Yojson.Safe.from_file config_path with
        | `Assoc fields -> Ok fields
        | _ -> Or_error.errorf "PolyQEnt configuration %s is not a JSON object" config_path
        | exception (Sys_error msg | Yojson.Json_error msg) ->
            Or_error.errorf "PolyQEnt configuration cannot be read: %s" msg)
    with
    | Error _ as e -> e
    | Ok config_fields ->
    if false then (
      Debug.print @@ lazy (PCSP.Problem.str_of pqes);
      Debug.print @@ lazy "");
    (* output generated PQEs, and the inverse of the renaming they were printed
       under, by which a name in PolyQEnt's model is read back *)
    let s, model_name =
      if true then (
        let pqes =
          PCSP.Problem.elim_ite_quant @@ PCSP.Problem.remove_unused_params pqes
        in
        Debug.print ~id:None
        @@ lazy
             (sprintf "******* if-eliminated PQEs:\n%s"
             @@ PCSP.Problem.str_of pqes);
        let esenv = PCSP.Problem.senv_of pqes in
        let formulas =
          List.map (Set.to_list (PCSP.Problem.formulas_of pqes))
            ~f:(fun (usenv, c) ->
              (usenv, Logic.ExtTerm.to_old_fml esenv usenv c))
        in
        let names =
          Set.Poly.union_list
          @@ Map.key_set esenv
             :: List.concat_map formulas ~f:(fun (usenv, phi) ->
                 [ Map.key_set usenv; LogicOld.Formula.tvs_of phi ])
        in
        let renaming = polyqent_names names in
        let name_of x =
          Ident.name_of_tvar
          @@ Option.value (Map.Poly.find renaming x) ~default:x
        in
        String.concat
          ((Map.data
           @@ Map.Poly.mapi esenv ~f:(fun ~key ~data ->
               assert (ExtTerm.is_real_sort data);
               "(declare-const " ^ name_of key ^ " Real)\n"))
          @ Set.to_list
              (Set.Poly.of_list @@ List.filter_map formulas
                 ~f:(fun (usenv, phi) ->
                   if LogicOld.Formula.is_true @@ Evaluator.simplify phi then
                     None
                   else
                     let phi = LogicOld.Formula.rename renaming phi in
                     Option.return
                     @@ sprintf "(assert %s)\n"
                          (let s =
                             let phis =
                               LogicOld.Formula.disjuncts_list_of phi
                             in
                             let phis1, phis2 =
                               List.partition_map phis ~f:(function
                                 | LogicOld.Formula.UnaryOp (Not, phi, _) ->
                                     First phi
                                 | phi ->
                                     Second phi (*ToDo: [phi] may contain =>*))
                             in
                             SMT.Smtlib2.str_of_formula
                             @@
                             if List.is_empty phis1 then
                               let conc =
                                 LogicOld.Formula.or_of
                                   phis2 (*ToDo: phis2 may contain =>?*)
                               in
                               if
                                 Map.is_empty usenv
                                 || LogicOld.Formula.is_imply conc
                               then conc
                               else
                                 (*ToDo: PolyQEnt requires this dummy condition*)
                                 LogicOld.(
                                   Formula.mk_imply
                                     (Atom.elim_true (Formula.mk_true ()))
                                     conc)
                             else
                               LogicOld.Formula.mk_imply
                                 (LogicOld.Formula.and_of phis1)
                                 (LogicOld.Formula.or_of phis2)
                           in
                           if Map.is_empty usenv then s
                           else
                             sprintf "(forall (%s) %s)"
                               (String.concat_map_list ~sep:" "
                                  (Map.Poly.to_alist usenv) ~f:(fun (x, sort) ->
                                    sprintf "(%s %s)" (name_of x)
                                      (SMT.Smtlib2.str_of_sort
                                         (ExtTerm.to_old_sort sort))))
                               s)))
          @ [ "(check-sat)\n"; "(get-model)\n" ]),
          let original =
            Map.Poly.of_alist_exn
            @@ List.map (Map.Poly.to_alist renaming) ~f:(fun (x, y) ->
                (Ident.name_of_tvar y, x))
          in
          fun v ->
            Option.value (Map.Poly.find original v) ~default:(Ident.Tvar v) )
      else
        ( Printer.Smtlib2.of_pcsp ~id:None (*ToDo*) ~add_missing_forall:false
            pqes,
          fun v -> Ident.Tvar v )
    in
    (* why PolyQEnt gave no answer, for the error message: a non-zero exit
       (its own parse error on a non-polynomial term is the usual case) or no
       output at all *)
    let failure_reason = ref "" in
    let res =
      (* the query file is this call's alone (it is in this call's scratch
         directory) and nothing reads it once PolyQEnt has answered, so it is
         removed on every exit, an exception or a timeout included.  A failing
         run's query is printed under [verbose] instead of being kept. *)
      with_scratch (fun dir ->
          let filename = Filename.concat dir "query.smt2" in
          Out_channel.with_file filename ~f:(fun channel ->
              Format.fprintf (Format.formatter_of_out_channel channel) "%s@." s);
          (* the copy is named by process and call, so calls never share one;
             it is the same text PolyQEnt is given *)
          Option.iter config.query_copy_dir ~f:(fun copy_dir ->
              let copy =
                Filename.concat copy_dir
                  (sprintf "query_p%d_%d.smt2"
                     (Pid.to_int @@ Core_unix.getpid ())
                     (Atomic.fetch_and_add query_copies 1))
              in
              Out_channel.write_all copy ~data:(s ^ "\n");
              prerr_endline ("PolyQEnt query copied to " ^ copy));
          (* PolyQEnt writes the polynomial system it derives to its
             [output_path] and hands that file to its solver, and it fills a
             missing [output_path] with one fixed name in the working
             directory, so two runs at once from one directory read each
             other's system.  Each call therefore passes a copy of the
             configuration whose [output_path] is in the call's scratch
             directory; the copy and the system go with it. *)
          let system_file = Filename.concat dir "system.smt2" in
          let config_file = Filename.concat dir "config.json" in
          (Yojson.Safe.to_file config_file
           @@ `Assoc
                (List.filter config_fields ~f:(fun (k, _) ->
                     not (String.equal k "output_path"))
                @ [ ("output_path", `String system_file) ]));
          (* PolyQEnt d9a87b83d406c21e904467c3a0549ed5e1e89b0d *)
          let cmd =
            (match
               match timeout with Some _ -> timeout | None -> config.timeout_ms
             with
              | None -> ""
              | Some timeout -> sprintf "timeout %f " (float_of_int timeout /. 1000.))
            ^ Filename.quote config.path ^ " " ^ Filename.quote filename
            ^ " " ^ Filename.quote config_file
          in
          let (s0, ss1), status =
            Common.Util.Command.read_process cmd ~f:(fun cin ->
              let s0 =
                ignore (In_channel.input_line cin);
                In_channel.input_line cin
              in
              let ss1 =
                ignore (In_channel.input_line cin);
                let rec loop acc =
                  match In_channel.input_line cin with
                  | None -> acc
                  | Some s -> loop (s :: acc)
                in
                List.rev @@ loop []
              in
              (s0, ss1))
          in
          match (status, s0) with
          | Error err, _ ->
              Debug.print
              @@ lazy (Core_unix.Exit_or_signal.to_string_hum (Error err));
              Debug.print @@ lazy "Error";
              Debug.print @@ lazy (sprintf "the query PolyQEnt failed on:\n%s" s);
              failure_reason :=
                sprintf "PolyQEnt %s (the query is printed under verbose)"
                  (Core_unix.Exit_or_signal.to_string_hum (Error err));
              None
          | Ok _, Some "The system is sat" ->
              let ss =
                let rec loop acc = function
                  | [] -> if String.(acc = "") then [] else [ acc ]
                  | s :: ss ->
                      if String.contains s ':' then
                        if String.(acc = "") then loop s ss else acc :: loop s ss
                      else loop (acc ^ s) ss
                in
                loop "" ss1
              in
              Some (Some ss)
          | Ok _, Some "The system is unsat" -> Some None
          (* PolyQEnt could not decide the system.  Reported as the [unknown]
             verdict, the same as its [unsat] just above (which is also not a
             conclusion about the entailment): turning it into an exception made
             the tool print a backtrace where it had an answer to give. *)
          | Ok _, Some "The system is unknown" -> Some None
          | Ok _, Some s -> failwith s
          | Ok _, None ->
              failure_reason := "PolyQEnt printed no answer";
              None
      )
    in
    let open Or_error in
    (match res with
      | None ->
          Or_error.error_string
          @@ sprintf "PQE solving failed: %s" !failure_reason
      | Some (Some ss) ->
          Debug.print @@ lazy "satisfiable";
          let model =
            List.map ss ~f:(fun s ->
                match String.split s ~on:':' with
                | [ v; r ] -> (
                    let r =
                      try
                        Typeinf.typeinf_term
                          ~print:(fun _ -> ())
                          ~sort_opt:(Some LogicOld.T_real.SReal)
                          ~default:(Some LogicOld.T_real.SReal (*ToDo*))
                        @@ SMT.Smtlib2.of_term ~print:Debug.print ~inline:true
                             SMT.Problem.
                               {
                                 decl_reading = SMT.Problem.Synthesize;
                                 lifted_universals = Map.Poly.empty;
                                 candidates = Map.Poly.empty;
                                 uni_sort = Set.Poly.empty;
                                 uni_senv = Map.Poly.empty;
                                 exi_senv = Map.Poly.empty;
                                 dep_map = Map.Poly.empty;
                                 kind_map = Map.Poly.empty;
                                 fenv = Map.Poly.empty;
                                 dtenv = Map.Poly.empty;
                               }
                        @@ SMT.Parser.sexp SMT.Lexer.token
                        @@ Lexing.from_string r
                      with exn ->
                        Debug.print @@ lazy ("Failed to parse: " ^ r);
                        if true then raise exn else LogicOld.T_real.rzero ()
                    in
                    (*print_endline @@ LogicOld.Term.str_of r;*)
                    ( model_name v,
                      match Evaluator.eval_term r with
                      | Value.Real r -> ExtTerm.mk_real r
                      | _ -> failwith ("unexpected @ 1" ^ s) ))
                | _ -> failwith ("unexpected @ 2: " ^ s))
          in
          Ok (PCSP.Problem.Sat (Map.Poly.of_alist_exn model))
      | Some None ->
          (* We cannot conclude that PQEs is unsatisfiable, even though PolyQEnt reports unsat. *)
          Debug.print @@ lazy "unknown";
          Ok PCSP.Problem.Unknown)
    >>= fun sol ->
    if print_sol then print_endline (PCSP.Problem.str_of_sol_with_witness sol);
    Ok sol
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
