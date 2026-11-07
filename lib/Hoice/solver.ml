(* Backend that hands a CHC problem to the external HoIce solver.  The clauses
   are registered as rules of a Z3 fixedpoint object (in-process, through the
   Z3 library) only so that Z3 prints them as SMT-LIB Horn clauses; that text,
   with each assertion universally closed and headless clauses routed through
   a fresh nullary query predicate, is piped to the [hoice] process, and the
   first verdict line of its output is read back.  Only the verdict is read:
   [sat] carries an empty solution and [unsat] no refutation; HoIce's
   [unknown] and [timeout] are answered as such.  A problem with any predicate
   kind but the ordinary one is refused before translation, and an error
   report, unparsable output, output with no verdict and a failure to run the
   process each become an [Error], never a verdict. *)
open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

module type SolverType = sig
  val solve :
    ?print_sol:bool -> PCSP.Problem.t -> PCSP.Problem.solution Or_error.t
end

module Make (Cfg : Config.ConfigType) : SolverType = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (* A NEW context and a NEW fixedpoint for every call.

     The fixedpoint was once created with the module: each call registered its
     relations and appended its rules to the same object, and the export is
     built by printing that object, so the second problem's file carried the
     first problem's rules as well.  Two problems each satisfiable on their own
     -- one asserting P(0), the other its negation -- came back sat and then
     unsat, the second having been handed both.  This is not an incremental
     API: [solve] takes a whole problem.

     The context is per call too.  A module is made where a solver
     configuration is loaded, which can be one domain, and [solve] can then
     run in another (a task domain of a parallel portfolio); a context shared
     by the module would be given handles in both domains' heaps, and the Z3
     OCaml bindings delete a context when a finalizer reads its handle count
     at zero in a read separate from the decrement, so two domains sweeping
     in parallel can delete it twice.  A context made by the call stays in
     the domain running the call.  It also gives each problem's recursive
     functions a context in which they are declared once, as Z3 5.x
     requires. *)
  let mk_ctx () =
    let options =
      match config.timeout with
      | None -> []
      | Some timeout -> [ ("timeout", string_of_int (timeout * 1000)) ]
    in
    Z3.mk_context options

  (* The answer to the one [(check-sat)] of the script, read from HoIce's
     output (standard error merged in), which is a sequence of
     - warning blocks, a line starting "; |===| Warning:" up to a line
       "; |===|", which are skipped;
     - error reports, a line [(error "] up to a line [")], one per command
       HoIce could not execute;
     - the verdict line: [sat], [unsat], [unknown] or [timeout] (the last when
       its [--timeout] expires), after which nothing is read (a proof, when
       one was asked for, follows it).
     Guarantees: the result is a verdict only if the first line that is
     neither blank nor part of a warning block is one of those four words, so
     no error report precedes it.  An error before the verdict is an [Error]
     even when a verdict follows, because the command HoIce failed on may have
     been a declaration or an assertion, and a [sat] about a script with an
     assertion dropped is not an answer about this problem.  An error report,
     an unrecognised line and output that ends before a verdict are each an
     [Error] carrying the output, never an exception: this function used to
     raise on all three, and on HoIce's own [unknown], so the run ended in an
     uncaught exception instead of an answer. *)
  let get_status_from_hoice_output output =
    let whole () = String.concat ~sep:"\n" output in
    let rec read_error errors = function
      | [] -> Or_error.errorf "unterminated error report from hoice:\n%s" (whole ())
      | "\")" :: _ ->
          Or_error.errorf "hoice reported an error:\n%s"
            (String.concat ~sep:"\n" (List.rev errors))
      | line :: tail -> read_error (line :: errors) tail
    in
    let rec skip_warning = function
      | [] -> Or_error.errorf "unterminated warning from hoice:\n%s" (whole ())
      | "; |===|" :: tail -> read tail
      | _ :: tail -> skip_warning tail
    and read = function
      | [] -> Or_error.errorf "hoice printed no verdict:\n%s" (whole ())
      | line :: tail -> (
          match String.strip line with
          | "" -> read tail
          | "sat" -> Ok (PCSP.Problem.Sat Map.Poly.empty (* ToDo: a solution *))
          | "unsat" -> Ok (PCSP.Problem.Unsat None (* ToDo *))
          | "unknown" -> Ok PCSP.Problem.Unknown
          | "timeout" -> Ok PCSP.Problem.Timeout
          | "(error \"" -> read_error [] tail
          | s when String.is_prefix s ~prefix:"; |===| Warning:" ->
              skip_warning tail
          | s -> Or_error.errorf "unrecognised output from hoice: %s" s)
    in
    read output

  let solve ?(print_sol = false) pcsp =
    (* This backend solves CHC only, and `-p chc`, `-p pfwcsp`, `-p dqchc` … are
       all the *same* problem constructor (the name documents the input, nothing
       checks it), so the compatibility table cannot refuse the pairing: the
       check has to happen here.  It used to be a bare [assert], which told the
       operator nothing but a file and a line. *)
    (* Every kind but [Ord] states an obligation the clauses do not: a
       non-empty predicate may not be false everywhere, a disjunctively
       well-founded one may not contain a self loop, and so on.  This engine
       reads the clauses and nothing else, so it can only honour [Ord].
       Listing the kinds to REFUSE, which is what this used to do, left the
       ones nobody thought of accepted: only well-founded and functional were
       named, so a disjunctively well-founded or non-empty predicate was
       converted to an ordinary Horn relation with its obligation dropped, and
       both fixtures that violate it came back sat.  Naming the one kind that
       IS supported cannot go stale that way. *)
    PCSP.Problem.refuse_non_ord_kinds ~backend:"Hoice" pcsp;
    let ctx = mk_ctx () in
    let solver = Z3.Fixedpoint.mk_fixedpoint ctx in
    let pcsp = PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf pcsp in
    let dtenv =
      Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx @@ PCSP.Problem.dtenv_of pcsp
    in
    let query_name, exi_senv =
      (* A helper the export needs, which must not be a name the input already
         uses.  Two fixed spellings were tried in turn, the second inside the
         handler of the first, so an input declaring both -- and both are legal
         SMT-LIB identifiers -- raised "[Map.add_exn] got key already present"
         and was refused, although its two predicates are independent and every
         other engine answers sat.  Two candidates are not freshness: the name is
         now lengthened until it is one the problem does not hold, which
         terminates because each step is longer than every name it has seen. *)
      let senv = PCSP.Problem.senv_of pcsp in
      let rec fresh name =
        if Map.Poly.mem senv (Ident.Tvar name) then fresh (name ^ "_") else name
      in
      let query_name = fresh "__query__" in
      ( query_name,
        Map.Poly.add_exn senv ~key:(Ident.Tvar query_name)
          ~data:Logic.BoolTerm.SBool )
    in
    let fenv = PCSP.Problem.fenv_of pcsp in
    let penv =
      List.map (Map.Poly.to_alist exi_senv) ~f:(fun (Ident.Tvar name, sort) ->
          let arg_sorts =
            List.map (Logic.Sort.args_of sort)
              ~f:
                (Logic.ExtTerm.to_old_sort
                >> Z3Smt.Z3interface.of_sort ctx dtenv)
          in
          let symbol = Z3.Symbol.mk_string ctx name in
          ( Ident.Pvar name,
            Z3.FuncDecl.mk_func_decl ctx symbol arg_sorts
              (Z3.Boolean.mk_sort ctx) ))
    in
    let exists_query = ref false in
    List.iter ~f:(snd >> Z3.Fixedpoint.register_relation solver) penv;
    (* one converter for every clause: the recursive functions of [fenv] are
       declared in [ctx] once, which Z3 5.x requires *)
    let of_formula =
      Z3Smt.Z3interface.formula_converter ~id:None (*ToDo*) ctx penv fenv dtenv
    in
    Set.iter (PCSP.Problem.clauses_of pcsp) ~f:(fun (uni_senv, ps, ns, phi) ->
        let senv, phi =
          (* assume that [phi] is alpha-renamed *)
          Formula.elim_let_equivalid @@ Normalizer.normalize_let
          @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi
        in
        let body =
          Formula.and_of
          @@ Formula.mk_neg phi
             :: (Set.to_list
                @@ Set.Poly.map ns
                     ~f:
                       (Logic.ExtTerm.to_old_atm exi_senv uni_senv
                       >> Formula.mk_atom))
        in
        let head =
          Formula.and_of @@ Set.to_list
          @@ Set.Poly.map ~f:Formula.mk_atom
          @@
          match Set.length ps with
          | 0 ->
              exists_query := true;
              Set.Poly.singleton
                (Atom.mk_pvar_app (Ident.Pvar query_name) [] [])
          | 1 -> Set.Poly.map ps ~f:(Logic.ExtTerm.to_old_atm exi_senv uni_senv)
          | _ -> assert false
        in
        let phi' = Formula.mk_imply body head in
        Debug.print @@ lazy (Formula.str_of phi');
        let senv =
          Map.Poly.to_alist
          @@ Map.force_merge (Logic.to_old_sort_env_map uni_senv) senv
        in
        let c =
          of_formula senv phi'
        in
        Z3.Fixedpoint.add_rule solver c None);
    (* set params *)
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_bool params
      (Z3.Symbol.mk_string ctx "print_fixedpoint_extensions")
      false;
    Z3.Fixedpoint.set_parameters solver params;
    (* make smt string *)
    let prefix = ref "" in
    let inputs =
      let reg_assert = Str.regexp "^(assert \\(.*\\)$" in
      let reg_forall = Str.regexp "^(forall " in
      Z3.Fixedpoint.to_string solver
      |> String.split_on_chars ~on:[ '\n' ]
      |> List.map ~f:(fun line ->
             if Str.string_match reg_assert line 0 then
               let matched_str = Str.matched_group 1 line in
               let line' = !prefix in
               line'
               ^
               if not @@ Str.string_match reg_forall matched_str 0 then (
                 prefix := ")\n";
                 "(assert (forall () " ^ matched_str)
               else (
                 prefix := "";
                 line)
             else line)
    in
    let inputs =
      String.split_lines @@ Common.Smtlib.strip_annotations
      @@ String.concat ~sep:"\n" (inputs @ [ !prefix ])
    in
    let inputs =
      inputs
      @
      if !exists_query then
        [ sprintf "(assert (forall () (not (%s))))" query_name ]
      else []
    in
    let inputs = inputs @ [ "(check-sat)" ] in
    let inputs =
      if config.produce_proofs then
        ("(set-option :produce-proofs true)" :: inputs) @ [ "(get-proof)" ]
      else inputs
    in
    let inputs = inputs @ [ "(exit)" ] in
    Debug.print @@ lazy ("input to Hoice: \n" ^ String.concat ~sep:"\n" inputs);
    let args =
      match config.timeout with
      | None -> []
      | Some timeout -> [ "--timeout"; string_of_int timeout ]
    in
    try
      Util.Command.sync_command (Util.Command.resolve_tool "hoice") args inputs
      |> get_status_from_hoice_output
      |> Or_error.map ~f:(fun res ->
             if print_sol then print_endline (PCSP.Problem.str_of_solution res);
             res)
    with Util.Command.Shell_error error ->
      Debug.print @@ lazy (sprintf "Shell Error in hoice: %s\n" error);
      Or_error.error_string error
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
