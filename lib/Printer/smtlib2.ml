open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* Decide on the original environment, before assertion-only preprocessing can
   discard a definition. Unsupported nonempty environments cannot safely use
   Fixedpoint serialization, which omits their defining equations. *)
let has_supported_defining_context fenv =
  if Map.Poly.is_empty fenv then false
  else if Z3Smt.Z3interface.supports_defining_equations fenv then true
  else
    raise
      (PCSP.Problem.NoTemplate
         "the SMT-LIB2 printer cannot preserve this known defining context: \
          supported definitions have Bool/Int signatures, true properties and \
          known calls preserving integer argument positions")

let of_pcsp ~id ?(add_missing_forall = false) (*~print*) pcsp =
  let defining_context =
    has_supported_defining_context (PCSP.Problem.fenv_of pcsp)
  in
  let rec go disambiguate_among =
    let ctx = Z3.mk_context [] in
    let solver = Z3.Fixedpoint.mk_fixedpoint ctx in
    (* print @@ lazy (sprintf "===================== pcsp ====================: \n%s" (PCSP.Problem.str_of pcsp)); *)
    let pcsp = PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf pcsp in
    let dtenv =
      Z3Smt.Z3interface.z3_dtenv_of_dtenv ~disambiguate_among ctx
      @@ PCSP.Problem.dtenv_of pcsp
    in
    let fenv = PCSP.Problem.fenv_of pcsp in
    let exi_senv = PCSP.Problem.senv_of pcsp in
    (* A predicate KIND is a condition on the solution itself -- a functional
       predicate must be total and single-valued, a well-founded one
       well-founded -- and a constraint format has nowhere to put one.  Written
       as an ordinary [declare-fun ... Bool], the unknown loses that condition,
       and the file is a RELAXATION of the problem it names: every [FN] can be
       [false], which falsifies the premise of every clause mentioning it, so a
       solver reading the file answers [sat] on problems that are [unsat].  So
       every kind is written in the reader's extended syntax, one declaration
       command per kind (the reader's [simple_kind_of_command] and its
       [declare-nwfp] and [declare-parityp] cases are the other half of this
       contract), and the file reads back as the problem it came from.  An
       external solver meets a command it does not know and says so, where the
       plain declaration let it answer a weaker question silently. *)
    let symbol n =
      let plain =
        (not (String.is_empty n))
        && (not (Char.is_digit n.[0]))
        && String.for_all n ~f:(fun c ->
            Char.is_alphanum c || String.mem "~!@$%^&*_-+=<>.?/" c)
      in
      if plain then n else "|" ^ n ^ "|"
    in
    let sort_str s =
      Z3.Sort.to_string
      @@ Z3Smt.Z3interface.of_sort ctx dtenv
      @@ Logic.ExtTerm.to_old_sort s
    in
    (* an NWF family is its shared and per-tag sorts only; the priority fields
       of the record it shares with a parity family are placeholders there.  A
       parity family is the other way round: per-tag sorts and priorities, and
       no shared sorts *)
    let family_str ~parity (nwf : Kind.nwf) =
      let sorts ss = String.concat_map_list ~sep:" " ss ~f:sort_str in
      let trunc =
        let pris = List.init (nwf.max_pri + 3) ~f:Fn.id in
        if List.for_all pris ~f:(fun i -> nwf.trunc i = i) then "identity"
        else if
          List.for_all pris ~f:(fun i ->
              nwf.trunc i = SMT.Smtlib2.halve_truncation i)
        then "halve"
        else
          raise
            (PCSP.Problem.NoTemplate
               (sprintf
                  "the family %s has a truncation that is neither the \
                   identity nor halving, and only those two can be written"
                  (Ident.name_of_tvar nwf.name)))
      in
      let field key body =
        if String.is_empty body then sprintf "(%s)" key
        else sprintf "(%s %s)" key body
      in
      let tags =
        field "tags"
        @@ String.concat_map_list ~sep:" "
           (List.sort ~compare:Stdlib.compare
           @@ Hashtbl.Poly.to_alist nwf.sorts_map)
           ~f:(fun (t, ss) ->
             sprintf "(%s (%s))" (symbol @@ Ident.name_of_tvar t) (sorts ss))
      in
      if not parity then
        sprintf "(%s %s %s)"
          (symbol @@ Ident.name_of_tvar nwf.name)
          (field "shared" @@ sorts nwf.sorts_shared)
          tags
      else if not (List.is_empty nwf.sorts_shared) then
        (* a parity relation relates the disjoint union of its members'
           domains and nothing is shared; every consumer asserts it *)
        raise
          (PCSP.Problem.NoTemplate
             (sprintf "the parity family %s has shared sorts"
                (Ident.name_of_tvar nwf.name)))
      else
      sprintf "(%s %s %s %s %s %s)"
        (symbol @@ Ident.name_of_tvar nwf.name)
        tags
        (field "max-priority" @@ string_of_int nwf.max_pri)
        (field "priority"
        @@ String.concat_map_list ~sep:" " (Map.Poly.to_alist nwf.sigma)
             ~f:(fun (p, i) ->
               sprintf "(%s %d)" (symbol @@ Ident.name_of_tvar p) i))
        (field "accepting"
        @@ String.concat_map_list ~sep:" " (Set.to_list nwf.acc_set)
             ~f:string_of_int)
        (field "truncation" trunc)
    in
    let member cmd nwf (l, r) =
      sprintf "%s %s %s %s" cmd
        (family_str ~parity:(String.equal cmd "declare-parityp") nwf)
        (symbol @@ Ident.name_of_tvar l)
        (symbol @@ Ident.name_of_tvar r)
    in
    let kinded_decls =
      Map.Poly.filter_mapi (PCSP.Problem.kind_map_of pcsp) ~f:(fun ~key ~data ->
          if not (Map.Poly.mem exi_senv key) then None
          else
            match data with
            | Kind.FN -> Some "declare-fnp"
            | Kind.Uniq (j, prov) ->
                Some (sprintf "declare-uniqp %d %s" j (Kind.str_of_provenance prov))
            | Kind.WF -> Some "declare-wfp"
            (* the canonical form for every position set, the empty one
               included; [declare-nep] is read as its alias and never written *)
            | Kind.Tot u ->
                Some
                  (sprintf "declare-totp (%s)"
                     (String.concat_map_list ~sep:" " u ~f:string_of_int))
            | Kind.DWF -> Some "declare-dwfp"
            | Kind.Integ -> Some "declare-integp"
            | Kind.Adm false -> Some "declare-admp"
            | Kind.Adm true -> Some "declare-admcp"
            | Kind.NWF (nwf, tags) -> Some (member "declare-nwfp" nwf tags)
            | Kind.Parity (nwf, tags) -> Some (member "declare-parityp" nwf tags)
            (* an ordinary predicate needs no command of its own, and a non-Bool
               unknown is refused below with its own reason *)
            | Kind.Ord | Kind.IntFun | Kind.RealFun | Kind.RegEx -> None)
    in
    (* Fixedpoint serialization requires a predicate at a rule's head, even for
       a goal.  Its temporary relation must avoid every user symbol, including
       binders and datatype/function names, not just the unknown declarations.
       The diagnostic form contains those environments and formulas; substring
       exclusion is conservative and terminates on this finite text. *)
    let occupied = PCSP.Problem.str_of pcsp in
    let rec fresh_query name =
      if String.is_substring occupied ~substring:name then fresh_query (name ^ "_")
      else name
    in
    let query_name = fresh_query "__query__" in
    let exi_senv =
      Map.Poly.add_exn exi_senv ~key:(Ident.Tvar query_name)
        ~data:Logic.BoolTerm.SBool
    in
    let penv =
      List.map (Map.Poly.to_alist exi_senv) ~f:(fun (Ident.Tvar name, sort) ->
          let arg_sorts, ret_sort = Logic.Sort.args_ret_of sort in
          if Logic.ExtTerm.is_bool_sort ret_sort then
            let arg_sorts =
              List.map arg_sorts
                ~f:
                  (Logic.ExtTerm.to_old_sort
                  >> Z3Smt.Z3interface.of_sort ctx dtenv)
            in
            let symbol = Z3.Symbol.mk_string ctx name in
            ( Ident.Pvar name,
              Z3.FuncDecl.mk_func_decl ctx symbol arg_sorts
                (Z3.Boolean.mk_sort ctx) )
            (* else if Logic.ExtTerm.is_real_sort ret_sort then (
             assert (List.is_empty arg_sorts);
             let symbol = Z3.Symbol.mk_string ctx name in
             ( Ident.Pvar name,
               Z3.FuncDecl.mk_const_decl ctx symbol
                 (Z3.Arithmetic.Real.mk_sort ctx) )) *)
          else
            (* An unknown whose result sort is not Bool -- what a Horn logic makes of
               `(declare-fun u () Int)`, a FUNCTION to synthesise rather than a relation.
               It cannot be written in this format at all: the output is built through Z3's
               fixedpoint API, which registers RELATIONS, and SMT-LIB2's Horn dialect has no
               syntax for "synthesise this integer" either.  Encoding it as an array-sorted
               universal would change the problem rather than print it, turning an existential
               into a universal.  So this is an unsupported INPUT and is refused as one, by name:
               an assertion here reaches the user as a bare failure naming a file and a line, with
               nothing on the verdict stream, which is a correct refusal wearing the appearance of
               an internal error -- and every harness in this tree reads a non-zero exit with no
               verdict as the tool crashing. *)
            raise
              (PCSP.Problem.NoTemplate
                 (sprintf
                    "the SMT-LIB2 printer writes predicate variables as Z3 \
                     fixedpoint relations, which must return Bool, but the \
                     unknown `%s' returns %s.  An unknown of non-Bool result \
                     sort is a function to synthesise and this format cannot \
                     state one."
                    name
                    (Term.str_of_sort @@ Logic.ExtTerm.to_old_sort ret_sort))))
    in
    List.iter ~f:(snd >> Z3.Fixedpoint.register_relation solver) penv;
    (* one converter for every clause: the recursive functions of [fenv] are
       declared in [ctx] once, which Z3 5.x requires *)
    let export_solver = Z3.Solver.mk_solver ctx None in
    let equations, definitions, of_formula =
      if not defining_context then
        (0, "", Z3Smt.Z3interface.formula_converter ~id ctx penv fenv dtenv)
      else
        (* Fixedpoint serialization omits known definitions, including unused
           contradictory ones. For this supported family, ordinary declarations
           let a Solver serializer collect every dependency without installing
           native recursive definitions. Equations are added first only to make
           the serializer retain those dependencies; replace their assertions
           and declarations with one complete define-funs-rec command below. *)
        let z3fenv =
          Map.Poly.mapi fenv ~f:(fun ~key ~data:(params, sret, _, _, _) ->
              Z3.FuncDecl.mk_func_decl_s ctx (Ident.name_of_tvar key)
                (List.map params
                   ~f:(snd >> Z3Smt.Z3interface.of_sort ctx dtenv))
                (Z3Smt.Z3interface.of_sort ctx dtenv sret))
        in
        let convert env phi =
          Z3Smt.Z3interface.of_formula_with_z3fenv ~id ctx env penv z3fenv dtenv
            phi
        in
        let equations = Z3Smt.Z3interface.defining_equations_of fenv in
        Z3.Solver.add export_solver (List.map equations ~f:(convert []));
        let name var sort =
          Z3.Expr.to_string
          @@ Z3Smt.Z3interface.of_term ~id ctx [] [] z3fenv dtenv
          @@ Term.mk_var var sort
        in
        let signatures, bodies =
          List.unzip
          @@ List.map (Map.Poly.to_alist fenv)
               ~f:(fun (var, (params, sret, body, _, _)) ->
                 let params =
                   String.concat_map_list ~sep:" " params ~f:(fun (v, s) ->
                       sprintf "(%s %s)" (name v s)
                         (Z3.Sort.to_string
                         @@ Z3Smt.Z3interface.of_sort ctx dtenv s))
                 in
                 let body =
                   if Term.is_let_free body then body else Term.elim_let body
                 in
                 ( sprintf "(%s (%s) %s)"
                     (Z3.Expr.to_string
                     @@ Z3.Expr.mk_const_s ctx (Ident.name_of_tvar var)
                          (Z3Smt.Z3interface.of_sort ctx dtenv sret))
                     params
                     (Z3.Sort.to_string
                     @@ Z3Smt.Z3interface.of_sort ctx dtenv sret),
                   Z3.Expr.to_string
                   @@ Z3Smt.Z3interface.of_term ~id ctx [] penv z3fenv dtenv
                        body ))
        in
        ( List.length equations,
          sprintf "(define-funs-rec (%s) (%s))"
            (String.concat ~sep:" " signatures)
            (String.concat ~sep:" " bodies),
          convert )
    in
    Set.iter (PCSP.Problem.clauses_of pcsp) ~f:(fun (uni_senv, ps, ns, phi) ->
        let senv, phi =
          (* assume that [phi] is alpha-renamed *)
          Formula.elim_let_equivalid
          @@ Normalizer.normalize_let ~rename:true
          @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi
        in
        let body =
          Evaluator.simplify @@ Formula.and_of
          @@ Formula.mk_neg phi
             :: (Set.to_list
                @@ Set.Poly.map ~f:Formula.mk_atom
                @@ Set.Poly.map ns
                     ~f:(Logic.ExtTerm.to_old_atm exi_senv uni_senv))
        in

        let head =
          match Set.length ps with
          | 0 ->
              Formula.mk_atom
              @@ Atom.mk_pvar_app (Ident.Pvar query_name) [] []
          | 1 ->
              Formula.or_of @@ Set.to_list
              @@ Set.Poly.map ~f:Formula.mk_atom
              @@ Set.Poly.map ps ~f:(Logic.ExtTerm.to_old_atm exi_senv uni_senv)
          (* Not a solver limitation, though it long read as one: a
             constrained Horn clause has at most one head atom BY DEFINITION of
             the format, so a problem with a disjunctive head has no SMT-LIB2
             Horn form to be written in at all.  Refusing is correct and no
             solver upgrade will change it -- so it is refused as an
             UNSUPPORTED INPUT, by the same route as the non-Bool unknown
             above.  A [failwith] here is indistinguishable from an internal
             error: it escapes as a backtrace with nothing on the verdict
             stream, and a harness reads a non-zero exit with no verdict as
             the tool crashing, which is a correct refusal convicted of the
             one outcome such a check exists to catch. *)
          | _ ->
              raise
                (PCSP.Problem.NoTemplate
                   "a disjunctive head cannot be written as a constrained Horn \
                    clause: the format allows at most one head atom")
        in
        let phi' = Formula.mk_imply body head in
        let senv =
          Map.Poly.to_alist
          @@ Map.force_merge (Logic.to_old_sort_env_map uni_senv) senv
        in
        let c =
          if defining_context then
            of_formula [] (Formula.mk_forall_if_bounded senv phi')
          else of_formula senv phi'
        in
        if defining_context then Z3.Solver.add export_solver [ c ]
        else Z3.Fixedpoint.add_rule solver c None);
    (* set params *)
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_bool params
      (Z3.Symbol.mk_string ctx "print_fixedpoint_extensions")
      false;
    Z3.Fixedpoint.set_parameters solver params;
    (* make smt string *)
    let prefix = ref "" in
    let lines =
      (if not defining_context then Z3.Fixedpoint.to_string solver
       else
         let text = Z3.Solver.to_string export_solver in
         let slice a b = String.sub text ~pos:a ~len:(b - a) in
         let remaining = ref equations in
         let declarations, assertions =
           List.partition_map (Common.Smtlib.parse text) ~f:(function
             | Common.Smtlib.List (a, b, Common.Smtlib.Atom (c, d) :: rest) ->
                 if String.equal (slice c d) "assert" then
                   if !remaining > 0 then (
                     decr remaining;
                     Second "")
                   else Second (slice a b)
                 else
                   let known =
                     match (slice c d, rest) with
                     | "declare-fun", Common.Smtlib.Atom (e, f) :: _ ->
                         let token = slice e f in
                         Map.Poly.existsi fenv
                           ~f:(fun ~key ~data:(_, s, _, _, _) ->
                             String.equal token
                               (Z3.Expr.to_string
                               @@ Z3.Expr.mk_const_s ctx
                                    (Ident.name_of_tvar key)
                                    (Z3Smt.Z3interface.of_sort ctx dtenv s)))
                     | _ -> false
                   in
                   First (if known then "" else slice a b)
             | _ -> failwith "unexpected SMT-LIB solver serialization")
         in
         assert (!remaining = 0);
         String.concat ~sep:"\n"
           ([ "(set-logic HORN)" ] @ declarations @ [ definitions ] @ assertions))
      |> String.split_on_chars ~on:[ '\n' ]
    in
    let inputs =
      let reg_assert = Str.regexp "^(assert \\(.*\\)$" in
      let reg_forall = Str.regexp "^(forall " in
      List.map lines ~f:(fun line ->
          if Str.string_match reg_assert line 0 then
            let matched_str = Str.matched_group 1 line in
            let line' = !prefix in
            line'
            ^
            if
              add_missing_forall
              && (not @@ Str.string_match reg_forall matched_str 0)
            then (
              prefix := ")\n";
              "(assert (forall () " ^ matched_str)
            else (
              prefix := "";
              line)
          else line)
    in
    (* let inputs =
       let reg_decl_const_name = Str.regexp "(declare-fun \\(.*\\) () Real)" in
       (* for PQEs *)
       List.map inputs ~f:(fun line ->
           if Str.string_match reg_decl_const_name line 0 then
             sprintf "(declare-const %s Real)" @@ Str.matched_group 1 line
           else line)
     in *)
    let inputs =
      String.split_lines @@ Common.Smtlib.eliminate_query ~name:query_name
      @@ String.concat ~sep:"\n" (inputs @ [ !prefix ])
    in
    let inputs = inputs @ [ "(check-sat)" ] in
    (* let inputs = if config.produce_proofs then
      "(set-option :produce-proofs true)" :: inputs @ ["(get-proof)"]
     else inputs in *)
    let inputs = inputs @ [ "(exit)" ] in
    let inputs =
      if Map.is_empty kinded_decls then inputs
      else
        List.map inputs ~f:(fun line ->
            match String.chop_prefix line ~prefix:"(declare-fun " with
            | None -> line
            | Some rest -> (
                let name =
                  if String.is_prefix rest ~prefix:"|" then
                    Option.map
                      (String.index (String.drop_prefix rest 1) '|')
                      ~f:(fun i -> String.sub rest ~pos:1 ~len:i)
                  else Option.map (String.lsplit2 rest ~on:' ') ~f:fst
                in
                match
                  Option.bind name ~f:(fun n ->
                      Map.Poly.find kinded_decls (Ident.Tvar n))
                with
                | None -> line
                | Some command -> sprintf "(%s %s" command rest))
    in
    let text = String.concat ~sep:"\n" inputs in
    (* Two datatypes can carry constructors of the same name -- one parametric
     datatype instantiated twice gives [int Lst] and [bool Lst], each with
     [nil] -- and a printed file has only the name: [nil] there stands for two
     constructors of two sorts and no reader can tell them apart.  Z3 says
     "ambiguous constant reference ... use a qualified expression
     (as nil <sort>)" and then answers about the assertions it could read.
     Only the file matters, so the check is made on the file: the datatypes it
     actually declares are collected from it, and if two of those spell a
     constructor or accessor the same the problem is printed again with those
     names made distinct.  A file that declares one datatype, or two that do
     not collide, is printed exactly as before. *)
    if not (List.is_empty disambiguate_among) then text
    else
      let declared =
        String.split_lines text
        |> List.filter_map ~f:(fun line ->
            match String.chop_prefix line ~prefix:"(declare-datatypes ((" with
            | None -> None
            | Some rest -> (
                if
                  (* a sort name is quoted when it contains a space, which an
                    instantiated datatype's name does: |int Lst| *)
                  String.is_prefix rest ~prefix:"|"
                then
                  match String.index (String.drop_prefix rest 1) '|' with
                  | None -> None
                  | Some i -> Some (String.sub rest ~pos:1 ~len:i)
                else
                  match String.lsplit2 rest ~on:' ' with
                  | None -> None
                  | Some (name, _) -> Some name))
      in
      let collides =
        let dtenv = PCSP.Problem.dtenv_of pcsp in
        let names = Stdlib.Hashtbl.create 32 in
        let dup = ref false in
        List.iter (Map.Poly.data dtenv) ~f:(fun data ->
            List.iter (Datatype.full_dts_of data) ~f:(fun dt ->
                if
                  List.mem declared
                    (Datatype.full_name_of_dt dt)
                    ~equal:String.equal
                then
                  List.iter (Datatype.conses_of_dt dt) ~f:(fun cons ->
                      let note n =
                        match Stdlib.Hashtbl.find_opt names n with
                        | Some owner
                          when not
                                 (String.equal owner
                                    (Datatype.full_name_of_dt dt)) ->
                            dup := true
                        | Some _ -> ()
                        | None ->
                            Stdlib.Hashtbl.replace names n
                              (Datatype.full_name_of_dt dt)
                      in
                      note (Datatype.name_of_cons cons);
                      List.iter (Datatype.sels_of_cons cons) ~f:(function
                          | Datatype.Sel (n, _) | Datatype.InSel (n, _, _) ->
                          note n))));
        !dup
      in
      if collides then go declared else text
  in
  go []
