(* OCaml 5's native effect interface, read as the effect interface the
   RCaml/EffCaml translation understands.

   The translation ([MBcgen.fold_expr]) recognises effect handling through a
   small interface a program declares for itself: a GADT [type 'a eff] whose
   constructors are the operations, a variant [type ('a, 'b) continuation],
   the record types [effect_handler] ([effc] only) and [handler] ([retc],
   [exnc], [effc]), and the externals [perform], [try_with], [match_with] and
   [continue].  [desugar] rewrites a parse tree written against OCaml 5's own
   interface into one written against that declared interface, before the
   OCaml type checker runs:

   - [type _ Effect.t += C : ... -> t Effect.t | ...] items (one consecutive
     group of them) become one [type 'a eff = C : ... -> t eff | ...]
     declaration followed by the declared interface, at the place of the
     group;
   - [Effect.perform], [Effect.Deep.continue], [Effect.Deep.match_with],
     [Effect.Deep.try_with], the types [Effect.t], [Effect.Deep.continuation],
     [Effect.Deep.handler], [Effect.Deep.effect_handler] and the fields
     [retc], [exnc], [effc] (qualified or not, with or without [Stdlib.]) name
     their declared counterparts, and [open Effect], [open Effect.Deep] are
     dropped, which leaves the unqualified names bound to the same
     counterparts;
   - in a handler record's [effc] function, a final [| _ -> None] case (the
     case that forwards every other operation, which OCaml's open [Effect.t]
     requires for exhaustiveness) is dropped: the closed [eff] type has no
     other operation, and the translation reads an operation a handler does
     not list exactly as it reads it in the declared interface;
   - [match e with p -> r | ... | effect C x, k -> h | ...] becomes
     [match_with f a { retc; exnc = Stdlib.raise; effc }], with [retc] the
     value cases, [effc] one [C x -> Some (fun (k : (_, _) continuation) -> h)]
     case per effect case, and [f a] the scrutinee when it is an identifier
     applied to an identifier or a constant (whose evaluation cannot perform),
     [(fun () -> e) ()] otherwise; a match with no value case and
     [try e with effect C x, k -> h] become [try_with] alike.

   A file that mentions none of [Effect], [Stdlib.Effect] or an [effect]
   pattern is returned physically unchanged, so a program written against the
   declared interface is translated exactly as before.

   What the rewrite cannot represent it refuses with [Failure], naming the
   construct and its location, rather than dropping it: [Effect.Shallow],
   [discontinue] (the handler calculus has no rule for resuming a
   continuation with an exception), exception cases beside effect cases,
   guards on effect cases, an effect case whose operation pattern is not a
   constructor pattern or whose continuation pattern is not a variable or
   [_], [Effect.t] extensions in more than one group or without a result
   type, and a file that mixes the native interface with a declared one.

   Continuations are read as multi-shot, as in the calculus the translation
   implements (Kawamata et al., POPL 2024), whereas OCaml's are one-shot: an
   OCaml run that resumes a continuation a second time raises
   [Continuation_already_resumed] where the translated program resumes again.
   Nothing here detects a second resumption. *)

open Parsetree

let fail loc fmt =
  Format.kasprintf
    (fun msg ->
      failwith
      @@ Format.asprintf "[native effects] %a: %s" Location.print_loc loc msg)
    fmt

(* the path of a long identifier with a leading [Stdlib] removed *)
let path_of lid =
  match Longident.flatten lid with "Stdlib" :: rest -> rest | p -> p

let is_effect_path lid =
  match path_of lid with "Effect" :: _ -> true | _ -> false

let declared_values = [ "perform"; "continue"; "match_with"; "try_with" ]
let declared_types = [ "eff"; "continuation"; "handler"; "effect_handler" ]
let handler_fields = [ "retc"; "exnc"; "effc" ]

(* the declared interface after [type 'a eff], as the encoded benchmarks write it *)
let interface_text =
  {|type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
type ('a,'b) handler = {
  retc: 'a -> 'b;
  exnc: exn -> 'b;
  effc: 'c.'c eff -> (('c,'b) continuation -> 'b) option
}
external perform : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"
|}

let parse_structure s = Parse.implementation (Lexing.from_string s)
let parse_expression s = Parse.expression (Lexing.from_string s)
let lid ?(loc = Location.none) s = Location.mkloc (Longident.Lident s) loc

(* Does the structure use the native interface?  A syntactic scan: any long
   identifier under [Effect], an [open] of it, or an [effect] pattern. *)
let uses_native (str : structure) =
  let found = ref false in
  let check lid = if is_effect_path lid then found := true in
  let open Ast_iterator in
  let it =
    {
      default_iterator with
      expr =
        (fun it e ->
          (match e.pexp_desc with
          | Pexp_ident { txt; _ } | Pexp_construct ({ txt; _ }, _) -> check txt
          | Pexp_field (_, { txt; _ }) -> check txt
          | Pexp_record (fields, _) ->
              List.iter (fun ({ Location.txt; _ }, _) -> check txt) fields
          | _ -> ());
          default_iterator.expr it e);
      typ =
        (fun it t ->
          (match t.ptyp_desc with
          | Ptyp_constr ({ txt; _ }, _) -> check txt
          | _ -> ());
          default_iterator.typ it t);
      pat =
        (fun it p ->
          (match p.ppat_desc with
          | Ppat_effect _ -> found := true
          | Ppat_construct ({ txt; _ }, _) -> check txt
          | _ -> ());
          default_iterator.pat it p);
      module_expr =
        (fun it m ->
          (match m.pmod_desc with
          | Pmod_ident { txt; _ } -> check txt
          | _ -> ());
          default_iterator.module_expr it m);
      type_extension =
        (fun it te ->
          check te.ptyext_path.txt;
          default_iterator.type_extension it te);
    }
  in
  it.structure it str;
  !found

(* Set by [desugar] while it rewrites a file with [open Effect]
   ([effect_opened]) or [open Effect.Deep] ([deep_opened]) at its top level:
   the unqualified names those opens bring into scope are read as the
   qualified ones.  The unqualified type [t] is read as [Effect.t] only when
   the file declares no type [t] of its own. *)
let effect_opened = ref false
let deep_opened = ref false

(* the declared counterpart of a native value name, or a refusal *)
let value_name loc lid =
  let lid =
    match lid with
    | Longident.Lident (("discontinue" | "discontinue_with_backtrace") as x)
      when !deep_opened ->
        Longident.Ldot
          ( Location.mknoloc
              (Longident.Ldot
                 ( Location.mknoloc (Longident.Lident "Effect"),
                   Location.mknoloc "Deep" )),
            Location.mknoloc x )
    | _ -> lid
  in
  match path_of lid with
  | [ "Effect"; "perform" ] -> Some "perform"
  | [ "Effect"; "Deep"; (("continue" | "match_with" | "try_with") as x) ] ->
      Some x
  | [ "Effect"; "Deep"; (("discontinue" | "discontinue_with_backtrace") as x) ]
    ->
      fail loc
        "Effect.Deep.%s is not supported: the handler calculus the translation \
         targets has no rule for resuming a continuation with an exception"
        x
  | "Effect" :: "Shallow" :: _ ->
      fail loc
        "Effect.Shallow is not supported: the translation has deep handlers \
         only"
  | "Effect" :: _ ->
      fail loc "%s is not supported by the translation"
        (String.concat "." (Longident.flatten lid))
  | _ -> None

let type_name loc lid =
  match path_of lid with
  | [ "Effect"; "t" ] -> Some "eff"
  | [ "t" ] when !effect_opened -> Some "eff"
  | [ "Effect"; "Deep"; (("continuation" | "handler" | "effect_handler") as x) ]
    ->
      Some x
  | "Effect" :: "Shallow" :: _ ->
      fail loc
        "Effect.Shallow is not supported: the translation has deep handlers \
         only"
  | "Effect" :: _ ->
      fail loc "the type %s is not supported by the translation"
        (String.concat "." (Longident.flatten lid))
  | _ -> None

let field_name loc lid =
  match path_of lid with
  | [ "Effect"; "Deep"; x ] when List.mem x handler_fields -> Some x
  | "Effect" :: _ ->
      fail loc "the field %s is not supported by the translation"
        (String.concat "." (Longident.flatten lid))
  | _ -> None

let is_effect_open_target lid =
  match path_of lid with
  | [ "Effect" ] | [ "Effect"; "Deep" ] -> true
  | "Effect" :: "Shallow" :: _ -> false
  | _ -> false

(* an expression whose evaluation cannot perform an operation *)
let is_inert e =
  match e.pexp_desc with
  | Pexp_ident _ | Pexp_constant _ | Pexp_construct (_, None) -> true
  | _ -> false

let is_wild_none_case c =
  match (c.pc_lhs.ppat_desc, c.pc_guard, c.pc_rhs.pexp_desc) with
  | Ppat_any, None, Pexp_construct ({ txt = Longident.Lident "None"; _ }, None)
    ->
      true
  | _ -> false

(* the [effc] function for the given effect cases (operation pattern,
   continuation pattern, clause body) *)
let mk_effc cases =
  let effc_cases =
    List.map
      (fun (p_op, p_k, body) ->
        let k_annot =
          Ast_helper.Pat.constraint_ ~loc:p_k.ppat_loc p_k
            (Parse.core_type (Lexing.from_string "(__eff_a, _) continuation"))
        in
        let rhs =
          Ast_helper.Exp.construct ~loc:body.pexp_loc (lid "Some")
            (Some
               (Ast_helper.Exp.function_ ~loc:body.pexp_loc
                  [
                    {
                      pparam_loc = p_k.ppat_loc;
                      pparam_desc = Pparam_val (Nolabel, None, k_annot);
                    };
                  ]
                  None (Pfunction_body body)))
        in
        Ast_helper.Exp.case p_op rhs)
      cases
  in
  let skeleton =
    parse_expression
      "fun (type __eff_a) (__eff_e : __eff_a eff) -> match __eff_e with _ -> \
       None"
  in
  match skeleton.pexp_desc with
  | Pexp_function
      (params, c, Pfunction_body ({ pexp_desc = Pexp_match (s, _); _ } as m)) ->
      {
        skeleton with
        pexp_desc =
          Pexp_function
            ( params,
              c,
              Pfunction_body { m with pexp_desc = Pexp_match (s, effc_cases) }
            );
      }
  | _ -> assert false

(* the parts of an effect case [effect P, k -> body] *)
let effect_case c =
  match c.pc_lhs.ppat_desc with
  | Ppat_effect (p_op, p_k) ->
      let loc = c.pc_lhs.ppat_loc in
      if Option.is_some c.pc_guard then
        fail loc "a guard on an effect case is not supported";
      (match p_op.ppat_desc with
      | Ppat_construct _ -> ()
      | _ ->
          fail loc
            "an effect case must name one operation by a constructor pattern \
             (an effect case for every operation is not supported)");
      (match p_k.ppat_desc with
      | Ppat_var _ | Ppat_any -> ()
      | _ ->
          fail loc
            "the continuation of an effect case must be bound to a variable or \
             _");
      Some (p_op, p_k, c.pc_rhs)
  | _ -> None

let rec has_exception_pattern p =
  match p.ppat_desc with
  | Ppat_exception _ -> true
  | Ppat_or (p1, p2) -> has_exception_pattern p1 || has_exception_pattern p2
  | Ppat_alias (p, _) | Ppat_constraint (p, _) -> has_exception_pattern p
  | _ -> false

(* [retc] for the value cases: [fun x -> r] for a single unguarded case
   binding a variable, [_] or [()]; [fun v -> match v with cases] otherwise *)
let mk_retc loc value_cases =
  let rec simple p =
    match p.ppat_desc with
    | Ppat_var _ | Ppat_any -> true
    | Ppat_construct ({ txt = Longident.Lident "()"; _ }, None) -> true
    | Ppat_constraint (p, _) -> simple p
    | _ -> false
  in
  match value_cases with
  | [ { pc_lhs; pc_guard = None; pc_rhs } ] when simple pc_lhs ->
      Ast_helper.Exp.function_ ~loc
        [
          {
            pparam_loc = pc_lhs.ppat_loc;
            pparam_desc = Pparam_val (Nolabel, None, pc_lhs);
          };
        ]
        None (Pfunction_body pc_rhs)
  | _ ->
      Ast_helper.Exp.function_ ~loc
        [
          {
            pparam_loc = loc;
            pparam_desc =
              Pparam_val
                ( Nolabel,
                  None,
                  Ast_helper.Pat.var ~loc (Location.mkloc "__eff_v" loc) );
          };
        ]
        None
        (Pfunction_body
           (Ast_helper.Exp.match_ ~loc
              (Ast_helper.Exp.ident ~loc (lid ~loc "__eff_v"))
              value_cases))

(* [match_with f a handler] or [try_with f a handler] for a handled
   computation [e] *)
let mk_handling loc attrs e fields =
  let f, a =
    match e.pexp_desc with
    | Pexp_apply (({ pexp_desc = Pexp_ident _; _ } as f), [ (Nolabel, a) ])
      when is_inert a ->
        (f, a)
    | _ ->
        ( Ast_helper.Exp.function_ ~loc:e.pexp_loc
            [
              {
                pparam_loc = e.pexp_loc;
                pparam_desc =
                  Pparam_val
                    ( Nolabel,
                      None,
                      Ast_helper.Pat.construct ~loc:e.pexp_loc (lid "()") None
                    );
              };
            ]
            None (Pfunction_body e),
          Ast_helper.Exp.construct ~loc:e.pexp_loc (lid "()") None )
  in
  let name = if List.length fields = 1 then "try_with" else "match_with" in
  Ast_helper.Exp.apply ~loc ~attrs
    (Ast_helper.Exp.ident ~loc (lid ~loc name))
    [
      (Nolabel, f);
      (Nolabel, a);
      ( Nolabel,
        Ast_helper.Exp.record ~loc
          (List.map (fun (n, e) -> (lid ~loc n, e)) fields)
          None );
    ]

(* the [match] or [try] with effect cases, rewritten; [None] when it has none *)
let rewrite_handling e =
  let split cases =
    List.partition_map
      (fun c ->
        match effect_case c with Some ec -> Either.Right ec | None -> Left c)
      cases
  in
  match e.pexp_desc with
  | Pexp_match (scrut, cases) -> (
      match split cases with
      | _, [] -> None
      | value_cases, eff_cases ->
          List.iter
            (fun c ->
              if has_exception_pattern c.pc_lhs then
                fail c.pc_lhs.ppat_loc
                  "an exception case beside effect cases is not supported")
            value_cases;
          let effc = ("effc", mk_effc eff_cases) in
          let fields =
            if value_cases = [] then [ effc ]
            else
              [
                ("retc", mk_retc e.pexp_loc value_cases);
                ( "exnc",
                  Ast_helper.Exp.ident ~loc:e.pexp_loc
                    (Location.mkloc
                       (Longident.Ldot
                          ( Location.mknoloc (Longident.Lident "Stdlib"),
                            Location.mknoloc "raise" ))
                       e.pexp_loc) );
                effc;
              ]
          in
          Some (mk_handling e.pexp_loc e.pexp_attributes scrut fields))
  | Pexp_try (body, cases) -> (
      match split cases with
      | _, [] -> None
      | [], eff_cases ->
          Some
            (mk_handling e.pexp_loc e.pexp_attributes body
               [ ("effc", mk_effc eff_cases) ])
      | c :: _, _ ->
          fail c.pc_lhs.ppat_loc
            "an exception handler beside effect cases in a try is not supported"
      )
  | _ -> None

(* drop the final forwarding case [| _ -> None] of an [effc] function *)
let drop_forwarding_case e =
  let rec go e =
    match e.pexp_desc with
    | Pexp_function (params, c, Pfunction_body body) ->
        {
          e with
          pexp_desc = Pexp_function (params, c, Pfunction_body (go body));
        }
    | Pexp_newtype (t, body) -> { e with pexp_desc = Pexp_newtype (t, go body) }
    | Pexp_match (s, cases) -> (
        match List.rev cases with
        | last :: (_ :: _ as rest) when is_wild_none_case last ->
            { e with pexp_desc = Pexp_match (s, List.rev rest) }
        | _ -> e)
    | Pexp_function (params, c, Pfunction_cases (cases, l, a)) -> (
        match List.rev cases with
        | last :: (_ :: _ as rest) when is_wild_none_case last ->
            {
              e with
              pexp_desc =
                Pexp_function (params, c, Pfunction_cases (List.rev rest, l, a));
            }
        | _ -> e)
    | _ -> e
  in
  go e

let rename_lid loc rename ({ Location.txt; _ } as l) =
  match rename loc txt with
  | Some x -> { l with Location.txt = Longident.Lident x }
  | None -> l

let mapper =
  let open Ast_mapper in
  {
    default_mapper with
    expr =
      (fun m e ->
        let e = default_mapper.expr m e in
        let loc = e.pexp_loc in
        match e.pexp_desc with
        | Pexp_ident l ->
            { e with pexp_desc = Pexp_ident (rename_lid loc value_name l) }
        | Pexp_field (r, l) ->
            { e with pexp_desc = Pexp_field (r, rename_lid loc field_name l) }
        | Pexp_record (fields, base) ->
            let fields =
              List.map
                (fun (l, v) ->
                  let l = rename_lid loc field_name l in
                  match l.Location.txt with
                  | Longident.Lident "effc" -> (l, drop_forwarding_case v)
                  | _ -> (l, v))
                fields
            in
            { e with pexp_desc = Pexp_record (fields, base) }
        | Pexp_open
            ({ popen_expr = { pmod_desc = Pmod_ident { txt; _ }; _ }; _ }, body)
          when is_effect_open_target txt ->
            {
              body with
              pexp_attributes = e.pexp_attributes @ body.pexp_attributes;
            }
        | Pexp_construct ({ txt; _ }, _) when is_effect_path txt ->
            fail loc "%s is not supported by the translation"
              (String.concat "." (Longident.flatten txt))
        | Pexp_match _ | Pexp_try _ -> (
            match rewrite_handling e with Some e' -> e' | None -> e)
        | _ -> e);
    typ =
      (fun m t ->
        let t = default_mapper.typ m t in
        match t.ptyp_desc with
        | Ptyp_constr (l, args) ->
            {
              t with
              ptyp_desc = Ptyp_constr (rename_lid t.ptyp_loc type_name l, args);
            }
        | _ -> t);
    pat =
      (fun m p ->
        match p.ppat_desc with
        | Ppat_effect _ ->
            fail p.ppat_loc
              "an effect pattern is supported only as a case of a match or try"
        | Ppat_construct ({ txt; _ }, _) when is_effect_path txt ->
            fail p.ppat_loc "%s is not supported by the translation"
              (String.concat "." (Longident.flatten txt))
        | _ -> default_mapper.pat m p);
    case =
      (fun m c ->
        (* the effect pattern of a case is taken apart by [rewrite_handling];
           map its parts here so that the pattern check above sees only
           misplaced effect patterns *)
        match c.pc_lhs.ppat_desc with
        | Ppat_effect (p_op, p_k) ->
            {
              pc_lhs =
                {
                  c.pc_lhs with
                  ppat_desc = Ppat_effect (m.pat m p_op, m.pat m p_k);
                };
              pc_guard = Option.map (m.expr m) c.pc_guard;
              pc_rhs = m.expr m c.pc_rhs;
            }
        | _ -> default_mapper.case m c);
  }

(* the [type 'a eff = ...] declaration for the operations of a group of
   [Effect.t] extensions *)
let eff_declaration exts =
  let ctors =
    List.concat_map
      (fun te ->
        List.map
          (fun ec ->
            let loc = ec.pext_loc in
            match ec.pext_kind with
            | Pext_decl (vars, (Pcstr_tuple _ as args), Some res) ->
                Ast_helper.Type.constructor ~loc ~attrs:ec.pext_attributes ~vars
                  ~args ~res ec.pext_name
            | Pext_decl (_, Pcstr_record _, _) ->
                fail loc "an operation with a record argument is not supported"
            | Pext_decl (_, _, None) ->
                fail loc
                  "an operation must state its result type ([%s : ... -> t \
                   Effect.t])"
                  ec.pext_name.txt
            | Pext_rebind _ ->
                fail loc "rebinding an operation is not supported")
          te.ptyext_constructors)
      exts
  in
  let decl =
    Ast_helper.Type.mk
      ~attrs:[ Ast_helper.Attr.mk (Location.mknoloc "boxed") (PStr []) ]
      ~params:
        [
          (Ast_helper.Typ.var "a", (Asttypes.NoVariance, Asttypes.NoInjectivity));
        ]
      ~kind:(Ptype_variant ctors) (Location.mknoloc "eff")
  in
  Ast_helper.Str.type_ Asttypes.Recursive [ decl ]

let is_effect_extension si =
  match si.pstr_desc with
  | Pstr_typext te -> (
      match path_of te.ptyext_path.txt with
      | [ "Effect"; "t" ] -> true
      | [ "t" ] when !effect_opened -> true
      | "Effect" :: _ -> fail te.ptyext_loc "only Effect.t can be extended"
      | _ -> false)
  | _ -> false

(* a top-level declaration of a name of the declared interface *)
let declares_interface si =
  match si.pstr_desc with
  | Pstr_primitive vd -> List.mem vd.pval_name.txt declared_values
  | Pstr_type (_, decls) ->
      List.exists (fun d -> List.mem d.ptype_name.txt declared_types) decls
  | _ -> false

let desugar ?(print = fun (_ : string Lazy.t) -> ()) (str : structure) =
  if not (uses_native str) then str
  else
    let opens path =
      List.exists
        (fun si ->
          match si.pstr_desc with
          | Pstr_open
              { popen_expr = { pmod_desc = Pmod_ident { txt; _ }; _ }; _ } ->
              path_of txt = path
          | _ -> false)
        str
    in
    let declares_t =
      List.exists
        (fun si ->
          match si.pstr_desc with
          | Pstr_type (_, decls) ->
              List.exists (fun d -> d.ptype_name.txt = "t") decls
          | _ -> false)
        str
    in
    effect_opened := opens [ "Effect" ] && not declares_t;
    deep_opened := opens [ "Effect"; "Deep" ];
    Fun.protect ~finally:(fun () ->
        effect_opened := false;
        deep_opened := false)
    @@ fun () ->
    (match List.find_opt declares_interface str with
    | Some si ->
        fail si.pstr_loc
          "the file uses OCaml's Effect module and also declares the effect \
           interface by hand (eff, continuation, perform, ...); use one of \
           them"
    | None -> ());
    (* one consecutive group of [Effect.t] extensions *)
    let rec split_before acc = function
      | si :: rest when not (is_effect_extension si) ->
          split_before (si :: acc) rest
      | rest -> (List.rev acc, rest)
    in
    let before, rest = split_before [] str in
    let rec take_group acc = function
      | si :: rest when is_effect_extension si -> take_group (si :: acc) rest
      | rest -> (List.rev acc, rest)
    in
    let group, after = take_group [] rest in
    if group = [] then
      fail
        (match str with si :: _ -> si.pstr_loc | [] -> Location.none)
        "the file uses OCaml's Effect module but declares no operation (type _ \
         Effect.t += ...)";
    (match List.find_opt is_effect_extension after with
    | Some si ->
        fail si.pstr_loc
          "all Effect.t extensions must form one consecutive group of items"
    | None -> ());
    let exts =
      List.map
        (fun si ->
          match si.pstr_desc with Pstr_typext te -> te | _ -> assert false)
        group
    in
    let drop_opens =
      List.filter (fun si ->
          match si.pstr_desc with
          | Pstr_open
              { popen_expr = { pmod_desc = Pmod_ident { txt; _ }; _ }; _ } ->
              not (is_effect_open_target txt)
          | _ -> true)
    in
    let str' =
      drop_opens before
      @ (eff_declaration exts :: parse_structure interface_text)
      @ drop_opens after
    in
    let str' = mapper.Ast_mapper.structure mapper str' in
    print
    @@ lazy
         ("[native effects] the program as translated:\n"
         ^ Pprintast.string_of_structure str');
    str'
