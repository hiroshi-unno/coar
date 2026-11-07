open Ppxlib

(* Expected branches are identified before deriving, then consumed exactly once
   inside the corresponding generated serializer binding. *)
type expected = {
  loc : Location.t;
  field : string;
  key : string;
  serializer : string;
  mutable consumed : bool;
}

let expected = ref []
let final_component = function
  | Longident.Lident name | Longident.Ldot (_, name) -> name
  | Longident.Lapply _ -> ""

let attribute name attrs =
  List.find_opt
    (fun a ->
      let actual = a.attr_name.txt in
      actual = name || actual = "yojson." ^ name || actual = "deriving.yojson." ^ name)
    attrs

let string_payload attr =
  match attr.attr_payload with
  | PStr [{ pstr_desc = Pstr_eval ({ pexp_desc = Pexp_constant (Pconst_string (s, _, _)); _ }, _); _ }] -> s
  | _ -> Location.raise_errorf ~loc:attr.attr_loc "full JSON: unsupported key attribute"

let derives_serializer attrs =
  List.exists
    (fun attr ->
      if attr.attr_name.txt <> "deriving" then false
      else
        let found = ref false in
        let visitor = object
          inherit Ast_traverse.iter as super
          method! expression e =
            (match e.pexp_desc with
             | Pexp_ident { txt; _ } when List.mem (final_component txt) ["yojson"; "to_yojson"] -> found := true
             | _ -> ());
            super#expression e
        end in
        visitor#payload attr.attr_payload;
        !found)
    attrs

(* These bodies have been reviewed as total scalar encoders with no hidden
   default omission. Adding an entry requires reviewing the encoder body. *)
let audited_custom_serializer bindings attr =
  let filename = attr.attr_loc.loc_start.pos_fname in
  let ends path = filename = path || Filename.check_suffix filename ("/" ^ path) in
  let encoder = match attr.attr_payload with
    | PStr [{ pstr_desc = Pstr_eval ({ pexp_desc = Pexp_ident { txt = Longident.Lident name; _ }; _ }, _); _ }] -> Some name
    | _ -> None
  in
  let reviewed =
    if ends "lib/PCSat/classification/DT_WFClassifier.ml" && encoder = Some "qualifier_type_to_json" then
      Some ("qualifier_type_to_json", "function | `Interval -> `String \"interval\" | `Octagon -> `String \"octagon\"")
    else if ends "test/config_full_json.ml" && encoder = Some "custom_to_yojson" then
      Some ("custom_to_yojson", "fun x -> `String (if x then \"yes\" else \"no\")")
    else None
  in
  match reviewed with
  | None -> false
  | Some (name, body) ->
      match List.filter (fun (binding, _) -> binding = name) bindings with
      | [(_, actual)] ->
          let canonical expression = Format.asprintf "%a" Pprintast.expression expression in
          canonical actual = canonical (Parse.expression (Lexing.from_string body))
      | _ -> false

let require_strict_reader attrs =
  let visitor = object
    inherit Ast_traverse.iter as super
    method! expression expression =
      (match expression.pexp_desc with
       | Pexp_apply ({ pexp_desc = Pexp_ident { txt; _ }; _ }, arguments)
         when List.mem (final_component txt) ["yojson"; "of_yojson"] ->
           List.iter (fun (_, argument) ->
               match argument.pexp_desc with
               | Pexp_record (fields, _) ->
                   List.iter (fun (name, value) ->
                       if final_component name.txt = "strict" then
                         match value.pexp_desc with
                         | Pexp_construct ({ txt = Longident.Lident "true"; _ }, None) -> ()
                         | _ -> Location.raise_errorf ~loc:value.pexp_loc
                             "full JSON: derived types require a literal strict=true reader") fields
               | _ -> ()) arguments
       | _ -> ());
      super#expression expression
  end in
  List.iter (fun attr -> if attr.attr_name.txt = "deriving" then visitor#payload attr.attr_payload) attrs

let before tree =
  expected := [];
  let bindings = ref [] in
  let binding_visitor = object
    inherit Ast_traverse.iter as super
    method! value_binding vb =
      (match vb.pvb_pat.ppat_desc with
       | Ppat_var name -> bindings := (name.txt, vb.pvb_expr) :: !bindings
       | _ -> ());
      super#value_binding vb
  end in
  binding_visitor#structure tree;
  let visitor = object
    inherit Ast_traverse.iter as super
    method! attribute attr =
      let name = attr.attr_name.txt in
      if List.mem name ["to_yojson"; "yojson.to_yojson"; "deriving.yojson.to_yojson"]
         && not (audited_custom_serializer !bindings attr) then
        Location.raise_errorf ~loc:attr.attr_loc
          "full JSON: custom serializer is outside the audited scalar-encoder allowlist";
      super#attribute attr
    method! structure_item item =
      let declarations = match item.pstr_desc with
        | Pstr_type (_, declarations) when List.exists (fun td -> derives_serializer td.ptype_attributes) declarations -> declarations
        | _ -> []
      in
      List.iter (fun td -> require_strict_reader td.ptype_attributes) declarations;
      List.iter (fun td ->
        let serializer = if td.ptype_name.txt = "t" then "to_yojson" else td.ptype_name.txt ^ "_to_yojson" in
        let labels = match td.ptype_kind with
          | Ptype_record labels -> labels
          | Ptype_variant constructors ->
              List.concat_map (fun c -> match c.pcd_args with Pcstr_record labels -> labels | Pcstr_tuple _ -> []) constructors
          | Ptype_abstract | Ptype_open -> []
        in
        List.iter (fun label ->
            match attribute "default" label.pld_attributes with
            | None -> ()
            | Some _ ->
                let key = match attribute "key" label.pld_attributes with
                  | None -> label.pld_name.txt
                  | Some a -> string_payload a
                in
                expected := { loc = label.pld_loc; field = label.pld_name.txt;
                              key; serializer; consumed = false } :: !expected)
          labels) declarations;
      super#structure_item item
  end in
  visitor#structure tree;
  tree

let same_location a b =
  a.Location.loc_start = b.Location.loc_start && a.Location.loc_end = b.Location.loc_end

let ident name e = match e.pexp_desc with
  | Pexp_ident { txt; _ } -> final_component txt = name
  | _ -> false

let branch_field condition yes no =
  match condition.pexp_desc, yes.pexp_desc, no.pexp_desc with
  | Pexp_apply (op, [(Nolabel, { pexp_desc = Pexp_field (_, field); _ }); (Nolabel, _)]),
    Pexp_ident { txt = Longident.Lident "fields"; _ },
    Pexp_construct ({ txt = Longident.Lident "::"; _ }, Some
      { pexp_desc = Pexp_tuple [
          { pexp_desc = Pexp_tuple [{ pexp_desc = Pexp_constant (Pconst_string (key, _, _)); _ }; _]; _ };
          tail ]; _ })
    when ident "=" op && ident "fields" tail -> Some (final_component field.txt, key)
  | _ -> None

let rec pattern_name pattern = match pattern.ppat_desc with
  | Ppat_var name -> Some name.txt
  | Ppat_constraint (pattern, _) -> pattern_name pattern
  | _ -> None

let after tree =
  let mapper = object
    inherit Ast_traverse.map as super
    val mutable binding = ""
    method! value_binding vb =
      let old = binding in
      binding <- (match pattern_name vb.pvb_pat with
        | Some name when name = "to_yojson" || Filename.check_suffix name "_to_yojson" -> name
        | _ -> old);
      Fun.protect (fun () -> super#value_binding vb) ~finally:(fun () -> binding <- old)
    method! expression e =
      let e = super#expression e in
      match e.pexp_desc with
      | Pexp_ifthenelse (condition, yes, Some no) -> (
          match branch_field condition yes no with
          | None -> e
          | Some (field, key) ->
              let matches = List.filter (fun item ->
                  item.serializer = binding && item.field = field && item.key = key
                  && same_location item.loc e.pexp_loc) !expected in
              (match matches with
               | [] -> e
               | [item] when not item.consumed ->
                   item.consumed <- true;
                   let loc = condition.pexp_loc in
                   let open Ast_builder.Default in
                   let full = pexp_apply ~loc
                       (pexp_ident ~loc { txt = Longident.Ldot (Longident.Lident "ConfigJsonRuntime", "is_full"); loc })
                       [(Nolabel, eunit ~loc)] in
                   let stdlib name = pexp_ident ~loc { txt = Longident.Ldot (Longident.Lident "Stdlib", name); loc } in
                   let not_full = pexp_apply ~loc (stdlib "not") [(Nolabel, full)] in
                   let guard = pexp_apply ~loc (stdlib "&&") [(Nolabel, condition); (Nolabel, not_full)] in
                   { e with pexp_desc = Pexp_ifthenelse (guard, yes, Some no) }
               | _ -> Location.raise_errorf ~loc:e.pexp_loc "full JSON: ambiguous or repeated omission branch"))
      | _ -> e
  end in
  let tree = mapper#structure tree in
  List.iter (fun item ->
      if not item.consumed then
        Location.raise_errorf ~loc:item.loc
          "full JSON: missing derived omission branch for %s.%s (JSON key %s)"
          item.serializer item.field item.key) !expected;
  expected := [];
  tree

let () =
  Driver.register_transformation "config_full_json_before"
    ~instrument:(Driver.Instrument.make before ~position:Before);
  Driver.register_transformation "config_full_json_after"
    ~instrument:(Driver.Instrument.make after ~position:After)
