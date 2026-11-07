(* The YAML exchange format for software verification witnesses, version 2.x
   (https://gitlab.com/sosy-lab/benchmarking/sv-witnesses, the schemas under
   format/schemas/ and the guide user-guide/Witness-Format.md), as OCaml
   values, and their printing.

   The types cover the elements of format 2.1 whether or not the composer
   produces them yet (loop invariants, assumption and branching waypoints,
   cycle segments), so that adding one later is a matter of constructing it.
   Elements that version 2.2 added (a waypoint's thread_id) and the ghost
   instrumentation entry are absent. Every record field is printed under the
   schema's key, in the schema's order; an optional field that is [None] is
   left out, which is what the schema means by optional. *)

type data_model = ILP32 | LP64

let string_of_data_model = function ILP32 -> "ILP32" | LP64 -> "LP64"

type location = {
  file_name : string;  (** one of the task's input_files *)
  line : int;  (** physical line in that file, from 1 *)
  column : int option;  (** physical column, from 1, a tab counting 1 *)
  function_ : string option;  (** the enclosing function, for readers *)
}

type producer = {
  name : string;
  version : string;
  configuration : string option;
  command_line : string option;
  description : string option;
}

type task = {
  input_files : string list;
  input_file_hashes : (string * string) list;  (** file name -> SHA-256 *)
  specification : string;  (** the property's formula, as in a .prp file *)
  data_model : data_model;
  language : string;  (** "C", the only value the format allows *)
}

type metadata = {
  format_version : string;
  uuid : string;
  creation_time : string;  (** ISO 8601 *)
  producer : producer;
  task : task;
}

type expression_format = C_expression | Ext_c_expression

(* Violation witnesses. *)

type waypoint_type = Assumption | Target | Function_enter | Function_return | Branching
type action = Follow | Avoid | Cycle

type constraint_ = {
  value : string;
  format : expression_format option;  (** absent for a branching waypoint *)
}

type waypoint = {
  wp_type : waypoint_type;
  action : action;
  wp_location : location;
  constraint_ : constraint_ option;
}

type segment = waypoint list

(* Correctness witnesses. *)

type invariant_type =
  | Loop_invariant
  | Loop_transition_invariant
  | Location_invariant
  | Location_transition_invariant

type invariant = {
  inv_type : invariant_type;
  inv_location : location;
  inv_value : string;
  inv_format : expression_format;
}

type entry =
  | Violation_sequence of { metadata : metadata; segments : segment list }
  | Invariant_set of { metadata : metadata; invariants : invariant list }

type t = entry list

(* Printing. Strings are written double-quoted, so that a value such as the
   format version "2.1" or a function named "null" cannot be read back as a
   number, a Boolean or null; integers are written plain. *)

let scalar style value =
  `Scalar
    {
      Yaml.anchor = None;
      tag = None;
      value;
      plain_implicit = style = `Plain;
      quoted_implicit = style <> `Plain;
      style;
    }

let str s = scalar `Double_quoted s
let int n = scalar `Plain (string_of_int n)

(* Keys are the schema's identifiers and are written plain, except where they
   are data (the file names of input_file_hashes), which are quoted. *)
let map ?(key_style = `Plain) fields =
  `O
    {
      Yaml.m_anchor = None;
      m_tag = None;
      m_implicit = true;
      m_members = List.map (fun (k, v) -> (scalar key_style k, v)) fields;
    }

let seq items = `A { Yaml.s_anchor = None; s_tag = None; s_implicit = true; s_members = items }

(* [opt key f x] is the field [key: f x] when [x] is present, nothing otherwise. *)
let opt key f = function Some x -> [ (key, f x) ] | None -> []

let yaml_of_location l =
  map
    ([ ("file_name", str l.file_name); ("line", int l.line) ]
    @ opt "column" int l.column
    @ opt "function" str l.function_)

let yaml_of_metadata m =
  let p = m.producer and t = m.task in
  map
    [ ("format_version", str m.format_version);
      ("uuid", str m.uuid);
      ("creation_time", str m.creation_time);
      ( "producer",
        map
          ([ ("name", str p.name); ("version", str p.version) ]
          @ opt "configuration" str p.configuration
          @ opt "command_line" str p.command_line
          @ opt "description" str p.description) );
      ( "task",
        map
          [ ("input_files", seq (List.map str t.input_files));
            ("input_file_hashes", map ~key_style:`Double_quoted (List.map (fun (f, h) -> (f, str h)) t.input_file_hashes));
            ("specification", str t.specification);
            ("data_model", str (string_of_data_model t.data_model));
            ("language", str t.language) ] ) ]

let string_of_format = function C_expression -> "c_expression" | Ext_c_expression -> "ext_c_expression"

let string_of_waypoint_type = function
  | Assumption -> "assumption"
  | Target -> "target"
  | Function_enter -> "function_enter"
  | Function_return -> "function_return"
  | Branching -> "branching"

let string_of_action = function Follow -> "follow" | Avoid -> "avoid" | Cycle -> "cycle"

let yaml_of_waypoint w =
  map
    [ ( "waypoint",
        map
          ([ ("type", str (string_of_waypoint_type w.wp_type));
             ("action", str (string_of_action w.action));
             ("location", yaml_of_location w.wp_location) ]
          @ opt "constraint"
              (fun c ->
                map ([ ("value", str c.value) ] @ opt "format" (fun f -> str (string_of_format f)) c.format))
              w.constraint_) ) ]

let string_of_invariant_type = function
  | Loop_invariant -> "loop_invariant"
  | Loop_transition_invariant -> "loop_transition_invariant"
  | Location_invariant -> "location_invariant"
  | Location_transition_invariant -> "location_transition_invariant"

let yaml_of_invariant i =
  map
    [ ( "invariant",
        map
          [ ("type", str (string_of_invariant_type i.inv_type));
            ("location", yaml_of_location i.inv_location);
            ("value", str i.inv_value);
            ("format", str (string_of_format i.inv_format)) ] ) ]

let yaml_of_entry = function
  | Violation_sequence { metadata; segments } ->
      map
        [ ("entry_type", str "violation_sequence");
          ("metadata", yaml_of_metadata metadata);
          ( "content",
            seq (List.map (fun s -> map [ ("segment", seq (List.map yaml_of_waypoint s)) ]) segments) ) ]
  | Invariant_set { metadata; invariants } ->
      map
        [ ("entry_type", str "invariant_set");
          ("metadata", yaml_of_metadata metadata);
          ("content", seq (List.map yaml_of_invariant invariants)) ]

let to_string (w : t) =
  match Yaml.yaml_to_string (seq (List.map yaml_of_entry w)) with
  | Ok s -> s
  | Error (`Msg m) -> failwith ("printing the witness: " ^ m)
