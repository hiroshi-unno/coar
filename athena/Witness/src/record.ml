(* The part of Ptr2ArrFC's transformation record (the .p2a.json written beside
   its output) that a witness needs: which input it was made from (path,
   SHA-256, the Frama-C machine description it was read with) and the source
   map, which ties each printed statement to the input statement it comes from
   and to its role for a witness. Every other field of the record is ignored. *)

type input_position = {
  line : int;  (** physical line in the input file, from 1 *)
  column : int option;  (** physical column of the statement's first character, from 1 *)
  func : string option;  (** the input function that holds it *)
}

type role = Loop_head | Branch | Call | Target | Other

type statement = {
  output_line : int;
  output_column : int;
  role : role;
  input : input_position option;  (** [None]: from another file, or made by the transformation *)
  property : string option;  (** for a target: the property violated there, by its SV-COMP name *)
}

(* An integer type of a name: [Bool], or an integer or enumeration type of
   this width and signedness. *)
type int_type = Bool_type | Int_type of { width : int; signed : bool }

type name = {
  name : string;  (** the name in the output *)
  original : string option;  (** the name in the input, for a name that comes from it *)
  name_func : string option;  (** the enclosing function, for a formal or a local *)
  kind : string;  (** global | function | formal | local *)
  name_role : string;  (** program | index | addr | generated | shadow | marker | stop | exhausted *)
  int_type : int_type option;
}

type t = {
  path : string;  (** the input's path as given to Ptr2ArrFC *)
  sha256 : string;
  machdep : string;
  source_map : statement list;  (** in output order *)
  names : name list;  (** empty for a record that has none *)
}

exception Malformed of string

let malformed fmt = Printf.ksprintf (fun s -> raise (Malformed s)) fmt

let field name = function
  | `Assoc fields -> (
      match List.assoc_opt name fields with Some v -> v | None -> malformed "missing field %s" name)
  | _ -> malformed "expected an object holding %s" name

let to_string name = function `String s -> s | _ -> malformed "%s: expected a string" name
let to_int name = function `Int n -> n | _ -> malformed "%s: expected an integer" name

let to_option f name = function `Null -> None | v -> Some (f name v)

let role_of_string = function
  | "loop-head" -> Loop_head
  | "branch" -> Branch
  | "call" -> Call
  | "target" -> Target
  | "other" -> Other
  | r -> malformed "source_map: unknown role %s" r

let input_position_of_json name j =
  {
    line = to_int (name ^ ".line") (field "line" j);
    column =
      (match j with
      | `Assoc fs -> Option.bind (List.assoc_opt "column" fs) (to_option to_int (name ^ ".column"))
      | _ -> None);
    func =
      (match j with
      | `Assoc fs -> Option.bind (List.assoc_opt "function" fs) (to_option to_string (name ^ ".function"))
      | _ -> None);
  }

let statement_of_json j =
  {
    output_line = to_int "output_line" (field "output_line" j);
    output_column = to_int "output_column" (field "output_column" j);
    role = role_of_string (to_string "role" (field "role" j));
    input = to_option input_position_of_json "input" (field "input" j);
    property = to_option to_string "property" (field "property" j);
  }

let optional name = function `Assoc fs -> List.assoc_opt name fs | _ -> None

let int_type_of_json j =
  match optional "kind" j with
  | Some (`String "bool") -> Some Bool_type
  | Some (`String ("int" | "enum")) -> (
      match (optional "width" j, optional "signed" j) with
      | Some (`Int width), Some (`Bool signed) -> Some (Int_type { width; signed })
      | _ -> None)
  | _ -> None

let name_of_json j =
  {
    name = to_string "names.name" (field "name" j);
    original = to_option to_string "names.original" (field "original" j);
    name_func = Option.bind (optional "function" j) (to_option to_string "names.function");
    kind = to_string "names.kind" (field "kind" j);
    name_role = to_string "names.role" (field "role" j);
    int_type = Option.bind (optional "type" j) int_type_of_json;
  }

let of_json j =
  let input = field "input" j in
  let sm = field "source_map" j in
  let statements =
    match field "statements" sm with
    | `List l -> List.map statement_of_json l
    | _ -> malformed "source_map.statements: expected a list"
  in
  {
    path = to_string "input.path" (field "path" input);
    sha256 = to_string "input.sha256" (field "sha256" input);
    machdep = to_string "input.machdep" (field "machdep" input);
    source_map = statements;
    names =
      (match optional "names" j with
      | None | Some `Null -> []
      | Some (`List l) -> List.map name_of_json l
      | Some _ -> malformed "names: expected a list");
  }

let read path =
  match of_json (Yojson.Safe.from_file path) with
  | r -> Ok r
  | exception Malformed m -> Error (Printf.sprintf "%s: malformed record: %s" path m)
  | exception Yojson.Json_error m -> Error (Printf.sprintf "%s: %s" path m)
  | exception Sys_error m -> Error m

(* The data model a Frama-C machine description stands for. Only the two
   machdeps Ptr2ArrFC reads an SV-COMP task with are known; any other has no
   data model this composer will vouch for. *)
let data_model_of_machdep = function
  | "gcc_x86_32" -> Some Witness.ILP32
  | "gcc_x86_64" -> Some Witness.LP64
  | _ -> None
