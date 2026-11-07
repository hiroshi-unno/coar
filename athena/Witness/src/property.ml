(* SV-COMP property files (.prp): one formula per line, each
   CHECK( init(<entry>()), LTL(<formula>) ), as listed in the competition rules
   (https://sv-comp.sosy-lab.org/2027/rules.php, "Properties"). A file for
   valid-memsafety holds three such lines, one per sub-property. *)

type kind =
  | Unreach_call of string  (** the function whose call must not be reached *)
  | No_overflow
  | Valid_deref
  | Valid_free
  | Valid_memtrack
  | Valid_memcleanup
  | Termination
  | No_data_race

type t = {
  kind : kind;
  formula : string;  (** the line as written, surrounding blanks removed *)
}

(* The names --violated and the record use for a property. *)
let name = function
  | Unreach_call _ -> "unreach-call"
  | No_overflow -> "no-overflow"
  | Valid_deref -> "valid-deref"
  | Valid_free -> "valid-free"
  | Valid_memtrack -> "valid-memtrack"
  | Valid_memcleanup -> "valid-memcleanup"
  | Termination -> "termination"
  | No_data_race -> "no-data-race"

let is_memsafety = function Valid_deref | Valid_free | Valid_memtrack -> true | _ -> false

let strip_blanks s = String.concat "" (String.split_on_char ' ' s |> List.concat_map (String.split_on_char '\t'))

let has_prefix ~prefix s =
  String.length s >= String.length prefix && String.sub s 0 (String.length prefix) = prefix

let has_suffix ~suffix s =
  let n = String.length s and m = String.length suffix in
  n >= m && String.sub s (n - m) m = suffix

(* The LTL formula of one line, blanks removed: "G!call(reach_error())" for
   CHECK( init(main()), LTL(G ! call(reach_error())) ). *)
let ltl_of_line line =
  let s = strip_blanks line in
  match String.index_opt s ',' with
  | Some i when has_prefix ~prefix:"CHECK(init(" s ->
      let rest = String.sub s (i + 1) (String.length s - i - 1) in
      if has_prefix ~prefix:"LTL(" rest && has_suffix ~suffix:"))" rest then
        Ok (String.sub rest 4 (String.length rest - 6))
      else Error ("not a CHECK( init(...), LTL(...) ) line: " ^ line)
  | _ -> Error ("not a CHECK( init(...), LTL(...) ) line: " ^ line)

let kind_of_ltl ltl =
  match ltl with
  | "G!overflow" -> Ok No_overflow
  | "Gvalid-deref" -> Ok Valid_deref
  | "Gvalid-free" -> Ok Valid_free
  | "Gvalid-memtrack" -> Ok Valid_memtrack
  | "Gvalid-memcleanup" -> Ok Valid_memcleanup
  | "Fend" -> Ok Termination
  | "G!data-race" -> Ok No_data_race
  | _ when has_prefix ~prefix:"G!call(" ltl && has_suffix ~suffix:"())" ltl ->
      Ok (Unreach_call (String.sub ltl 7 (String.length ltl - 10)))
  | _ -> Error ("unknown property LTL(" ^ ltl ^ ")")

let ( let* ) = Result.bind

(* The properties of a .prp file's text, in file order. A file that holds more
   than one must be the valid-memsafety one: its lines all memory-safety
   sub-properties, each once. *)
let parse text =
  let lines =
    String.split_on_char '\n' text |> List.map String.trim |> List.filter (fun l -> l <> "")
  in
  let* props =
    List.fold_right
      (fun line acc ->
        let* acc = acc in
        let* ltl = ltl_of_line line in
        let* kind = kind_of_ltl ltl in
        Ok ({ kind; formula = line } :: acc))
      lines (Ok [])
  in
  match props with
  | [] -> Error "the property file holds no property"
  | [ _ ] -> Ok props
  | _ ->
      let kinds = List.map (fun p -> p.kind) props in
      if List.for_all is_memsafety kinds && List.length (List.sort_uniq compare kinds) = List.length kinds
      then Ok props
      else Error "a property file with several properties must hold only the memory-safety ones, each once"

let read path =
  match In_channel.with_open_bin path In_channel.input_all with
  | text -> parse text
  | exception Sys_error e -> Error e
