(* What witness a result gets, decided from the property, the result and the
   transformation record's source map. No file is read or written here.

   What is produced, and why each refusal is one:
   - TRUE for unreach-call and no-overflow: an invariant set holding the loop
     invariants of the result's invariant lines (Invariants), when there are
     any; for termination, the loop transition invariants of its transition
     lines and the loop invariants of its invariant lines; when there are
     none, an invariant set with no invariant. An empty set is a correct
     correctness witness (it claims nothing beyond the result); it is
     confirmed only when a validator proves the program on its own.
   - TRUE for the memory-safety sub-properties, valid-memcleanup and
     no-data-race: none. The SV-COMP 2027 rules require no correctness witness
     for them (valid-memsafety's is a demonstration of format 2.4).
   - FALSE for unreach-call, no-overflow, valid-deref and valid-free: a
     violation sequence ending in a segment holding one target waypoint, at
     the input statement whose evaluation directly contains the violation,
     after one segment per assumption waypoint of the result's state lines
     (the loop-head visits of one violating execution, in order). Such a
     sequence represents the executions that pass those visits with those
     values and reach the violation there, so it is correct whenever the
     execution the lines come from does.
   - FALSE for valid-memtrack and valid-memcleanup: none, since those
     violations need format 2.3; for termination: none, since a
     non-termination witness needs a cycle the result does not carry; for
     no-data-race: none, since it needs two targets in one segment.

   When the source map holds several targets for the property, the result
   does not say which one the violation is reached at. The one at the
   smallest input position is taken: a witness at a target the violation is
   not reached at is merely not confirmed, which scores as no witness at all. *)

type request = {
  input_file : string;  (** the input file's name as the verifier was given it *)
  input_sha256 : string;
  record : Record.t;
  properties : Property.t list;  (** the property file's, in file order *)
  result : bool;
  violated : Property.kind option;  (** --violated *)
  data_model : Witness.data_model;
  producer : Witness.producer;
  format_version : string;
  uuid : string;
  creation_time : string;
  invariant_lines : Invariants.line list;  (** --invariants; empty without it *)
}

type outcome =
  | Write of Witness.t
  | No_witness of string  (** why this result gets none *)
  | Invalid of string  (** the request is inconsistent *)

exception Stop of outcome

let invalid fmt = Printf.ksprintf (fun s -> raise (Stop (Invalid s))) fmt
let no_witness fmt = Printf.ksprintf (fun s -> raise (Stop (No_witness s))) fmt

let metadata r (p : Property.t) =
  {
    Witness.format_version = r.format_version;
    uuid = r.uuid;
    creation_time = r.creation_time;
    producer = r.producer;
    task =
      {
        input_files = [ r.input_file ];
        input_file_hashes = [ (r.input_file, r.input_sha256) ];
        specification = p.formula;
        data_model = r.data_model;
        language = "C";
      };
  }

let compare_position (a : Record.input_position) (b : Record.input_position) =
  compare (a.line, Option.value ~default:0 a.column) (b.line, Option.value ~default:0 b.column)

(* The distinct input positions of the source map's targets whose property
   satisfies [keep], with that property, smallest first. Several printed
   statements commonly come from one input statement; a target the
   transformation made, with no input position, cannot be written. *)
let targets r keep =
  List.filter_map
    (fun (s : Record.statement) ->
      match (s.role, s.input, s.property) with
      | Record.Target, Some pos, Some prop when keep prop -> Some (pos, prop)
      | _ -> None)
    r.record.source_map
  |> List.sort_uniq (fun (a, p) (b, q) ->
         match compare_position a b with 0 -> compare p q | c -> c)

(* The one property a FALSE result is about: the file's single property, or
   for valid-memsafety the sub-property given by --violated or, without it,
   the one of the first memory-safety target in the source map. *)
let violated_property r note =
  match (r.properties, r.violated) with
  | [ p ], None -> p
  | [ p ], Some v ->
      if p.kind = v then p
      else invalid "--violated %s is not the property file's %s" (Property.name v) (Property.name p.kind)
  | ps, Some v -> (
      match List.find_opt (fun (p : Property.t) -> p.kind = v) ps with
      | Some p -> p
      | None -> invalid "--violated %s is not in the property file" (Property.name v))
  | ps, None -> (
      let names = List.map (fun (p : Property.t) -> Property.name p.kind) ps in
      match targets r (fun prop -> List.mem prop names) with
      | [] -> no_witness "no target of a memory-safety property in the source map, and no --violated"
      | (_, prop) :: rest ->
          let p = List.find (fun (p : Property.t) -> Property.name p.kind = prop) ps in
          note
            (Printf.sprintf "violated sub-property: %s (%s)" prop
               (if List.exists (fun (_, q) -> q <> prop) rest then "guessed: the first target of several properties"
                else "the only property with a target"));
          p)

let violation r note =
  let p = violated_property r note in
  (match p.kind with
  | Unreach_call "reach_error" | No_overflow | Valid_deref | Valid_free -> ()
  | Unreach_call f ->
      no_witness "the source map marks calls of reach_error only, and the property is about %s" f
  | Valid_memtrack | Valid_memcleanup ->
      no_witness "a %s violation witness needs format 2.3" (Property.name p.kind)
  | Termination -> no_witness "a non-termination witness needs a cycle, which the result does not carry"
  | No_data_race -> no_witness "athena does not verify multi-threaded programs");
  let name = Property.name p.kind in
  let pos =
    match targets r (String.equal name) with
    | [] -> no_witness "no target of %s in the source map" name
    | [ (pos, _) ] -> pos
    | (pos, _) :: rest ->
        note
          (Printf.sprintf "guessed the target: %d candidates for %s, took the first (line %d)"
             (1 + List.length rest) name pos.line);
        pos
  in
  let location =
    { Witness.file_name = r.input_file; line = pos.line; column = pos.column; function_ = pos.func }
  in
  let target = { Witness.wp_type = Target; action = Follow; wp_location = location; constraint_ = None } in
  let path =
    Invariants.path_waypoints r.record ~input_file:r.input_file note r.invariant_lines |> List.map (fun w -> [ w ])
  in
  if path <> [] then note (Printf.sprintf "%d assumption waypoints from the path" (List.length path));
  Write [ Violation_sequence { metadata = metadata r p; segments = path @ [ [ target ] ] } ]

let correctness r note =
  if r.violated <> None then invalid "--violated is for --result false";
  match r.properties with
  | [ ({ kind = Unreach_call _ | No_overflow; _ } as p) ] ->
      let dropped = ref [] in
      let invariants =
        Invariants.to_witness r.record ~input_file:r.input_file
          (fun why -> if not (List.mem why !dropped) then dropped := why :: !dropped)
          r.invariant_lines
      in
      List.iter (fun why -> note ("dropped: " ^ why)) (List.rev !dropped);
      if r.invariant_lines <> [] then
        note (Printf.sprintf "%d loop invariants from %d lines" (List.length invariants) (List.length r.invariant_lines));
      Write [ Invariant_set { metadata = metadata r p; invariants } ]
  | [ ({ kind = Termination; _ } as p) ] ->
      let dropped = ref [] in
      let note_drop why = if not (List.mem why !dropped) then dropped := why :: !dropped in
      let transitions =
        Invariants.to_witness ~kind:Transition r.record ~input_file:r.input_file note_drop r.invariant_lines
      in
      let invariants = Invariants.to_witness r.record ~input_file:r.input_file note_drop r.invariant_lines in
      List.iter (fun why -> note ("dropped: " ^ why)) (List.rev !dropped);
      if r.invariant_lines <> [] then
        note
          (Printf.sprintf "%d loop transition invariants and %d loop invariants from %d lines"
             (List.length transitions) (List.length invariants) (List.length r.invariant_lines));
      Write [ Invariant_set { metadata = metadata r p; invariants = transitions @ invariants } ]
  | [ { kind = Valid_memcleanup | No_data_race; _ } as p ] ->
      no_witness "SV-COMP requires no correctness witness for %s" (Property.name p.kind)
  | _ -> no_witness "SV-COMP requires no correctness witness for valid-memsafety"

(* The outcome, and the notes for stderr (what was chosen without the result
   saying so), in the order they were made; the notes stand whatever the
   outcome. *)
let compose r =
  let notes = ref [] in
  let note n = notes := n :: !notes in
  let outcome = try if r.result then correctness r note else violation r note with Stop o -> o in
  (outcome, List.rev !notes)
