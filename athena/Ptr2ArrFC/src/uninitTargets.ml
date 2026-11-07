(* The local variables that start uninitialised (--uninit), where they are
   declared, and the jumps that enter a block without passing its start.

   A target is an automatic local variable (register ones included) whose
   declaration has no initialiser: in the normalised program, a variable of
   some block's locals that no Local_init defines. The temporaries the front
   end makes are targets too. A variable-length array is one as well: the
   front end turns it into a pointer initialised by a call of its allocator
   (__fc_vla_alloc), and the array the call allocates starts uninitialised.
   Static locals, parameters and globals are not targets (C gives the first
   and the last the value zero, and a call gives a parameter its value).

   The front end moves a declaration without an initialiser to the start of
   its block, so the value a target starts with is given there. C makes the
   value indeterminate each time the declaration is reached, and each time
   the block is entered, which the start of the block stands for exactly
   unless the block is entered by a jump (a case label of a switch outside
   it, a goto from outside it), or a goto jumps back from after the
   declaration to a label of the block before it. The first is handled where
   the jump is made ([jump_sources]); the second is refused ([backward_gotos]).
   A temporary of the front end has no declaration in the input: it is
   declared at the start of its block, as the output prints it.

   Contract: every function here reads the AST of the current project and
   changes nothing. *)

open Cil_types

let vla_alloc = "__fc_vla_alloc"

type target = {
  var : varinfo;
  block : block;  (** the block that declares it *)
  vla : exp option;
      (** a variable-length array: the size in bytes its allocation is
          given (the variable is the pointer the allocation returns) *)
}

(* The scalars of a value of type [t]. *)
let rec leaves t =
  match Ast_types.unroll_node t with
  | TArray (t', len) -> Cil.lenOfArray len * leaves t'
  | TComp ci ->
      List.fold_left (fun n f -> n + leaves f.ftype) 0 (Option.value ~default:[] ci.cfields)
  | _ -> 1

(* The variable-length arrays of [fd], each with the size its allocation
   is given, and the other variables a Local_init defines. *)
let initialised fd =
  let vlas = Hashtbl.create 4 and inits = Hashtbl.create 16 in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vinst i =
        (match i with
         | Local_init (v, ConsInit (f, [ n ], _), _) when f.vname = vla_alloc ->
             Hashtbl.replace vlas v.vid n
         | Local_init (v, _, _) -> Hashtbl.replace inits v.vid ()
         | _ -> ());
        Cil.SkipChildren
    end
  in
  ignore (Visitor.visitFramacFunction v fd);
  (vlas, inits)

(* The targets of [fd], in the order of its blocks and their locals. *)
let targets fd =
  let vlas, inits = initialised fd in
  let acc = ref [] in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vblock b =
        List.iter
          (fun var ->
            if var.vstorage <> Static then
              match Hashtbl.find_opt vlas var.vid with
              | Some n -> acc := { var; block = b; vla = Some n } :: !acc
              | None ->
                  if not (Hashtbl.mem inits var.vid) then
                    acc := { var; block = b; vla = None } :: !acc)
          b.blocals;
        Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacFunction v fd);
  List.rev !acc

(* The statement ids of a block, at any depth. *)
let block_sids b =
  let h = Hashtbl.create 16 in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vstmt s =
        Hashtbl.replace h s.sid ();
        Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacBlock v b);
  h

(* The jumps of [fd]: each goto with its target, each switch with its case
   targets. *)
let jumps fd =
  let acc = ref [] in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vstmt s =
        (match s.skind with
         | Goto (t, _) -> acc := (s, [ !t ]) :: !acc
         | Switch (_, _, cases, _) -> acc := (s, cases) :: !acc
         | _ -> ());
        Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacFunction v fd);
  List.rev !acc

(* The statements outside block [b] that jump to a statement inside it, in
   the order of [jumps]: entering [b] there skips its start. *)
let jump_sources jumps b =
  let inside = block_sids b in
  List.filter_map
    (fun (s, targets) ->
      if (not (Hashtbl.mem inside s.sid))
         && List.exists (fun t -> Hashtbl.mem inside t.sid) targets
      then Some s
      else None)
    jumps

(* The position of a location: its file and its character offset there. *)
let position loc =
  let p, _ = Fileloc.to_lexing_loc loc in
  (p.Lexing.pos_fname, p.Lexing.pos_cnum)

(* For each target of [fd] that is not a temporary of the front end nor a
   variable-length array (whose allocation runs where it is declared), the
   gotos that jump back over its declaration: from after it to a label of
   its block before it. When the label, the goto and the declaration are
   not in one file their order is unknown, and every goto to a label of the
   block is reported. *)
let backward_gotos fd =
  let jumps = jumps fd in
  List.concat_map
    (fun t ->
      if t.var.vtemp || t.vla <> None then []
      else begin
        let inside = block_sids t.block in
        let df, dc = position t.var.vdecl in
        List.filter_map
          (fun (s, targets) ->
            match (s.skind, targets) with
            | Goto (_, gloc), [ l ] when Hashtbl.mem inside l.sid -> (
                let lloc =
                  List.find_map (function Label (_, loc, _) -> Some loc | _ -> None) l.labels
                in
                match lloc with
                | None -> None
                | Some lloc ->
                    let lf, lc = position lloc and gf, gc = position gloc in
                    let known = lf = df && gf = df in
                    if (known && lc < dc && gc > dc) || not known then Some (t, s, l) else None)
            | _ -> None)
          jumps
      end)
    (targets fd)
