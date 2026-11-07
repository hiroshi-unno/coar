(* Unions whose members the program reads and writes are all of one type: the
   Juliet "_34" tasks' [union { char *unionFirst; char *unionSecond; }],
   written through one member and read through the other, and the unions of
   system headers no statement touches (a spinlock's [head_tail]/[tickets],
   pthread's [__size]/[__align]) inside structures the program passes
   around.  A union is outside the fragment, and for these nothing the
   program does depends on it being one.

   Before the fragment check, such a union becomes a structure holding one
   member of that type and, when the union is larger, an array of unsigned
   char after it; every access to another member becomes an access to that
   one.  With no member accessed, the member is an unsigned integer of the
   union's alignment.  The structure is used only when its size and its
   alignment are the union's, so sizeof, the layout of what contains it and
   every offset stay as they were.

   Why the meaning does not change: every member of a union starts at its
   beginning, and reading a member of the type last stored through another
   member reads that value (C11 6.5.2.3p3 with footnote 95 and 6.2.6.1p7:
   the representation is reinterpreted in the same type).  A member never
   accessed is never read or written by itself; it is only copied with the
   whole union, and the structure is copied whole too.  What a copy carries
   in the bytes no accessed member covers is the padding the structure
   gives them.

   Left as unions (and refused by the fragment check as before): members of
   different types accessed, a bit-field member, a member with _Alignas, an
   attribute on the union (packed, aligned), and a union whose structure
   would not keep its size and alignment. *)

open Cil_types

let norm t = Cil.typeDeepDropAllAttributes (Ast_types.unroll_deep t)

(* An unsigned integer type of alignment [a] at most [size] bytes long. *)
let word_of_alignment a size =
  List.find_opt
    (fun t -> Cil.bytesAlignOf t = a && Cil.bitsSizeOf t / 8 <= size)
    [ Cil_const.ucharType; Cil_const.ushortType; Cil_const.uintType; Cil_const.ulongType;
      Cil_const.ulongLongType ]

let run () =
  let file = Ast.get () in
  let unions =
    List.filter_map
      (function GCompTag (ci, _) when not ci.cstruct -> Some ci | _ -> None)
      file.globals
  in
  if unions = [] then 0
  else begin
    (* the members accessed, by union *)
    let accessed : (int, fieldinfo list) Hashtbl.t = Hashtbl.create 8 in
    let note fi =
      if not fi.fcomp.cstruct then begin
        let l = Option.value ~default:[] (Hashtbl.find_opt accessed fi.fcomp.ckey) in
        if not (List.memq fi l) then Hashtbl.replace accessed fi.fcomp.ckey (l @ [ fi ])
      end
    in
    let rec note_offset = function
      | Field (fi, off) -> note fi; note_offset off
      | Index (_, off) -> note_offset off
      | NoOffset -> ()
    in
    let collect =
      object
        inherit Visitor.frama_c_inplace

        method! voffs o = note_offset o; Cil.DoChildren

        method! vinitoffs o = note_offset o; Cil.DoChildren
      end
    in
    Visitor.visitFramacFileSameGlobals collect file;
    let tags = Hashtbl.create 16 in
    List.iter
      (function GCompTag (ci, _) | GCompTagDecl (ci, _) -> Hashtbl.replace tags ci.cname () | _ -> ())
      file.globals;
    (* union key -> the member every access goes to *)
    let keeper : (int, fieldinfo) Hashtbl.t = Hashtbl.create 8 in
    let folded = ref 0 in
    List.iter
      (fun ci ->
        match ci.cfields with
        | None | Some [] -> ()
        | Some fields ->
            let plain fi = fi.fbitfield = None && fi.falignas = None in
            let s = Option.value ~default:[] (Hashtbl.find_opt accessed ci.ckey) in
            let size = Cil.bitsSizeOf (Cil_const.mk_tcomp ci) / 8 in
            let align = Cil.bytesAlignOf (Cil_const.mk_tcomp ci) in
            let member =
              if ci.cattr <> [] || not (List.for_all plain fields) then None
              else
                match s with
                | [] -> (
                    match word_of_alignment align size with
                    | Some t -> Some (List.hd fields, t)
                    | None -> None)
                | fi :: rest ->
                    let t = norm fi.ftype in
                    if List.for_all (fun g -> Cil_datatype.Typ.equal (norm g.ftype) t) rest then
                      Some (fi, fi.ftype)
                    else None
            in
            match member with
            | None -> ()
            | Some (fi, t) ->
                let tsize = Cil.bitsSizeOf t / 8 in
                if Cil.bytesAlignOf t = align && tsize <= size then begin
                  let pad = size - tsize in
                  let saved = (ci.cfields, ci.cstruct, ci.cname, fi.ftype, fi.forder) in
                  fi.ftype <- t;
                  fi.forder <- 0;
                  fi.fsize_in_bits <- None;
                  fi.foffset_in_bits <- None;
                  let pad_field =
                    { fi with
                      fname = "__p2a_union_rest";
                      forder = 1;
                      ftype =
                        Cil_const.mk_tarray Cil_const.ucharType (Some (Cil.integer ~loc:fi.floc pad));
                      fbitfield = None;
                      falignas = None;
                      fattr = [];
                      faddrof = false;
                      fsize_in_bits = None;
                      foffset_in_bits = None }
                  in
                  ci.cfields <- Some (if pad > 0 then [ fi; pad_field ] else [ fi ]);
                  ci.cstruct <- true;
                  (* struct and union tags share one name space in C *)
                  if Hashtbl.mem tags ci.cname then begin
                    let rec go k =
                      let n = Printf.sprintf "%s__p2a_u%d" ci.cname k in
                      if Hashtbl.mem tags n then go (k + 1) else n
                    in
                    let n = go 0 in
                    Hashtbl.replace tags n ();
                    ci.cname <- n
                  end;
                  if Cil.bitsSizeOf (Cil_const.mk_tcomp ci) / 8 = size
                     && Cil.bytesAlignOf (Cil_const.mk_tcomp ci) = align
                  then begin
                    List.iter (fun g -> Hashtbl.replace keeper g.fcomp.ckey fi) s;
                    incr folded
                  end
                  else begin
                    (* not the union's layout after all: left as it was *)
                    let fields, cstruct, cname, ftype, forder = saved in
                    ci.cfields <- fields;
                    ci.cstruct <- cstruct;
                    ci.cname <- cname;
                    fi.ftype <- ftype;
                    fi.forder <- forder;
                    fi.fsize_in_bits <- None;
                    fi.foffset_in_bits <- None
                  end
                end)
      unions;
    if !folded > 0 then begin
      (* every access to an accessed member goes to the one kept *)
      let rec redirect = function
        | Field (g, off) -> (
            match Hashtbl.find_opt keeper g.fcomp.ckey with
            | Some fi when g != fi && g.fcomp == fi.fcomp -> Field (fi, redirect off)
            | _ -> Field (g, redirect off))
        | Index (e, off) -> Index (e, redirect off)
        | NoOffset -> NoOffset
      in
      let rewrite =
        object
          inherit Visitor.frama_c_inplace

          method! voffs o = Cil.ChangeDoChildrenPost (redirect o, fun o -> o)

          method! vinitoffs o = Cil.ChangeDoChildrenPost (redirect o, fun o -> o)
        end
      in
      Visitor.visitFramacFileSameGlobals rewrite file;
      Fragment.mark_ast_changed ()
    end;
    !folded
  end
