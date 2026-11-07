(* The region partition and each region's representation.

   A region is a class of the points-to analysis that holds an object or is
   dereferenced. Classes are disjoint by construction, so the regions partition
   the objects, every pointer location lies in one region (the class it points
   to) and every region has at most one successor (the class its pointer slot
   points to).

   A region is typed with cell type sigma when every object in it is a sigma or
   an array of sigma, every pointer value into it has type sigma* (or a pointer
   to an array of sigma), and no pointer into it addresses a field of a
   cell. The cell type is compared after unrolling typedefs and dropping
   qualifiers and attributes. Otherwise it is a byte region. A pointer to void
   says nothing about the cell type and is not counted.

   Contract: [compute st] reads the current project's AST and the finished
   analysis [st]; the regions are numbered from 0 in the order of their
   representatives' creation, so the numbering is deterministic. *)

open Cil_types

type kind = Typed of typ | Byte of string  (** why it is not typed *)

type obj = Var of varinfo | Alloc of PointsTo.site

type region = {
  rid : int;
  rep : PointsTo.node;
  mutable objects : obj list;
  mutable cell_types : typ list;  (** the distinct candidate cell types *)
  mutable field_address : bool;
  mutable dereferenced : bool;
  mutable mem_sizes : exp list;
      (** the byte counts memset, memcpy and memmove are given into it *)
  mutable kind : kind;
}

type t = { st : PointsTo.t; by_rep : (int, region) Hashtbl.t; mutable list : region list }

let rec elem t =
  match Ast_types.unroll_node t with TArray (t', _) -> elem t' | _ -> t

let normal t = Cil.typeDeepDropAllAttributes (Ast_types.unroll_deep t)

let same_type a b = Cil_datatype.Typ.equal (normal a) (normal b)

(* Number of sigma cells in a [t], when [t] is sigma or a (nested) array of it. *)
let rec cells_of t =
  match Ast_types.unroll_node t with
  | TArray (t', len) -> Cil.lenOfArray len * cells_of t'
  | _ -> 1

let region_of_node r n =
  let rep = PointsTo.find n in
  match Hashtbl.find_opt r.by_rep rep.id with
  | Some reg -> reg
  | None ->
      let reg =
        { rid = -1; rep; objects = []; cell_types = []; field_address = false;
          dereferenced = false; mem_sizes = []; kind = Byte "undetermined" }
      in
      Hashtbl.add r.by_rep rep.id reg;
      reg

let add_type reg t =
  let t = normal (elem t) in
  if not (Ast_types.is_void t || List.exists (same_type t) reg.cell_types) then
    reg.cell_types <- reg.cell_types @ [ t ]

(* Does the offset address a field of a cell (after the array indices that
   select the cell)? *)
let rec reaches_field = function
  | NoOffset -> false
  | Index (_, off) -> reaches_field off
  | Field _ -> true

(* How many cells of type [sigma] the byte count [n] (an input expression)
   is, when that is known statically: [k] for [k * sizeof(sigma)] and
   [sizeof(sigma) * k], the cells of [sizeof(T)] for T sigma or an array of
   it, and [c / sizeof(sigma)] for a constant c that is a multiple of it
   (sizes in the input's layout, which the input's constants are written
   in). *)
type cells = Count of exp | Const of int

let size_in_cells sigma n =
  let strip = PointsTo.strip_casts in
  let size_of e =
    match (strip e).enode with
    | SizeOf t -> Some t
    | SizeOfE e' -> Some (Cil.typeOf e')
    | _ -> None
  in
  let whole t = same_type (elem t) sigma in
  let n' = strip n in
  match n'.enode with
  | (SizeOf _ | SizeOfE _) when Option.fold ~none:false ~some:whole (size_of n') ->
      Option.map (fun t -> Const (cells_of t)) (size_of n')
  | BinOp (Mult, k, s, _) when Option.fold ~none:false ~some:(same_type sigma) (size_of s) ->
      Some (Count k)
  | BinOp (Mult, s, k, _) when Option.fold ~none:false ~some:(same_type sigma) (size_of s) ->
      Some (Count k)
  | _ -> (
      let bytes = Cil.bitsSizeOf sigma / 8 in
      match Cil.constFoldToInt n' with
      | Some c when bytes > 0 && Z.(equal (rem c (of_int bytes)) zero) ->
          Some (Const (Z.to_int (Z.div c (Z.of_int bytes))))
      | _ -> None)

let compute (st : PointsTo.t) : t =
  let r = { st; by_rep = Hashtbl.create 16; list = [] } in
  Hashtbl.iter
    (fun _ vi ->
      let reg = region_of_node r (PointsTo.var_node st vi) in
      reg.objects <- Var vi :: reg.objects;
      add_type reg vi.vtype)
    st.address_taken;
  Hashtbl.iter
    (fun sid site ->
      let reg = region_of_node r (PointsTo.alloc_node st sid) in
      reg.objects <- Alloc site :: reg.objects)
    st.sites;
  let pointer_value e =
    match Ast_types.unroll_node (Cil.typeOf e) with
    | TPtr t when not (Ast_types.is_fun t) ->
        let reg = region_of_node r (PointsTo.ptee st e) in
        add_type reg t
    | _ -> ()
  in
  let visitor =
    object
      inherit Visitor.frama_c_inplace

      method! vexpr e =
        (match e.enode with
         | Const _ -> ()
         | StartOf (Var _, _) when Hashtbl.mem st.exempt e.eid -> ()
         | _ when Fragment.is_null_constant e -> ()
         | _ -> pointer_value e);
        (match e.enode with
         | (AddrOf lv | StartOf lv) when not (Hashtbl.mem st.exempt e.eid) ->
             if reaches_field (snd lv) then
               (region_of_node r (PointsTo.loc_of st lv)).field_address <- true
         | _ -> ());
        Cil.DoChildren

      method! vlval lv =
        (match lv with
         | Mem e, _ -> (region_of_node r (PointsTo.ptee st e)).dereferenced <- true
         | _ -> ());
        Cil.DoChildren

      (* The result of an allocation is typed by what receives it. *)
      method! vinst i =
        (match i with
         | Call (Some lv, Var f, _, _)
           when List.mem f.vname PointsTo.allocators && not (PointsTo.is_defined f)
           -> (
             match Ast_types.unroll_node (Cil.typeOfLval lv) with
             | TPtr t ->
                 add_type (region_of_node r (PointsTo.pt st (PointsTo.loc_of st lv))) t
             | _ -> ())
         | Local_init (v, ConsInit (f, _, _), _)
           when List.mem f.vname PointsTo.allocators && not (PointsTo.is_defined f) -> (
             match Ast_types.unroll_node v.vtype with
             | TPtr t -> add_type (region_of_node r (PointsTo.pt st (PointsTo.var_node st v))) t
             | _ -> ())
         | _ -> ());
        (* the byte counts of the block functions, which decide whether the
           region can stay typed *)
        (match i with
         | Call (_, Var f, d :: _ :: n :: _, _) | Local_init (_, ConsInit (f, d :: _ :: n :: _, _), _)
           when List.mem f.vname Fragment.memory_functions && not (PointsTo.is_defined f) ->
             let reg = region_of_node r (PointsTo.ptee st d) in
             reg.mem_sizes <- n :: reg.mem_sizes
         | _ -> ());
        Cil.DoChildren
    end
  in
  Visitor.visitFramacFileSameGlobals visitor (Ast.get ());
  (* A class that holds no object and is never dereferenced needs no array
     (the pointers into it only ever hold NULL); it stays out. *)
  let regs =
    Hashtbl.fold
      (fun _ reg acc ->
        if reg.objects <> [] || reg.dereferenced then reg :: acc else acc)
      r.by_rep []
    |> List.sort (fun a b -> compare a.rep.id b.rep.id)
  in
  let regs =
    List.mapi
      (fun i reg ->
        let kind =
          if reg.field_address then Byte "a pointer addresses a field of a cell"
          else
            match reg.cell_types with
            | [] -> Typed Cil_const.charType
            | [ t ]
              when Cil.bitsSizeOf t > 8
                   && List.exists (fun n -> size_in_cells (normal t) n = None) reg.mem_sizes ->
                Byte "memset, memcpy or memmove is given a size that is not a known number of cells"
            | [ t ] -> Typed (normal t)
            | ts ->
                Byte
                  (Format.asprintf "it is accessed at several types: %a"
                     (Pretty_utils.pp_list ~sep:", " Cil_datatype.Typ.pretty)
                     ts)
        in
        let reg' = { reg with rid = i; kind } in
        Hashtbl.replace r.by_rep reg.rep.id reg';
        reg')
      regs
  in
  r.list <- regs;
  r

(* The region an existing class belongs to; [None] for a class that holds no
   object and is never dereferenced. *)
let find r n =
  let rep = PointsTo.find n in
  match Hashtbl.find_opt r.by_rep rep.id with
  | Some reg when reg.rid >= 0 -> Some reg
  | _ -> None
