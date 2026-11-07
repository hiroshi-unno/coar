(* The layout of the objects in memory the translation tracks: integer
   variables whose address is taken, arrays, structs, and any nesting of
   these (no unions).

   An object of element type T, allocated [count] times (1 for a global or
   an ordinary local, the run-time length for a variable-length array), is
   split into components: one per leaf field of T, a leaf being an integer
   reached through struct fields, with the arrays on the way counted as
   dimensions.  A component is one variable of the LTS; it is an array
   variable when the object is allocated more than once or the leaf is
   inside an array, indexed row-major by the outer count and then the
   arrays on its path ([arr[i].a[j]] is one array indexed i * len(a) + j).

   Addresses are byte offsets, as getelementptr computes them from the
   DataLayout; an access is mapped back to the leaves it covers.  So the
   same bytes can be read under another type, as clang does when it passes
   a struct by value as one integer, provided the access covers whole
   leaves. *)

exception Unsupported of Llvm.lltype

type comp = {
  path : int list;  (** the struct fields chosen on the way to the leaf *)
  width : int;
  dims : int list;  (** the lengths of the arrays on the way, outer first *)
}

let rec components ty =
  match Llvm.classify_type ty with
  | Integer -> [ { path = []; width = Llvm.integer_bitwidth ty; dims = [] } ]
  | Array ->
      let n = Llvm.array_length ty in
      List.map (fun c -> { c with dims = n :: c.dims }) (components (Llvm.element_type ty))
  | Struct when not (Ir.is_union ty || Llvm.is_opaque ty) ->
      List.concat
        (List.mapi
           (fun i f -> List.map (fun c -> { c with path = i :: c.path }) (components f))
           (Array.to_list (Ir.struct_element_types ty)))
  | _ -> raise (Unsupported ty)

(* The number of leaves of a component in one value of the type. *)
let count c = List.fold_left ( * ) 1 c.dims

let size layout ty = Llvm_target.DataLayout.abi_size ty layout
let store_size layout ty = Llvm_target.DataLayout.store_size ty layout
let field_offset layout ty i = Llvm_target.DataLayout.offset_of_element ty i layout

exception Partial

(* The leaves of a value of type [ty] that lie in the bytes [lo, hi): their
   path, their index in each array on the way, their byte offset and
   width.  Raises [Partial] when a leaf lies partly inside. *)
let leaves_in layout ty ~lo ~hi =
  let rec go ty base path idx acc =
    match Llvm.classify_type ty with
    | Integer ->
        let bytes = store_size layout ty in
        let stop = Int64.add base bytes in
        if stop <= lo || base >= hi then acc
        else if base >= lo && stop <= hi then
          (List.rev path, List.rev idx, base, Llvm.integer_bitwidth ty) :: acc
        else raise Partial
    | Array ->
        let e = Llvm.element_type ty in
        let s = size layout e in
        let n = Llvm.array_length ty in
        let acc = ref acc in
        for j = 0 to n - 1 do
          let b = Int64.add base (Int64.mul (Int64.of_int j) s) in
          if Int64.add b s > lo && b < hi then
            acc := go e b path (Int64.of_int j :: idx) !acc
        done;
        !acc
    | Struct ->
        let acc = ref acc in
        Array.iteri
          (fun i f ->
            let b = Int64.add base (field_offset layout ty i) in
            if Int64.add b (size layout f) > lo && b < hi then
              acc := go f b (i :: path) idx !acc)
          (Ir.struct_element_types ty);
        !acc
    | _ -> raise (Unsupported ty)
  in
  List.rev (go ty 0L [] [] [])

(* The nonzero leaves of a constant of type [ty], as (path, array indices,
   constant); [Error c] names a part that is not an integer constant. *)
let nonzero_leaves init =
  let rec go c path idx acc =
    match Llvm.classify_value c with
    | ConstantAggregateZero | NullValue -> Ok acc
    | ConstantInt ->
        Ok
          (if Llvm.int64_of_const c = Some 0L then acc
           else (List.rev path, List.rev idx, c) :: acc)
    | ConstantArray | ConstantDataArray | ConstantStruct ->
        let ty = Llvm.type_of c in
        let is_struct = Llvm.classify_type ty = Struct in
        let n =
          if is_struct then Array.length (Ir.struct_element_types ty)
          else Llvm.array_length ty
        in
        let rec elements i acc =
          if i >= n then Ok acc
          else
            match Llvm.aggregate_element c i with
            | None -> Error c
            | Some e -> (
                let path, idx = if is_struct then (i :: path, idx) else (path, i :: idx) in
                match go e path idx acc with
                | Ok acc -> elements (i + 1) acc
                | Error _ as e -> e)
        in
        elements 0 acc
    | _ -> Error c
  in
  Result.map List.rev (go init [] [] [])

(* The bits of the byte [b] repeated over [n] bits (n a multiple of 8, at
   most 64), read as a signed n-bit number. *)
let repeated_byte b n =
  let b = Int64.logand b 0xFFL in
  let rec fill k acc =
    if k = 0 then acc else fill (k - 8) (Int64.logor (Int64.shift_left acc 8) b)
  in
  let bits = fill n 0L in
  if n < 64 && Int64.logand bits (Int64.shift_left 1L (n - 1)) <> 0L then
    Int64.sub bits (Int64.shift_left 1L n)
  else bits

(* [n] bits from [lo] set, as a signed [w]-bit number (w at most 64). *)
let bit_mask ~lo ~n w =
  let ones = if n >= 64 then -1L else Int64.sub (Int64.shift_left 1L n) 1L in
  let m = Int64.shift_left ones lo in
  if w < 64 && Int64.logand m (Int64.shift_left 1L (w - 1)) <> 0L then
    Int64.sub m (Int64.shift_left 1L w)
  else m
