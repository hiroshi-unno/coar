(* Steensgaard's points-to analysis over CIL (Steensgaard, "Points-to analysis
   in almost linear time", POPL 1996), insensitive to context, flow and fields.

   Abstract locations: one per variable (global, local, formal; a string
   literal is a global array), one per function result, one per allocation
   site. Each equivalence class of locations points to at most one class
   ([pt]); an assignment of a pointer value unifies the class the target points
   to with the class the value points to, recursively. A structure or array
   variable is one location for all its pointer slots (field insensitivity),
   so a region holds one pointer slot and the class it points to is the
   region's successor.

   Soundness: every pointer value computed by an execution without undefined
   behaviour of a program in the fragment points to an object in the class
   [ptee e] of the expression that computed it. The fragment is what makes
   this hold: no integer is cast to a pointer, no external function outside
   the modelled table receives or returns a pointer, and no function pointer
   hides a call target.

   Determinism: the representative of a class is the member with the smallest
   creation number, and creation follows the order of the AST, so the same
   input always gives the same classes and the same representatives. *)

open Cil_types

type node = { id : int; mutable link : node option; mutable pt : node option }

type site = { sid : int; func : string; loc : Fileloc.t; allocator : string }

type t = {
  vars : (int, node) Hashtbl.t;  (** variable id -> location *)
  rets : (int, node) Hashtbl.t;  (** function variable id -> its result *)
  allocs : (int, node) Hashtbl.t;  (** allocation statement id -> site *)
  sites : (int, site) Hashtbl.t;
  address_taken : (int, varinfo) Hashtbl.t;
      (** variables whose address is taken: the objects that are variables *)
  exempt : (int, unit) Hashtbl.t;
      (** ids of the string-literal expressions passed to external functions:
          these stay literals and do not make the literal an object *)
  mutable counter : int;
}

let create () =
  { vars = Hashtbl.create 64; rets = Hashtbl.create 16;
    allocs = Hashtbl.create 16; sites = Hashtbl.create 16;
    address_taken = Hashtbl.create 16; exempt = Hashtbl.create 16;
    counter = 0 }

let fresh st =
  st.counter <- st.counter + 1;
  { id = st.counter; link = None; pt = None }

let rec find n =
  match n.link with
  | None -> n
  | Some p ->
      let r = find p in
      n.link <- Some r;
      r

let rec join a b =
  let a = find a and b = find b in
  if a != b then begin
    let keep, drop = if a.id < b.id then (a, b) else (b, a) in
    drop.link <- Some keep;
    match (keep.pt, drop.pt) with
    | None, p -> keep.pt <- p
    | Some _, None -> ()
    | Some p, Some q -> join p q
  end

(* The class [n] points to, created empty when [n] points nowhere yet. *)
let pt st n =
  let n = find n in
  match n.pt with
  | Some p -> find p
  | None ->
      let p = fresh st in
      n.pt <- Some p;
      p

let get tbl st key =
  match Hashtbl.find_opt tbl key with
  | Some n -> n
  | None ->
      let n = fresh st in
      Hashtbl.add tbl key n;
      n

let var_node st vi = get st.vars st vi.vid
let ret_node st f = get st.rets st f.vid
let alloc_node st sid = get st.allocs st sid

let rec strip_casts e =
  match e.enode with CastE (_, e') -> strip_casts e' | _ -> e

(* The location an lvalue denotes (offsets are ignored: field insensitivity). *)
let rec loc_of st (host, _) =
  match host with Var vi -> var_node st vi | Mem e -> ptee st e

(* The class of objects the value of [e] may point to. *)
and ptee st e =
  match e.enode with
  | Lval lv -> pt st (loc_of st lv)
  | AddrOf lv | StartOf lv -> loc_of st lv
  | CastE (_, e')
    when not (Ast_types.is_ptr (Cil.typeOf e') || Ast_types.is_array (Cil.typeOf e')) ->
      (* a pointer made from an integer (the null constant, or a function
         number converted to a data pointer) points to no object *)
      fresh st
  | CastE (_, e') -> ptee st e'
  | BinOp ((PlusPI | MinusPI), p, _, _) -> ptee st p
  | _ -> fresh st

let is_defined vi =
  try Kernel_function.is_definition (Globals.Functions.get vi)
  with Not_found -> false

let formals_of f =
  try Kernel_function.get_formals (Globals.Functions.get f) with Not_found -> []

let allocators =
  [ "malloc"; "calloc"; "realloc"; "alloca"; "__builtin_alloca"; "__fc_vla_alloc";
    "__VERIFIER_nondet_String" ]

(* A call [ret = f(args)] at statement [sid]. *)
let call st ~sid ~func ~loc ret f args =
  let target () = match ret with Some lv -> Some (loc_of st lv) | None -> None in
  if is_defined f then begin
    let rec bind fs as_ =
      match (fs, as_) with
      | fv :: fs', a :: as' ->
          join (pt st (var_node st fv)) (ptee st a);
          bind fs' as'
      | _ -> ()
    in
    bind (formals_of f) args;
    Option.iter (fun t -> join (pt st t) (pt st (ret_node st f))) (target ())
  end
  else if List.mem f.vname allocators then begin
    let site = alloc_node st sid in
    if not (Hashtbl.mem st.sites sid) then
      Hashtbl.add st.sites sid { sid; func; loc; allocator = f.vname };
    Option.iter (fun t -> join (pt st t) site) (target ());
    (* realloc's block replaces its argument's, in the same region *)
    match (f.vname, args) with
    | "realloc", p :: _ -> join (ptee st p) site
    | _ -> ()
  end
  else if List.mem f.vname Fragment.memory_functions || List.mem f.vname Fragment.string_functions
  then begin
    (* memcpy and memmove copy the pointers the source holds into the
       destination; the others copy characters or write a byte. The result
       is the first argument. *)
    (match (f.vname, args) with
     | ("memcpy" | "memmove"), d :: s :: _ -> join (ptee st d) (ptee st s)
     | _ -> ());
    match (f.vname, args, target ()) with
    | ("strlen" | "strcmp"), _, _ -> ()
    | _, d :: _, Some t -> join (pt st t) (ptee st d)
    | _ -> ()
  end
  else
    (* An external function in the modelled table other than an allocator
       (free) or one that takes and returns no pointer: its string-literal
       arguments stay literals. *)
    List.iter
      (fun a ->
        if Fragment.is_string_literal_ptr a then
          Hashtbl.replace st.exempt (strip_casts a).eid ())
      args

(* Unify the location [target] with every scalar of an initializer. *)
let rec init st target = function
  | SingleInit e -> join (pt st target) (ptee st e)
  | CompoundInit (_, l) -> List.iter (fun (_, i) -> init st target i) l

let analyse () : t =
  let st = create () in
  let file = Ast.get () in
  (* Create the variable locations in the order of the AST first, so that the
     representatives do not depend on the order the statements are visited. *)
  List.iter
    (function
      | GVar (vi, _, _) | GVarDecl (vi, _) -> ignore (var_node st vi)
      | GFun (fd, _) ->
          ignore (ret_node st fd.svar);
          List.iter (fun v -> ignore (var_node st v)) fd.sformals;
          List.iter (fun v -> ignore (var_node st v)) fd.slocals
      | _ -> ())
    file.globals;
  let func = ref "" in
  let visitor =
    object (self)
      inherit Visitor.frama_c_inplace

      method! vglob_aux g =
        (match g with
         | GVar (vi, { init = Some (CInit i) }, _) -> init st (var_node st vi) i
         | GFun (fd, _) -> func := fd.svar.vname
         | _ -> ());
        Cil.DoChildren

      method! vinst i =
        let sid = match self#current_stmt with Some s -> s.sid | None -> -1 in
        (match i with
         | Set (lv, e, _) -> join (pt st (loc_of st lv)) (ptee st e)
         | Call (ret, Var f, args, loc) -> call st ~sid ~func:!func ~loc ret f args
         | Local_init (v, ConsInit (f, args, Plain_func), loc) ->
             call st ~sid ~func:!func ~loc (Some (Cil.var v)) f args
         | Local_init (v, AssignInit i, _) -> init st (var_node st v) i
         | Local_init (_, ConsInit (_, _, Constructor), _)
         | Call (_, Mem _, _, _) | Asm _ | Skip _ | Code_annot _ -> ());
        Cil.DoChildren

      method! vstmt_aux s =
        (match (s.skind, self#current_func) with
         | Return (Some e, _), Some fd -> join (pt st (ret_node st fd.svar)) (ptee st e)
         | _ -> ());
        Cil.DoChildren

      method! vexpr e =
        (match e.enode with
         | (AddrOf (Var vi, _) | StartOf (Var vi, _))
           when not (Hashtbl.mem st.exempt e.eid) ->
             if not (Ast_types.is_fun vi.vtype) then
               Hashtbl.replace st.address_taken vi.vid vi
         | _ -> ());
        Cil.DoChildren
    end
  in
  (* The exempt literals are recorded when their call is visited, and the
     visitor reaches an instruction before the expressions inside it. *)
  Visitor.visitFramacFileSameGlobals visitor file;
  st
