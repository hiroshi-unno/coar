(* Models of the external functions that call a function the program gives
   them: qsort and bsearch (C11 7.22.5).  Passing a function pointer to an
   external function is outside the fragment, since the external function
   runs the program's code at points the transformation cannot see.  For
   these two the points are known: the comparison function is called on
   elements of the array (and, for bsearch, the key), and nothing else.

   Before function pointers are made function numbers, each call is
   replaced by a call to a function added to the program, specialised to the
   element type, that calls the comparison function through its pointer.
   The defunctionalization then turns that call into its test of function
   numbers, as for any call through a pointer, and the rest of the
   transformation reads and writes the elements as the program does.

   What each model does:

   - qsort(base, n, size, cmp): an insertion sort by adjacent exchanges.
     Element j moves left past element j-1 while cmp(&base[j-1], &base[j])
     is positive; when it is 0 the model chooses arbitrarily whether to move
     on.  C leaves the order of elements that compare equal unspecified
     (7.22.5.2p4), and a comparison function that is not consistent with a
     total preorder makes the behaviour undefined (7.22.5p4), so the results
     C allows are exactly the arrangements of the elements sorted by cmp in
     which each run of equal elements is in any order.  Inserting each
     element at an arbitrary place within its run reaches every such
     arrangement, and only those.
   - bsearch(key, base, n, size, cmp): compares the key with every element,
     in order, and returns a pointer to one of the elements that compare
     equal to it, chosen arbitrarily, or NULL when none does.  C lets it
     return any matching element (7.22.5.1p4) and requires the array to be
     partitioned by the key, so the matching elements are exactly those
     with cmp 0.

   The sequence of comparisons differs from any library's: the models
   preserve the results on the assumption that the comparison function has
   no effect but its result and returns for every pair of elements (and
   the key).  A model reads every element bsearch's binary search may read
   and more; C requires the whole array to be valid (7.22.5p1, 7.1.4).

   A call is modelled only when the element type is known: the base
   argument, under its casts, is a pointer to a complete object type that is
   not an array, a function or void (or the address of an array of such
   elements, read as its first element's), and the size argument is a constant
   equal to that type's size; for qsort the type must not be const.  Any
   other call is left as it is, and the fragment check refuses it as
   before.

   Contract: [run ()] rewrites the current project in place and returns
   the number of calls replaced; it adds one function per external function
   and element type.  It must run before the function pointers are made
   numbers. *)

open Cil_types

let loc0 = Fileloc.unknown

type plan =
  | Qsort of typ * exp * exp * exp  (** element type, base, n, cmp *)
  | Bsearch of typ * exp * exp * exp * exp  (** element type, key, base, n, cmp *)

(* The element type of a call's array: the type the base argument points
   to under its casts, when [size] is a constant equal to its size. *)
let element ~writes base size =
  let b = LibModels.strip_casts base in
  match Ast_types.unroll_node (Cil.typeOf b) with
  | TPtr t -> (
      match (Ast_types.unroll_node t, b.enode) with
      | TArray (et, _), AddrOf lv -> (
          (* the address of an array: its elements *)
          match Ast_types.unroll_node et with
          | TVoid | TFun _ | TArray _ -> None
          | _ when not (Cil.isCompleteType et) -> None
          | _ when writes && Ast_types.is_const et -> None
          | _ -> (
              match Cil.isInteger (Cil.constFold true size) with
              | Some z when Z.equal z (Z.of_int (Cil.bytesSizeOf et)) ->
                  Some (et, Cil.new_exp ~loc:b.eloc (StartOf lv))
              | _ -> None))
      | (TVoid | TFun _ | TArray _), _ -> None
      | _ when not (Cil.isCompleteType t) -> None
      | _ when writes && Ast_types.is_const t -> None
      | _ -> (
          match Cil.isInteger (Cil.constFold true size) with
          | Some z when Z.equal z (Z.of_int (Cil.bytesSizeOf t)) -> Some (t, b)
          | _ -> None))
  | _ -> None

let plan_of f args =
  if Fragment.is_defined f then None
  else
    match (f.vname, args) with
    | "qsort", [ base; n; size; cmp ] ->
        Option.map (fun (t, b) -> Qsort (t, b, n, cmp)) (element ~writes:true base size)
    | "bsearch", [ key; base; n; size; cmp ] ->
        Option.map (fun (t, b) -> Bsearch (t, key, b, n, cmp)) (element ~writes:false base size)
    | _ -> None

let key = function
  | Qsort (t, _, _, _) -> Format.asprintf "qsort:%a" Cil_datatype.Typ.pretty t
  | Bsearch (t, _, _, _, _) -> Format.asprintf "bsearch:%a" Cil_datatype.Typ.pretty t

let args_of = function
  | Qsort (_, b, n, cmp) -> [ b; n; cmp ]
  | Bsearch (_, k, b, n, cmp) -> [ k; b; n; cmp ]

(* The type the external function's prototype gives its [i]th parameter,
   or [default]. *)
let param_type f i default =
  match Ast_types.unroll_node f.vtype with
  | TFun (_, Some ps, _) when List.length ps > i ->
      let _, t, _ = List.nth ps i in
      t
  | _ -> default

let const_void_ptr = Cil_const.mk_tptr (Cil_const.mk_tvoid ~tattr:[ ("const", []) ] ())

(* int ( * )(const void *, const void * ), the comparison function's type
   when the external function has no prototype. *)
let default_cmp_type =
  Cil_const.mk_tptr
    (Cil_const.mk_tfun Cil_const.intType
       (Some [ ("", const_void_ptr, []); ("", const_void_ptr, []) ])
       false)

let size_type = Cil_const.ulongType

let run () =
  let file = Ast.get () in
  let plans = Hashtbl.create 8 in
  let collect =
    object (self)
      inherit Visitor.frama_c_inplace

      method! vinst i =
        (match i with
         | Call (_, Var f, args, _) | Local_init (_, ConsInit (f, args, Plain_func), _) -> (
             match plan_of f args with
             | Some p -> Option.iter (fun st -> Hashtbl.replace plans st.sid (f, p)) self#current_stmt
             | None -> ())
         | _ -> ());
        Cil.SkipChildren
    end
  in
  Visitor.visitFramacFileSameGlobals collect file;
  if Hashtbl.length plans = 0 then 0
  else begin
    let added = ref [] in
    let given = Hashtbl.create 8 in
    let fresh base =
      let rec go k =
        let n =
          Defunc.fresh_global_name file (if k = 0 then base else Printf.sprintf "%s_%d" base k)
        in
        if Hashtbl.mem given n then go (k + 1) else (Hashtbl.replace given n (); n)
      in
      go 0
    in
    let nondet_int =
      lazy
        (match LibModels.find_function file "__VERIFIER_nondet_int" with
         | Some vi -> vi
         | None ->
             let ft = Cil_const.mk_tfun Cil_const.intType (Some []) false in
             let vi = Cil.makeGlobalVar "__VERIFIER_nondet_int" ft in
             Cil.setFormalsDecl vi ft;
             let spec = Cil.empty_funspec () in
             added := GFunDecl (spec, vi, loc0) :: !added;
             Globals.Functions.replace_by_declaration spec vi loc0;
             vi)
    in
    let stmt, set, call, ret, if_, bin, int, ev, while_ =
      LibModels.(stmt, set, call, ret, if_, bin, int, ev, while_)
    in
    let brk () = Cil.mkStmt ~valid_sid:true (Break loc0) in
    (* the comparison through the pointer [cmp], its arguments converted to
       the parameter types of [cmp]'s type *)
    let cmp_call r cmp a b =
      let ps =
        match Ast_types.unroll_node (Cil.typeOf cmp) with
        | TPtr ft -> (
            match Ast_types.unroll_node ft with
            | TFun (_, Some [ (_, ta, _); (_, tb, _) ], _) -> [ ta; tb ]
            | _ -> [ const_void_ptr; const_void_ptr ])
        | _ -> [ const_void_ptr; const_void_ptr ]
      in
      stmt
        (Call
           ( Some r,
             Mem cmp,
             List.map2 (fun e t -> Cil.mkCast ~newt:t e) [ a; b ] ps,
             loc0 ))
    in
    let ptr_at p i = Cil.new_exp ~loc:loc0 (BinOp (PlusPI, p, i, Cil.typeOf p)) in
    let helpers = Hashtbl.create 8 in
    let helper (f : varinfo) p =
      let k = key p in
      match Hashtbl.find_opt helpers k with
      | Some vi -> vi
      | None ->
          let rty =
            match Ast_types.unroll_node f.vtype with
            | TFun (r, _, _) -> r
            | _ -> Cil_const.voidType
          in
          let fd =
            Cil.emptyFunction (fresh (match p with Qsort _ -> "__p2a_qsort" | Bsearch _ -> "__p2a_bsearch"))
          in
          let formals =
            match p with
            | Qsort (t, _, _, _) ->
                [ ("base", Cil_const.mk_tptr t); ("n", param_type f 1 size_type);
                  ("cmp", param_type f 3 default_cmp_type) ]
            | Bsearch (t, _, _, _, _) ->
                [ ("key", param_type f 0 const_void_ptr); ("base", Cil_const.mk_tptr t);
                  ("n", param_type f 2 size_type); ("cmp", param_type f 4 default_cmp_type) ]
          in
          Cil.update_var_type fd.svar
            (Cil_const.mk_tfun rty (Some (List.map (fun (n, t) -> (n, t, [])) formals)) false);
          let fv = List.map (fun (n, t) -> Cil.makeFormalVar fd n t) formals in
          let local n t = Cil.makeLocalVar fd n t in
          let body =
            match (p, fv) with
            | Qsort (t, _, _, _), [ base; n; cmp ] ->
                let nt = Cil.typeOf (ev n) in
                let i = local "i" nt and j = local "j" nt in
                let c = local "c" Cil_const.intType and d = local "d" Cil_const.intType in
                let tmp = local "tmp" t in
                let prev () = Cil.mkMem ~addr:(ptr_at (ev base) (bin MinusA (ev j) (Cil.mkCast ~newt:nt (int 1)))) ~off:NoOffset in
                let cur () = Cil.mkMem ~addr:(ptr_at (ev base) (ev j)) ~off:NoOffset in
                let lv e = Cil.new_exp ~loc:loc0 (Lval e) in
                [ set (Cil.var i) (int 1);
                  while_ (bin Lt (ev i) (ev n))
                    [ set (Cil.var j) (ev i);
                      while_ (int 1)
                        [ if_ (bin Eq (ev j) (Cil.mkCast ~newt:nt (int 0))) [ brk () ] [];
                          cmp_call (Cil.var c) (ev cmp)
                            (ptr_at (ev base) (bin MinusA (ev j) (Cil.mkCast ~newt:nt (int 1))))
                            (ptr_at (ev base) (ev j));
                          if_ (bin Lt (ev c) (int 0)) [ brk () ] [];
                          (* equal: either place within the run *)
                          if_ (bin Eq (ev c) (int 0))
                            [ call (Some (Cil.var d)) (Lazy.force nondet_int) [];
                              if_ (bin Eq (ev d) (int 0)) [ brk () ] [] ]
                            [];
                          set (Cil.var tmp) (lv (prev ()));
                          set (prev ()) (lv (cur ()));
                          set (cur ()) (ev tmp);
                          set (Cil.var j) (bin MinusA (ev j) (Cil.mkCast ~newt:nt (int 1))) ];
                      set (Cil.var i) (bin PlusA (ev i) (Cil.mkCast ~newt:nt (int 1))) ];
                  ret None ]
            | Bsearch _, [ key; base; n; cmp ] ->
                let nt = Cil.typeOf (ev n) in
                let i = local "i" nt in
                let c = local "c" Cil_const.intType and d = local "d" Cil_const.intType in
                let r = local "r" rty in
                let null = Cil.mkCast ~newt:rty (int 0) in
                [ set (Cil.var r) null;
                  set (Cil.var i) (int 0);
                  while_ (bin Lt (ev i) (ev n))
                    [ cmp_call (Cil.var c) (ev cmp) (ev key) (ptr_at (ev base) (ev i));
                      if_ (bin Eq (ev c) (int 0))
                        [ if_ (bin Eq (ev r) null)
                            [ set (Cil.var r) (ptr_at (ev base) (ev i)) ]
                            (* another match: either one *)
                            [ call (Some (Cil.var d)) (Lazy.force nondet_int) [];
                              if_ (bin Ne (ev d) (int 0)) [ set (Cil.var r) (ptr_at (ev base) (ev i)) ] [] ] ]
                        [];
                      set (Cil.var i) (bin PlusA (ev i) (Cil.mkCast ~newt:nt (int 1))) ];
                  ret (Some (ev r)) ]
            | _ -> assert false
          in
          fd.sbody.bstmts <- body;
          added := GFun (fd, loc0) :: !added;
          Globals.Functions.replace_by_definition (Cil.empty_funspec ()) fd loc0;
          Cfg.cfgFun fd;
          Hashtbl.replace helpers k fd.svar;
          fd.svar
    in
    let calls = Hashtbl.create 8 in
    Hashtbl.iter
      (fun sid (f, p) ->
        let h = helper f p in
        let formals =
          match Ast_types.unroll_node h.vtype with
          | TFun (_, Some fs, _) -> List.map (fun (_, t, _) -> t) fs
          | _ -> []
        in
        let args = List.map2 (fun a t -> Cil.mkCast ~newt:t a) (args_of p) formals in
        Hashtbl.replace calls sid (h, args))
      plans;
    file.globals <- Defunc.insert_before_functions (List.rev !added) file.globals;
    let rewrite =
      object (self)
        inherit Visitor.frama_c_inplace

        method! vinst i =
          match match self#current_stmt with Some s -> Hashtbl.find_opt calls s.sid | None -> None with
          | None -> Cil.SkipChildren
          | Some (h, args) -> (
              match i with
              | Call (r, _, _, loc) -> Cil.ChangeTo [ Call (r, Var h, args, loc) ]
              | Local_init (v, ConsInit (_, _, k), loc) ->
                  Cil.ChangeTo [ Local_init (v, ConsInit (h, args, k), loc) ]
              | _ -> Cil.SkipChildren)
      end
    in
    let helper_ids = Hashtbl.fold (fun _ vi acc -> vi.vid :: acc) helpers [] in
    List.iter
      (function
        | GFun (fd, _) when not (List.mem fd.svar.vid helper_ids) ->
            ignore (Visitor.visitFramacFunction rewrite fd)
        | _ -> ())
      file.globals;
    Fragment.mark_ast_changed ();
    Hashtbl.length plans
  end
