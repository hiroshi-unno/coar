(* A string literal reaching an external function through a local variable
   that holds nothing else, as CIL's temporaries do:
   [__cil_tmp1 = "bob: %d\n"; printf(__cil_tmp1, bob);] (the SV-COMP
   product-lines tasks).  A pointer other than a string literal passed to an
   external function is outside the fragment, and the variable is such a
   pointer although the value it passes is the literal.

   Before the fragment check, such an argument is replaced by the literal.
   The variable qualifies when it is a local (not a parameter) of pointer
   type whose address is never taken, it is written exactly once in its
   function, by an assignment or an initialiser whose value is a string
   literal, and that write strictly dominates the call.  Then at the call
   the variable holds the literal's pointer on every path, so the argument's
   value does not change; and a read the write does not dominate (an
   indeterminate pointer) is never replaced, so nothing the input does is
   hidden.  Only the arguments of calls to functions without a body are
   rewritten; the write stays, and the transformation treats it as any
   other assignment of a literal. *)

open Cil_types

(* The literal a write of [v] stores, with the statement holding it. *)
type write = { stmt : stmt; value : exp option (* Some literal, None otherwise *) }

let literal_of e = if Fragment.is_string_literal_ptr e then Some e else None

(* The qualifying variables of [fd]: vid -> (statement of the write, literal). *)
let candidates fd =
  let writes : (int, write list) Hashtbl.t = Hashtbl.create 8 in
  let taken = Hashtbl.create 8 in
  let add v w =
    Hashtbl.replace writes v.vid (w :: Option.value ~default:[] (Hashtbl.find_opt writes v.vid))
  in
  let v =
    object (self)
      inherit Visitor.frama_c_inplace

      method! vinst i =
        let stmt = Option.get self#current_stmt in
        (match i with
         | Set ((Var v, NoOffset), e, _) -> add v { stmt; value = literal_of e }
         | Set ((Var v, _), _, _) -> add v { stmt; value = None }
         | Local_init (v, AssignInit (SingleInit e), _) -> add v { stmt; value = literal_of e }
         | Local_init (v, _, _) -> add v { stmt; value = None }
         | Call (Some (Var v, _), _, _, _) -> add v { stmt; value = None }
         | _ -> ());
        Cil.DoChildren

      method! vexpr e =
        (match e.enode with
         | AddrOf (Var v, _) | StartOf (Var v, _) -> Hashtbl.replace taken v.vid ()
         | _ -> ());
        Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacFunction v fd);
  let result = Hashtbl.create 8 in
  List.iter
    (fun vi ->
      if Ast_types.is_ptr vi.vtype && not (Hashtbl.mem taken vi.vid) then
        match Hashtbl.find_opt writes vi.vid with
        | Some [ { stmt; value = Some lit } ] -> Hashtbl.replace result vi.vid (stmt, lit)
        | _ -> ())
    fd.slocals;
  result

(* Replaces the qualifying arguments of the external calls; the number of
   arguments replaced. *)
let run () =
  let file = Ast.get () in
  let count = ref 0 in
  List.iter
    (function
      | GFun (fd, _) ->
          let cands = candidates fd in
          if Hashtbl.length cands > 0 then begin
            let kf = Globals.Functions.get fd.svar in
            Dominators.compute_dominators kf;
            let rec replace stmt e =
              match e.enode with
              | CastE (t, e') -> (
                  match replace stmt e' with
                  | Some e'' -> Some (Cil.new_exp ~loc:e.eloc (CastE (t, e'')))
                  | None -> None)
              | Lval (Var v, NoOffset) -> (
                  match Hashtbl.find_opt cands v.vid with
                  | Some (w, lit) when Dominators.strictly_dominates w stmt ->
                      Some (Cil.copy_exp lit)
                  | _ -> None)
              | _ -> None
            in
            let rewrite =
              object (self)
                inherit Visitor.frama_c_inplace

                method! vinst i =
                  match i with
                  | Call (r, (Var f as fv), args, loc) when not (Fragment.is_defined f) ->
                      let stmt = Option.get self#current_stmt in
                      let changed = ref false in
                      let args =
                        List.map
                          (fun a ->
                            match replace stmt a with
                            | Some a' -> changed := true; incr count; a'
                            | None -> a)
                          args
                      in
                      if !changed then Cil.ChangeTo [ Call (r, fv, args, loc) ]
                      else Cil.SkipChildren
                  | _ -> Cil.SkipChildren
              end
            in
            ignore (Visitor.visitFramacFunction rewrite fd)
          end
      | _ -> ())
    file.globals;
  if !count > 0 then Fragment.mark_ast_changed ();
  !count
