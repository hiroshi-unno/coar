(* A measurement instrument: binary interpolation queries written to files,
   one per query, and read back, so that a replay can ask the same queries
   of other leaf procedures in one process.  Nothing is written unless
   COAR_INTERP_DUMP_DIR names a directory.

   A file is an SMT-LIB script:
     ; coar interpolation query
     ; source: <the command line's last argument>
     ; args: a0:Int a1:Real ...
     (declare-fun a0 () Int) ...
     (assert <phi1>)
     (assert <phi2>)
   Every free variable is renamed first ([a<i>] for the shared arguments in
   their order, [v<i>] for the others), so that the names Z3 prints are the
   names read back.  Only quantifier-free queries over Bool, Int and Real
   variables are written, the formulas printed by Z3 from the tree's own
   encoding; any other query is counted in [<dir>/skipped.txt] with the
   reason, one line each.

   Contract of the pair.  [read (file of record args phi1 phi2)] is
   [(args', phi1', phi2', source)] with [args'] the renamed arguments, and [phi1'],
   [phi2'] equivalent to the renamed [phi1], [phi2] (Z3's printer may share
   subterms by [let] and fold constants, so the text is not the input's). *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let dir = Lazy.from_val (Sys.getenv "COAR_INTERP_DUMP_DIR")
let counter = ref 0

let sort_name s =
  if Term.is_int_sort s then Some "Int"
  else if Term.is_real_sort s then Some "Real"
  else if Term.is_bool_sort s then Some "Bool"
  else None

let skip d reason =
  Out_channel.with_file ~append:true (Filename.concat d "skipped.txt")
    ~f:(fun oc -> fprintf oc "%s\n" reason)

(* [record args phi1 phi2]: the query written to a new file of the dump
   directory, when there is one.  Never raises but an asynchronous
   exception; a failure to write is counted as a skip. *)
let record args phi1 phi2 =
  match Lazy.force dir with
  | None -> ()
  | Some d -> (
      try
        if
          not
            (Formula.is_quantifier_free phi1 && Formula.is_quantifier_free phi2)
        then skip d "quantified"
        else
          let env =
            Set.to_list
              (Set.diff
                 (Set.union
                    (Formula.term_sort_env_of phi1)
                    (Formula.term_sort_env_of phi2))
                 (Set.Poly.of_list args))
          in
          let all = args @ env in
          if List.exists all ~f:(fun (_, s) -> Option.is_none (sort_name s))
          then skip d "sort"
          else
            let renamed =
              List.mapi args ~f:(fun i (x, s) ->
                  (x, (Ident.Tvar (sprintf "a%d" i), s)))
              @ List.mapi env ~f:(fun i (x, s) ->
                  (x, (Ident.Tvar (sprintf "v%d" i), s)))
            in
            let sub =
              Map.Poly.of_alist_exn
                (List.map renamed ~f:(fun (x, (y, s)) -> (x, Term.mk_var y s)))
            in
            let phi1 = Formula.subst sub phi1
            and phi2 = Formula.subst sub phi2 in
            let ctx = Z3.mk_context [] in
            let dtenv =
              Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx Map.Poly.empty
            in
            (* encoded with no bound-variable environment, so that every
               free variable is a Z3 constant printed by its name (with the
               variables as an environment, Z3 prints de Bruijn indices,
               which no reader takes back) *)
            let str phi =
              Z3.Expr.to_string
              @@ Z3Smt.Z3interface.of_formula ~id:None ctx [] [] Map.Poly.empty
                   dtenv phi
            in
            let s1 = str phi1 and s2 = str phi2 in
            let decl (_, (y, s)) =
              sprintf "(declare-fun %s () %s)" (Ident.name_of_tvar y)
                (Option.value_exn (sort_name s))
            in
            let args_line =
              String.concat ~sep:" "
                (List.filteri renamed ~f:(fun i _ -> i < List.length args)
                |> List.map ~f:(fun (_, (y, s)) ->
                    sprintf "%s:%s" (Ident.name_of_tvar y)
                      (Option.value_exn (sort_name s))))
            in
            incr counter;
            let file =
              Filename.concat d
                (sprintf "q%d_%06d.smt2"
                   (Core_unix.getpid () |> Pid.to_int)
                   !counter)
            in
            let argv = Sys.get_argv () in
            Out_channel.with_file file ~f:(fun oc ->
                fprintf oc
                  "; coar interpolation query\n; source: %s\n; args: %s\n"
                  (if Array.is_empty argv then ""
                   else argv.(Array.length argv - 1))
                  args_line;
                List.iter renamed ~f:(fun r -> fprintf oc "%s\n" (decl r));
                fprintf oc "(assert %s)\n(assert %s)\n" s1 s2)
      with exn when not (Common.Timer.is_async exn) ->
        skip d ("error " ^ Exn.to_string exn))

(* [read file]: the query of a file [record] wrote: the shared arguments,
   [phi1], [phi2] and the source line.  Raises on a file of another
   shape. *)
let read file =
  let text = In_channel.read_all file in
  let lines = String.split_lines text in
  let field prefix =
    List.find_map lines ~f:(String.chop_prefix ~prefix)
    |> Option.value ~default:""
  in
  let sort_of = function
    | "Int" -> T_int.SInt
    | "Real" -> T_real.SReal
    | "Bool" -> T_bool.SBool
    | s -> failwith ("QueryDump.read: sort " ^ s)
  in
  let args =
    String.split (field "; args: ") ~on:' '
    |> List.filter ~f:(Fn.non String.is_empty)
    |> List.map ~f:(fun a ->
        match String.lsplit2 a ~on:':' with
        | Some (x, s) -> (Ident.Tvar x, sort_of s)
        | None -> failwith ("QueryDump.read: argument " ^ a))
  in
  let ctx = Z3.mk_context [] in
  let dtenv = Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx Map.Poly.empty in
  let asserts =
    Z3.AST.ASTVector.to_expr_list
      (Z3.SMT.parse_smtlib2_string ctx text [] [] [] [])
  in
  match asserts with
  | [ e1; e2 ] ->
      let dec e = Z3Smt.Z3interface.formula_of ctx [] [] dtenv e in
      (args, dec e1, dec e2, field "; source: ")
  | l -> failwith (sprintf "QueryDump.read: %d assertions" (List.length l))
