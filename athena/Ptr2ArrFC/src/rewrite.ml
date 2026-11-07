(* Building the output program as a new Frama-C project.

   Contract: the functions here read the current project's AST and return a new
   project holding the output's AST; the current project is never modified, so
   the input stays available beside the output for the record and the checks.
   Each also returns the pairing of the copy's statements with the input's
   ([statement_pairs]), from which the record's source map is built.

   The identity transformation is the normalised program
   with the one front-end artefact the output must not contain removed: a
   variable-length array is allocated by a call to Frama-C's [__fc_vla_alloc]
   and released by [__fc_vla_free] at the end of its block. The identity output
   calls [alloca] instead and drops the release. For an execution with no
   undefined behaviour this preserves meaning: [alloca]'s block outlives the
   array's scope (it is released when the function returns), and a program that
   used the array after its scope ended already had undefined behaviour. *)

open Cil_types

let vla_alloc = "__fc_vla_alloc"
let vla_free = "__fc_vla_free"

(* In the current project: variable-length arrays allocated by [alloca], their
   release dropped. *)
let vla_to_alloca () =
      let file = Ast.get () in
      let drop_free =
        object
          inherit Visitor.frama_c_inplace

          method! vinst = function
            | Call (_, Var f, _, loc) when f.vname = vla_free ->
                Cil.ChangeTo [ Skip loc ]
            | _ -> Cil.SkipChildren
        end
      in
      Visitor.visitFramacFileSameGlobals drop_free file;
      file.globals <-
        List.filter
          (function
            | GFunDecl (_, vi, _) when vi.vname = vla_free -> false | _ -> true)
          file.globals;
      List.iter
        (function
          | GFunDecl (_, vi, _) when vi.vname = vla_alloc ->
              (* glibc's prototype, so that the declaration printed beside the
                 calls agrees with the compilers' built-in [alloca]. *)
              vi.vname <- "alloca";
              vi.vattr <- Ast_attributes.drop "FC_BUILTIN" vi.vattr
          | _ -> ())
        file.globals


(* The statements of the copy, each paired with the statement of the input it
   was copied from: (input sid, output sid). Taken right after the copy, before
   the transformation splits or adds statements; a statement it adds lies
   inside one of these, so the pairing names the input statement every output
   statement comes from. *)
let statement_pairs copier =
  let acc = ref [] in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vstmt_aux s =
        (try
           let o = Visitor_behavior.Get_orig.stmt copier#behavior s in
           acc := (o.sid, s.sid) :: !acc
         with Not_found -> ());
        Cil.DoChildren
    end
  in
  Visitor.visitFramacFileSameGlobals v (Ast.get ());
  List.rev !acc

(* A copy of the current project named [name], with the pairing of its
   statements with the input's ([statement_pairs]), taken before anything
   rewrites the copy. *)
let copy name =
  let copier = ref None in
  let prj =
    File.create_project_from_visitor name (fun prj ->
        let v = new Visitor.frama_c_copy prj in
        copier := Some (v :> Visitor.frama_c_visitor);
        v)
  in
  let pairs =
    Project.on prj (fun () -> match !copier with Some c -> statement_pairs c | None -> []) ()
  in
  (prj, pairs)

(* The normalised program; with the statement pairs. *)
let identity () =
  let prj, pairs = copy "ptr2arr_output" in
  Project.on prj vla_to_alloca ();
  (prj, pairs)

(* The pointer-replacing transformation: a copy of the input, transformed in
   place. Raises what [Transform.run] raises. *)
(* [wrap] is the --wrap-integers mode, if any; [check_overflow] adds the
   checks of signed overflow; [uninit] is the --uninit mode. They rewrite
   the copy before the transformation: the nondeterministic starting values
   first, so that the reductions reduce what their generators draw, then the
   checks, so that the reductions do not see them and the checks see the
   program's own operations only. [integers_auto] (--integers=auto, with
   whether the value analysis is used) replaces [wrap]: the scan runs where
   the reductions would, on the program they would rewrite, and either
   chooses the fixed-width reading (no reductions) or places them leaving
   out those it shows cannot change a value. *)
let transform ?(defunc = Defunc.none) ~size ?unbounded ?scalar_cells ~safety ?markers ?memtrack_check ?check_memtrack ?nonterminating ~wrap
    ?(check_overflow = false) ?(uninit = "keep") ?integers_auto () =
  let prj, pairs = copy "ptr2arr_output" in
  let ctx =
    Project.on prj
      (fun () ->
        (* the variables that start uninitialised, found before the passes
           below add their temporaries *)
        let uninit_targets =
          if uninit <> "check" then []
          else
            List.concat_map
              (function
                | Cil_types.GFun (fd, _) ->
                    List.map (fun t -> (fd.Cil_types.svar.vname, t)) (UninitTargets.targets fd)
                | _ -> [])
              (Ast.get ()).Cil_types.globals
        in
        let ust = if uninit = "nondet" then Some (Uninit.create ?fnid:defunc.fnid_type ()) else None in
        Option.iter Uninit.run ust;
        let ost = if check_overflow then Some (Overflow.create ()) else None in
        Option.iter Overflow.run ost;
        let wst =
          match integers_auto with
          | None -> Option.map (fun mode -> Wrap.create ~mode ()) wrap
          | Some eva -> (
              let scan = IntScan.run ~eva () in
              IntScan.last := Some scan;
              match scan.reading with
              | Bv -> None
              | Int -> Some (Wrap.create ~mode:Wrap.Unsigned ~scan ()))
        in
        Option.iter Wrap.run wst;
        let ctx =
          Transform.run ~size ?unbounded ?scalar_cells ~safety ?markers ?memtrack_check ?check_memtrack ?nonterminating
            ?wrap:(Option.map Wrap.fn wst) ?bad_call:defunc.bad_call ~uninit ~uninit_targets ()
        in
        (* the temporaries of the calls through function pointers *)
        if defunc.temps <> [] then
          List.iter
            (function
              | Cil_types.GFun (fd, _) ->
                  List.iter
                    (fun (v : Cil_types.varinfo) ->
                      if List.mem (fd.svar.vname, v.vname) defunc.temps then
                        Hashtbl.replace ctx.Transform.roles v.vid "generated")
                    fd.slocals
              | _ -> ())
            (Ast.get ()).Cil_types.globals;
        Option.iter
          (fun w ->
            Wrap.finish w;
            List.iter
              (fun v -> Hashtbl.replace ctx.Transform.roles v.Cil_types.vid "generated")
              (Wrap.created w))
          wst;
        Option.iter
          (fun o ->
            Overflow.finish o;
            List.iter
              (fun v -> Hashtbl.replace ctx.Transform.roles v.Cil_types.vid "generated")
              (Overflow.created o);
            Option.iter
              (fun v -> Hashtbl.replace ctx.Transform.roles v.Cil_types.vid "program")
              (Overflow.renamed o);
            Option.iter
              (fun v ->
                Hashtbl.replace ctx.Transform.roles v.Cil_types.vid "marker";
                ctx.Transform.overflow_marker <- Some v)
              (Overflow.marker o))
          ost;
        Option.iter
          (fun u ->
            List.iter
              (fun v -> Hashtbl.replace ctx.Transform.roles v.Cil_types.vid "generated")
              (Uninit.created u);
            ctx.Transform.uninit_generators <- Uninit.generators u;
            ctx.Transform.uninit_targets <-
              List.map
                (fun (v, func, leaves, placed) ->
                  { Transform.u_name = v.Cil_types.vorig_name; u_var = v.vname; u_func = func;
                    u_loc = v.vdecl;
                    u_leaves = leaves; u_placed = List.map Uninit.placement_name placed;
                    u_checked = None })
                (Uninit.targets u))
          ust;
        ctx)
      ()
  in
  (prj, pairs, ctx)

(* The input instrumented with the region monitor; with the statement
   pairs. *)
let monitor () =
  let prj, pairs = copy "ptr2arr_monitor" in
  (* The cleanup first: the instrumentation adds declarations of its runtime
     that the kernel's function table does not know, and a visit of the whole
     file after that stops on them. *)
  Project.on prj
    (fun () ->
      vla_to_alloca ();
      Monitor.run ())
    ();
  (prj, pairs)

(* An output of --wrap-integers, run as in the mathematical reading; with the
   statement pairs. *)
let zreading () =
  let prj, pairs = copy "ptr2arr_zreading" in
  Project.on prj Zreading.run ();
  (prj, pairs)
