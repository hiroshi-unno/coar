(* Translation of a HORS problem with finite data and a trivial tree automaton
   (the dialect TRecS reads) into an equivalent one without finite data and
   with an alternating tree automaton (the dialect HorSat2 reads).

   [convert p] requires an [RSFD] whose automaton is a [TTA], and answers an
   [RSFD] whose automaton is an [ATA], whose rules contain no [Fd], [Case] or
   [CaseFd], and whose value tree is the value tree of [p], so that the two
   problems have the same answer.  Two translations make it so:

   - The automaton.  A trivial automaton accepts a tree when some run labels
     every node with a state such that each node [a t1 ... tn] in state [q]
     uses a transition [q a -> q1 ... qn] and each [ti] is in state [qi]; a
     node with no transition is rejected, and every infinite path is
     accepted.  That is the alternating automaton with, for each [q] and [a],
     the disjunction over the transitions [q a -> q1 ... qn] of the
     conjunctions [(1,q1) /\ ... /\ (n,qn)], an empty conjunction being
     [true] and an empty disjunction [false], read under the same trivial
     acceptance condition.  The [br] symbol of a generated problem is an
     ordinary terminal here, with the transitions [q br -> q q] the reduction
     writes, so both of its children must be accepted, as TRecS checks them.
   - The finite data.  With [n] data values (the states of the problem's
     input automaton), a data value [i] becomes the selector
     [Fd_i y1 ... yn -> yi] and [_case n x t1 ... tn] becomes [x t1 ... tn]:
     the data sort becomes [o -> ... -> o -> o] ([n] arrows).  A case on a
     known value [i] is its [i]-th branch.  Every step is a reduction of the
     scheme, so the value tree is unchanged.  The branches of a case on a
     variable must be trees (sort [o]), which is what an EHMTT's reduction
     produces: its type system gives every [case] the output-tree type, and
     the reduction joins a branch's alternatives with [br].  A case of a
     higher sort would need eta-expansion into a fresh non-terminal before
     the encoding; it is refused instead.

   Every name the translation introduces is fresh: it differs from every
   non-terminal, rule parameter, terminal and automaton state of [p] and from
   every other introduced name.

   The sorts are inferred by unification: [o] for trees, a data sort for a
   value and a case's scrutinee, a terminal's arity from the automaton's
   transitions where it has any.  A sort left unconstrained is [o].  The
   ranks section lists every terminal of the rules and of the automaton.
   Raises [Failure] when the problem is not of that dialect, when its rules
   are not simply sorted, when a terminal is given two arities, or when a
   case on a variable has branches of a higher sort. *)
open Core
open Ast
open Automata
open SimpleSort

(* A term annotated with the sort of every case, which the translation
   needs once the whole problem has been sorted. *)
type aterm =
  | AFd of int
  | ANt of Ident.tvar
  | AVar of Ident.tvar
  | ATerm of Ident.tvar
  | AApp of aterm * aterm
  | ACase of [ `Var of Ident.tvar | `Fd of int ] * aterm list * sort

let index_of_fd (trs : TTA.trs) = function
  | Either.Second idx -> idx
  | First id -> (
      match
        List.find_mapi trs ~f:(fun i (s, _) ->
            if String.equal (Ident.name_of_tvar id) s then Some i else None)
      with
      | Some idx -> idx
      | None -> failwithf "unknown data value %s" (Ident.name_of_tvar id) ())

let convert = function
  | Problem.RSFD (trs_in, rules, TreeAutomaton.TTA trs_out) ->
      let n = List.length trs_in in
      let nts = Hashtbl.create (module String) in
      let terms = Hashtbl.create (module String) in
      let sort_of tbl id =
        Hashtbl.find_or_add tbl (Ident.name_of_tvar id) ~default:fresh
      in
      (* the automaton fixes the arity of every terminal it reads *)
      List.iter trs_out ~f:(fun (_q, body) ->
          List.iter body ~f:(fun (a, qs) ->
              unify (sort_of terms (Ident.Tvar a)) (tree_sort (List.length qs))));
      let rec infer env = function
        | RSFD.Fd id -> (AFd (index_of_fd trs_in id), D)
        | Nonterm id -> (ANt id, sort_of nts id)
        | Term id -> (ATerm id, sort_of terms id)
        | Var id -> (
            match List.Assoc.find ~equal:Ident.tvar_equal env id with
            | Some s -> (AVar id, s)
            | None -> failwithf "unbound variable %s" (Ident.name_of_tvar id) ()
            )
        | App (t1, t2) ->
            let a1, s1 = infer env t1 in
            let a2, s2 = infer env t2 in
            let r = fresh () in
            unify s1 (Arr (s2, r));
            (AApp (a1, a2), r)
        | (Case (_, ts) | CaseFd (_, ts)) as t ->
            if List.length ts <> n then
              failwithf "a case with %d branches over %d data values"
                (List.length ts) n ();
            let scrut =
              match t with
              | Case (x, _) ->
                  (match List.Assoc.find ~equal:Ident.tvar_equal env x with
                  | Some s -> unify s D
                  | None ->
                      failwithf "unbound variable %s" (Ident.name_of_tvar x) ());
                  `Var x
              | CaseFd (id, _) -> `Fd (index_of_fd trs_in id)
              | _ -> assert false
            in
            let r = fresh () in
            let ats =
              List.map ts ~f:(fun t ->
                  let a, s = infer env t in
                  unify s r;
                  a)
            in
            (ACase (scrut, ats, r), r)
      in
      let arules =
        List.map rules ~f:(fun (id, (xs, t)) ->
            let env = List.map xs ~f:(fun x -> (x, fresh ())) in
            unify (sort_of nts id)
              (List.fold_right env ~init:O ~f:(fun (_, s) acc -> Arr (s, acc)));
            let a, s = infer env t in
            unify s O;
            (id, (xs, a)))
      in
      (* a terminal builds a tree from trees *)
      Hashtbl.iteri terms ~f:(fun ~key ~data ->
          let rec check s =
            match repr s with
            | Arr (a, b) ->
                (match repr a with
                | V _ -> unify a O
                | O -> ()
                | _ -> failwithf "terminal %s takes a non-tree argument" key ());
                check b
            | V _ -> unify s O
            | O -> ()
            | D -> failwithf "terminal %s is used as a data value" key ()
          in
          check data);
      (* Every name the translation introduces (the selectors' non-terminals
         and their parameters) is drawn to avoid every
         name the problem spells -- its non-terminals, the parameters of its
         rules, its terminals and the automaton's states -- and every name
         drawn before it, since a minted name equal to an input name would
         make two symbols one. *)
      let taken = Hash_set.create (module String) in
      List.iter rules ~f:(fun (id, (xs, _)) ->
          Hash_set.add taken (Ident.name_of_tvar id);
          List.iter xs ~f:(fun x -> Hash_set.add taken (Ident.name_of_tvar x)));
      Hashtbl.iter_keys nts ~f:(Hash_set.add taken);
      Hashtbl.iter_keys terms ~f:(Hash_set.add taken);
      List.iter trs_out ~f:(fun (q, body) ->
          Hash_set.add taken q;
          List.iter body ~f:(fun (_, qs) ->
              List.iter qs ~f:(Hash_set.add taken)));
      let mint prefix =
        let v =
          Ident.mk_fresh_tvar_avoiding ~prefix
            ~taken:(fun v -> Hash_set.mem taken (Ident.name_of_tvar v))
            ()
        in
        Hash_set.add taken (Ident.name_of_tvar v);
        v
      in
      let fd_names = Hashtbl.create (module Int) in
      let extra = ref [] in
      (* drawn one after another, so that the [j]-th parameter is the [j]-th
         name drawn *)
      let ys =
        lazy
          (List.rev
             (List.fold (List.range 0 n) ~init:[] ~f:(fun acc _ ->
                  mint "fd__y" :: acc)))
      in
      let fd_value i =
        RSFD.Nonterm
          (Hashtbl.find_or_add fd_names i ~default:(fun () ->
               let name = mint "FdVal__" in
               let ys = Lazy.force ys in
               extra := (name, (ys, RSFD.Var (List.nth_exn ys i))) :: !extra;
               name))
      in
      let rec tr = function
        | AFd i -> fd_value i
        | ANt id -> RSFD.Nonterm id
        | AVar id -> RSFD.Var id
        | ATerm id -> RSFD.Term id
        | AApp (a1, a2) -> RSFD.App (tr a1, tr a2)
        | ACase (`Fd i, ats, _) -> tr (List.nth_exn ats i)
        | ACase (`Var x, ats, s) ->
            if arity s <> 0 then
              failwith "a case whose branches are not trees (a higher sort)";
            RSFD.apps (RSFD.Var x) (List.map ats ~f:tr)
      in
      let rules' = List.map arules ~f:(fun (id, (xs, a)) -> (id, (xs, tr a))) in
      let rules' = rules' @ List.rev !extra in
      let ranks =
        Hashtbl.to_alist terms
        |> List.map ~f:(fun (a, s) -> (a, arity s))
        |> List.sort ~compare:(fun (a, _) (b, _) -> String.compare a b)
      in
      let ata =
        List.map trs_out ~f:(fun (q, body) ->
            let syms =
              List.dedup_and_sort ~compare:String.compare (List.map body ~f:fst)
            in
            ( q,
              List.map syms ~f:(fun a ->
                  ( a,
                    List.filter_map body ~f:(fun (a', qs) ->
                        if String.equal a a' then
                          Some (List.mapi qs ~f:(fun i q' -> (i + 1, q')))
                        else None) )) ))
      in
      Problem.RSFD (trs_in, rules', TreeAutomaton.ATA (ranks, ata))
  | p ->
      failwithf "not a problem with a trivial tree automaton: it specifies %s"
        (Problem.dialect_str_of p) ()
