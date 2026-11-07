(* Translation of a HORS problem with an alternating tree automaton (the
   dialect HorSat2 reads) into an equivalent one with a trivial tree automaton
   (the dialect TRecS reads), the inverse of [TrivialToAlternating] on the
   fragment where it exists.

   [convert p] requires an [RSFD] whose automaton is an [ATA] and answers the
   [RSFD] with the same input automaton, the rules eta-expanded to bodies of
   the tree sort ([eta_expand], which keeps the value tree) and a [TTA]
   accepting exactly the trees the [ATA] accepts, so the two problems have
   the same answer.  Both automata are read under the trivial acceptance condition:
   every infinite path is accepted, and a node is rejected only by a missing
   transition.

   The fragment: every disjunct of every transition's DNF constrains each
   child with at most one state.  An alternating transition
   [q a -> D1 \/ ... \/ Dk] (rank [n] for [a]) then becomes the [k] trivial
   transitions [q a -> s1 ... sn], one per disjunct [Dj], where [si] is the
   state [Dj] puts on child [i] or, when [Dj] leaves child [i] free, a fresh
   universal state [qtop] with [qtop b -> qtop ... qtop] for every ranked
   terminal [b] at its rank.  [true] (an empty conjunction) is the all-[qtop]
   transition; [false] (an empty disjunction) and a missing transition give
   none.  Exactness: an alternating run at a node [a] in state [q] picks one
   disjunct and must accept child [i] from the state the disjunct names, or
   from nothing at all when it names none; a trivial run picks one transition
   and must accept child [i] from [si], and [qtop] accepts every tree over the
   ranked alphabet, a partial or infinite one included.  So the per-node
   choices correspond one to one and the accepted trees coincide.  A
   conjunction putting two states on one child would need the intersection
   of two states' languages at that child, a product state this translation
   does not build; it is refused.

   The result is in general nondeterministic: a transition with several
   disjuncts becomes several trivial transitions for one [(q, a)].  A model
   checker whose input class is deterministic trivial automata (TRecS) can
   take the result only when it is deterministic, which a caller checks
   ([TTA.nondeterministic_pair]).

   Every name introduced -- [qtop], the parameters [eta_expand] adds, and a
   terminal for the initial state when it has no transition, below -- is
   fresh: it differs from every state, terminal, non-terminal and rule
   parameter of [p] and from every other introduced name.

   Raises [Failure] when [p] is not of that dialect, when a transition leaves
   the fragment (the message names the transition), when a transition or a
   rule uses a terminal the ranks section does not list, when a transition
   names a child beyond its terminal's rank, or when [eta_expand] fails (the
   rules are not simply sorted or carry finite data). *)
open Core
open Ast
open Automata

let pr_transition q a (dest : ATA.dest) =
  Format.asprintf "%s %s -> %a." q a ATA.pr_dest dest

(* The terminals a rule's body names.  A [Term] spelling one of the rule's
   parameters is that parameter: the checkers' format tells a variable from a
   terminal by the rule's parameter list, not by the spelling, and a
   generated rule may write a parameter as a [Term]. *)
let terms_of (xs : Ident.tvar list) t =
  let rec go = function
    | RSFD.Term id ->
        if List.mem xs id ~equal:Ident.tvar_equal then []
        else [ Ident.name_of_tvar id ]
    | App (t1, t2) -> go t1 @ go t2
    | Case (_, ts) | CaseFd (_, ts) -> List.concat_map ts ~f:go
    | Fd _ | Nonterm _ | Var _ -> []
  in
  go t

(* [eta_expand ~rank_of ~mint rules] gives every rule a body of the tree
   sort: a rule [F x1 ... xn -> t] whose body [t] still takes [k] arguments
   becomes [F x1 ... xn y1 ... yk -> t y1 ... yk] with fresh parameters
   [yj] drawn by [mint].  HorSat2 reads a rule whose body is a function, and
   a generated scheme has such rules; TRecS reduces a non-terminal only when
   it is applied to exactly as many arguments as its rule has parameters,
   and refuses the over-application such a rule leads to as an arity
   mismatch.  The expansion keeps the value tree: [F a1 ... an b1 ... bk]
   reduces to [t[a/x] b1 ... bk] under either rule.  The sorts are inferred
   by unification, a terminal's from its rank ([rank_of]), a [Term] that
   spells a parameter being that parameter, and the start symbol (the first
   rule's) of the tree sort.  Raises [Failure] when the rules are not simply
   sorted, name an unbound variable or carry finite data (a value or a
   case), which the alternating dialect does not have. *)
let eta_expand ~rank_of ~mint (rules : RSFD.t) : RSFD.t =
  let nts = Hashtbl.create (module String) in
  let sort_of_nt id =
    Hashtbl.find_or_add nts (Ident.name_of_tvar id) ~default:SimpleSort.fresh
  in
  let rec infer env = function
    | RSFD.Nonterm id -> sort_of_nt id
    | (Var id | Term id) as t -> (
        match List.Assoc.find ~equal:Ident.tvar_equal env id with
        | Some s -> s
        | None -> (
            match t with
            | Term _ ->
                SimpleSort.tree_sort
                  (rank_of "in the rules" (Ident.name_of_tvar id))
            | _ -> failwithf "unbound variable %s" (Ident.name_of_tvar id) ()))
    | App (t1, t2) ->
        let s1 = infer env t1 in
        let s2 = infer env t2 in
        let r = SimpleSort.fresh () in
        SimpleSort.unify s1 (SimpleSort.Arr (s2, r));
        r
    | Fd _ | Case _ | CaseFd _ ->
        failwith
          "the rules carry finite data (a value or a case), which a problem \
           with an alternating automaton does not have"
  in
  let bodies =
    List.map rules ~f:(fun (id, (xs, t)) ->
        let env = List.map xs ~f:(fun x -> (x, SimpleSort.fresh ())) in
        let s = infer env t in
        SimpleSort.unify (sort_of_nt id)
          (List.fold_right env ~init:s ~f:(fun (_, sx) acc ->
               SimpleSort.Arr (sx, acc)));
        s)
  in
  (match rules with
  | (start, _) :: _ -> SimpleSort.unify (sort_of_nt start) SimpleSort.O
  | [] -> ());
  List.map2_exn rules bodies ~f:(fun (id, (xs, t)) s ->
      match SimpleSort.arity s with
      | 0 -> (id, (xs, t))
      | k ->
          let ys = List.init k ~f:(fun _ -> Ident.Tvar (mint "eta")) in
          (id, (xs @ ys, RSFD.apps t (List.map ys ~f:(fun y -> RSFD.Var y)))))

let convert = function
  | Problem.RSFD (trs_in, rules, TreeAutomaton.ATA (ranks, ata)) ->
      let rank_of where a =
        match List.Assoc.find ~equal:String.equal ranks a with
        | Some n -> n
        | None ->
            failwithf "terminal %s (%s) has no rank in the %%BEGINR section" a
              where ()
      in
      List.iter rules ~f:(fun (_, (xs, t)) ->
          List.iter (terms_of xs t) ~f:(fun a ->
              ignore (rank_of "in the rules" a)));
      (* every name of the problem, so that a minted one is none of them *)
      let taken = Hash_set.create (module String) in
      List.iter rules ~f:(fun (id, (xs, t)) ->
          Hash_set.add taken (Ident.name_of_tvar id);
          List.iter xs ~f:(fun x -> Hash_set.add taken (Ident.name_of_tvar x));
          List.iter (terms_of xs t) ~f:(Hash_set.add taken));
      List.iter ranks ~f:(fun (a, _) -> Hash_set.add taken a);
      List.iter trs_in ~f:(fun (q, body) ->
          Hash_set.add taken q;
          List.iter body ~f:(fun (a, qs) ->
              Hash_set.add taken a;
              List.iter qs ~f:(Hash_set.add taken)));
      List.iter ata ~f:(fun (q, body) ->
          Hash_set.add taken q;
          List.iter body ~f:(fun (a, dest) ->
              Hash_set.add taken a;
              List.iter dest
                ~f:(List.iter ~f:(fun (_, q') -> Hash_set.add taken q'))));
      let mint prefix =
        let v =
          Ident.mk_fresh_tvar_avoiding ~prefix
            ~taken:(fun v -> Hash_set.mem taken (Ident.name_of_tvar v))
            ()
        in
        Hash_set.add taken (Ident.name_of_tvar v);
        Ident.name_of_tvar v
      in
      let qtop = lazy (mint "qtop") in
      let used_top = ref false in
      let top () =
        used_top := true;
        Lazy.force qtop
      in
      let disjunct q a n (dest : ATA.dest) conj =
        let slots = Array.create ~len:n None in
        List.iter conj ~f:(fun (i, q') ->
            if i < 1 || i > n then
              failwithf
                "the transition %s names child %d of %s, whose rank is %d"
                (pr_transition q a dest) i a n ();
            match slots.(i - 1) with
            | None -> slots.(i - 1) <- Some q'
            | Some q'' when String.equal q'' q' -> ()
            | Some q'' ->
                failwithf
                  "the transition %s puts the two states %s and %s on child %d \
                   of %s, which a trivial tree automaton cannot express (each \
                   disjunct may constrain a child with at most one state); run \
                   it with HorSat2 instead"
                  (pr_transition q a dest) q'' q' i a ());
        Array.to_list slots
        |> List.map ~f:(function Some q' -> q' | None -> top ())
      in
      let tta =
        List.map ata ~f:(fun (q, body) ->
            ( q,
              List.concat_map body ~f:(fun (a, dest) ->
                  let n =
                    rank_of ("in the automaton's transition from " ^ q) a
                  in
                  List.map dest ~f:(disjunct q a n dest)
                  |> List.dedup_and_sort ~compare:(List.compare String.compare)
                  |> List.map ~f:(fun qs -> (a, qs))) ))
      in
      let tta =
        if !used_top then
          let q = Lazy.force qtop in
          tta
          @ [
              ( q,
                List.map ranks ~f:(fun (b, n) ->
                    (b, List.init n ~f:(fun _ -> q))) );
            ]
        else tta
      in
      (* The checkers read the initial state off the first transition listed,
         so the initial state must have one; when it has none it rejects
         every tree with a root, and a transition on a fresh terminal, which
         labels no node, keeps it first without accepting anything more. *)
      let tta =
        match tta with
        | (q, []) :: rest -> (q, [ (mint "notree", []) ]) :: rest
        | [] -> failwith "the alternating automaton has no state"
        | tta -> tta
      in
      Problem.RSFD
        (trs_in, eta_expand ~rank_of ~mint rules, TreeAutomaton.TTA tta)
  | p ->
      failwithf
        "not a problem with an alternating tree automaton: it specifies %s"
        (Problem.dialect_str_of p) ()
