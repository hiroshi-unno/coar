(* A solver for the effect constraints [MBcgen] generates: subeffecting
   between control effects (continuation effects, answer types) and inclusion
   between operation signatures, over effect, sort and row (operation
   signature) variables.

   [Make(..).solve ?templates eff_constrs opsig_constrs] returns a
   substitution for the variables occurring in the constraints.  It works in
   stages: simplification of the subeffect, subsort and operation-signature
   constraints to a fixpoint ([fully_simplify_subs]), unification of the
   equalities that leaves ([fully_unify_eqls]), preprocessing, a search over
   the remaining effect compositions ([solve_main], which may branch), and a
   postprocessing that resolves, eliminates and squashes the variables of the
   result.  A constraint that cannot be unified raises [Solve_failure]. *)

open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast.Ident
open Ast.LogicOld

module Config = struct
  (* What [solve_main] does when no rule implied by the constraints applies.
     [Guess] assigns [Pure] to every effect variable with a one-element
     composition [[ev] <: eff] left, and the empty closed signature to every
     row variable whose lower bound mentions it; neither is implied by the
     constraints, so a satisfiable set can be refuted.  [Forced_shape] makes
     the same assignments except where the constraints force otherwise: an
     effect variable that is impure in every solution gets a fresh impure
     effect, and a row variable gets the closed signature over the operations
     every solution must contain, or the set is refuted when those operations
     are not all allowed by its lower bounds.  On a set where [Guess] ends in a
     solution, [Forced_shape] ends in the same one: it differs only where
     [Guess] assigns what no solution has. *)
  type last_resort = Guess | Forced_shape [@@deriving yojson]

  type t = {
    verbose : bool; [@default false]
    last_resort : last_resort; [@default Guess]
    forced_shape_limit : int; [@default 64]
        (** under [Forced_shape], the number of fresh impure effects and
            non-empty signatures one [solve] may introduce; a recursive
            constraint can demand an unbounded descent of answer types (a
            recursive call under a handler that forwards the operation it
            performs has no finite typing), and past the limit the set is
            refuted *)
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "MBcsol"

    (* a leaf: no nested config to load *)
    let instantiate = Or_error.return
  end)
end

module Make (Config : Config.ConfigType) = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_module_name "MBcsol"
  let print_log = false

  exception Solve_failure of string

  (* A read-only firing census of [solve_main]'s last-resort steps, printed to
     stderr when the environment variable COAR_MBCSOL_CENSUS is set: one line
     per firing (with what [Forced_shape] would do differently there) and one
     per [solve] (its outcome, and on success a digest of the solution, so two
     runs can be compared for an identical solution).  It changes nothing the
     solver computes. *)
  let census_on = Option.is_some (Sys.getenv "COAR_MBCSOL_CENSUS")

  module Census =
    Common.Debug.Make
      ((val Common.Debug.Config.(if census_on then enable else disable)))

  let census fmt = ksprintf (fun s -> Census.print @@ lazy ("MBcsol census: " ^ s)) fmt

  (* fresh impure effects and non-empty signatures [Forced_shape] introduced
     in the current [solve]; reset by [solve], which is not reentrant *)
  let forced_shape_count = ref 0

  module Constr = struct
    type t = {
      sub_sv_sv : (svar * svar) Set.Poly.t;
      sub_evs_eff : (evar list * Sort.e) Set.Poly.t;
      sub_effs_eff : (Sort.e list * Sort.e) Set.Poly.t;
      ecomps : ((Sort.c * Sort.c) list * (Sort.c * Sort.c)) Set.Poly.t;
      sub_ov_ov : (rvar * rvar) Set.Poly.t;
      sub_ov_opsig :
        (rvar * ((string, Sort.t) ALMap.t * rvar option)) Set.Poly.t;
      sub_opsig_ov :
        (((string, Sort.t) ALMap.t * rvar option) * rvar) Set.Poly.t;
    }

    let empty =
      {
        sub_sv_sv = Set.Poly.empty;
        sub_evs_eff = Set.Poly.empty;
        sub_effs_eff = Set.Poly.empty;
        ecomps = Set.Poly.empty;
        sub_ov_ov = Set.Poly.empty;
        sub_ov_opsig = Set.Poly.empty;
        sub_opsig_ov = Set.Poly.empty;
      }

    let add_sub_sv_sv x c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (Ast.Ident.name_of_svar (fst x))
                (Ast.Ident.name_of_svar (snd x)));
      { c with sub_sv_sv = Set.add c.sub_sv_sv x }

    let add_sub_evs_eff (evs, eff) c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (String.concat_map_list ~sep:" " evs ~f:Ast.Ident.name_of_evar)
                (Term.str_of_cont eff));
      { c with sub_evs_eff = Set.add c.sub_evs_eff (evs, eff) }

    let add_sub_effs_eff (effs, eff) c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (String.concat_map_list ~sep:" " effs ~f:Term.str_of_cont)
                (Term.str_of_cont eff));
      if List.for_all effs ~f:Sort.is_evar then
        {
          c with
          sub_evs_eff =
            Set.add c.sub_evs_eff (List.map effs ~f:Sort.let_evar, eff);
        }
      else { c with sub_effs_eff = Set.add c.sub_effs_eff (effs, eff) }

    let add_ecomp (effs, (c1, c2)) c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s => %s"
                (String.concat_map_list ~sep:" " effs ~f:(fun (c1, c2) ->
                     Term.str_of_cont (Sort.mk_cont_eff c1 c2)))
                (Term.str_of_triple c1) (Term.str_of_triple c2));
      { c with ecomps = Set.add c.ecomps (effs, (c1, c2)) }

    let add_sub_ov_ov x c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (Ast.Ident.name_of_rvar (fst x))
                (Ast.Ident.name_of_rvar (snd x)));
      { c with sub_ov_ov = Set.add c.sub_ov_ov x }

    let add_sub_ov_opsig (ovar, (map, opt)) c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (Ast.Ident.name_of_rvar ovar)
                (Term.str_of_opsig (Sort.OpSig (map, opt))));
      match (map, opt) with
      | [], Some ovar' ->
          { c with sub_ov_ov = Set.add c.sub_ov_ov (ovar, ovar') }
      | _ -> { c with sub_ov_opsig = Set.add c.sub_ov_opsig (ovar, (map, opt)) }

    let add_sub_opsig_ov ((map, opt), ovar) c =
      if print_log then
        Debug.print
        @@ lazy
             (sprintf "adding %s <: %s"
                (Term.str_of_opsig (Sort.OpSig (map, opt)))
                (Ast.Ident.name_of_rvar ovar));
      match (map, opt) with
      | [], Some ovar' ->
          { c with sub_ov_ov = Set.add c.sub_ov_ov (ovar', ovar) }
      | _ -> { c with sub_opsig_ov = Set.add c.sub_opsig_ov ((map, opt), ovar) }

    let ovars_of c =
      Set.Poly.union_list
        [
          Set.concat_map c.sub_evs_eff ~f:(snd >> Term.rvs_of_cont);
          Set.concat_map c.sub_effs_eff ~f:(fun (effs, eff) ->
              Set.Poly.union_list @@ List.map (eff :: effs) ~f:Term.rvs_of_cont);
          Set.concat_map c.ecomps ~f:(fun (effs, (c1, c2)) ->
              Set.Poly.union_list
              @@ List.map ((c1, c2) :: effs)
                   ~f:(Tuple2.uncurry Sort.mk_cont_eff >> Term.rvs_of_cont));
          Set.concat_map c.sub_ov_ov ~f:(fun (ovar1, ovar2) ->
              Set.Poly.of_list [ ovar1; ovar2 ]);
          Set.concat_map c.sub_ov_opsig ~f:(fun (ovar, (map, opt)) ->
              Set.add (Term.rvs_of_opsig (Sort.OpSig (map, opt))) ovar);
          Set.concat_map c.sub_opsig_ov ~f:(fun ((map, opt), ovar) ->
              Set.add (Term.rvs_of_opsig (Sort.OpSig (map, opt))) ovar);
        ]

    let upper_constrained_ovars_of c =
      Set.Poly.union_list
        [
          Set.concat_map c.sub_evs_eff
            ~f:(snd >> Term.polar_rvs_of_cont ~pos:false);
          Set.concat_map c.sub_effs_eff ~f:(fun (effs, eff) ->
              Set.Poly.union_list
              @@ Term.polar_rvs_of_cont ~pos:false eff
                 :: List.map effs ~f:(Term.polar_rvs_of_cont ~pos:true));
          Set.concat_map c.ecomps ~f:(fun (effs, (c1, c2)) ->
              Set.Poly.union_list
              @@ Term.polar_rvs_of_cont ~pos:false (Sort.mk_cont_eff c1 c2)
                 :: List.map effs
                      ~f:
                        (Tuple2.uncurry Sort.mk_cont_eff
                        >> Term.polar_rvs_of_cont ~pos:true));
          Set.concat_map c.sub_ov_ov ~f:(fst >> Set.Poly.singleton);
          Set.concat_map c.sub_ov_opsig ~f:(fun (ovar, (map, opt)) ->
              Set.add
                (Term.polar_rvs_of_opsig ~pos:false (Sort.OpSig (map, opt)))
                ovar);
          Set.concat_map c.sub_opsig_ov ~f:(fun ((map, opt), _) ->
              Term.polar_rvs_of_opsig ~pos:true (Sort.OpSig (map, opt)));
        ]

    let upper_unconstrained_ovars_of c =
      Set.diff (ovars_of c) (upper_constrained_ovars_of c)

    let evars_of c =
      Set.Poly.union_list
        [
          Set.concat_map c.sub_evs_eff ~f:(fun (effs, eff) ->
              Set.union (Set.Poly.of_list effs) (Term.evs_of_cont eff));
          Set.concat_map c.sub_effs_eff ~f:(fun (effs, eff) ->
              Set.Poly.union_list @@ List.map (eff :: effs) ~f:Term.evs_of_cont);
          Set.concat_map c.ecomps ~f:(fun (effs, (c1, c2)) ->
              Set.Poly.union_list
              @@ List.map ((c1, c2) :: effs)
                   ~f:(Tuple2.uncurry Sort.mk_cont_eff >> Term.evs_of_cont));
          Set.concat_map c.sub_ov_opsig ~f:(fun (_, (map, opt)) ->
              Term.evs_of_opsig (Sort.OpSig (map, opt)));
          Set.concat_map c.sub_opsig_ov ~f:(fun ((map, opt), _) ->
              Term.evs_of_opsig (Sort.OpSig (map, opt)));
        ]

    let lower_constrained_evars_of c =
      Set.Poly.union_list
        [
          Set.concat_map c.sub_evs_eff ~f:(fun (evs, eff) ->
              if List.is_empty evs && Sort.is_evar eff then Set.Poly.empty
              else Term.polar_evs_of_cont ~pos:true eff);
          Set.concat_map c.sub_effs_eff ~f:(fun (effs, eff) ->
              Set.Poly.union_list
              @@ Term.polar_evs_of_cont ~pos:true eff
                 :: List.map effs ~f:(Term.polar_evs_of_cont ~pos:false));
          Set.concat_map c.ecomps ~f:(fun (effs, (c1, c2)) ->
              Set.Poly.union_list
              @@ Term.polar_evs_of_cont ~pos:true (Sort.mk_cont_eff c1 c2)
                 :: List.map effs
                      ~f:
                        (Tuple2.uncurry Sort.mk_cont_eff
                        >> Term.polar_evs_of_cont ~pos:false));
          Set.concat_map c.sub_ov_opsig ~f:(fun (_, (map, opt)) ->
              Term.polar_evs_of_opsig ~pos:true (Sort.OpSig (map, opt)));
          Set.concat_map c.sub_opsig_ov ~f:(fun ((map, opt), _) ->
              Term.polar_evs_of_opsig ~pos:false (Sort.OpSig (map, opt)));
        ]

    let lower_unconstrained_evars_of c =
      Set.diff (evars_of c) (lower_constrained_evars_of c)

    (* The analyses below read constraints and never add to them, and they
       create no fresh variable, so running them does not move the fresh-name
       counters a later step reads.  Each returns a fact true of every
       solution of [c] (for the sort-level calculus: subtyping on signatures
       is width subtyping with a larger signature below, operation sorts are
       compared pointwise, arguments contravariantly, an impure effect is
       never below the pure one, and a composition containing an impure
       effect is impure). *)

    (* For each row variable [rv], every pair [(sl, su)] of the sorts one
       operation has in a lower bound [{..., op : sl, ...} <: rv'] and an upper
       bound [rv'' <: {..., op : su, ...}] with [rv' <: ... <: rv <: ... <:
       rv''] in [sub_ov_ov].  Guarantees: [sl <: su] holds in every solution
       (width subtyping is transitive), although no constraint states it. *)
    let row_pairs c : (Sort.t * Sort.t) Set.Poly.t =
      let above =
        let tc = PartOrd.transitive_closure_of c.sub_ov_ov in
        fun rv ->
          Set.add
            (Set.Poly.filter_map tc ~f:(fun (rv1, rv2) ->
                 if Ast.Ident.rvar_equal rv1 rv then Some rv2 else None))
            rv
      in
      Set.concat_map c.sub_opsig_ov ~f:(fun ((lmap, _), rv) ->
          let rvs = above rv in
          Set.concat_map c.sub_ov_opsig ~f:(fun (rv', (umap, _)) ->
              if not (Set.mem rvs rv') then Set.Poly.empty
              else
                Set.Poly.of_list
                @@ List.filter_map lmap ~f:(fun (op, sl) ->
                    Option.map
                      (List.Assoc.find umap ~equal:String.equal op)
                      ~f:(fun su -> (sl, su)))))

    (* The subeffect pairs [(e1, e2)] that [t1 <: t2] (resp. [c1 <: c2], [o1 <:
       o2], [e1 <: e2]) entails by decomposing both sides where they have the
       same constructor; a variable on either side stops the descent, so the
       result is a subset of what is entailed, never more. *)
    let rec eff_pairs_of_sorts acc (t1, t2) =
      match (t1, t2) with
      | Sort.SArrow (a1, c1), Sort.SArrow (a2, c2) ->
          eff_pairs_of_conts (eff_pairs_of_sorts acc (a2, a1)) (c1, c2)
      | T_tuple.STuple ss1, T_tuple.STuple ss2
        when List.length ss1 = List.length ss2 ->
          List.fold2_exn ss1 ss2 ~init:acc ~f:(fun acc s1 s2 ->
              eff_pairs_of_sorts acc (s1, s2))
      | _ -> acc

    and eff_pairs_of_conts acc ((c1 : Sort.c), (c2 : Sort.c)) =
      let acc = eff_pairs_of_sorts acc (c1.val_type, c2.val_type) in
      let acc = eff_pairs_of_opsigs acc (c2.op_sig, c1.op_sig) in
      eff_pairs_of_effs acc (c1.cont_eff, c2.cont_eff)

    and eff_pairs_of_effs acc (e1, e2) =
      let acc = (e1, e2) :: acc in
      match (e1, e2) with
      | Sort.Eff (c11, c12), Sort.Eff (c21, c22) ->
          eff_pairs_of_conts (eff_pairs_of_conts acc (c21, c11)) (c12, c22)
      | _ -> acc

    and eff_pairs_of_opsigs acc (o1, o2) =
      match (o1, o2) with
      | Sort.OpSig (m1, _), Sort.OpSig (m2, _) ->
          List.fold m1 ~init:acc ~f:(fun acc (op, s1) ->
              match List.Assoc.find m2 ~equal:String.equal op with
              | Some s2 -> eff_pairs_of_sorts acc (s1, s2)
              | None -> acc)
      | _ -> acc

    (* The effect variables impure in every solution of [c]: the least set
       closed under "an impure effect (a syntactic [c1 => c2] or a member)
       below [EVar ev], or in a composition below it, puts [ev] in the set",
       where "below" is read off [sub_evs_eff], [sub_effs_eff] and the
       decomposed [row_pairs].  Guarantees: every member is impure in every
       solution (impurity flows upward, and every edge used is entailed). *)
    let forced_impure c : evar Set.Poly.t =
      let edges =
        List.concat
          [
            Set.fold (row_pairs c) ~init:[] ~f:eff_pairs_of_sorts;
            Set.fold c.sub_evs_eff ~init:[] ~f:(fun acc (evs, eff) ->
                List.fold evs ~init:acc ~f:(fun acc ev ->
                    (Sort.EVar ev, eff) :: acc));
            Set.fold c.sub_effs_eff ~init:[] ~f:(fun acc (effs, eff) ->
                List.fold effs ~init:acc ~f:(fun acc e -> (e, eff) :: acc));
          ]
      in
      let rec fix imp =
        let imp' =
          List.fold edges ~init:imp ~f:(fun imp (e1, e2) ->
              let impure1 =
                match e1 with
                | Sort.Eff _ -> true
                | Sort.EVar ev -> Set.mem imp ev
                | _ -> false
              in
              match e2 with
              | Sort.EVar ev2 when impure1 -> Set.add imp ev2
              | _ -> imp)
        in
        if Set.length imp' = Set.length imp then imp else fix imp'
      in
      fix Set.Poly.empty

    (* [required_domain c rv]: the operations every solution's signature for
       [rv] contains, the least set containing the explicit operations of each
       upper bound [rv <: {ops | tail}], the required operations of [tail] and
       of each [rv'] with [rv <: rv'], and those required operations of a
       lower bound's tail [{ops | tail} <: rv] that [ops] does not list.
       Guarantees: [required_domain c rv ⊆ dom(σ rv)] for every solution [σ]. *)
    let required_domain c : rvar -> string Set.Poly.t =
      let get m rv = Option.value ~default:Set.Poly.empty (Map.Poly.find m rv) in
      let step m =
        let add m rv ops =
          Map.Poly.set m ~key:rv ~data:(Set.union (get m rv) ops)
        in
        let m =
          Set.fold c.sub_ov_opsig ~init:m ~f:(fun m (rv, (umap, tail)) ->
              let m = add m rv (Set.Poly.of_list (List.map umap ~f:fst)) in
              match tail with Some t -> add m rv (get m t) | None -> m)
        in
        let m =
          Set.fold c.sub_ov_ov ~init:m ~f:(fun m (rv, rv') ->
              add m rv (get m rv'))
        in
        Set.fold c.sub_opsig_ov ~init:m ~f:(fun m ((lmap, tail), rv) ->
            match tail with
            | Some t ->
                add m t
                  (Set.diff (get m rv) (Set.Poly.of_list (List.map lmap ~f:fst)))
            | None -> m)
      in
      let rec fix m =
        let m' = step m in
        if Map.Poly.equal Set.equal m m' then m else fix m'
      in
      get (fix Map.Poly.empty)

    (* [allowed_domain c rv]: [None] for "any operation", else a set
       containing every operation a solution's signature for [rv] can have:
       the greatest assignment with [allowed(rv) ⊆ ops ∪ allowed(tail)] for each
       lower bound [{ops | tail} <: rv] (a closed one has no tail),
       [allowed(rv) ⊆ allowed(rv'')] for [rv'' <: rv], and [allowed(tail) ⊆
       allowed(rv)] for an upper bound [rv <: {ops | tail}].  Guarantees:
       [dom(σ rv) ⊆ allowed_domain c rv] for every solution [σ]; so
       [required_domain c rv ⊄ allowed_domain c rv] means [c] has none. *)
    let allowed_domain c : rvar -> string Set.Poly.t option =
      let get m rv = Option.join (Map.Poly.find m rv) in
      let meet a b =
        match (a, b) with
        | None, x | x, None -> x
        | Some a, Some b -> Some (Set.inter a b)
      in
      let step m =
        let restrict m rv allowed =
          Map.Poly.set m ~key:rv ~data:(meet (get m rv) allowed)
        in
        let m =
          Set.fold c.sub_opsig_ov ~init:m ~f:(fun m ((lmap, tail), rv) ->
              let ops = Set.Poly.of_list (List.map lmap ~f:fst) in
              restrict m rv
                (match tail with
                | None -> Some ops
                | Some t -> Option.map (get m t) ~f:(Set.union ops)))
        in
        let m =
          Set.fold c.sub_ov_ov ~init:m ~f:(fun m (rv'', rv) ->
              restrict m rv (get m rv''))
        in
        Set.fold c.sub_ov_opsig ~init:m ~f:(fun m (rv, (_, tail)) ->
            match tail with Some t -> restrict m t (get m rv) | None -> m)
      in
      let rec fix m =
        let m' = step m in
        if Map.Poly.equal (Option.equal Set.equal) m m' then m else fix m'
      in
      get (fix Map.Poly.empty)
  end

  module SimplResult = struct
    type t = {
      constr : Constr.t;
      eeqls : (Sort.e * Sort.e) Set.Poly.t;
      seqls : (Sort.t * Sort.t) Set.Poly.t;
      oeqls : (Sort.o * Sort.o) Set.Poly.t;
    }

    let empty =
      {
        constr = Constr.empty;
        eeqls = Set.Poly.empty;
        seqls = Set.Poly.empty;
        oeqls = Set.Poly.empty;
      }

    let map_constr f res = { res with constr = f res.constr }

    let add_eeqls x res =
      if print_log then
        Set.iter x ~f:(fun (e1, e2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_cont e1)
                    (Term.str_of_cont e2)));
      { res with eeqls = Set.union x res.eeqls }

    let add_seqls x res =
      if print_log then
        Set.iter x ~f:(fun (s1, s2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_sort s1)
                    (Term.str_of_sort s2)));
      { res with seqls = Set.union x res.seqls }

    let add_oeqls x res =
      if print_log then
        Set.iter x ~f:(fun (o1, o2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_opsig o1)
                    (Term.str_of_opsig o2)));
      { res with oeqls = Set.union x res.oeqls }
  end

  module SimplState = struct
    type t = {
      res : SimplResult.t;
      esubs : (Sort.e * Sort.e) Set.Poly.t;
      ssubs : (Sort.t * Sort.t) Set.Poly.t;
      osubs : (Sort.o * Sort.o) Set.Poly.t;
    }

    let map_res f state = { state with res = f state.res }
    let map_constr f state = map_res (SimplResult.map_constr f) state

    let add_esubs x state =
      if print_log then
        Set.iter x ~f:(fun (e1, e2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s <: %s" (Term.str_of_cont e1)
                    (Term.str_of_cont e2)));
      { state with esubs = Set.union x state.esubs }

    let add_ssubs x state =
      if print_log then
        Set.iter x ~f:(fun (s1, s2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s <: %s" (Term.str_of_sort s1)
                    (Term.str_of_sort s2)));
      { state with ssubs = Set.union x state.ssubs }

    let add_osubs x state =
      if print_log then
        Set.iter x ~f:(fun (o1, o2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s <: %s" (Term.str_of_opsig o1)
                    (Term.str_of_opsig o2)));
      { state with osubs = Set.union x state.osubs }

    let add_subs c1 c2 state =
      let open Sort in
      state
      |> add_osubs (Set.Poly.singleton (c2.op_sig, c1.op_sig))
      |> add_ssubs (Set.Poly.singleton (c1.val_type, c2.val_type))
      |> add_esubs (Set.Poly.singleton (c1.cont_eff, c2.cont_eff))
  end

  let rec simplify_esubs (state : SimplState.t) =
    match Set.choose state.esubs with
    | None -> state
    | Some (e1, e2) -> (
        let state = { state with esubs = Set.remove state.esubs (e1, e2) } in
        if Stdlib.(e1 = e2) then simplify_esubs state
        else
          match (e1, e2) with
          | _, Sort.Pure ->
              state
              |> SimplState.map_res
                   (SimplResult.add_eeqls (Set.Poly.singleton (e1, e2)))
              |> simplify_esubs
          | Sort.EVar ev1, _ ->
              state
              |> SimplState.map_constr (Constr.add_sub_evs_eff ([ ev1 ], e2))
              |> simplify_esubs
          | Sort.Pure, Sort.EVar _ ->
              state
              |> SimplState.map_constr (Constr.add_sub_evs_eff ([], e2))
              |> simplify_esubs
          | Sort.Eff (c1, c2), Sort.EVar ev ->
              let cv1 = Sort.mk_fresh_triple () in
              let cv2 = Sort.mk_fresh_triple () in
              let cont = Sort.mk_cont_eff cv1 cv2 in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_cont cont);
              state
              |> SimplState.map_res
                   (SimplResult.add_eeqls
                      (Set.Poly.singleton (Sort.EVar ev, cont)))
              |> SimplState.add_subs cv1 c1 |> SimplState.add_subs c2 cv2
              |> simplify_esubs
          | Sort.Pure, Sort.Eff (c1, c2) ->
              (* A pure computation embedded at an effectful type [c1 => c2]
                 passes its continuation's answer through unchanged, so its
                 initial and final answer types must agree: [c1 <: c2], which
                 [resolve_svs] closes into an equality when both answer types
                 are still variables.  Dropping or weakening this constraint
                 lets a pure branch of an effectful join return to an answer
                 type nothing observes. *)
              state |> SimplState.add_subs c1 c2 |> simplify_esubs
          | Sort.Eff (c11, c12), Sort.Eff (c21, c22) ->
              state
              |> SimplState.add_subs c21 c11
              |> SimplState.add_subs c12 c22
              |> simplify_esubs
          | _ -> failwith "unknown effect")

  let rec simplify_ssubs (state : SimplState.t) =
    match Set.choose state.ssubs with
    | None -> state
    | Some (t1, t2) -> (
        let state = { state with ssubs = Set.remove state.ssubs (t1, t2) } in
        if Stdlib.(t1 = t2) then simplify_ssubs state
        else
          match (t1, t2) with
          | t, Sort.SArrow (t', c) ->
              let sv = Sort.mk_fresh_svar () in
              let cv = Sort.mk_fresh_triple () in
              let sort = Sort.SArrow (sv, cv) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res
                   (SimplResult.add_seqls (Set.Poly.singleton (t, sort)))
              |> SimplState.add_subs cv c
              |> SimplState.add_ssubs (Set.Poly.singleton (t', sv))
              |> simplify_ssubs
          | Sort.SArrow (t', c), t ->
              let sv = Sort.mk_fresh_svar () in
              let cv = Sort.mk_fresh_triple () in
              let sort = Sort.SArrow (sv, cv) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res
                   (SimplResult.add_seqls (Set.Poly.singleton (t, sort)))
              |> SimplState.add_subs c cv
              |> SimplState.add_ssubs (Set.Poly.singleton (sv, t'))
              |> simplify_ssubs
          | t, T_array.SArray (t1, t2) ->
              let sv1 = Sort.mk_fresh_svar () in
              let sv2 = Sort.mk_fresh_svar () in
              let sort = T_array.SArray (sv1, sv2) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res
                   (SimplResult.add_seqls (Set.Poly.singleton (t, sort)))
              |> SimplState.add_ssubs
                   (Set.Poly.of_list [ (sv1, t1); (sv2, t2) ])
              |> simplify_ssubs
          | T_array.SArray (t1, t2), t ->
              let sv1 = Sort.mk_fresh_svar () in
              let sv2 = Sort.mk_fresh_svar () in
              let sort = T_array.SArray (sv1, sv2) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res
                   (SimplResult.add_seqls (Set.Poly.singleton (t, sort)))
              |> SimplState.add_ssubs
                   (Set.Poly.of_list [ (t1, sv1); (t2, sv2) ])
              |> simplify_ssubs
          | t, T_tuple.STuple (_ :: _ as ss) ->
              let svs =
                List.init (List.length ss) ~f:(fun _ -> Sort.mk_fresh_svar ())
              in
              let sort = T_tuple.STuple svs in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res
                   (SimplResult.add_seqls (Set.Poly.singleton (t, sort)))
              |> SimplState.add_ssubs (Set.Poly.of_list (List.zip_exn svs ss))
              |> simplify_ssubs
          | T_tuple.STuple (_ :: _ as ss), t ->
              let svs =
                List.init (List.length ss) ~f:(fun _ -> Sort.mk_fresh_svar ())
              in
              let sort = T_tuple.STuple svs in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res
                   (SimplResult.add_seqls (Set.Poly.singleton (t, sort)))
              |> SimplState.add_ssubs (Set.Poly.of_list (List.zip_exn ss svs))
              |> simplify_ssubs
          | t, T_dt.SDT dt when Fn.non List.is_empty (Datatype.params_of dt) ->
              let args = Datatype.params_of dt in
              let svs =
                List.init (List.length args) ~f:(fun _ -> Sort.mk_fresh_svar ())
              in
              let sort = T_dt.SDT (Datatype.update_params dt svs) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res
                   (SimplResult.add_seqls (Set.Poly.singleton (t, sort)))
              |> SimplState.add_ssubs
                   (Set.Poly.of_list (List.zip_exn svs args) (*ToDo*))
              |> simplify_ssubs
          | T_dt.SDT dt, t when Fn.non List.is_empty (Datatype.params_of dt) ->
              let args = Datatype.params_of dt in
              let svs =
                List.init (List.length args) ~f:(fun _ -> Sort.mk_fresh_svar ())
              in
              let sort = T_dt.SDT (Datatype.update_params dt svs) in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res
                   (SimplResult.add_seqls (Set.Poly.singleton (t, sort)))
              |> SimplState.add_ssubs
                   (Set.Poly.of_list (List.zip_exn args svs) (*ToDo*))
              |> simplify_ssubs
          | Sort.SVar sv1, Sort.SVar sv2 ->
              state
              |> SimplState.map_constr (Constr.add_sub_sv_sv (sv1, sv2))
              |> simplify_ssubs
          | t, T_ref.SRef t' | T_ref.SRef t', t ->
              let sv = Sort.mk_fresh_svar () in
              let sort = T_ref.SRef sv in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_sort sort);
              state
              |> SimplState.map_res
                   (SimplResult.add_seqls
                      (Set.Poly.of_list [ (t, sort); (t', sv) ]))
              |> simplify_ssubs
          | _, T_dt.SUS _
          | T_dt.SUS _, _
          | _, T_dt.SDT _
          | T_dt.SDT _, _
          | _, T_tuple.STuple []
          | T_tuple.STuple [], _
          | _, T_bool.SBool
          | T_bool.SBool, _
          | _, T_int.SInt
          | T_int.SInt, _
          | _, T_int.SRefInt
          | T_int.SRefInt, _
          | _, T_real.SReal
          | T_real.SReal, _
          | _, T_string.SString
          | T_string.SString, _
          | _, T_trace.STrace _
          | T_trace.STrace _, _
          | _, T_regex.SRegEx
          | T_regex.SRegEx, _ ->
              state
              |> SimplState.map_res
                   (SimplResult.add_seqls (Set.Poly.singleton (t1, t2)))
              |> simplify_ssubs
          | _ -> failwith "unknown sort")

  let rec simplify_osubs (state : SimplState.t) =
    match Set.choose state.osubs with
    | None -> state
    | Some (o1, o2) -> (
        let state = { state with osubs = Set.remove state.osubs (o1, o2) } in
        if Stdlib.(o1 = o2) then simplify_osubs state
        else
          match (o1, o2) with
          | Sort.OpSig (opmap1, None), Sort.OpSig (opmap2, None) ->
              let _lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              state
              |> SimplState.map_res
                   (SimplResult.add_oeqls
                      (Set.Poly.singleton
                         ( Sort.empty_closed_opsig,
                           Sort.OpSig (ALMap.of_alist_exn rights, None) )))
              |> SimplState.add_ssubs (Set.Poly.of_list (List.map boths ~f:snd))
              |> simplify_osubs
          | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, None) ->
              let _lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              if List.is_empty rights then
                state
                |> SimplState.add_ssubs
                     (Set.Poly.of_list (List.map boths ~f:snd))
                |> simplify_osubs
              else
                let rv = mk_fresh_rvar () in
                if print_log then
                  Debug.print
                  @@ lazy ("introducing " ^ Ast.Ident.name_of_rvar rv);
                state
                |> SimplState.map_res
                     (SimplResult.map_constr
                        (Constr.add_sub_ov_opsig
                           (rv1, (ALMap.of_alist_exn rights, Some rv))))
                |> SimplState.add_ssubs
                     (Set.Poly.of_list (List.map boths ~f:snd))
                |> simplify_osubs
          | Sort.OpSig (opmap1, None), Sort.OpSig (opmap2, Some rv2) ->
              let lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              state
              |> SimplState.map_res
                   (SimplResult.add_oeqls
                      (Set.Poly.singleton
                         ( Sort.empty_closed_opsig,
                           Sort.OpSig (ALMap.of_alist_exn rights, None) )))
              |> SimplState.map_res
                   (SimplResult.map_constr
                      (Constr.add_sub_opsig_ov
                         ((ALMap.of_alist_exn lefts, None), rv2)))
              |> SimplState.add_ssubs (Set.Poly.of_list (List.map boths ~f:snd))
              |> simplify_osubs
          | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, Some rv2) ->
              let lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              if List.is_empty rights then
                state
                |> SimplState.map_res
                     (SimplResult.map_constr
                        (Constr.add_sub_opsig_ov
                           ((ALMap.of_alist_exn lefts, Some rv1), rv2)))
                |> SimplState.add_ssubs
                     (Set.Poly.of_list (List.map boths ~f:snd))
                |> simplify_osubs
              else if List.is_empty lefts then
                state
                |> SimplState.add_ssubs
                     (Set.Poly.of_list (List.map boths ~f:snd))
                |> SimplState.map_res
                     (SimplResult.map_constr
                        (Constr.add_sub_ov_opsig
                           (rv1, (ALMap.of_alist_exn rights, Some rv2))))
                |> simplify_osubs
              else
                let rv = mk_fresh_rvar () in
                if print_log then
                  Debug.print
                  @@ lazy ("introducing " ^ Ast.Ident.name_of_rvar rv);
                state
                |> SimplState.map_res
                     (SimplResult.map_constr
                        (Constr.add_sub_ov_opsig
                           (rv1, (ALMap.of_alist_exn rights, Some rv))))
                |> SimplState.map_res
                     (SimplResult.map_constr
                        (Constr.add_sub_opsig_ov
                           ((ALMap.of_alist_exn lefts, Some rv), rv2)))
                |> SimplState.add_ssubs
                     (Set.Poly.of_list (List.map boths ~f:snd))
                |> simplify_osubs
          | _ -> failwith "unknown opsig")

  let print_ecomps ecomps =
    Debug.print @@ lazy "==== ecomps:";
    Set.iter ecomps ~f:(fun (effs, (c1, c2)) ->
        Debug.print
        @@ lazy
             (sprintf "%s <: %s => %s"
                (String.concat_map_list ~sep:" " effs ~f:(fun (c1, c2) ->
                     Term.str_of_cont (Sort.mk_cont_eff c1 c2)))
                (Term.str_of_triple c1) (Term.str_of_triple c2)))

  let print_ov_ov sub_ov_ov =
    Debug.print @@ lazy "==== sub_ov_ov:";
    Set.iter sub_ov_ov ~f:(fun (ovar1, ovar2) ->
        Debug.print
        @@ lazy
             (sprintf "%s <: %s"
                (Ast.Ident.name_of_rvar ovar1)
                (Ast.Ident.name_of_rvar ovar2)))

  let print_ov_opsig sub_ov_opsig =
    Debug.print @@ lazy "==== sub_ov_opsig:";
    Set.iter sub_ov_opsig ~f:(fun (ovar, (map, opt)) ->
        Debug.print
        @@ lazy
             (sprintf "%s <: %s"
                (Ast.Ident.name_of_rvar ovar)
                (Term.str_of_opsig (Sort.OpSig (map, opt)))))

  let print_opsig_ov sub_opsig_ov =
    Debug.print @@ lazy "==== sub_opsig_ov:";
    Set.iter sub_opsig_ov ~f:(fun ((map, opt), ovar) ->
        Debug.print
        @@ lazy
             (sprintf "%s <: %s"
                (Term.str_of_opsig (Sort.OpSig (map, opt)))
                (Ast.Ident.name_of_rvar ovar)))

  let print_ev_ev sub_ev_ev =
    Debug.print @@ lazy "==== sub_ev_ev:";
    Set.iter sub_ev_ev ~f:(fun (evar1, evar2) ->
        Debug.print
        @@ lazy
             (sprintf "%s <: %s"
                (Ast.Ident.name_of_evar evar1)
                (Ast.Ident.name_of_evar evar2)))

  let print_evs_eff sub_evs_eff =
    Debug.print @@ lazy "==== sub_evs_eff:";
    Set.iter sub_evs_eff ~f:(fun (evs, eff) ->
        Debug.print
        @@ lazy
             (sprintf "%s <: %s"
                (String.concat_map_list ~sep:" " evs ~f:Ast.Ident.name_of_evar)
                (Term.str_of_cont eff)))

  let print_effs_eff sub_effs_eff =
    Debug.print @@ lazy "==== sub_effs_eff:";
    Set.iter sub_effs_eff ~f:(fun (effs, eff) ->
        Debug.print
        @@ lazy
             (sprintf "%s <: %s"
                (String.concat_map_list ~sep:" " effs ~f:Term.str_of_cont)
                (Term.str_of_cont eff)))

  let print_esubs esubs =
    Debug.print @@ lazy "==== esubs:";
    Set.iter esubs ~f:(fun (e1, e2) ->
        Debug.print
        @@ lazy (sprintf "%s <: %s" (Term.str_of_cont e1) (Term.str_of_cont e2)))

  let print_ssubs ssubs =
    Debug.print @@ lazy "==== ssubs:";
    Set.iter ssubs ~f:(fun (s1, s2) ->
        Debug.print
        @@ lazy (sprintf "%s <: %s" (Term.str_of_sort s1) (Term.str_of_sort s2)))

  let print_osubs osubs =
    Debug.print @@ lazy "==== osubs:";
    Set.iter osubs ~f:(fun (o1, o2) ->
        Debug.print
        @@ lazy
             (sprintf "%s <: %s" (Term.str_of_opsig o1) (Term.str_of_opsig o2)))

  let print_ecompsubs ecompsubs =
    Debug.print @@ lazy "==== ecompsubs:";
    Set.iter ecompsubs ~f:(fun (effs, eff) ->
        Debug.print
        @@ lazy
             (sprintf "%s <: %s"
                (String.concat_map_list ~sep:" " effs ~f:Term.str_of_cont)
                (Term.str_of_cont eff)))

  let rec fully_simplify_subs (state : SimplState.t) =
    if
      Set.is_empty state.esubs && Set.is_empty state.ssubs
      && Set.is_empty state.osubs
    then state.res
    else (
      if print_log then Debug.print @@ lazy "#### fully_simplify_subs";
      if print_log then (
        print_esubs state.esubs;
        print_ssubs state.ssubs;
        print_osubs state.osubs);
      let state = state |> simplify_esubs |> simplify_ssubs |> simplify_osubs in
      fully_simplify_subs state)

  let simplify_ecompsubs (res : SimplResult.t) ecompsubs =
    if print_log then (
      Debug.print @@ lazy "#### simplify_ecompsubs";
      print_ecompsubs ecompsubs);
    let rec go (res : SimplResult.t) ecompsubs =
      match Set.choose ecompsubs with
      | None -> res
      | Some (effs, eff) ->
          let ecompsubs = Set.remove ecompsubs (effs, eff) in
          let effs = List.filter effs ~f:(Sort.is_pure >> not) in
          if Sort.is_pure eff then
            let res =
              SimplResult.add_eeqls
                (Set.Poly.of_list (List.map effs ~f:(fun e -> (e, eff))))
                res
            in
            go res ecompsubs
          else if Sort.is_evar eff && List.exists effs ~f:Sort.is_eff then (
            let eff' =
              Sort.mk_cont_eff (Sort.mk_fresh_triple ())
                (Sort.mk_fresh_triple ())
            in
            if print_log then
              Debug.print @@ lazy ("introducing " ^ Term.str_of_cont eff');
            let res =
              SimplResult.add_eeqls (Set.Poly.singleton (eff, eff')) res
            in
            go res (Set.add ecompsubs (effs, eff')))
          else if List.for_all (eff :: effs) ~f:Sort.is_eff then
            let res =
              SimplResult.map_constr
                (Constr.add_ecomp
                   (List.map effs ~f:Sort.let_eff, Sort.let_eff eff))
                res
            in
            go res ecompsubs
          else
            let res =
              SimplResult.map_constr (Constr.add_sub_effs_eff (effs, eff)) res
            in
            go res ecompsubs
    in
    go res ecompsubs

  let map_eql eql ~f = Set.Poly.map eql ~f:(fun (a1, a2) -> (f a1, f a2))
  let subst_cont_cont (ev, e) = Term.subst_conts_cont (Map.Poly.singleton ev e)
  let subst_cont_sort (ev, e) = Term.subst_conts_sort (Map.Poly.singleton ev e)

  let subst_cont_opsig (ev, e) =
    Term.subst_conts_opsig (Map.Poly.singleton ev e)

  let subst_sort_cont (sv, s) = Term.subst_sorts_cont (Map.Poly.singleton sv s)
  let subst_sort_sort (sv, s) = Term.subst_sorts_sort (Map.Poly.singleton sv s)

  let subst_sort_opsig (sv, s) =
    Term.subst_sorts_opsig (Map.Poly.singleton sv s)

  let subst_opsig_cont (rv, o) =
    Term.subst_opsigs_cont (Map.Poly.singleton rv o)

  let subst_opsig_sort (rv, o) =
    Term.subst_opsigs_sort (Map.Poly.singleton rv o)

  let subst_opsig_opsig (rv, o) =
    Term.subst_opsigs_opsig (Map.Poly.singleton rv o)

  module Subst = struct
    type t = {
      etheta : (evar, Sort.e) Map.Poly.t;
      stheta : (svar, Sort.t) Map.Poly.t;
      otheta : (rvar, Sort.o) Map.Poly.t;
    }

    let equal s1 s2 =
      Map.Poly.equal Stdlib.( = ) s1.etheta s2.etheta
      && Map.Poly.equal Stdlib.( = ) s1.stheta s2.stheta
      && Map.Poly.equal Stdlib.( = ) s1.otheta s2.otheta

    let empty =
      {
        etheta = Map.Poly.empty;
        stheta = Map.Poly.empty;
        otheta = Map.Poly.empty;
      }

    let add_subst_cont (ev, e) sb =
      match e with
      | Sort.EVar ev' when Stdlib.(ev = ev') -> sb
      | _ ->
          if print_log then
            Debug.print
            @@ lazy
                 (sprintf "adding %s |-> %s"
                    (Ast.Ident.name_of_evar ev)
                    (Term.str_of_cont e));
          {
            etheta =
              sb.etheta
              |> Map.Poly.map ~f:(subst_cont_cont (ev, e))
              |> Map.Poly.add_exn ~key:ev ~data:e;
            stheta = Map.Poly.map sb.stheta ~f:(subst_cont_sort (ev, e));
            otheta = Map.Poly.map sb.otheta ~f:(subst_cont_opsig (ev, e));
          }

    let add_subst_sort (sv, s) sb =
      match s with
      | Sort.SVar sv' when Stdlib.(sv = sv') -> sb
      | _ ->
          if print_log then
            Debug.print
            @@ lazy
                 (sprintf "adding %s |-> %s"
                    (Ast.Ident.name_of_svar sv)
                    (Term.str_of_sort s));
          {
            etheta = Map.Poly.map sb.etheta ~f:(subst_sort_cont (sv, s));
            stheta =
              sb.stheta
              |> Map.Poly.map ~f:(subst_sort_sort (sv, s))
              |> Map.Poly.add_exn ~key:sv ~data:s;
            otheta = Map.Poly.map sb.otheta ~f:(subst_sort_opsig (sv, s));
          }

    let add_subst_opsig (rv, o) sb =
      match o with
      | Sort.OpSig (map, Some rv') when Stdlib.(rv = rv') ->
          assert (ALMap.is_empty map);
          sb
      | _ ->
          if print_log then
            Debug.print
            @@ lazy
                 (sprintf "adding %s |-> %s"
                    (Ast.Ident.name_of_rvar rv)
                    (Term.str_of_opsig o));
          {
            etheta = Map.Poly.map sb.etheta ~f:(subst_opsig_cont (rv, o));
            stheta = Map.Poly.map sb.stheta ~f:(subst_opsig_sort (rv, o));
            otheta =
              sb.otheta
              |> Map.Poly.map ~f:(subst_opsig_opsig (rv, o))
              |> Map.Poly.add_exn ~key:rv ~data:o;
          }

    let subst_to_sort sb =
      Term.subst_opsigs_sort sb.otheta
      <<< Term.subst_sorts_sort sb.stheta
      <<< Term.subst_conts_sort sb.etheta

    let subst_to_cont sb =
      Term.subst_opsigs_cont sb.otheta
      <<< Term.subst_sorts_cont sb.stheta
      <<< Term.subst_conts_cont sb.etheta

    let subst_to_opsig sb =
      Term.subst_opsigs_opsig sb.otheta
      <<< Term.subst_sorts_opsig sb.stheta
      <<< Term.subst_conts_opsig sb.etheta

    let ovars_of sb =
      Set.Poly.union_list
        (Map.key_set sb.otheta
         :: List.map (Map.data sb.otheta) ~f:Term.rvs_of_opsig
        @ List.map (Map.data sb.stheta) ~f:Term.rvs_of_sort
        @ List.map (Map.data sb.etheta) ~f:Term.rvs_of_cont)

    let evars_of sb =
      Set.Poly.union_list
        (Map.key_set sb.etheta
         :: List.map (Map.data sb.otheta) ~f:Term.evs_of_opsig
        @ List.map (Map.data sb.stheta) ~f:Term.evs_of_sort
        @ List.map (Map.data sb.etheta) ~f:Term.evs_of_cont)
  end

  module UniResult = struct
    type t = { subst : Subst.t }
  end

  module UniState = struct
    type t = {
      res : UniResult.t;
      eeqls : (Sort.e * Sort.e) Set.Poly.t;
      seqls : (Sort.t * Sort.t) Set.Poly.t;
      oeqls : (Sort.o * Sort.o) Set.Poly.t;
    }

    let add_eeqls x state =
      if print_log then
        Set.iter x ~f:(fun (e1, e2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_cont e1)
                    (Term.str_of_cont e2)));
      { state with eeqls = Set.union x state.eeqls }

    let add_seqls x state =
      if print_log then
        Set.iter x ~f:(fun (s1, s2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_sort s1)
                    (Term.str_of_sort s2)));
      { state with seqls = Set.union x state.seqls }

    let add_oeqls x state =
      if print_log then
        Set.iter x ~f:(fun (o1, o2) ->
            Debug.print
            @@ lazy
                 (sprintf "adding %s = %s" (Term.str_of_opsig o1)
                    (Term.str_of_opsig o2)));
      { state with oeqls = Set.union x state.oeqls }

    let add_eqls c1 c2 state =
      let open Sort in
      state
      |> add_oeqls (Set.Poly.singleton (c2.op_sig, c1.op_sig))
      |> add_seqls (Set.Poly.singleton (c1.val_type, c2.val_type))
      |> add_eeqls (Set.Poly.singleton (c1.cont_eff, c2.cont_eff))

    let subst_cont (ev, e) state =
      {
        res = { subst = Subst.add_subst_cont (ev, e) state.res.subst };
        eeqls = map_eql state.eeqls ~f:(subst_cont_cont (ev, e));
        seqls = map_eql state.seqls ~f:(subst_cont_sort (ev, e));
        oeqls = map_eql state.oeqls ~f:(subst_cont_opsig (ev, e));
      }

    let subst_sort (sv, s) state =
      {
        res = { subst = Subst.add_subst_sort (sv, s) state.res.subst };
        eeqls = map_eql state.eeqls ~f:(subst_sort_cont (sv, s));
        seqls = map_eql state.seqls ~f:(subst_sort_sort (sv, s));
        oeqls = map_eql state.oeqls ~f:(subst_sort_opsig (sv, s));
      }

    let subst_opsig (rv, o) state =
      {
        res = { subst = Subst.add_subst_opsig (rv, o) state.res.subst };
        eeqls = map_eql state.eeqls ~f:(subst_opsig_cont (rv, o));
        seqls = map_eql state.seqls ~f:(subst_opsig_sort (rv, o));
        oeqls = map_eql state.oeqls ~f:(subst_opsig_opsig (rv, o));
      }
  end

  let rec unify_eeqls (state : UniState.t) =
    match Set.choose state.eeqls with
    | None -> state
    | Some (e1, e2) -> (
        let state = { state with eeqls = Set.remove state.eeqls (e1, e2) } in
        let fail () =
          raise
          @@ Solve_failure
               (sprintf "unification failed: %s = %s" (Term.str_of_cont e1)
                  (Term.str_of_cont e2))
        in
        if Stdlib.(e1 = e2) then unify_eeqls state
        else
          match (e1, e2) with
          | Sort.Eff (c11, c12), Sort.Eff (c21, c22) ->
              state |> UniState.add_eqls c11 c21 |> UniState.add_eqls c12 c22
              |> unify_eeqls
          | Sort.EVar ev, e | e, Sort.EVar ev ->
              if Set.mem (Term.evs_of_cont e) ev then fail ()
              else state |> UniState.subst_cont (ev, e) |> unify_eeqls
          | _ -> fail ())

  let rec unify_seqls (state : UniState.t) =
    match Set.choose state.seqls with
    | None -> state
    | Some (s1, s2) -> (
        let state = { state with seqls = Set.remove state.seqls (s1, s2) } in
        let fail () =
          raise
          @@ Solve_failure
               (sprintf "unification failed: %s = %s" (Term.str_of_sort s1)
                  (Term.str_of_sort s2))
        in
        if Stdlib.(s1 = s2) then unify_seqls state
        else
          match (s1, s2) with
          | Sort.SArrow (t1, c1), Sort.SArrow (t2, c2) ->
              state |> UniState.add_eqls c1 c2
              |> UniState.add_seqls (Set.Poly.singleton (t1, t2))
              |> unify_seqls
          | T_array.SArray (t11, t12), T_array.SArray (t21, t22) ->
              state
              |> UniState.add_seqls
                   (Set.Poly.of_list [ (t11, t21); (t12, t22) ])
              |> unify_seqls
          | T_tuple.STuple ss1, T_tuple.STuple ss2 ->
              state
              |> UniState.add_seqls (Set.Poly.of_list (List.zip_exn ss1 ss2))
              |> unify_seqls
          | T_dt.SDT dt1, T_dt.SDT dt2 ->
              let args1 = Datatype.params_of dt1 in
              let args2 = Datatype.params_of dt2 in
              if List.length args1 = List.length args2 then
                state
                |> UniState.add_seqls
                     (Set.Poly.of_list (List.zip_exn args1 args2))
                |> unify_seqls
              else fail ()
          | Sort.SVar sv, t | t, Sort.SVar sv ->
              if Set.mem (Term.svs_of_sort t) sv then fail ()
              else state |> UniState.subst_sort (sv, t) |> unify_seqls
          | _ -> fail ())

  let rec unify_oeqls (state : UniState.t) =
    match Set.choose state.oeqls with
    | None -> state
    | Some (o1, o2) -> (
        let state = { state with oeqls = Set.remove state.oeqls (o1, o2) } in
        let fail () =
          raise
          @@ Solve_failure
               (sprintf "unification failed: %s = %s" (Term.str_of_opsig o1)
                  (Term.str_of_opsig o2))
        in
        if Stdlib.(o1 = o2) then unify_oeqls state
        else
          match (o1, o2) with
          | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, Some rv2)
            when Stdlib.(rv1 <> rv2) ->
              (*if List.is_empty opmap1 && List.is_empty opmap2 then
                          state
                          |> UniState.subst_opsig (rv1, Sort.OpSig ([], Some rv2))
                          |> unify_oeqls
                        else*)
              let lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              let rv = mk_fresh_rvar () in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Ast.Ident.name_of_rvar rv);
              let opsigl = Sort.OpSig (ALMap.of_alist_exn lefts, Some rv) in
              let opsigr = Sort.OpSig (ALMap.of_alist_exn rights, Some rv) in
              if
                Set.mem (Term.rvs_of_opsig opsigr) rv1
                || Set.mem (Term.rvs_of_opsig opsigl) rv2
              then fail ()
              else
                state
                |> UniState.subst_opsig (rv1, opsigr)
                |> UniState.subst_opsig (rv2, opsigl)
                |> UniState.add_seqls (Set.Poly.of_list (List.map boths ~f:snd))
                |> unify_oeqls
          | Sort.OpSig (opmap1, Some rv1), Sort.OpSig (opmap2, Some rv2)
            when Stdlib.(rv1 = rv2) ->
              let lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              if Fn.non List.is_empty lefts || Fn.non List.is_empty rights then
                fail ()
              else
                state
                |> UniState.add_seqls (Set.Poly.of_list (List.map boths ~f:snd))
                |> unify_oeqls
          | Sort.OpSig (opmap, Some rv), Sort.OpSig (opmap', None)
          | Sort.OpSig (opmap', None), Sort.OpSig (opmap, Some rv) ->
              let lefts, boths, rights = ALMap.split_lbr opmap opmap' in
              if Fn.non List.is_empty lefts then fail ()
              else
                let opsigr = Sort.OpSig (ALMap.of_alist_exn rights, None) in
                if Set.mem (Term.rvs_of_opsig opsigr) rv then fail ()
                else
                  state
                  |> UniState.subst_opsig (rv, opsigr)
                  |> UniState.add_seqls
                       (Set.Poly.of_list (List.map boths ~f:snd))
                  |> unify_oeqls
          | Sort.OpSig (opmap1, None), Sort.OpSig (opmap2, None) ->
              let lefts, boths, rights = ALMap.split_lbr opmap1 opmap2 in
              if Fn.non List.is_empty lefts || Fn.non List.is_empty rights then
                fail ()
              else
                state
                |> UniState.add_seqls (Set.Poly.of_list (List.map boths ~f:snd))
                |> unify_oeqls
          | _ -> fail ())

  let rec fully_unify_eqls (state : UniState.t) =
    if
      Set.is_empty state.eeqls && Set.is_empty state.seqls
      && Set.is_empty state.oeqls
    then state.res
    else (
      if print_log then (
        Debug.print @@ lazy "#### fully_unify_eqls";
        Debug.print @@ lazy "==== eeqls:";
        Set.iter state.eeqls ~f:(fun (e1, e2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s = %s" (Term.str_of_cont e1) (Term.str_of_cont e2)));
        Debug.print @@ lazy "==== seqls:";
        Set.iter state.seqls ~f:(fun (s1, s2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s = %s" (Term.str_of_sort s1) (Term.str_of_sort s2)));
        Debug.print @@ lazy "==== oeqls:";
        Set.iter state.oeqls ~f:(fun (o1, o2) ->
            Debug.print
            @@ lazy
                 (sprintf "%s = %s" (Term.str_of_opsig o1)
                    (Term.str_of_opsig o2))));
      state |> unify_oeqls |> unify_eeqls |> unify_seqls |> fully_unify_eqls)

  module PreprocResult = struct
    type t = { constr : Constr.t; subst : Subst.t }

    let empty = { constr = Constr.empty; subst = Subst.empty }
  end

  module PreprocState = struct
    type t = {
      res : PreprocResult.t;
      esubs : (Sort.e * Sort.e) Set.Poly.t;
      ssubs : (Sort.t * Sort.t) Set.Poly.t;
      osubs : (Sort.o * Sort.o) Set.Poly.t;
      ecompsubs : (Sort.e list * Sort.e) Set.Poly.t;
    }

    let init ecompsubs osubs =
      {
        res = PreprocResult.empty;
        esubs = Set.Poly.empty;
        ssubs = Set.Poly.empty;
        osubs;
        ecompsubs;
      }

    let add_esubs x state = { state with esubs = Set.union x state.esubs }
    let add_ssubs x state = { state with ssubs = Set.union x state.ssubs }
    let add_osubs x state = { state with osubs = Set.union x state.osubs }

    let add_subs c1 c2 state =
      let open Sort in
      add_esubs (Set.Poly.singleton (c1.cont_eff, c2.cont_eff))
      @@ add_ssubs (Set.Poly.singleton (c1.val_type, c2.val_type))
      @@ add_osubs (Set.Poly.singleton (c2.op_sig, c1.op_sig)) state

    (*let add_ecompsubs x state = { state with ecompsubs = x @ state.ecompsubs }*)

    let from_subst_constr (subst : Subst.t) (constr : Constr.t) : t =
      if print_log then Debug.print @@ lazy "#### from_subst_constr";
      let subst_to_cont = Subst.subst_to_cont subst in
      (*let subst_to_sort = Subst.subst_to_sort subst in*)
      let subst_to_opsig = Subst.subst_to_opsig subst in
      let ssubs, sub_sv_sv =
        Set.partition_map constr.sub_sv_sv ~f:(fun (sv1, sv2) ->
            match
              (Map.Poly.find subst.stheta sv1, Map.Poly.find subst.stheta sv2)
            with
            | Some s1, Some s2 -> First (s1, s2)
            | Some s1, None -> First (s1, Sort.SVar sv2)
            | None, Some s2 -> First (Sort.SVar sv1, s2)
            | None, None -> Second (sv1, sv2))
      in
      let sub_effs_eff =
        Set.Poly.map ~f:(fun (effs, eff) ->
            ( List.filter ~f:(Sort.is_pure >> not)
              @@ List.map effs ~f:subst_to_cont,
              subst_to_cont eff ))
        @@ Set.union
             (Set.Poly.map constr.sub_evs_eff ~f:(fun (evs, eff) ->
                  (List.map evs ~f:(fun evar -> Sort.EVar evar), eff)))
             constr.sub_effs_eff
      in
      (*let esubs, sub_effs_eff =
          List.partition_map sub_effs_eff ~f:(fun (effs, eff) ->
              match effs with
              | [ eff' ] -> First (eff', eff)
              | _ -> Second (effs, eff))
        in*)
      let ecomps, ecompsubs, sub_effs_eff =
        Set.partition3_map sub_effs_eff ~f:(fun (effs, eff) ->
            if List.for_all (eff :: effs) ~f:Sort.is_eff then
              `Fst (List.map effs ~f:Sort.let_eff, Sort.let_eff eff)
            else if
              Sort.is_pure eff
              || (Sort.is_evar eff && List.exists effs ~f:Sort.is_eff)
            then `Snd (effs, eff)
            else `Trd (effs, eff))
      in
      let _, sub_evs_eff, sub_effs_eff =
        Set.partition3_map sub_effs_eff ~f:(fun (effs, eff) ->
            match (effs, eff) with
            | [ eff' ], eff when Stdlib.(eff = eff') -> `Fst ()
            | _ ->
                if List.for_all effs ~f:Sort.is_evar then
                  `Snd (List.map effs ~f:Sort.let_evar, eff)
                else `Trd (effs, eff))
      in
      let ecomps =
        Set.union ecomps
          (Set.Poly.map constr.ecomps ~f:(fun (es, (c1, c2)) ->
               match subst_to_cont (Sort.mk_cont_eff c1 c2) with
               | Sort.Eff (c1, c2) ->
                   ( List.map es ~f:(fun (c1, c2) ->
                         match subst_to_cont (Sort.mk_cont_eff c1 c2) with
                         | Sort.Eff (c1, c2) -> (c1, c2)
                         | _ -> assert false),
                     (c1, c2) )
               | _ -> assert false))
      in
      let osubs_from_ov_ov, sub_ov_ov =
        Set.partition_map constr.sub_ov_ov ~f:(fun (ovar1, ovar2) ->
            match
              ( Map.Poly.find subst.otheta ovar1,
                Map.Poly.find subst.otheta ovar2 )
            with
            | ( Some (Sort.OpSig (map1, Some ov1)),
                Some (Sort.OpSig (map2, Some ov2)) )
              when ALMap.is_empty map1 && ALMap.is_empty map2 ->
                Second (ov1, ov2)
            | Some opsig1, Some opsig2 -> First (opsig1, opsig2)
            | Some (Sort.OpSig (map1, Some ov1)), None when ALMap.is_empty map1
              ->
                Second (ov1, ovar2)
            | Some opsig1, None -> First (opsig1, Sort.OpSig ([], Some ovar2))
            | None, Some (Sort.OpSig (map2, Some ov2)) when ALMap.is_empty map2
              ->
                Second (ovar1, ov2)
            | None, Some opsig2 -> First (Sort.OpSig ([], Some ovar1), opsig2)
            | None, None -> Second (ovar1, ovar2))
      in
      let sub_ov_ov = Set.filter sub_ov_ov ~f:(Tuple2.uncurry Stdlib.( <> )) in
      let sub_ov_opsig =
        constr.sub_ov_opsig |> Set.to_list
        |> List.classify (fun (ovar, _) (ovar', _) -> Stdlib.(ovar = ovar'))
        |> List.concat_map ~f:(fun sub_ov_opsig ->
            let sub_ov_opsig1, sub_ov_opsig2 =
              List.partition_tf sub_ov_opsig ~f:(snd >> snd >> Option.is_none)
            in
            match sub_ov_opsig1 with
            | [] -> sub_ov_opsig2
            | (ovar, _) :: _ -> (
                try
                  ( ovar,
                    ( ALMap.force_merge_list
                      @@ List.map ~f:(snd >> fst) sub_ov_opsig1,
                      None ) )
                  :: sub_ov_opsig2
                with exn_ when not (Common.Timer.is_async exn_) -> sub_ov_opsig))
        |> Set.Poly.of_list
      in
      let osubs_from_ov_opsig, sub_ov_opsig =
        Set.partition_map sub_ov_opsig ~f:(fun (ov, (map, opt)) ->
            match
              ( Map.Poly.find subst.otheta ov,
                subst_to_opsig (Sort.OpSig (map, opt)) )
            with
            | Some (Sort.OpSig (map', Some ov')), Sort.OpSig (map, opt)
              when ALMap.is_empty map' ->
                Second (ov', (map, opt))
            | Some opsig', opsig -> First (opsig', opsig)
            | None, Sort.OpSig (map, opt) -> Second (ov, (map, opt))
            | _ -> failwith "")
      in
      let osubs_from_opsig_ov, sub_opsig_ov =
        Set.partition_map constr.sub_opsig_ov ~f:(fun ((map, opt), ov) ->
            match
              ( subst_to_opsig (Sort.OpSig (map, opt)),
                Map.Poly.find subst.otheta ov )
            with
            | Sort.OpSig (map, opt), Some (Sort.OpSig (map', Some ov'))
              when ALMap.is_empty map' ->
                Second ((map, opt), ov')
            | opsig, Some opsig' -> First (opsig, opsig')
            | Sort.OpSig (map, opt), None -> Second ((map, opt), ov)
            | _ -> failwith "")
      in
      let osubs =
        Set.Poly.union_list
          [ osubs_from_ov_ov; osubs_from_ov_opsig; osubs_from_opsig_ov ]
      in
      {
        res =
          {
            constr =
              {
                sub_sv_sv;
                sub_evs_eff;
                sub_effs_eff;
                ecomps;
                sub_ov_ov;
                sub_ov_opsig;
                sub_opsig_ov;
              };
            subst;
          };
        esubs = Set.Poly.empty;
        ssubs;
        osubs;
        ecompsubs;
      }
  end

  let rec preprocess (state : PreprocState.t) =
    if
      Set.is_empty state.esubs && Set.is_empty state.ssubs
      && Set.is_empty state.osubs
      && Set.is_empty state.ecompsubs
    then state.res
    else (
      if print_log then Debug.print @@ lazy "\n### preprocess";
      let simpl_res =
        fully_simplify_subs
          {
            res =
              simplify_ecompsubs
                {
                  constr = state.res.constr;
                  eeqls = Set.Poly.empty;
                  seqls = Set.Poly.empty;
                  oeqls = Set.Poly.empty;
                }
                state.ecompsubs;
            esubs = state.esubs;
            ssubs = state.ssubs;
            osubs = state.osubs;
          }
      in
      let uni_res =
        fully_unify_eqls
          {
            res = { subst = state.res.subst };
            eeqls = simpl_res.eeqls;
            seqls = simpl_res.seqls;
            oeqls = simpl_res.oeqls;
          }
      in
      preprocess (PreprocState.from_subst_constr uni_res.subst simpl_res.constr))

  module SearchState = struct
    type t = { constr : Constr.t; subst : Subst.t }

    let init (res : PreprocResult.t) =
      { constr = res.constr; subst = res.subst }

    let add_subst_conts sub state =
      let rec aux sub =
        let sub' =
          Set.fold ~init:sub sub ~f:(fun sub subst ->
              Set.Poly.map sub ~f:(fun (ev, e) -> (ev, subst_cont_cont subst e)))
        in
        if Set.equal sub sub' then sub' else aux sub'
      in
      PreprocState.from_subst_constr
        (Set.fold ~init:state.subst (aux sub) ~f:(Fn.flip Subst.add_subst_cont))
        state.constr

    let add_subst_opsigs sub state =
      let rec aux sub =
        let sub' =
          Set.fold ~init:sub sub ~f:(fun sub subst ->
              Set.Poly.map sub ~f:(fun (ov, o) ->
                  (ov, subst_opsig_opsig subst o)))
        in
        if Set.equal sub sub' then sub' else aux sub'
      in
      PreprocState.from_subst_constr
        (Set.fold ~init:state.subst (aux sub)
           ~f:(Fn.flip Subst.add_subst_opsig))
        state.constr
  end

  let rec solve_ecomps ~embed (state : SearchState.t) =
    if print_log then (
      Debug.print @@ lazy "#### solve_ecomps";
      print_ecomps state.constr.ecomps);
    match Set.choose state.constr.ecomps with
    | None -> state
    | Some (es, (c_first, c_last)) -> (
        let ecomps = Set.remove state.constr.ecomps (es, (c_first, c_last)) in
        let state = { state with constr = { state.constr with ecomps } } in
        match es with
        | [] ->
            (*let uni_res =
                fully_unify_eqls
                  {
                    res = { subst = state.subst };
                    seqls = [ (s_first, s_last) ];
                    eeqls = [ (e_first, e_last) ];
                    oeqls = [ (o_first, o_last) ];
                  }
              in*)
            let preproc_res =
              preprocess
              @@ PreprocState.add_subs c_first c_last
              @@ PreprocState.from_subst_constr (*uni_res.subst*) state.subst
                   state.constr
            in
            solve_ecomps ~embed
              { constr = preproc_res.constr; subst = preproc_res.subst }
        | (c1, c2) :: es ->
            (*let uni_res =
                fully_unify_eqls
                  {
                    res = { subst = state.subst };
                    seqls = [ (s_last, s2) ];
                    eeqls = [ (e_last, e2) ];
                    oeqls = [ (o_last, o2) ];
                  }
              in*)
            let state =
              {
                state with
                constr =
                  {
                    state.constr with
                    ecomps = Set.add ecomps (es, (c_first, c1));
                  };
              }
            in
            let preproc_res =
              preprocess
              @@ PreprocState.add_subs c2 c_last
              @@ PreprocState.from_subst_constr (*uni_res.subst*) state.subst
                   state.constr
            in
            solve_ecomps ~embed
              { constr = preproc_res.constr; subst = preproc_res.subst })

  let rec solve_effs_eff ~embed acc (state : SearchState.t) =
    if print_log then Debug.print @@ lazy "#### solve_effs_eff";
    match Set.choose state.constr.sub_effs_eff with
    | None ->
        assert (List.is_empty acc);
        state
    (*| ([ Sort.EVar ev1 ], Sort.EVar ev2) :: sub_effs_eff
      when Ast.Ident.evar_equal ev1 ev2 ->
        let state =
          { state with constr = { state.constr with sub_effs_eff } }
        in
        solve_effs_eff ~embed acc state*)
    | Some (es, (Sort.EVar _ as e)) when List.for_all es ~f:Sort.is_evar ->
        let sub_effs_eff = Set.remove state.constr.sub_effs_eff (es, e) in
        let state =
          {
            state with
            constr =
              Constr.add_sub_evs_eff
                (List.map es ~f:Sort.let_evar, e)
                { state.constr with sub_effs_eff };
          }
        in
        solve_effs_eff ~embed acc state
    | Some (es, (Sort.Eff (c_first, c_last) as e)) -> (
        let sub_effs_eff = Set.remove state.constr.sub_effs_eff (es, e) in
        let state =
          { state with constr = { state.constr with sub_effs_eff } }
        in
        match es with
        | [] ->
            (*let uni_res =
                fully_unify_eqls
                  {
                    res = { subst = state.subst };
                    seqls = [ (s_first, s_last) ];
                    eeqls = [ (e_first, e_last) ];
                    oeqls = [ (o_first, o_last) ];
                  }
              in*)
            let preproc_res =
              preprocess
              @@ PreprocState.add_subs c_first c_last
              @@ PreprocState.from_subst_constr (*uni_res.subst*) state.subst
                   state.constr
            in
            solve_effs_eff ~embed acc
              { constr = preproc_res.constr; subst = preproc_res.subst }
        | Sort.Eff (c1, c2) :: es ->
            (*let uni_res =
                fully_unify_eqls
                  {
                    res = { subst = state.subst };
                    seqls = [ (s_last, s2) ];
                    eeqls = [ (e_last, e2) ];
                    oeqls = [ (o_last, o2) ];
                  }
              in*)
            let state =
              {
                state with
                constr =
                  {
                    state.constr with
                    sub_effs_eff =
                      Set.add sub_effs_eff (es, Sort.mk_cont_eff c_first c1);
                  };
              }
            in
            let preproc_res =
              preprocess
              @@ PreprocState.add_subs c2 c_last
              @@ PreprocState.from_subst_constr (*uni_res.subst*) state.subst
                   state.constr
            in
            solve_effs_eff ~embed acc
              { constr = preproc_res.constr; subst = preproc_res.subst }
        | Sort.EVar _ :: _ ->
            let es1, es2 = List.split_while es ~f:Sort.is_evar in
            if List.is_empty es2 then
              let state =
                {
                  state with
                  constr =
                    {
                      state.constr with
                      sub_evs_eff =
                        Set.add state.constr.sub_evs_eff
                          (List.map es1 ~f:Sort.let_evar, e);
                    };
                }
              in
              let preproc_res =
                preprocess
                @@ PreprocState.from_subst_constr state.subst state.constr
              in
              solve_effs_eff ~embed acc
                { constr = preproc_res.constr; subst = preproc_res.subst }
            else
              let c = Sort.mk_fresh_triple () in
              if print_log then
                Debug.print @@ lazy ("introducing " ^ Term.str_of_triple c);
              let cont1 = Sort.mk_cont_eff c c_last in
              let cont2 = Sort.mk_cont_eff c_first c in
              let state =
                {
                  state with
                  constr =
                    {
                      state.constr with
                      sub_evs_eff =
                        Set.add state.constr.sub_evs_eff
                          (List.map es1 ~f:Sort.let_evar, cont1);
                      sub_effs_eff = Set.add sub_effs_eff (es2, cont2);
                    };
                }
              in
              let preproc_res =
                preprocess
                @@ PreprocState.from_subst_constr state.subst state.constr
              in
              solve_effs_eff ~embed acc
                { constr = preproc_res.constr; subst = preproc_res.subst }
            (* let assume_eff () =
                let ov1, sv1, ev1 = Sort.mk_fresh_triple () in
                  let ov2, sv2, ev2 = Sort.mk_fresh_triple () in
                  let cont = Sort.mk_cont_eff (ov1, sv1, ev1) (ov2, sv2, ev2) in
                  if print_log then
                    Debug.print @@ lazy ("introducing " ^ Term.str_of_cont cont);
                  let cont' =
                    Sort.mk_cont_eff (o_first, s_first, e_first) (ov1, sv1, ev1)
                  in
                  let sub_effs_eff = (es, cont') :: sub_effs_eff in
                  let preproc_res =
                    preprocess
                    @@ PreprocState.add_esubs [ (ev2, e_last) ]
                    @@ PreprocState.add_ssubs [ (sv2, s_last) ]
                    @@ PreprocState.add_osubs [ (o_last, ov2) ]
                    @@ SearchState.add_subst_conts [ (ev, cont) ]
                       { state with constr = { state.constr with sub_effs_eff } }
                  in
                  solve_effs_eff ~embed acc
                    {
                      constr = preproc_res.constr;
                      subst = preproc_res.subst;
                    }
                in
                let assume_pure () =
                  let sub_effs_eff =
                    ( es,
                      Sort.Eff (o_first, s_first, e_first, o_last, s_last, e_last)
                    )
                    :: sub_effs_eff
                  in
                  let preproc_res =
                    preprocess
                    @@ SearchState.add_subst_conts [ (ev, Sort.Pure) ]
                       { state with constr = { state.constr with sub_effs_eff } }
                  in
                  solve_effs_eff ~embed acc
                  {
                       constr = preproc_res.constr;
                       subst = preproc_res.subst;
                  }
                in

                let assume1, assume2 =
                  if embed then (assume_eff, assume_pure)
                  else (assume_pure, assume_eff)
                in
                try assume1 () with Solve_failure _ -> assume2 () *)
        | _ -> failwith "unknown effect")
    | _ -> assert false

  (* The last resort for effect variables, reached when every remaining
     composition is of effect variables only and no rule implied by the
     constraints applies.  Its candidates are the variables [ev] of the
     one-element compositions [[ev] <: eff] in [c].  Under [Guess] each gets
     [Pure].  Under [Forced_shape] those outside [Constr.forced_impure c] get
     [Pure] and those inside get a fresh [c1 => c2]: assigning [Pure] to a
     variable that is impure in every solution can only end in failure, so on
     an input where [Guess] succeeds the two assign alike (and create the
     same fresh names, since none is created then).  Raises [Solve_failure]
     once [Forced_shape] has introduced [config.forced_shape_limit] fresh
     structures in this [solve]. *)
  let last_resort_effects (c : Constr.t) =
    let evs =
      Set.Poly.filter_map c.sub_evs_eff ~f:(function
        | [ ev ], _ -> Some ev
        | _ -> None)
    in
    let forced =
      if Set.is_empty evs then Set.Poly.empty
      else
        match config.last_resort with
        | Forced_shape -> Set.inter evs (Constr.forced_impure c)
        | Guess ->
            if census_on then Set.inter evs (Constr.forced_impure c)
            else Set.Poly.empty
    in
    if census_on && Fn.non Set.is_empty evs then
      census "H1 evars=%d forced_impure=%d" (Set.length evs)
        (Set.length forced);
    match config.last_resort with
    | Guess -> Set.Poly.map evs ~f:(fun ev -> (ev, Sort.Pure))
    | Forced_shape ->
        Set.Poly.map evs ~f:(fun ev ->
            if Set.mem forced ev then (
              incr forced_shape_count;
              if !forced_shape_count > config.forced_shape_limit then
                raise
                  (Solve_failure
                     (sprintf
                        "no effect typing found within %d forced impure \
                         effects and signatures"
                        config.forced_shape_limit));
              ( ev,
                Sort.mk_cont_eff (Sort.mk_fresh_triple ())
                  (Sort.mk_fresh_triple ()) ))
            else (ev, Sort.Pure))

  (* The last resort for row variables, reached after [last_resort_effects]
     found nothing.  Its candidates are the row variables [rv] with a lower
     bound that mentions [rv] itself.  Under [Guess] each gets the empty closed
     signature.  Under [Forced_shape] each gets the closed signature over
     [Constr.required_domain c rv] with a fresh sort per operation, after
     checking that domain against [Constr.allowed_domain c rv] and raising
     [Solve_failure] when it does not fit (no solution exists then); when the
     required domain is empty this is [Guess]'s assignment, and an empty
     signature is the only one [Guess] can succeed with, since a solution's
     domain contains the required one.  Shares [last_resort_effects]'s
     limit. *)
  let last_resort_signatures (c : Constr.t) =
    let rvs =
      Set.Poly.filter_map c.sub_opsig_ov ~f:(function
        | (opsig, ovar), ov
          when Set.mem (Term.rvs_of_opsig (Sort.OpSig (opsig, ovar))) ov ->
            Some ov
        | _ -> None)
    in
    let analyse () =
      let req = Constr.required_domain c in
      let allow = Constr.allowed_domain c in
      Set.Poly.map rvs ~f:(fun rv -> (rv, req rv, allow rv))
    in
    if census_on && Fn.non Set.is_empty rvs then (
      let a = analyse () in
      census "H2 rvars=%d required_nonempty=%d required_not_allowed=%d"
        (Set.length rvs)
        (Set.count a ~f:(fun (_, r, _) -> Fn.non Set.is_empty r))
        (Set.count a ~f:(fun (_, r, al) ->
             match al with None -> false | Some al -> not (Set.is_subset r ~of_:al))));
    match config.last_resort with
    | Guess -> Set.Poly.map rvs ~f:(fun ov -> (ov, Sort.empty_closed_opsig))
    | Forced_shape ->
        Set.Poly.map (analyse ()) ~f:(fun (rv, req, allow) ->
            (match allow with
            | Some allow when not (Set.is_subset req ~of_:allow) ->
                raise
                  (Solve_failure
                     (sprintf
                        "row %s must contain the operations %s, which its \
                         lower bounds do not allow"
                        (Ast.Ident.name_of_rvar rv)
                        (String.concat_set ~sep:"," (Set.diff req allow))))
            | _ -> ());
            if Set.is_empty req then (rv, Sort.empty_closed_opsig)
            else (
              incr forced_shape_count;
              if !forced_shape_count > config.forced_shape_limit then
                raise
                  (Solve_failure
                     (sprintf
                        "no effect typing found within %d forced impure \
                         effects and signatures"
                        config.forced_shape_limit));
              ( rv,
                Sort.OpSig
                  ( ALMap.of_alist_exn
                    @@ List.map (Set.to_list req) ~f:(fun op ->
                        (op, Sort.mk_fresh_svar ())),
                    None ) )))

  (* The two stops of [solve_main] where no rule applies and constraints are
     left that are not of the finishing forms (sequences of effect variables
     below an effect variable, subsorts between sort variables).  What is left
     is the residual form of Materzok and Biernacki's inference for subtyping
     delimited continuations (ICFP 2011, extended version, Sec. 3.4): an
     effect variable below an impure effect [ev <: C1 => C2], or a row bound
     that the row rules did not settle.  Their algorithm leaves these to a
     search (choose the pure effect, which needs [C1 <: C2], or a fresh impure
     one); this solver has no rule for them.  The state is therefore not shown
     unsatisfiable: the stop is a refusal of an incomplete solver, raised as
     [Solve_failure] so that every caller reports it in words as it does a
     unification failure, never an uncaught exception.  [residual_failure]
     reads the state only, to name the leftover constraints in the reason. *)
  let residual_failure (constr : Constr.t) =
    let str_of_bound (map, opt) = Term.str_of_opsig (Sort.OpSig (map, opt)) in
    let effects =
      List.filter_map (Set.to_list constr.sub_evs_eff) ~f:(fun (evs, eff) ->
          if Sort.is_evar eff then None
          else
            Some
              (sprintf "%s <: %s"
                 (String.concat_map_list ~sep:" " evs
                    ~f:Ast.Ident.name_of_evar)
                 (Term.str_of_cont eff)))
    in
    let rows =
      List.concat
        [
          List.map (Set.to_list constr.sub_ov_ov) ~f:(fun (r1, r2) ->
              Ast.Ident.name_of_rvar r1 ^ " <: " ^ Ast.Ident.name_of_rvar r2);
          List.map (Set.to_list constr.sub_ov_opsig) ~f:(fun (r, o) ->
              Ast.Ident.name_of_rvar r ^ " <: " ^ str_of_bound o);
          List.map (Set.to_list constr.sub_opsig_ov) ~f:(fun (o, r) ->
              str_of_bound o ^ " <: " ^ Ast.Ident.name_of_rvar r);
        ]
    in
    Solve_failure
      (sprintf
         "no rule applies to the residual constraints (%s), which a search \
          the solver does not make would have to settle%s%s"
         (String.concat ~sep:" and "
         @@ List.filter_map ~f:Fn.id
              [
                (if List.is_empty effects then None
                 else Some "an effect variable below an impure effect");
                (if List.is_empty rows then None
                 else Some "operation-signature row bounds");
              ])
         (if List.is_empty effects then ""
          else ": " ^ String.concat ~sep:", " effects)
         (if List.is_empty rows then ""
          else "; rows: " ^ String.concat ~sep:", " rows))

  let rec solve_main ~embed (state : SearchState.t) =
    if print_log then Debug.print @@ lazy "\n### solve_main";
    if Fn.non Set.is_empty state.constr.ecomps then (
      Debug.print @@ lazy "@ solve ecomps";
      let state = solve_ecomps ~embed state in
      let preproc_res =
        preprocess (PreprocState.from_subst_constr state.subst state.constr)
      in
      solve_main ~embed
        { constr = preproc_res.constr; subst = preproc_res.subst })
    else
      let oeqs =
        (* ToDo: construction of transitive closure is not required? *)
        let tc = PartOrd.transitive_closure_of state.constr.sub_ov_ov in
        let nodes =
          Set.to_list
            (Tuple2.uncurry Set.union (Set.unzip state.constr.sub_ov_ov))
        in
        let dict =
          Map.Poly.of_alist_exn @@ List.mapi nodes ~f:(fun i n -> (n, i))
        in
        let uf = UnionFind.mk_size_uf ~size:(List.length nodes) in
        Set.iter state.constr.sub_ov_ov ~f:(fun (ovar1, ovar2) ->
            if Set.mem tc (ovar1, ovar2) && Set.mem tc (ovar2, ovar1) then
              UnionFind.unite
                (Map.Poly.find_exn dict ovar1)
                (Map.Poly.find_exn dict ovar2)
                uf);
        let groups = UnionFind.get_groups uf in
        Set.Poly.of_list
        @@ List.concat_map groups ~f:(fun ids ->
            let id, ids = List.hd_tl ids in
            List.map ids ~f:(fun id' ->
                ( List.nth_exn nodes id',
                  Sort.mk_empty_open_opsig_from_rvar @@ List.nth_exn nodes id )))
      in
      if Fn.non Set.is_empty oeqs then (
        Debug.print @@ lazy "@ remove ovar cycles";
        if print_log then print_ov_ov state.constr.sub_ov_ov;
        let preproc_res =
          preprocess @@ SearchState.add_subst_opsigs oeqs state
        in
        solve_main ~embed
          { constr = preproc_res.constr; subst = preproc_res.subst })
      else
        let oeqs =
          Set.Poly.map ~f:(fun (ovar, (map, opt)) ->
              (ovar, Sort.OpSig (map, opt)))
          @@ Set.inter state.constr.sub_ov_opsig
               (Set.Poly.map state.constr.sub_opsig_ov ~f:(fun (opsig, ovar) ->
                    (ovar, opsig)))
        in
        if Fn.non Set.is_empty oeqs then (
          Debug.print @@ lazy "@ remove ovar opsig cycles";
          if print_log then (
            print_ov_ov state.constr.sub_ov_ov;
            print_ov_opsig state.constr.sub_ov_opsig;
            print_opsig_ov state.constr.sub_opsig_ov);
          let preproc_res =
            preprocess @@ SearchState.add_subst_opsigs oeqs state
          in
          solve_main ~embed
            { constr = preproc_res.constr; subst = preproc_res.subst })
        else
          let uovars, oeqs =
            let uovars =
              (*Set.diff*)
              Constr.upper_unconstrained_ovars_of state.constr
              (*(Subst.ovars_of state.subst)*)
            in
            ( uovars,
              Set.Poly.map uovars ~f:(fun ovar ->
                  (ovar, Sort.empty_closed_opsig)) )
          in
          if Fn.non Set.is_empty uovars then (
            Debug.print @@ lazy "@ remove upper unconstrained ovars";
            if print_log then (
              print_ov_ov state.constr.sub_ov_ov;
              print_ov_opsig state.constr.sub_ov_opsig;
              print_opsig_ov state.constr.sub_opsig_ov;
              print_evs_eff state.constr.sub_evs_eff;
              print_effs_eff state.constr.sub_effs_eff;
              Debug.print @@ lazy "==== upper unconstrained ovars:";
              Debug.print
              @@ lazy
                   (String.concat_map_set ~sep:"," ~f:Ast.Ident.name_of_rvar
                      uovars));
            let preproc_res =
              preprocess @@ SearchState.add_subst_opsigs oeqs state
            in
            solve_main ~embed
              { constr = preproc_res.constr; subst = preproc_res.subst })
          else
            let oeqs =
              let covars =
                Set.union
                  (Set.concat_map state.constr.sub_opsig_ov
                     ~f:(fun ((map, opt), _ovar) ->
                       Term.rvs_of_opsig (Sort.OpSig (map (*ToDo*), opt))))
                  (Set.concat_map state.constr.sub_ov_opsig
                     ~f:(fun (ovar, (_map, _opt)) -> Set.Poly.singleton ovar))
              in
              Set.Poly.of_list
              @@ List.filter_map ~f:(function
                | [ (ov, ov') ] ->
                    let opsig = Sort.OpSig (ALMap.empty, Some ov') in
                    if print_log then
                      Debug.print
                      @@ lazy ("introducing " ^ Term.str_of_opsig opsig);
                    Some (ov, opsig)
                | _ -> None)
              @@ List.classify (fun (ov1, _) (ov2, _) ->
                  Ast.Ident.rvar_equal ov1 ov2)
              @@ Set.to_list
              @@ Set.filter state.constr.sub_ov_ov
                   ~f:(fst >> Set.mem covars >> not)
            in
            if Fn.non Set.is_empty oeqs then (
              Debug.print @@ lazy "@ assign singleton ovar upper bound";
              if print_log then (
                print_ov_ov state.constr.sub_ov_ov;
                print_ov_opsig state.constr.sub_ov_opsig;
                print_opsig_ov state.constr.sub_opsig_ov);
              let preproc_res =
                preprocess @@ SearchState.add_subst_opsigs oeqs state
              in
              solve_main ~embed
                { constr = preproc_res.constr; subst = preproc_res.subst })
            else
              let oeqs =
                let covars =
                  Set.Poly.union_list
                    [
                      Set.concat_map state.constr.sub_ov_ov
                        ~f:(fun (ovar1, _ovar2) -> Set.Poly.singleton ovar1);
                      Set.concat_map state.constr.sub_opsig_ov
                        ~f:(fun ((map, opt), _ovar) ->
                          Term.rvs_of_opsig (Sort.OpSig (map (*ToDo*), opt)));
                      Set.concat
                      @@ Set.Poly.filter_map state.constr.sub_ov_opsig
                           ~f:(fun (ovar, (_map, opt)) ->
                             if Option.is_some opt then
                               Some (Set.Poly.singleton ovar)
                             else None);
                    ]
                in
                Set.Poly.of_list
                @@ List.map ~f:(fun ov_opsigs ->
                    let ov_opsigs = List.dedup_keep_last ov_opsigs in
                    let ov = fst @@ List.hd_exn ov_opsigs in
                    let ops =
                      List.dedup_keep_last
                      @@ List.concat_map ov_opsigs
                           ~f:(snd >> fst >> List.map ~f:fst)
                    in
                    let opsig =
                      Sort.OpSig
                        ( ALMap.of_alist_exn
                          @@ List.map ops ~f:(fun op ->
                              (op, Sort.mk_fresh_svar ())),
                          None )
                    in
                    if print_log then
                      Debug.print
                      @@ lazy ("introducing " ^ Term.str_of_opsig opsig);
                    (ov, opsig))
                @@ List.classify (fun (ov1, _) (ov2, _) ->
                    Ast.Ident.rvar_equal ov1 ov2)
                @@ Set.to_list
                @@ Set.filter state.constr.sub_ov_opsig
                     ~f:(fst >> Set.mem covars >> not)
              in
              if Fn.non Set.is_empty oeqs then (
                Debug.print @@ lazy "@ assign opsig upper boundd";
                if print_log then (
                  print_ov_ov state.constr.sub_ov_ov;
                  print_ov_opsig state.constr.sub_ov_opsig;
                  print_opsig_ov state.constr.sub_opsig_ov);
                let preproc_res =
                  preprocess @@ SearchState.add_subst_opsigs oeqs state
                in
                solve_main ~embed
                  { constr = preproc_res.constr; subst = preproc_res.subst })
              else
                let eeqs =
                  let ev_eff_lst1, sub_evs_eff =
                    Set.partition_map state.constr.sub_evs_eff
                      ~f:(fun (evs, eff) ->
                        if Sort.is_evar eff then
                          let ev = Sort.let_evar eff in
                          match evs with
                          | [] -> First (ev, Sort.Pure)
                          | [ ev' ] -> First (ev, Sort.EVar ev')
                          | _ -> Second (evs, eff)
                        else Second (evs, eff))
                  in
                  let ev_eff_lst2, sub_effs_eff =
                    Set.partition_map state.constr.sub_effs_eff
                      ~f:(fun (effs, eff) ->
                        if Sort.is_evar eff then
                          let ev = Sort.let_evar eff in
                          match effs with
                          | [] -> First (ev, Sort.Pure)
                          | [ eff ] -> First (ev, eff)
                          | _ -> Second (effs, eff)
                        else Second (effs, eff))
                  in
                  let cevars =
                    Set.Poly.union_list
                      [
                        Set.concat_map sub_evs_eff
                          ~f:(snd >> Term.polar_evs_of_cont ~pos:true);
                        Set.concat_map sub_effs_eff ~f:(fun (effs, eff) ->
                            Set.Poly.union_list
                            @@ Term.polar_evs_of_cont ~pos:true eff
                               :: List.map effs
                                    ~f:(Term.polar_evs_of_cont ~pos:false));
                        (* state.constr.ecomps is empty *)
                        Set.concat_map state.constr.sub_ov_opsig
                          ~f:(fun (_, (map, opt)) ->
                            Term.polar_evs_of_opsig ~pos:true
                              (Sort.OpSig (map, opt)));
                        Set.concat_map state.constr.sub_opsig_ov
                          ~f:(fun ((map, opt), _) ->
                            Term.polar_evs_of_opsig ~pos:false
                              (Sort.OpSig (map, opt)));
                      ]
                  in
                  Set.Poly.of_list
                  @@ List.filter_map ~f:(function
                    | [ (ev, eff) ] -> Some (ev, eff)
                    | _ -> None)
                  @@ List.classify (fun (ev1, _) (ev2, _) -> Stdlib.(ev1 = ev2))
                  @@ Set.to_list
                  @@ Set.filter ~f:(fst >> Set.mem cevars >> not)
                  @@ Set.union ev_eff_lst1 ev_eff_lst2
                in
                if Fn.non Set.is_empty eeqs then (
                  Debug.print @@ lazy "@ assign singleton effect lower bound";
                  if print_log then (
                    print_evs_eff state.constr.sub_evs_eff;
                    print_effs_eff state.constr.sub_effs_eff);
                  let preproc_res =
                    preprocess @@ SearchState.add_subst_conts eeqs state
                  in
                  solve_main ~embed
                    { constr = preproc_res.constr; subst = preproc_res.subst })
                else
                  let sub_ev_ev, eeqs =
                    (* ToDo: construction of transitive closure is not required? *)
                    let sub_ev_ev =
                      Set.Poly.filter_map state.constr.sub_evs_eff ~f:(function
                        | [ ev ], eff when Sort.is_evar eff ->
                            Some (ev, Sort.let_evar eff)
                        | _ -> None)
                    in
                    let tc = PartOrd.transitive_closure_of sub_ev_ev in
                    let nodes =
                      Set.to_list
                      @@ Tuple2.uncurry Set.union (Set.unzip sub_ev_ev)
                    in
                    let dict =
                      Map.Poly.of_alist_exn
                      @@ List.mapi nodes ~f:(fun i n -> (n, i))
                    in
                    let uf = UnionFind.mk_size_uf ~size:(List.length nodes) in
                    Set.iter sub_ev_ev ~f:(fun (evar1, evar2) ->
                        if Set.mem tc (evar1, evar2) && Set.mem tc (evar2, evar1)
                        then
                          UnionFind.unite
                            (Map.Poly.find_exn dict evar1)
                            (Map.Poly.find_exn dict evar2)
                            uf);
                    let groups = UnionFind.get_groups uf in
                    ( sub_ev_ev,
                      Set.Poly.of_list
                      @@ List.concat_map groups ~f:(fun ids ->
                          let id, ids = List.hd_tl ids in
                          List.map ids ~f:(fun id' ->
                              ( List.nth_exn nodes id',
                                Sort.EVar (List.nth_exn nodes id) ))) )
                  in
                  if Fn.non Set.is_empty eeqs then (
                    Debug.print @@ lazy "@ remove evar cycles";
                    if print_log then print_ev_ev sub_ev_ev;
                    let preproc_res =
                      preprocess @@ SearchState.add_subst_conts eeqs state
                    in
                    solve_main ~embed
                      { constr = preproc_res.constr; subst = preproc_res.subst })
                  else
                    let uevars, eeqs =
                      let uevars =
                        (*Set.diff*)
                        Constr.lower_unconstrained_evars_of state.constr
                        (*(Subst.evars_of state.subst)*)
                      in
                      ( uevars,
                        Set.Poly.map uevars ~f:(fun ev -> (ev, Sort.Pure)) )
                    in
                    if Fn.non Set.is_empty uevars then (
                      Debug.print @@ lazy "@ remove lower unconstrained evars";
                      if census_on then
                        census "H0 lower-unconstrained evars=%d"
                          (Set.length uevars);
                      if print_log then (
                        print_ov_ov state.constr.sub_ov_ov;
                        print_ov_opsig state.constr.sub_ov_opsig;
                        print_opsig_ov state.constr.sub_opsig_ov;
                        print_evs_eff state.constr.sub_evs_eff;
                        print_effs_eff state.constr.sub_effs_eff;
                        Debug.print @@ lazy "==== lower unconstrained evars:";
                        Debug.print
                        @@ lazy
                             (String.concat_map_set ~sep:","
                                ~f:Ast.Ident.name_of_evar uevars));
                      let preproc_res =
                        preprocess @@ SearchState.add_subst_conts eeqs state
                      in
                      solve_main ~embed
                        {
                          constr = preproc_res.constr;
                          subst = preproc_res.subst;
                        })
                    else if
                      not
                        (Set.for_all state.constr.sub_effs_eff
                           ~f:(fun (effs, eff) ->
                             List.for_all (eff :: effs) ~f:Sort.is_evar))
                    then (
                      if print_log then (
                        print_ov_ov state.constr.sub_ov_ov;
                        print_ov_opsig state.constr.sub_ov_opsig;
                        print_opsig_ov state.constr.sub_opsig_ov;
                        print_evs_eff state.constr.sub_evs_eff;
                        print_effs_eff state.constr.sub_effs_eff);
                      let state = solve_effs_eff ~embed [] state in
                      let preproc_res =
                        preprocess
                        @@ PreprocState.from_subst_constr state.subst
                             state.constr
                      in
                      solve_main ~embed
                        {
                          constr = preproc_res.constr;
                          subst = preproc_res.subst;
                        })
                    else
                      let eeqs = last_resort_effects state.constr in
                      if Fn.non Set.is_empty eeqs then (
                        Debug.print
                        @@ lazy
                             "@ WARNING: heuristically solve recursive effect \
                              constraints";
                        if print_log then print_evs_eff state.constr.sub_evs_eff;
                        let preproc_res =
                          preprocess @@ SearchState.add_subst_conts eeqs state
                        in
                        solve_main ~embed
                          {
                            constr = preproc_res.constr;
                            subst = preproc_res.subst;
                          })
                      else if
                        Set.is_empty state.constr.sub_ov_ov
                        && Set.is_empty state.constr.sub_ov_opsig
                        && Set.is_empty state.constr.sub_opsig_ov
                      then
                        if
                          Set.for_all state.constr.sub_evs_eff
                            ~f:(snd >> Sort.is_evar)
                        then state
                        else (
                          if print_log then
                            print_evs_eff state.constr.sub_evs_eff;
                          (* only [ev <: C1 => C2] is left: see
                             [residual_failure] *)
                          raise (residual_failure state.constr))
                      else
                        let oeqs = last_resort_signatures state.constr in
                        if Fn.non Set.is_empty oeqs then (
                          Debug.print
                          @@ lazy
                               "@ WARNING: heuristically solve recursive opsig \
                                constraints";
                          if print_log then (
                            print_ov_ov state.constr.sub_ov_ov;
                            print_ov_opsig state.constr.sub_ov_opsig;
                            print_opsig_ov state.constr.sub_opsig_ov);
                          let preproc_res =
                            preprocess
                            @@ SearchState.add_subst_opsigs oeqs state
                          in
                          solve_main ~embed
                            {
                              constr = preproc_res.constr;
                              subst = preproc_res.subst;
                            })
                        else if false then
                          (* ToDo: make the following heuristics complete *)
                          let oeqs =
                            Set.Poly.of_list
                            @@ List.map ~f:(fun ov_opsigs ->
                                let ov_opsigs =
                                  List.dedup_keep_last ov_opsigs
                                in
                                let ov = fst @@ List.hd_exn ov_opsigs in
                                let ops =
                                  List.dedup_keep_last
                                  @@ List.concat_map ov_opsigs
                                       ~f:(snd >> fst >> List.map ~f:fst)
                                in
                                let opsig =
                                  Sort.OpSig
                                    ( ALMap.of_alist_exn
                                      @@ List.map ops ~f:(fun op ->
                                          (op, Sort.mk_fresh_svar ())),
                                      None )
                                in
                                if print_log then
                                  Debug.print
                                  @@ lazy
                                       ("introducing " ^ Term.str_of_opsig opsig);
                                (ov, opsig))
                            @@ List.classify (fun (ov1, _) (ov2, _) ->
                                Ast.Ident.rvar_equal ov1 ov2)
                            @@ Set.to_list state.constr.sub_ov_opsig
                          in
                          if Fn.non Set.is_empty oeqs then (
                            Debug.print
                            @@ lazy
                                 "@ WARNING: speculatively assign opsig upper \
                                  boundd";
                            if print_log then (
                              print_ov_ov state.constr.sub_ov_ov;
                              print_ov_opsig state.constr.sub_ov_opsig;
                              print_opsig_ov state.constr.sub_opsig_ov);
                            let preproc_res =
                              preprocess
                              @@ SearchState.add_subst_opsigs oeqs state
                            in
                            solve_main ~embed
                              {
                                constr = preproc_res.constr;
                                subst = preproc_res.subst;
                              })
                          else (
                            if print_log then (
                              print_ov_ov state.constr.sub_ov_ov;
                              print_ov_opsig state.constr.sub_ov_opsig;
                              print_opsig_ov state.constr.sub_opsig_ov);
                            (* only unsettled row bounds are left: see
                               [residual_failure] *)
                            raise (residual_failure state.constr))
                        else
                          (* ToDo: this prevents us to obtain the least solution *)
                          let covars =
                            Set.Poly.union_list
                              [
                                Set.concat_map state.constr.sub_evs_eff
                                  ~f:(snd >> Term.polar_rvs_of_cont ~pos:true);
                                Set.concat_map state.constr.sub_effs_eff
                                  ~f:(fun (effs, eff) ->
                                    Set.Poly.union_list
                                    @@ Term.polar_rvs_of_cont ~pos:true eff
                                       :: List.map effs
                                            ~f:
                                              (Term.polar_rvs_of_cont ~pos:false));
                                (* state.constr.ecomps is empty *)
                                Set.concat_map state.constr.sub_ov_opsig
                                  ~f:(fun (_, (map, opt)) ->
                                    Term.polar_rvs_of_opsig ~pos:true
                                      (Sort.OpSig (map, opt)));
                                Set.concat_map state.constr.sub_opsig_ov
                                  ~f:(fun ((map, opt), _) ->
                                    Term.polar_rvs_of_opsig ~pos:false
                                      (Sort.OpSig (map, opt)));
                              ]
                          in
                          let oeqs =
                            Set.Poly.of_list
                            @@ List.filter_map ~f:(function
                              | [ (ov, opsig) ] -> Some (ov, opsig)
                              | _ -> None)
                            @@ List.classify (fun (ov1, _) (ov2, _) ->
                                Stdlib.(ov1 = ov2))
                            @@ Set.to_list
                            @@ Set.filter ~f:(fst >> Set.mem covars >> not)
                            @@ Set.union
                                 (if false then
                                    Set.Poly.map state.constr.sub_ov_ov
                                      ~f:(fun (ovar1, ovar2) ->
                                        ( ovar2,
                                          Sort.mk_empty_open_opsig_from_rvar
                                            ovar1 ))
                                  else Set.Poly.empty)
                                 (Set.Poly.map state.constr.sub_opsig_ov
                                    ~f:(fun ((map, opt), ovar) ->
                                      (ovar, Sort.OpSig (map, opt))))
                          in
                          if Fn.non Set.is_empty oeqs then (
                            Debug.print
                            @@ lazy
                                 "@ WARNING: assign singleton opsig lower bound";
                            if print_log then (
                              print_ov_ov state.constr.sub_ov_ov;
                              print_ov_opsig state.constr.sub_ov_opsig;
                              print_opsig_ov state.constr.sub_opsig_ov;
                              Debug.print @@ lazy "==== covars:";
                              Debug.print
                              @@ lazy
                                   (String.concat_map_set ~sep:","
                                      ~f:Ast.Ident.name_of_rvar covars);
                              Debug.print @@ lazy "==== oeqs:";
                              Debug.print
                              @@ lazy
                                   (String.concat_map_set ~sep:","
                                      ~f:(fun (ov, opsig) ->
                                        Ast.Ident.name_of_rvar ov ^ "="
                                        ^ Ast.LogicOld.Term.str_of_opsig opsig)
                                      oeqs));
                            let preproc_res =
                              preprocess
                              @@ SearchState.add_subst_opsigs oeqs state
                            in
                            solve_main ~embed
                              {
                                constr = preproc_res.constr;
                                subst = preproc_res.subst;
                              })
                          else (
                            if print_log then (
                              print_ov_ov state.constr.sub_ov_ov;
                              print_ov_opsig state.constr.sub_ov_opsig;
                              print_opsig_ov state.constr.sub_opsig_ov);
                            (* only unsettled row bounds are left: see
                               [residual_failure] *)
                            raise (residual_failure state.constr))

  let resolve_evs (constr : Constr.t) =
    if print_log then Debug.print @@ lazy "### resolve_evs";
    if print_log then (
      print_evs_eff constr.sub_evs_eff;
      print_effs_eff constr.sub_effs_eff);
    assert (
      Set.for_all constr.sub_evs_eff ~f:(snd >> Sort.is_evar)
      && Set.for_all constr.sub_effs_eff ~f:(fun (effs, eff) ->
          List.for_all (eff :: effs) ~f:Sort.is_evar));
    Set.Poly.union_list
      [
        Set.concat_map constr.sub_evs_eff ~f:(fun (evs, eff) ->
            Set.Poly.of_list (Sort.let_evar eff :: evs));
        Set.concat_map constr.sub_effs_eff ~f:(fun (effs, eff) ->
            Set.Poly.of_list (List.map (eff :: effs) ~f:Sort.let_evar));
      ]

  (* The substitution that resolves the subsort constraints left between sort
     variables, as a list of [(sv, rep)] meaning [sv := rep].

     Contract: a constraint [sv1 <: sv2] that survives to this point is read
     as the equality [sv1 = sv2] (a sort variable has no subsort but itself
     once no arrow is left to carry an effect), so every connected component
     of the graph of [constr.sub_sv_sv] becomes one variable.  The
     representative of a component is its least variable among [init_svs] --
     those of the constraints the caller passed in, which the caller's types
     mention -- or its least variable if it has none; every other variable of
     the component is mapped to it, and no representative is mapped.  The
     result is therefore idempotent and satisfies every constraint in
     [constr.sub_sv_sv].

     The equalities have to be closed transitively, not resolved pair by pair:
     a pure computation embedded where an effectful one is expected has a
     triple whose initial and final answer types are equal ([Pure <: s => s']
     yields [s <: s'], see [simplify_esubs]), and in an [if] that joins such a
     branch with one that performs an operation, the two answer types of the
     join are connected only through the pure branch's fresh variables.
     Resolving each pair to a representative separately mapped such a
     variable to both answer types at once, one was kept arbitrarily, and the
     function was generalised over two unrelated answer types: the normal
     return of its pure branch then never reached the result, and a false
     assertion about a caller was proved.

     Why equality and not the subsort itself: a sort variable left here is
     generalised by the caller, and a sort scheme carries no subsort
     constraints, so two variables related by [<:] but kept apart would be
     instantiated independently and the constraint would hold for no instance
     in particular.  Identifying a component is the most general substitution
     that keeps every such constraint for every instance (the most general
     unifier of the component's equations).  It is stronger than the subsorts
     need where the variables would later be instantiated to sorts related by
     a proper subsort (a pure arrow below an effectful one), so it can make a
     solve fail that the subsort direction would admit: a cost in
     completeness, never in soundness.

     What a consumer may rely on is therefore the typing, not the shape a
     particular instance has: after the collapse an answer type that a
     pair-by-pair resolution left pure can be an effectful computation sort
     (when a handler clause re-performs an operation, the handled program's
     top-level computation is typed as performing it, which it does).  The
     CPS translation for model checking reads every arity that must match
     something fixed outside the typing -- a tree constructor's rank in the
     specification -- from the operation declarations, not from these
     instances. *)
  let resolve_svs ~init_svs (constr : Constr.t) =
    if print_log then Debug.print @@ lazy "### resolve_svs";
    let components =
      Set.fold constr.sub_sv_sv ~init:[] ~f:(fun comps (sv1, sv2) ->
          let touching, rest =
            List.partition_tf comps ~f:(fun comp ->
                Set.mem comp sv1 || Set.mem comp sv2)
          in
          Set.Poly.union_list (Set.Poly.of_list [ sv1; sv2 ] :: touching)
          :: rest)
    in
    List.concat_map components ~f:(fun comp ->
        let rep =
          match Set.min_elt (Set.inter comp init_svs) with
          | Some sv -> sv
          | None -> Set.min_elt_exn comp
        in
        List.map (Set.to_list (Set.remove comp rep)) ~f:(fun sv -> (sv, rep)))

  let squash_evs_cont e =
    let evs = Set.to_list (Term.evs_of_cont e) in
    let sbs =
      Map.Poly.of_alist_exn (List.map evs ~f:(fun ev -> (ev, Sort.Pure)))
    in
    Term.subst_conts_cont sbs e

  let squash_evs_sort s =
    let evs = Set.to_list (Term.evs_of_sort s) in
    let sbs =
      Map.Poly.of_alist_exn (List.map evs ~f:(fun ev -> (ev, Sort.Pure)))
    in
    Term.subst_conts_sort sbs s

  let squash_evs_opsig o =
    let evs = Set.to_list (Term.evs_of_opsig o) in
    let sbs =
      Map.Poly.of_alist_exn (List.map evs ~f:(fun ev -> (ev, Sort.Pure)))
    in
    Term.subst_conts_opsig sbs o

  let squash_rvs_cont e =
    let rvs = Set.to_list (Term.rvs_of_cont e) in
    let sbs =
      Map.Poly.of_alist_exn
        (List.map rvs ~f:(fun rv -> (rv, Sort.empty_closed_opsig)))
    in
    Term.subst_opsigs_cont sbs e

  let squash_rvs_sort s =
    let rvs = Set.to_list (Term.rvs_of_sort s) in
    let sbs =
      Map.Poly.of_alist_exn
        (List.map rvs ~f:(fun rv -> (rv, Sort.empty_closed_opsig)))
    in
    Term.subst_opsigs_sort sbs s

  let squash_rvs_opsig o =
    let rvs = Set.to_list (Term.rvs_of_opsig o) in
    let sbs =
      Map.Poly.of_alist_exn
        (List.map rvs ~f:(fun rv -> (rv, Sort.empty_closed_opsig)))
    in
    Term.subst_opsigs_opsig sbs o

  let resolve ~init_svs (state : SearchState.t) : Subst.t =
    if print_log then Debug.print @@ lazy "### resolve";
    let subst_ev_pure = resolve_evs state.constr in
    let subst_sv_sv = resolve_svs ~init_svs state.constr in
    (* A conflict below means the residual sequences ask an effect variable
       to be pure while the substitution already binds it to another effect:
       the finishing step does not apply, so, as at the stops of [solve_main],
       this is a refusal ([Solve_failure], reported in words by the callers)
       and not an internal error. *)
    let etheta =
      Map.force_merge
        ~catch_dup:(fun (ev, e1, e2) ->
          raise
          @@ Solve_failure
               (sprintf
                  "the finishing step makes %s pure, but it is already bound \
                   (%s |-> %s != %s)"
                  (Ast.Ident.name_of_evar ev) (Ast.Ident.name_of_evar ev)
                  (Term.str_of_cont e1) (Term.str_of_cont e2)))
        (Map.of_set_exn
        @@ Set.Poly.map subst_ev_pure ~f:(fun ev -> (ev, Sort.Pure)))
      @@ Map.Poly.map state.subst.etheta ~f:(fun e ->
          let e =
            Set.fold subst_ev_pure ~init:e ~f:(fun e ev ->
                subst_cont_cont (ev, Sort.Pure) e)
          in
          List.fold subst_sv_sv ~init:e ~f:(fun e (sv1, sv2) ->
              subst_sort_cont (sv1, Sort.SVar sv2) e))
    in
    let stheta =
      Map.force_merge
        ~catch_dup:(fun (sv, s1, s2) ->
          raise
          @@ Solve_failure
               (sprintf
                  "the finishing step equates sort variable %s with %s, but \
                   it is already bound to %s"
                  (name_of_svar sv) (Term.str_of_sort s1) (Term.str_of_sort s2)))
        (Map.Poly.of_alist_exn
        @@ List.map subst_sv_sv ~f:(fun (sv1, sv2) -> (sv1, Sort.SVar sv2)))
      @@ Map.Poly.map state.subst.stheta ~f:(fun s ->
          let s =
            Set.fold subst_ev_pure ~init:s ~f:(fun s ev ->
                subst_cont_sort (ev, Sort.Pure) s)
          in
          List.fold subst_sv_sv ~init:s ~f:(fun s (sv1, sv2) ->
              subst_sort_sort (sv1, Sort.SVar sv2) s))
    in
    let otheta =
      Map.Poly.map state.subst.otheta ~f:(fun o ->
          let o =
            Set.fold subst_ev_pure ~init:o ~f:(fun o ev ->
                subst_cont_opsig (ev, Sort.Pure) o)
          in
          List.fold subst_sv_sv ~init:o ~f:(fun o (sv1, sv2) ->
              subst_sort_opsig (sv1, Sort.SVar sv2) o))
    in
    { etheta; stheta; otheta }

  let eliminate ~init_evs ~init_svs ~init_rvs (subst : Subst.t) : Subst.t =
    if print_log then Debug.print @@ lazy "### eliminate";
    let etheta = Map.Poly.filter_keys subst.etheta ~f:(Set.mem init_evs) in
    let stheta = Map.Poly.filter_keys subst.stheta ~f:(Set.mem init_svs) in
    let otheta = Map.Poly.filter_keys subst.otheta ~f:(Set.mem init_rvs) in
    { etheta; stheta; otheta }

  let squash ~init_evs ~init_rvs (subst : Subst.t) : Subst.t =
    if print_log then Debug.print @@ lazy "### squash";
    let etheta =
      Map.Poly.map subst.etheta ~f:(squash_evs_cont <<< squash_rvs_cont)
    in
    let etheta =
      Set.fold init_evs ~init:etheta ~f:(fun etheta ev ->
          match Map.Poly.add etheta ~key:ev ~data:Sort.Pure with
          | `Ok etheta -> etheta
          | `Duplicate -> etheta)
    in
    let stheta =
      Map.Poly.map subst.stheta ~f:(squash_evs_sort <<< squash_rvs_sort)
    in
    let otheta =
      Map.Poly.map subst.otheta ~f:(squash_evs_opsig <<< squash_rvs_opsig)
    in
    let otheta =
      Set.fold init_rvs ~init:otheta ~f:(fun otheta rv ->
          match Map.Poly.add otheta ~key:rv ~data:Sort.empty_closed_opsig with
          | `Ok otheta -> otheta
          | `Duplicate -> otheta)
    in
    { etheta; stheta; otheta }

  let postprocess ~init_evs ~init_svs ~init_rvs =
    if print_log then Debug.print @@ lazy "### postprocess";
    resolve ~init_svs
    >> eliminate ~init_evs ~init_svs ~init_rvs
    >> squash ~init_evs ~init_rvs

  let solve ?(templates = []) eff_constrs opsig_constrs =
    let ecompsubs = eff_constrs in
    let osubs = opsig_constrs in
    let init_evs =
      Set.Poly.union_list
        [
          Set.Poly.union_list (List.map templates ~f:Term.evs_of_triple);
          Set.concat_map ecompsubs ~f:(fun (effs, eff) ->
              Set.Poly.union_list (List.map (eff :: effs) ~f:Term.evs_of_cont));
          Set.concat_map osubs ~f:(fun (o1, o2) ->
              Set.Poly.union_list [ Term.evs_of_opsig o1; Term.evs_of_opsig o2 ]);
        ]
    in
    let init_svs =
      Set.Poly.union_list
        [
          Set.concat_map ecompsubs ~f:(fun (effs, eff) ->
              Set.Poly.union_list (List.map (eff :: effs) ~f:Term.svs_of_cont));
          Set.concat_map osubs ~f:(fun (o1, o2) ->
              Set.Poly.union_list [ Term.svs_of_opsig o1; Term.svs_of_opsig o2 ]);
        ]
    in
    let init_rvs =
      Set.Poly.union_list
        [
          Set.Poly.union_list (List.map templates ~f:Term.rvs_of_triple);
          Set.concat_map ecompsubs ~f:(fun (effs, eff) ->
              Set.Poly.union_list (List.map (eff :: effs) ~f:Term.rvs_of_cont));
          Set.concat_map osubs ~f:(fun (o1, o2) ->
              Set.Poly.union_list [ Term.rvs_of_opsig o1; Term.rvs_of_opsig o2 ]);
        ]
    in
    forced_shape_count := 0;
    let sol =
      try
        try
          PreprocState.init ecompsubs osubs
          |> preprocess |> SearchState.init |> solve_main ~embed:false
          |> postprocess ~init_evs ~init_svs ~init_rvs
        with
        (* Assigning a row variable joins the explicit operations of every
           open row it ends with to the assigned row's, and an operation the
           two list with different signatures has no join.  No rule below
           records that a row variable lacks the operations listed beside it
           (none is needed for soundness under the join), so such an
           assignment can be reached; it means this search found no typing,
           which every caller reports as a refusal, not an internal error. *)
        | Failure msg
          when String.is_prefix msg ~prefix:row_conflict_prefix ->
            raise
            @@ Solve_failure
                 (String.drop_prefix msg
                    (String.length row_conflict_prefix))
      with e ->
        if census_on then
          census "solve failed: %s"
            (match e with
            | Solve_failure reason -> "Solve_failure " ^ reason
            | e -> Exn.to_string e);
        raise e
    in
    if census_on then
      census "solve ok digest=%s"
        (Stdlib.Digest.to_hex @@ Stdlib.Digest.string
        @@ String.concat ~sep:";"
        @@ List.concat
             [
               List.map (Map.Poly.to_alist sol.etheta) ~f:(fun (ev, e) ->
                   name_of_evar ev ^ ":=" ^ Term.str_of_cont e);
               List.map (Map.Poly.to_alist sol.stheta) ~f:(fun (sv, t) ->
                   name_of_svar sv ^ ":=" ^ Term.str_of_sort t);
               List.map (Map.Poly.to_alist sol.otheta) ~f:(fun (rv, o) ->
                   name_of_rvar rv ^ ":=" ^ Term.str_of_opsig o);
             ]);
    Debug.print @@ lazy "==== found solution:";
    Map.Poly.iteri sol.etheta ~f:(fun ~key:ev ~data:e ->
        Debug.print
        @@ lazy (sprintf "%s := %s" (name_of_evar ev) (Term.str_of_cont e)));
    Map.Poly.iteri sol.stheta ~f:(fun ~key:sv ~data:s ->
        Debug.print
        @@ lazy (sprintf "%s := %s" (name_of_svar sv) (Term.str_of_sort s)));
    Map.Poly.iteri sol.otheta ~f:(fun ~key:sv ~data:s ->
        Debug.print
        @@ lazy (sprintf "%s := %s" (name_of_rvar sv) (Term.str_of_opsig s)));
    sol
end
