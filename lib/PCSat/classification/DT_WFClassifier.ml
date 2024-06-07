open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld
open PCSatCommon

module Config = struct
  let qualifier_type_of_json = function
    | `String "interval" -> Ok `Interval
    | `String "octagon" -> Ok `Octagon
    | _ -> Error "invalid qualifier type (expected 'interval' or 'octagon')"

  let qualifier_type_to_json = function
    | `Interval -> `String "interval"
    | `Octagon -> `String "octagon"

  type t = {
    verbose : bool;
    lex_deg : int;  (** Degree of lexicographic ranking function >= 0 *)
    qualifier : [ `Interval | `Octagon ];
        [@of_yojson qualifier_type_of_json] [@to_json qualifier_type_to_json]
        (** Type of qualifiers (for eager halfspace generation) *)
    approx_level : int;
        (** Approximation level of hyperplanes obtained from svm. If approx_level > 0, then use truncated continued fractions with length at most approx_level. If approx_level = 0, then the length of truncated continued fractions is chosen automatically. *)
    csvm : float;  (** c parameter for csvm *)
    eager_halfspace_gen : bool;  (** Enable eager halfspace generation. *)
    optimize_sum_coeff : bool;
        (** Optimize the sum of absolute values of coefficients of a piecewise affine ranking function. *)
    qualifier_reduction : bool;  (** Enable qualifier reduction. *)
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let check_lex_deg cfg =
    if cfg.lex_deg >= 0 then Ok cfg
    else Or_error.error_string "negative value is not supported for 'lex_deg'"

  let check_approx_level cfg =
    if cfg.approx_level >= 0 then Ok cfg
    else
      Or_error.error_string "negative value is not supported for 'approx_level'"

  let instantiate_ext_files cfg =
    let open Or_error in
    check_lex_deg cfg >>= check_approx_level
end

module Halfspace : sig
  type t

  val of_affine : Affine.t -> t
  val to_affine : t -> Affine.t
  val formula_of : t -> Formula.t
  val term_of : t -> Term.t
  val str_of : t -> string
  val eval : Ident.tvar list -> Term.t list -> t -> bool
end = struct
  type t = Affine.t

  (* f(x) --> f(x) >= 0 *)
  let of_affine a = a

  (* f(x) >= 0 --> f(x) *)
  let to_affine a = a

  let atom_of affine =
    let senv =
      Affine.vars affine
      |> List.map ~f:(fun x -> (x, Logic.IntTerm.SInt))
      |> Map.Poly.of_alist_exn
    in
    let tm =
      Logic.ExtTerm.to_old_term Map.Poly.empty senv (Affine.term_of affine) []
    in
    T_int.mk_geq tm (T_int.zero ())

  let term_of h = T_bool.of_atom (atom_of h)
  let formula_of h = Formula.mk_atom (atom_of h)
  let str_of h = formula_of h |> Evaluator.simplify |> Formula.str_of

  let eval params_src_tvar x h =
    let map = List.zip_exn params_src_tvar x |> Map.Poly.of_alist_exn in
    Formula.subst map (formula_of h) |> Evaluator.eval
end

let force_int tm =
  match Evaluator.eval_term tm with Value.Int n -> n | _ -> assert false

module StateExample : sig
  type t

  val of_term : Term.t list -> t
  val term_of : t -> Term.t list
  val z_of : t -> Z.t list
  val str_of : t -> string
end = struct
  type t = Term.t list

  let of_term l = l
  let term_of l = l
  let z_of = List.map ~f:force_int

  let str_of l =
    String.paren @@ String.concat_map_list ~sep:", " ~f:Term.str_of l
end

module TransitionExample : sig
  type t = StateExample.t * StateExample.t

  val of_term : Term.t list -> t
end = struct
  type t = StateExample.t * StateExample.t

  let of_term l =
    let x, y = List.split_n l (List.length l / 2) in
    (StateExample.of_term x, StateExample.of_term y)
end

module Template : sig
  val gen_template_affine : sort_env_list -> Term.t * Term.t list

  val gen_template_lexicographic :
    int -> sort_env_list -> Term.t list * Term.t list
end = struct
  (** Make an affine template and the list of all parameters. *)
  let gen_template_affine vars =
    let p = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
    let template, params =
      List.fold vars ~init:(p, [ p ]) ~f:(fun (template, params) (tvar, sort) ->
          let p = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
          ( T_int.mk_add template (T_int.mk_mult p (Term.mk_var tvar sort)),
            p :: params ))
    in
    (template, params)

  let gen_template_lexicographic deg vars =
    let gather =
      List.fold_right ~init:([], []) ~f:(fun (t, p) (ts, p') ->
          (t :: ts, p @ p'))
    in
    List.init deg ~f:(fun _ -> gen_template_affine vars) |> gather
end

module Lexicographic : sig
  type t = Ast.LogicOld.Term.t list

  val gt : t -> t -> Ast.LogicOld.Formula.t
  val gt_degenerate_negative : t -> t -> Ast.LogicOld.Formula.t
end = struct
  type t = Term.t list

  let gt x y =
    let rec gt' eq = function
      | [] -> []
      | (x, y) :: xys ->
          let x_gt_y =
            Formula.mk_and
              (Formula.mk_atom (T_int.mk_geq x (T_int.zero ())))
              (Formula.mk_atom (T_int.mk_gt x y))
          in
          let x_eq_y = Formula.eq x y in
          let xy_neg =
            Formula.mk_and
              (Formula.mk_atom (T_int.mk_lt x (T_int.zero ())))
              (Formula.mk_atom (T_int.mk_lt y (T_int.zero ())))
          in
          Formula.and_of (x_gt_y :: eq)
          :: gt' (Formula.mk_or x_eq_y xy_neg :: eq) xys
    in
    Formula.or_of (gt' [] (List.zip_exn x y))

  let gt_degenerate_negative x y =
    let rec gt_degenerate_negative' eq = function
      | [] -> []
      | (x, y) :: xys ->
          let x_gt_y =
            Formula.mk_and
              (Formula.mk_atom (T_int.mk_geq x (T_int.zero ())))
              (Formula.mk_atom (T_int.mk_gt x y))
          in
          Formula.and_of (x_gt_y :: eq)
          :: gt_degenerate_negative' (Formula.eq x y :: eq) xys
    in
    Formula.or_of (gt_degenerate_negative' [] (List.zip_exn x y))
end

module Make (Cfg : Config.ConfigType) (APCSP : PCSP.Problem.ProblemType) =
struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  type classifier = sort_env_map * (Ident.pvar * (sort_env_list * Formula.t))

  let model_postprocess model params =
    let zero_model =
      List.map
        ~f:(fun p ->
          let (t, _), _ = Term.let_var p in
          (t, T_int.zero ()))
        params
      |> Map.Poly.of_alist_exn
    in
    let model = remove_dontcare model |> Map.Poly.of_alist_exn in
    Map.Poly.merge model zero_model ~f:(fun ~key:_ -> function
      | `Left v | `Both (v, _) | `Right v -> Some v)

  module EagerHalfspaceGenerator : sig
    val gen_halfspaces :
      sort_env_list -> StateExample.t list -> Halfspace.t list
  end = struct
    let gen_halfspaces_interval params_src state_examples =
      let params_src_tvar = List.map ~f:fst params_src in
      List.concat_map
        ~f:(fun x -> StateExample.z_of x |> List.zip_exn params_src_tvar)
        state_examples
      |> List.concat_map ~f:(fun (v, b) ->
             let affine = Affine.(of_var v - of_z b) in
             [ affine; Affine.( ~- ) affine ])
      |> List.dedup_and_sort ~compare:Affine.compare
      |> List.map ~f:Halfspace.of_affine

    let rec combination2 = function
      | [] -> []
      | x :: l -> List.map ~f:(fun y -> (x, y)) l @ combination2 l

    let gen_halfspaces_octagon params_src state_examples =
      let params_src_tvar = List.map ~f:fst params_src in
      List.map
        ~f:(fun x -> StateExample.z_of x |> List.zip_exn params_src_tvar)
        state_examples
      |> List.concat_map ~f:combination2
      |> List.concat_map ~f:(fun ((p1, x1), (p2, x2)) ->
             let p1 = Affine.of_var p1 in
             let p2 = Affine.of_var p2 in
             Affine.
               [
                 p1 + p2 + of_z Z.(~-x1 - x2);
                 p1 - p2 + of_z Z.(~-x1 + x2);
                 ~-p1 + p2 + of_z Z.(x1 - x2);
                 ~-p1 - p2 + of_z Z.(x1 + x2);
               ])
      |> List.dedup_and_sort ~compare:Affine.compare
      |> List.map ~f:Halfspace.of_affine

    let gen_halfspaces params_src state_examples =
      match config.qualifier with
      | `Interval -> gen_halfspaces_interval params_src state_examples
      | `Octagon ->
          gen_halfspaces_interval params_src state_examples
          @ gen_halfspaces_octagon params_src state_examples
  end

  module Table : sig
    type t

    type halfspace_id
    (** type of indices of halfspaces *)

    type state_example_id
    (** type of indices of state examples *)

    val get_halfspace : t -> halfspace_id -> Halfspace.t
    val make_eager : sort_env_list -> TransitionExample.t list -> t
    val make_lazy : sort_env_list -> TransitionExample.t list -> t
    val add_hs : t -> Halfspace.t -> halfspace_id

    (*val get_hs_size : t -> int*)

    (*val get_all_transition_examples :
      t -> TransitionExample.t array*)

    val get_transition_example_id_list :
      t -> (state_example_id * state_example_id) list

    val get_hs_id_list : t -> halfspace_id list
    val eval_halfspace : t -> state_example_id -> halfspace_id -> bool
    val get_state_example : t -> state_example_id -> StateExample.t
    val get_params_src : t -> sort_env_list

    val get_state_example_map :
      t -> state_example_id -> (Ident.tvar, Term.t) Map.Poly.t

    val is_eager : t -> bool
  end = struct
    type t =
      | Eager of
          bool array array
          * Halfspace.t array
          * sort_env_list
          * TransitionExample.t array
      | Lazy of
          (int, bool array) Hashtbl.t
          * (int, Halfspace.t) Hashtbl.t
          * int ref
          * sort_env_list
          * TransitionExample.t array

    type halfspace_id = int
    type state_example_id = int

    let get_halfspace = function
      | Eager (_, hs, _, _) -> fun i -> hs.(i)
      | Lazy (_, hs, _, _, _) -> fun i -> Option.value_exn (Hashtbl.find hs i)

    let make_eager params_src transition_examples =
      let state_examples =
        List.concat_map ~f:(fun (x, y) -> [ x; y ]) transition_examples
      in
      let hs =
        EagerHalfspaceGenerator.gen_halfspaces params_src state_examples
      in
      let params_src_tvar = List.map ~f:fst params_src in
      Debug.print
      @@ lazy (sprintf "number of input qualifiers: %d" (List.length hs));
      let table, hs =
        if config.qualifier_reduction then (
          let choose_best_hs l =
            let abs_sum_of_coeff h =
              List.fold ~init:Z.zero
                ~f:(fun sum x -> Z.(sum + abs x))
                (Halfspace.to_affine h |> Affine.coeffs)
            in
            match
              List.map ~f:(fun h -> (h, abs_sum_of_coeff h)) l
              |> List.min_elt ~compare:(fun (_, x) (_, y) -> Z.compare x y)
            with
            | None -> assert false
            | Some (h, _) -> h
          in
          let rec make_table = function
            | [] -> fun _ -> []
            | hs -> (
                function
                | [] -> [ (choose_best_hs hs, []) ]
                | ex :: l ->
                    let hs_t, hs_f =
                      List.partition_tf hs
                        ~f:
                          (Halfspace.eval params_src_tvar
                             (StateExample.term_of ex))
                    in
                    let table_t = make_table hs_t l in
                    let table_f = make_table hs_f l in
                    List.map ~f:(fun (h, t) -> (h, true :: t)) table_t
                    @ List.map ~f:(fun (h, t) -> (h, false :: t)) table_f)
          in
          let hs, table =
            make_table hs
              (List.fold_right transition_examples
                 ~f:(fun (x, y) l -> x :: y :: l)
                 ~init:[])
            |> List.unzip
          in
          let table = List.map ~f:Array.of_list table |> Array.of_list in
          let hs = Array.of_list hs in
          Debug.print
          @@ lazy (sprintf "number of reduced qualifiers: %d" (Array.length hs));
          (table, hs))
        else
          let table =
            Array.make_matrix ~dimx:(List.length hs)
              ~dimy:(2 * List.length transition_examples)
              true
          in
          List.iteri hs ~f:(fun i h ->
              List.iteri transition_examples ~f:(fun j (x, y) ->
                  table.(i).(2 * j) <-
                    Halfspace.eval params_src_tvar (StateExample.term_of x) h;
                  table.(i).((2 * j) + 1) <-
                    Halfspace.eval params_src_tvar (StateExample.term_of y) h));
          let hs = Array.of_list hs in
          (table, hs)
      in
      Eager (table, hs, params_src, Array.of_list transition_examples)

    let make_lazy params_src transition_examples =
      let table = Hashtbl.create (module Int) in
      let hs = Hashtbl.create (module Int) in
      let ex = Array.of_list transition_examples in
      Lazy (table, hs, ref 0, params_src, ex)

    let add_hs t h =
      match t with
      | Eager _ -> failwith "adding qualifiers is not allowed in eager mode"
      | Lazy (table, hs, r, params_src, ex) ->
          let h_id = !r in
          let params_src_tvar = List.map ~f:fst params_src in
          let a =
            Array.init
              (2 * Array.length ex)
              ~f:(fun i ->
                let x, y = ex.(i / 2) in
                let x = if i % 2 = 0 then x else y in
                Halfspace.eval params_src_tvar (StateExample.term_of x) h)
          in
          Hashtbl.add_exn table ~key:h_id ~data:a;
          Hashtbl.add_exn hs ~key:h_id ~data:h;
          r := h_id + 1;
          h_id

    let get_all_transition_examples = function
      | Eager (_, _, _, ex) -> ex
      | Lazy (_, _, _, _, ex) -> ex

    let get_transition_example_id_list t =
      let len = get_all_transition_examples t |> Array.length in
      List.init len ~f:(fun i -> (2 * i, (2 * i) + 1))

    let get_hs_size = function
      | Eager (_, hs, _, _) -> Array.length hs
      | Lazy (_, hs, _, _, _) -> Hashtbl.length hs

    let get_hs_id_list t =
      let len = get_hs_size t in
      List.init len ~f:(fun i -> i)

    let eval_halfspace t x_id =
      match t with
      | Eager (table, _, _, _) -> fun h_id -> table.(h_id).(x_id)
      | Lazy (table, _, _, _, _) ->
          fun h_id -> (Option.value_exn (Hashtbl.find table h_id)).(x_id)

    let get_state_example t i =
      let ex = get_all_transition_examples t in
      let x, y = ex.(i / 2) in
      if i % 2 = 0 then x else y

    let get_params_src = function
      | Eager (_, _, params_src, _) -> params_src
      | Lazy (_, _, _, params_src, _) -> params_src

    let get_state_example_map t i =
      let params_src_tvar = List.map ~f:fst @@ get_params_src t in
      get_state_example t i |> StateExample.term_of
      |> List.zip_exn params_src_tvar
      |> Map.Poly.of_alist_exn

    let is_eager = function Eager _ -> true | Lazy _ -> false
  end

  type 'a dtree =
    | Leaf of 'a
    | Node of Table.halfspace_id * 'a dtree * 'a dtree

  let rec dtree_fmap f = function
    | Leaf x -> Leaf (f x)
    | Node (h, tt, ft) -> Node (h, dtree_fmap f tt, dtree_fmap f ft)

  (* classify transition examples by a halfspace h *)
  let rec classify_transition_examples t h = function
    | [] -> ([], [], [], [])
    | (x, y) :: ex -> (
        let tt, tf, ft, ff = classify_transition_examples t h ex in
        match (Table.eval_halfspace t x h, Table.eval_halfspace t y h) with
        | true, true -> ((x, y) :: tt, tf, ft, ff)
        | true, false -> (tt, (x, y) :: tf, ft, ff)
        | false, true -> (tt, tf, (x, y) :: ft, ff)
        | false, false -> (tt, tf, ft, (x, y) :: ff))

  let generate_constraints_template lex2wf t transition_example_id_list =
    let template_terms, _ =
      Template.gen_template_lexicographic (config.lex_deg + 1)
        (Table.get_params_src t)
    in
    let fenv = Map.Poly.empty in
    (*TODO: generate fenv*)
    let t_src_gt_t_dst =
      List.map
        ~f:(fun (src, dst) ->
          let t_src =
            List.map
              ~f:(Term.subst (Table.get_state_example_map t src))
              template_terms
          in
          let t_dst =
            List.map
              ~f:(Term.subst (Table.get_state_example_map t dst))
              template_terms
          in
          lex2wf t_src t_dst)
        transition_example_id_list
    in
    (fenv, t_src_gt_t_dst)

  let max_sat_template lex2wf t transition_example_id_list =
    let fenv, t_x_gt_t_y =
      generate_constraints_template lex2wf t transition_example_id_list
    in
    let soft_constraints =
      Map.Poly.singleton "txgtty" (List.map ~f:(fun x -> (x, 1)) t_x_gt_t_y)
    in
    match Z3Smt.Z3interface.max_smt ~id fenv [] soft_constraints with
    | Some (num_sat, _) -> num_sat
    | None -> assert false

  module DecisionTreeTemplate : sig
    type t = (Term.t list * Term.t list) dtree

    val eval_dtree :
      Table.t -> Table.state_example_id -> t -> Ast.LogicOld.Term.t list

    val to_term : Table.t -> t -> Ast.LogicOld.Term.t list
    val collect_params : t -> Term.t list
  end = struct
    type t = (Term.t list * Term.t list) dtree

    let rec eval_dtree t x = function
      | Leaf (term, _) ->
          List.map ~f:(Term.subst (Table.get_state_example_map t x)) term
      | Node (h, tt, ft) ->
          if Table.eval_halfspace t x h then eval_dtree t x tt
          else eval_dtree t x ft

    let rec to_term t = function
      | Leaf (term, _) -> term
      | Node (h, tt, ft) ->
          let tf = List.zip_exn (to_term t tt) (to_term t ft) in
          List.map tf ~f:(fun (tmt, tmf) ->
              T_bool.mk_if_then_else
                (Table.get_halfspace t h |> Halfspace.term_of)
                tmt tmf)

    let rec collect_params = function
      | Leaf (_, p) -> p
      | Node (_, tt, ft) -> collect_params tt @ collect_params ft
  end

  module BuildDT : sig
    (*val assign_label :
        Table.t ->
        (Table.state_example_id * Table.state_example_id) list ->
        Lacaml.D.mat * Lacaml.D.vec

      val has_examples_in_both_side :
        Table.t -> Table.halfspace_id -> Table.state_example_id list -> bool

      val filter_hyperplanes :
        Table.t ->
        Table.state_example_id list ->
        Table.halfspace_id list ->
        Table.halfspace_id list

      val choose_halfspace_eager :
        (Ast.LogicOld.Term.t list ->
        Ast.LogicOld.Term.t list ->
        Ast.LogicOld.Formula.t) ->
        Table.t ->
        (Table.state_example_id * Table.state_example_id) list ->
        Table.halfspace_id list ->
        Table.halfspace_id
        * ((Table.state_example_id * Table.state_example_id) list * int)
        * ((Table.state_example_id * Table.state_example_id) list * int)

      val choose_halfspace_lazy :
        (Ast.LogicOld.Term.t list ->
        Ast.LogicOld.Term.t list ->
        Ast.LogicOld.Formula.t) ->
        Table.t ->
        (Table.state_example_id * Table.state_example_id) list ->
        Table.halfspace_id
        * ((Table.state_example_id * Table.state_example_id) list * int)
        * ((Table.state_example_id * Table.state_example_id) list * int)
    *)

    type build_dtree_info

    (*
      val choose_halfspace :
        (Ast.LogicOld.Term.t list ->
        Ast.LogicOld.Term.t list ->
        Ast.LogicOld.Formula.t) ->
        Table.t ->
        (Table.state_example_id * Table.state_example_id) list ->
        build_dtree_info ->
        Table.halfspace_id
        * ((Table.state_example_id * Table.state_example_id) list * int)
        * ((Table.state_example_id * Table.state_example_id) list * int)

      val update_info :
        Table.t ->
        Table.halfspace_id ->
        build_dtree_info ->
        build_dtree_info * build_dtree_info

      val build_dtree' :
        (Ast.LogicOld.Term.t list ->
        Ast.LogicOld.Term.t list ->
        Ast.LogicOld.Formula.t) ->
        Table.t ->
        (Table.state_example_id * Table.state_example_id) list ->
        int ->
        build_dtree_info ->
        (Ast.LogicOld.Term.t list * Ast.LogicOld.Term.t list) dtree*)

    val build_dtree :
      (Ast.LogicOld.Term.t list ->
      Ast.LogicOld.Term.t list ->
      Ast.LogicOld.Formula.t) ->
      Table.t ->
      (Table.state_example_id * Table.state_example_id) list
      * int
      * build_dtree_info ->
      DecisionTreeTemplate.t

    val initialize :
      (Ast.LogicOld.Term.t list ->
      Ast.LogicOld.Term.t list ->
      Ast.LogicOld.Formula.t) ->
      Table.t ->
      (Table.state_example_id * Table.state_example_id) list
      * int
      * build_dtree_info
  end = struct
    (* evaluate each soft constraint by the model returned by Z3interface.max_smt
     * almost the same as max_sat_template*)
    let assign_label t transition_example_id_list =
      let open Lacaml.D in
      let fenv, t_src_gt_t_dst =
        generate_constraints_template Lexicographic.gt t
          transition_example_id_list
      in
      let soft_constraints =
        Map.Poly.singleton "txgtty"
          (List.map ~f:(fun x -> (x, 1)) t_src_gt_t_dst)
      in
      match Z3Smt.Z3interface.max_smt ~id fenv [] soft_constraints with
      | Some (_, model) ->
          let model = Map.Poly.of_alist_exn @@ LogicOld.remove_dontcare model in
          let labels =
            List.map t_src_gt_t_dst ~f:(fun c ->
                if Evaluator.eval @@ Formula.subst model c then 1. else -1.)
          in
          let src_label, dst_label =
            List.unzip
            @@ List.map2_exn transition_example_id_list labels
                 ~f:(fun (src, dst) label -> ((src, label), (dst, label)))
          in
          let state_label =
            List.map
              ~f:(fun (x, label) ->
                ( List.map ~f:Z.to_float @@ StateExample.z_of
                  @@ Table.get_state_example t x,
                  label ))
              (src_label @ dst_label)
          in
          let compare (x, l) (x', l') =
            let x_comp = List.compare Float.compare x x' in
            if x_comp = 0 then Float.compare l l' else x_comp
          in
          let state_label = List.dedup_and_sort ~compare state_label in
          List.iter
            ~f:(fun (x, label) ->
              Debug.print
              @@ lazy
                   (let x_str =
                      String.concat_map_list ~sep:", " ~f:string_of_float x
                    in
                    let label_str = string_of_float label in
                    sprintf "%s: %s" (String.paren x_str) label_str))
            state_label;
          let samples, labels = List.unzip state_label in
          let labels = Array.of_list labels |> Vec.of_array in
          let samples =
            List.map ~f:Array.of_list samples |> Array.of_list |> Mat.of_array
          in
          (samples, labels)
      | None -> assert false

    let has_state_examples_in_both_side t h = function
      | [] -> false
      | x :: ex ->
          List.exists ex ~f:(fun y ->
              Stdlib.( <> )
                (Table.eval_halfspace t x h)
                (Table.eval_halfspace t y h))

    let filter_hyperplanes t ex hs =
      List.filter hs ~f:(fun h -> has_state_examples_in_both_side t h ex)

    let choose_halfspace_eager lex2wf t transition_example_id_list h_id_list =
      let try_halfspace h_id =
        let ex_tt, ex_tf, ex_ft, ex_ff =
          classify_transition_examples t h_id transition_example_id_list
        in
        let progress =
          List.length transition_example_id_list > List.length ex_tt
          && List.length transition_example_id_list > List.length ex_ff
        in
        let t_max_sat = max_sat_template lex2wf t ex_tt in
        let f_max_sat = max_sat_template lex2wf t ex_ff in
        let plogp p = if Float.(p >. 0.) then p *. Float.log2 p else 0. in
        let ent p n = ~-.(plogp (p /. (p +. n)) +. plogp (n /. (p +. n))) in
        let gain =
          let ex_tt_p = float_of_int t_max_sat in
          let ex_ff_p = float_of_int f_max_sat in
          let ex_tf_p = float_of_int (List.length ex_tf) in
          let ex_tf_n = float_of_int (List.length ex_ft) in
          ex_tt_p +. ex_ff_p
          +. ((ex_tf_p +. ex_tf_n) *. (1. -. ent ex_tf_p ex_tf_n))
        in
        (gain, progress, h_id, (ex_tt, t_max_sat), (ex_ff, f_max_sat))
      in
      let _, _, best_halfspace, (ex_tt, t_max_sat), (ex_ff, f_max_sat) =
        List.map ~f:try_halfspace h_id_list
        |> List.filter ~f:(fun (_, p, _, _, _) -> p)
        (* making progress *)
        |> fun l ->
        (List.sort
           ~compare:(fun (g0, _, _, _, _) (g1, _, _, _, _) ->
             Stdlib.compare g0 g1)
           l
         |> List.iter ~f:(fun (g, _, h_id, _, _) ->
                Debug.print
                @@ lazy
                     (let s = Table.get_halfspace t h_id |> Halfspace.str_of in
                      s ^ ": gain = " ^ string_of_float g));
         l)
        |> List.max_elt ~compare:(fun (g0, _, _, _, _) (g1, _, _, _, _) ->
               Stdlib.compare g0 g1)
        (* take a halfspace with maximum information gain *)
        |> function
        | Some x -> x
        | None -> assert false
      in
      (best_halfspace, (ex_tt, t_max_sat), (ex_ff, f_max_sat))

    let approximate_hyperplane t ex w b : Halfspace.t =
      let tvars, w = Map.Poly.to_alist w |> List.unzip in
      let bw_float = b :: w in
      let bw_q = List.map ~f:Q.of_float bw_float in
      let bw_q_den = List.map ~f:Q.den bw_q in
      let bw_q_den_lcm = List.fold ~init:Z.one ~f:Z.lcm bw_q_den in
      let bw_z =
        List.map ~f:(fun x -> Q.(x * of_bigint bw_q_den_lcm |> num)) bw_q
      in
      let exact_bw = bw_z in
      let abs_exact_bw = List.map ~f:Z.abs exact_bw in
      let sorted_abs_exact_bw = List.sort ~compare:Z.compare abs_exact_bw in
      let halfspace_of_bw bw =
        let w = List.zip_exn tvars (List.tl_exn bw) in
        let b = List.hd_exn bw in
        Affine.make w b |> Halfspace.of_affine
      in
      if config.approx_level > 0 then
        let abs_approx_bw =
          ContFrac.approximate_ratio abs_exact_bw config.approx_level
        in
        let approx_bw =
          List.zip_exn abs_approx_bw exact_bw
          |> List.map ~f:(fun (a, s) ->
                 if Z.Compare.(s < Z.zero) then Z.(~-a) else a)
        in
        halfspace_of_bw approx_bw
      else
        let state_examples =
          Set.Poly.of_list @@ List.concat_map ex ~f:(fun (x, y) -> [ x; y ])
        in
        let exact_halfspace = halfspace_of_bw bw_z in
        let len_tvars = List.length tvars in
        let rec loop level cut =
          let lb = List.nth_exn sorted_abs_exact_bw cut in
          let abs_exact_bw' =
            List.map
              ~f:(fun n -> if Z.Compare.(n >= lb) then n else Z.zero)
              abs_exact_bw
          in
          let abs_approx_bw' = ContFrac.approximate_ratio abs_exact_bw' level in
          let approx_bw =
            List.zip_exn abs_approx_bw' exact_bw
            |> List.map ~f:(fun (a, s) ->
                   if Z.Compare.(s < Z.zero) then Z.(~-a) else a)
          in
          let h = halfspace_of_bw approx_bw in
          let params_src_tvar = Table.get_params_src t |> List.map ~f:fst in
          if
            Set.for_all state_examples ~f:(fun ex ->
                let ex_term =
                  Table.get_state_example t ex |> StateExample.term_of
                in
                Bool.(
                  Halfspace.eval params_src_tvar ex_term h
                  = Halfspace.eval params_src_tvar ex_term exact_halfspace))
          then h
          else if cut <= 0 then loop (level + 1) len_tvars
          else loop level (cut - 1)
        in
        loop 1 len_tvars

    let choose_halfspace_lazy lex2wf t transition_example_id_list =
      let samples, labels = assign_label t transition_example_id_list in
      let params_src = Table.get_params_src t in
      let eval_hyperplane (w, b) sample =
        List.zip_exn (List.map ~f:fst params_src) (Array.to_list sample)
        |> List.fold ~init:b ~f:(fun a (x, b) ->
               a +. (b *. Map.Poly.find_exn w x))
      in
      let is_useless_hyperplane (w, b) samples =
        let has_pos =
          Array.exists samples ~f:(fun sample ->
              Float.(eval_hyperplane (w, b) sample >=. 0.))
        in
        let has_neg =
          Array.exists samples ~f:(fun sample ->
              Float.(eval_hyperplane (w, b) sample <. 0.))
        in
        not (has_pos && has_neg)
      in
      let undersample samples labels =
        let samples = Lacaml.D.Mat.to_array samples in
        let labels = Lacaml.D.Vec.to_array labels in
        let pos_samples, neg_samples =
          Array.partitioni_tf samples ~f:(fun i _ -> Float.(labels.(i) >. 0.))
        in
        let undersample_major major minor =
          let remove_index =
            match
              Array.findi major ~f:(fun _ sample ->
                  Array.mem minor sample ~equal:(Array.equal Stdlib.( = )))
            with
            | Some (i, _) -> i
            | None -> 0
          in
          Array.filteri major ~f:(fun i _ -> remove_index <> i)
        in
        let pos_samples, neg_samples =
          if Array.length pos_samples > Array.length neg_samples then
            let pos_samples = undersample_major pos_samples neg_samples in
            (pos_samples, neg_samples)
          else
            let neg_samples = undersample_major neg_samples pos_samples in
            (pos_samples, neg_samples)
        in
        let samples = Array.append pos_samples neg_samples in
        let labels =
          Array.init (Array.length samples) ~f:(fun i ->
              if i < Array.length pos_samples then 1. else -1.)
        in
        (Lacaml.D.Mat.of_array samples, Lacaml.D.Vec.of_array labels)
      in
      let rec get_useful_hyperplane samples labels =
        let n_pos =
          Lacaml.D.Vec.to_list labels |> List.count ~f:(fun x -> Float.(x > 0.))
        in
        let n_neg = Lacaml.D.Vec.dim labels - n_pos in
        let weights =
          [ (1, 1. /. float_of_int n_pos); (-1, 1. /. float_of_int n_neg) ]
        in
        let w, b =
          if n_pos = 1 && n_neg = 1 then (
            Debug.print @@ lazy "2 samples";
            let samples = Lacaml.D.Mat.to_array samples in
            Array.iter
              ~f:(fun sample ->
                Debug.print
                @@ lazy
                     (Array.map ~f:string_of_float sample
                     |> Array.to_list |> String.concat ~sep:", "))
              samples;
            let w =
              List.mapi
                ~f:(fun i x -> (x, samples.(1).(i) -. samples.(0).(i)))
                (List.map ~f:fst params_src)
            in
            let b =
              Array.foldi ~init:0.
                ~f:(fun i sum a ->
                  let b = samples.(1).(i) in
                  sum +. (a *. a) -. (b *. b))
                samples.(0)
              /. 2.
            in
            Debug.print
            @@ lazy
                 ("w = "
                 ^ String.concat_map_list ~sep:", " w ~f:(fun (_, a) ->
                       string_of_float a));
            Debug.print @@ lazy ("b = " ^ string_of_float b);
            let eval_hyperplane sample =
              List.foldi ~init:b
                ~f:(fun i sum (_, a) -> sum +. (a *. sample.(i)))
                w
            in
            Debug.print
            @@ lazy
                 ("sample0 = " ^ string_of_float @@ eval_hyperplane samples.(0));
            Debug.print
            @@ lazy
                 ("sample1 = " ^ string_of_float @@ eval_hyperplane samples.(1));
            (Map.Poly.of_alist_exn w, b))
          else
            Qualifier.SVM.get_hyperplane_float config.csvm ~weights params_src
              samples labels
        in
        if is_useless_hyperplane (w, b) (Lacaml.D.Mat.to_array samples) then
          let samples, labels = undersample samples labels in
          get_useful_hyperplane samples labels
        else (w, b)
      in
      let w, b = get_useful_hyperplane samples labels in
      let hs = approximate_hyperplane t transition_example_id_list w b in
      let h_id = Table.add_hs t hs in
      let ex_tt, _, _, ex_ff =
        classify_transition_examples t h_id transition_example_id_list
      in
      let t_max_sat = max_sat_template lex2wf t ex_tt in
      let f_max_sat = max_sat_template lex2wf t ex_ff in
      (h_id, (ex_tt, t_max_sat), (ex_ff, f_max_sat))

    type build_dtree_info =
      | InfoEager of Table.halfspace_id list * Table.state_example_id list
      | InfoLazy

    let choose_halfspace lex2wf t transition_example_id_list = function
      | InfoEager (h_id_list, _) ->
          choose_halfspace_eager lex2wf t transition_example_id_list h_id_list
      | InfoLazy -> choose_halfspace_lazy lex2wf t transition_example_id_list

    let split_info t new_halfspace = function
      | InfoEager (h_id_list, state_example_id_list) ->
          let t_state_example_id_list, f_state_example_id_list =
            List.partition_tf state_example_id_list ~f:(fun x ->
                Table.eval_halfspace t x new_halfspace)
          in
          let t_hs = filter_hyperplanes t t_state_example_id_list h_id_list in
          let f_hs = filter_hyperplanes t f_state_example_id_list h_id_list in
          ( InfoEager (t_hs, t_state_example_id_list),
            InfoEager (f_hs, f_state_example_id_list) )
      | InfoLazy -> (InfoLazy, InfoLazy)

    let rec build_dtree lex2wf t (transition_example_id_list, num_max_sat, info)
        =
      Debug.print @@ lazy (sprintf "num_max_sat = %d" num_max_sat);
      List.iter
        ~f:(fun (x, y) ->
          let x_str = Table.get_state_example t x |> StateExample.str_of in
          let y_str = Table.get_state_example t y |> StateExample.str_of in
          Debug.print @@ lazy (x_str ^ " " ^ y_str))
        transition_example_id_list;
      if List.length transition_example_id_list = num_max_sat then
        Leaf
          (Template.gen_template_lexicographic (config.lex_deg + 1)
             (Table.get_params_src t))
      else
        let ( best_halfspace,
              (transition_example_id_list_tt, t_max_sat),
              (transition_example_id_list_ff, f_max_sat) ) =
          choose_halfspace lex2wf t transition_example_id_list info
        in
        Debug.print
        @@ lazy (Table.get_halfspace t best_halfspace |> Halfspace.str_of);
        let tinfo, finfo = split_info t best_halfspace info in
        let ttree =
          build_dtree lex2wf t (transition_example_id_list_tt, t_max_sat, tinfo)
        in
        let ftree =
          build_dtree lex2wf t (transition_example_id_list_ff, f_max_sat, finfo)
        in
        Node (best_halfspace, ttree, ftree)

    let initialize lex2wf t =
      let transition_example_id_list = Table.get_transition_example_id_list t in
      let state_example_id_list =
        transition_example_id_list
        |> List.concat_map ~f:(fun (x, y) -> [ x; y ])
      in
      let info =
        if config.eager_halfspace_gen then
          InfoEager (Table.get_hs_id_list t, state_example_id_list)
        else InfoLazy
      in
      let max_sat = max_sat_template lex2wf t transition_example_id_list in
      (transition_example_id_list, max_sat, info)
  end

  module ImplicitCycle = struct
    let rec add_unsat_example t src dst =
      let rec add_dst dst = function
        | Leaf (l, _) -> l := dst :: !l
        | Node (h, tt, ft) ->
            if Table.eval_halfspace t dst h then add_dst dst tt
            else add_dst dst ft
      in
      let rec add_src src = function
        | Leaf (_, l) -> l := src :: !l
        | Node (h, tt, ft) ->
            if Table.eval_halfspace t src h then add_src src tt
            else add_src src ft
      in
      function
      | Leaf _ -> ()
      | Node (h, tt, ft) -> (
          match
            (Table.eval_halfspace t src h, Table.eval_halfspace t dst h)
          with
          | true, true -> add_unsat_example t src dst tt
          | false, false -> add_unsat_example t src dst ft
          | true, false ->
              add_src src tt;
              add_dst dst ft
          | false, true ->
              add_src src ft;
              add_dst dst tt)

    let rec collect_nonempty_dt :
        (Table.state_example_id list ref * Table.state_example_id list ref)
        dtree ->
        (Table.state_example_id list * Table.state_example_id list) list =
      function
      | Leaf (dst, src) ->
          if Fn.non List.is_empty !dst && Fn.non List.is_empty !src then
            [ (!dst, !src) ]
          else []
      | Node (_, tt, ft) -> collect_nonempty_dt tt @ collect_nonempty_dt ft

    exception GapNotFound

    (** [ find_gap t dt unsat_keys example_map ] analyzes implicit cycles in [ unsat_keys ] and returns two distinct state examples between which we can cut an implicit cycle in [ unsat_keys ] *)
    let find_gap t dt unsat_keys example_map =
      let unsat_dt = dtree_fmap (fun _ -> (ref [], ref [])) dt in
      List.iter ~f:(fun k -> Debug.print @@ lazy k) unsat_keys;
      List.iter
        ~f:(fun key ->
          let src, dst = Map.Poly.find_exn example_map key in
          Debug.print
          @@ lazy
               (let src_str =
                  Table.get_state_example t src |> StateExample.str_of
                in
                let dst_str =
                  Table.get_state_example t dst |> StateExample.str_of
                in
                key ^ ": " ^ src_str ^ " " ^ dst_str);
          add_unsat_example t src dst unsat_dt)
        unsat_keys;
      match
        collect_nonempty_dt unsat_dt
        |> List.find_map ~f:(fun (dsts, srcs) ->
               List.cartesian_product dsts srcs
               |> List.find ~f:(fun (dst, src) ->
                      Stdlib.( <> )
                        (Table.get_state_example t dst)
                        (Table.get_state_example t src)))
      with
      | Some (dst, src) -> (dst, src)
      | None -> raise GapNotFound

    let choose_separating_halfspace_eager t x y transition_example_id_list =
      let cross_hyperplane_t_f h x y =
        Table.eval_halfspace t x h && not (Table.eval_halfspace t y h)
      in
      let hs_xt_yf =
        List.filter
          ~f:(fun h -> cross_hyperplane_t_f h x y)
          (Table.get_hs_id_list t)
      in
      let count_xt_yf h =
        List.count
          ~f:(fun (x, y) -> cross_hyperplane_t_f h x y)
          transition_example_id_list
      in
      let hs_xt_yf = List.map ~f:(fun h -> (count_xt_yf h, h)) hs_xt_yf in
      let hs_xf_yt =
        List.filter
          ~f:(fun h -> cross_hyperplane_t_f h y x)
          (Table.get_hs_id_list t)
      in
      let count_xf_yt h =
        List.count
          ~f:(fun (x, y) -> cross_hyperplane_t_f h y x)
          transition_example_id_list
      in
      let hs_xf_yt = List.map ~f:(fun h -> (count_xf_yt h, h)) hs_xf_yt in
      List.min_elt
        ~compare:(fun (c0, _) (c1, _) -> compare c0 c1)
        (hs_xt_yf @ hs_xf_yt)
      |> function
      | Some (_, x) -> x
      | None -> assert false

    let choose_separating_halfspace_lazy ~id t x y transition_example_id_list =
      let fenv = Map.Poly.empty in
      (*TODO: generate fenv*)
      let term, params =
        Template.gen_template_affine (Table.get_params_src t)
      in
      let formula = Formula.mk_atom (T_int.mk_geq term (T_int.zero ())) in
      let hard =
        let xp = Formula.subst (Table.get_state_example_map t x) formula in
        let yn =
          Formula.mk_neg
            (Formula.subst (Table.get_state_example_map t y) formula)
        in
        [ xp; yn ]
      in
      let soft =
        List.map
          ~f:(fun (x, y) ->
            let xn =
              Formula.mk_neg
                (Formula.subst (Table.get_state_example_map t x) formula)
            in
            let yp = Formula.subst (Table.get_state_example_map t y) formula in
            (Formula.mk_or xn yp, 1))
          transition_example_id_list
      in
      let soft = Map.Poly.singleton "noncrossing" soft in
      match Z3Smt.Z3interface.max_smt ~id fenv hard soft with
      | Some (_, model) ->
          let model = model_postprocess model params in
          let term = Term.subst model term in
          let term_affine = Logic.ExtTerm.of_old_term term |> Affine.of_term in
          let h = Option.value_exn term_affine |> Halfspace.of_affine in
          Table.add_hs t h
      | None -> assert false

    let choose_separating_halfspace ~id t x y transition_example_id_list =
      if Table.is_eager t then
        choose_separating_halfspace_eager t x y transition_example_id_list
      else choose_separating_halfspace_lazy ~id t x y transition_example_id_list

    (* [ dtree_separate t dst src transition_example_id_list dt ] adds a hyperplane to dt and returns a new tree [ dt' ] so that dst and src are in different segments in [ dt' ] *)
    let rec dtree_separate t dst src transition_example_id_list :
        DecisionTreeTemplate.t -> DecisionTreeTemplate.t = function
      | Leaf _ ->
          let h =
            choose_separating_halfspace ~id t dst src transition_example_id_list
          in
          let tt =
            Leaf
              (Template.gen_template_lexicographic (config.lex_deg + 1)
                 (Table.get_params_src t))
          in
          let ft =
            Leaf
              (Template.gen_template_lexicographic (config.lex_deg + 1)
                 (Table.get_params_src t))
          in
          Node (h, tt, ft)
      | Node (h, tt, ft) -> (
          match
            (Table.eval_halfspace t dst h, Table.eval_halfspace t src h)
          with
          | true, true ->
              let transition_example_id_list' =
                List.filter
                  ~f:(fun (x, y) ->
                    Table.eval_halfspace t x h && Table.eval_halfspace t y h)
                  transition_example_id_list
              in
              Node
                (h, dtree_separate t dst src transition_example_id_list' tt, ft)
          | false, false ->
              let transition_example_id_list' =
                List.filter
                  ~f:(fun (x, y) ->
                    (not (Table.eval_halfspace t x h))
                    && not (Table.eval_halfspace t y h))
                  transition_example_id_list
              in
              Node
                (h, tt, dtree_separate t dst src transition_example_id_list' ft)
          | _, _ -> Node (h, tt, ft))
  end

  let sum_of_abs_params template_params =
    let qs, constraints =
      (* for each p in template_params, generate a fresh parameter q and a constraint -q <= p <= q *)
      List.map
        ~f:(fun p ->
          let q = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
          let p_le_q = Formula.mk_atom (T_int.mk_leq p q) in
          let minus_q_le_p =
            Formula.mk_atom (T_int.mk_leq (T_int.mk_neg q) p)
          in
          (q, Formula.mk_and p_le_q minus_q_le_p))
        template_params
      |> List.unzip
    in
    (T_int.mk_sum (T_int.zero ()) qs, constraints)

  let rec loop_elimination ~id lex2wf t dt =
    let example_map =
      List.mapi
        ~f:(fun i e -> (sprintf "D%d" i, e))
        (Table.get_transition_example_id_list t)
      |> Map.Poly.of_alist_exn
    in
    let constraints =
      Map.Poly.map
        ~f:(fun (x, y) ->
          lex2wf
            (DecisionTreeTemplate.eval_dtree t x dt)
            (DecisionTreeTemplate.eval_dtree t y dt))
        example_map
    in
    Debug.print @@ lazy "synthesizing linear functions";
    Debug.print
    @@ lazy ("constraint size = " ^ string_of_int (Map.Poly.length constraints));
    let fenv = Map.Poly.empty in
    (*TODO: generate fenv*)
    match Z3Smt.Z3interface.check_sat_unsat_core ~id fenv constraints with
    | `Sat model ->
        let model =
          if config.optimize_sum_coeff then
            let template_params = DecisionTreeTemplate.collect_params dt in
            let obj, abs_constraints = sum_of_abs_params template_params in
            match
              Z3Smt.Z3interface.check_opt_maximize ~id fenv
                (Map.Poly.data constraints @ abs_constraints)
                (T_int.mk_neg obj)
            with
            | Some (_, _, model) -> model
            | None -> assert false
          else model
        in
        let model =
          model_postprocess model (DecisionTreeTemplate.collect_params dt)
        in
        dtree_fmap (fun (t, _) -> List.map ~f:(Term.subst model) t) dt
    | `Unsat unsat_keys ->
        Debug.print @@ lazy "cut implicit cycle";
        let x, y = ImplicitCycle.find_gap t dt unsat_keys example_map in
        Debug.print
        @@ lazy
             (let x_str = Table.get_state_example t x |> StateExample.str_of in
              let y_str = Table.get_state_example t y |> StateExample.str_of in
              "separate: " ^ x_str ^ " and " ^ y_str);
        let dt' =
          ImplicitCycle.dtree_separate t x y
            (Table.get_transition_example_id_list t)
            dt
        in
        loop_elimination ~id lex2wf t dt'
    | `Unknown reason -> failwith reason
    | `Timeout -> failwith "timeout"

  let split_sort_env params =
    let n = List.length params / 2 in
    let params_src, params_dst = List.split_n params n in
    (params_src, params_dst)

  let init_table pvar params table labeling =
    let alist = labeling in
    let tt = TruthTable.get_table table pvar in
    Debug.print
    @@ lazy (sprintf "    labeled atoms (%d):" (TruthTable.num_atoms alist));
    Debug.print @@ lazy (TruthTable.str_of_atoms tt alist);
    let _neg_ex, pneg_ex, pos_ex, ppos_ex = TruthTable.papps_of tt alist in
    (* ToDo: ppos_ex can be non-empty *)
    (* temporarily allow negative examples *)
    assert (Set.is_empty pneg_ex && Set.is_empty ppos_ex);
    let params_src, _ = split_sort_env params in
    let transition_examples =
      Set.Poly.map ~f:(fun (_, t) -> TransitionExample.of_term t) pos_ex
    in
    if config.eager_halfspace_gen then
      Table.make_eager params_src (Set.to_list transition_examples)
    else Table.make_lazy params_src (Set.to_list transition_examples)

  let rec term_of_dtree t = function
    | Leaf term -> term
    | Node (h, tt, ft) ->
        List.zip_exn (term_of_dtree t tt) (term_of_dtree t ft)
        |> List.map ~f:(fun (x, y) ->
               T_bool.mk_if_then_else
                 (Table.get_halfspace t h |> Halfspace.term_of)
                 x y)

  let decision_tree_main ~id lex2wf table params =
    let pre_dt =
      BuildDT.build_dtree lex2wf table (BuildDT.initialize lex2wf table)
    in
    List.iter
      ~f:(fun tm -> Debug.print @@ lazy (Term.str_of tm))
      (dtree_fmap fst pre_dt |> term_of_dtree table);
    let dtx = loop_elimination ~id lex2wf table pre_dt in
    let params_src, params_dst = split_sort_env params in
    let map_x2y =
      let params_src_tvar = List.map ~f:fst params_src in
      let params_dst_term = Term.of_sort_env params_dst in
      List.zip_exn params_src_tvar params_dst_term |> Map.Poly.of_alist_exn
    in
    let dtx_term = term_of_dtree table dtx in
    let dty_term = List.map ~f:(Term.subst map_x2y) dtx_term in
    Debug.print @@ lazy "** Decision tree";
    List.iter
      ~f:(fun t ->
        Debug.print @@ lazy (Evaluator.simplify_term t |> Term.str_of))
      dtx_term;
    lex2wf dtx_term dty_term

  let mk_classifier pvar params table labeling _examples =
    let table = init_table pvar params table labeling in
    let wf =
      try decision_tree_main ~id:None (*ToDo*) Lexicographic.gt table params
      with ImplicitCycle.GapNotFound ->
        decision_tree_main ~id:None
          (*ToDo*) Lexicographic.gt_degenerate_negative table params
    in
    Ok
      [
        ( Map.Poly.empty (* parameters of parametric candidate*),
          (pvar, (params, wf)) );
      ]
end
