open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld
open PCSatCommon

let get_hyperplane_float c ?(weights = []) params_x x y :
    (Ident.tvar, float) Map.Poly.t * float =
  let open Libsvm in
  let n_feat = List.length params_x in
  let problem = Svm.Problem.create_dense ~x ~y in
  let model = Svm.train ~kernel:`LINEAR ~c ~weights problem in
  let n_sv = Svm.Model.get_n_sv model in
  let w = Array.create ~len:n_feat 0. in
  for i = 0 to n_sv - 1 do
    let sv = Svm.Model.get_sv model i in
    let sv_coef = Svm.Model.get_sv_coef model 0 i in
    Array.iter ~f:(fun (i, v) -> w.(i) <- w.(i) +. (sv_coef *. v)) sv
  done;
  let b = ~-.(Svm.Model.get_rho model 0) in
  let w =
    List.zip_exn (List.map ~f:fst params_x) (Array.to_list w)
    |> Map.Poly.of_alist_exn
  in
  (w, b)

(* [params] may contain a boolean parameter*)
let rec classify approx_level csvm params pos_examples neg_examples =
  let open Lacaml.D in
  if Set.is_empty pos_examples || Set.is_empty neg_examples then Set.Poly.empty
  else
    let eval_halfspace h x =
      let params_tvar = List.map ~f:fst params in
      let m = List.zip_exn params_tvar x |> Map.Poly.of_alist_exn in
      Evaluator.eval (Formula.subst m h)
    in
    let rec get_useful_halfspace pos_examples neg_examples =
      let n_pos = Set.length pos_examples in
      let n_neg = Set.length neg_examples in
      if n_pos = 1 && n_neg = 1 then
        let pos_example =
          List.map
            ~f:(fun x ->
              match Evaluator.eval_term x with
              | Value.Int i -> i
              | _ -> assert false)
            (match Set.to_list pos_examples with
            | [ ex ] -> ex
            | _ -> assert false)
        in
        let neg_example =
          List.map
            ~f:(fun x ->
              match Evaluator.eval_term x with
              | Value.Int i -> i
              | _ -> assert false)
            (match Set.to_list neg_examples with
            | [ ex ] -> ex
            | _ -> assert false)
        in
        let w =
          List.zip_exn pos_example neg_example
          |> List.map ~f:(fun (p, n) -> Z.(of_int 2 * (n - p)))
        in
        (* 2 * (neg_example - pos_example) *)
        let b =
          List.zip_exn pos_example neg_example
          |> List.fold ~init:Z.zero ~f:(fun sum (p, n) ->
                 Z.(sum + (p * p) - (n * n)))
        in
        (* |pos_example|^2 - |neg_example|^2 *)
        let t =
          List.fold ~init:(T_int.mk_int b)
            ~f:(fun sum ((tvar, sort), c) ->
              T_int.mk_add sum
                (T_int.mk_mult (T_int.mk_int c) (Term.mk_var tvar sort)))
            (List.zip_exn params w)
        in
        Formula.mk_atom (T_int.mk_geq t (T_int.zero ()))
      else
        let weights =
          [ (1, 1. /. float_of_int n_pos); (-1, 1. /. float_of_int n_neg) ]
        in
        let convert_example example =
          List.map
            ~f:(fun x ->
              match Evaluator.eval_term x with
              | Value.Int i -> Z.to_float i
              | _ -> assert false)
            example
          |> List.to_array
        in
        let pos_examples_labels =
          Set.to_array pos_examples
          |> Array.map ~f:(fun e -> (convert_example e, 1.))
        in
        let neg_examples_labels =
          Set.to_array neg_examples
          |> Array.map ~f:(fun e -> (convert_example e, -1.))
        in
        let examples, labels =
          Array.append pos_examples_labels neg_examples_labels |> Array.unzip
        in
        let labels = Vec.of_array labels in
        let examples = Mat.of_array examples in
        let w, b = get_hyperplane_float csvm ~weights params examples labels in
        let wb_to_int w b =
          let lcm_den =
            Map.Poly.fold w ~init:(Q.den b) ~f:(fun ~key:_ ~data:q a ->
                Z.lcm a (Q.den q))
          in
          let mul_lcm_den x = Q.(x * Q.of_bigint lcm_den) |> Q.num in
          let b' = mul_lcm_den b in
          let w' = Map.Poly.map ~f:mul_lcm_den w in
          (w', b')
        in
        let make_halfspace w b =
          let t =
            Map.Poly.fold w ~init:(T_int.mk_int b)
              ~f:(fun ~key:tvar ~data:c t ->
                T_int.mk_add t
                  (T_int.mk_mult (T_int.mk_int c) (Term.mk_var tvar T_int.SInt)))
          in
          Formula.mk_atom (T_int.mk_geq t (T_int.zero ()))
        in
        let exact_w = Map.Poly.map ~f:Q.of_float w in
        let exact_b = Q.of_float b in
        let exact_w, exact_b = wb_to_int exact_w exact_b in
        let exact_bw =
          exact_b
          :: List.map params ~f:(fun (key, _) -> Map.Poly.find_exn exact_w key)
        in
        let abs_exact_bw = List.map ~f:Z.abs exact_bw in
        let sorted_abs_exact_bw = List.sort ~compare:Z.compare abs_exact_bw in
        let all_examples = Set.union pos_examples neg_examples in
        let h =
          if approx_level <= 0 then
            let exact_halfspace = make_halfspace exact_w exact_b in
            let len_params = List.length params in
            let rec loop level cut =
              let lb = List.nth_exn sorted_abs_exact_bw cut in
              let abs_exact_bw' =
                List.map
                  ~f:(fun n -> if Z.Compare.(n >= lb) then n else Z.zero)
                  abs_exact_bw
              in
              let abs_approx_bw' =
                ContFrac.approximate_ratio abs_exact_bw' level
              in
              let approx_bw' =
                List.zip_exn abs_approx_bw' exact_bw
                |> List.map ~f:(fun (a, s) ->
                       if Z.Compare.(s < Z.zero) then Z.(~-a) else a)
              in
              let w' =
                List.zip_exn (List.map ~f:fst params) (List.tl_exn approx_bw')
                |> Map.Poly.of_alist_exn
              in
              let b' = List.hd_exn approx_bw' in
              let h = make_halfspace w' b' in
              if
                Set.for_all all_examples ~f:(fun ex ->
                    Bool.(
                      eval_halfspace h ex = eval_halfspace exact_halfspace ex))
              then h
              else if cut <= 0 then loop (level + 1) len_params
              else loop level (cut - 1)
            in
            loop 1 len_params
          else
            let abs_approx_bw =
              ContFrac.approximate_ratio abs_exact_bw approx_level
            in
            let approx_bw =
              List.zip_exn abs_approx_bw exact_bw
              |> List.map ~f:(fun (a, s) ->
                     if Z.Compare.(s < Z.zero) then Z.(~-a) else a)
            in
            let w' =
              List.zip_exn (List.map ~f:fst params) (List.tl_exn approx_bw)
              |> Map.Poly.of_alist_exn
            in
            let b' = List.hd_exn approx_bw in
            make_halfspace w' b'
        in
        if Set.Poly.map all_examples ~f:(eval_halfspace h) |> Set.length < 2
        then
          (* all examples are classified positive (or negative) by h -> undersample majority class *)
          if n_pos > n_neg then
            (* remove one element *)
            let elm = Option.value_exn (Set.min_elt pos_examples) in
            let pos_examples' = Set.remove pos_examples elm in
            get_useful_halfspace pos_examples' neg_examples
          else
            let elm = Option.value_exn (Set.max_elt neg_examples) in
            let neg_examples' = Set.remove neg_examples elm in
            get_useful_halfspace pos_examples neg_examples'
        else h
    in
    let h = get_useful_halfspace pos_examples neg_examples in
    let pos_examples_t, pos_examples_f =
      Set.partition_tf pos_examples ~f:(eval_halfspace h)
    in
    let neg_examples_t, neg_examples_f =
      Set.partition_tf neg_examples ~f:(eval_halfspace h)
    in
    let hst = classify approx_level csvm params pos_examples_t neg_examples_t in
    let hsf = classify approx_level csvm params pos_examples_f neg_examples_f in
    Set.add (Set.union hst hsf) h

let svm_half_spaces_of approx_level csvm sorts pos_examples neg_examples =
  let params = LogicOld.sort_env_list_of_sorts sorts in
  ( params,
    Set.union
      (Set.Poly.of_list params
      |> Set.Poly.filter_map ~f:(function
           | x, T_bool.SBool -> Some (Term.mk_var x T_bool.SBool)
           | _, T_int.SInt -> None
           | _, T_real.SReal -> failwith "real"
           | _, s -> failwith ("not supported" ^ Term.str_of_sort s))
      |> Set.Poly.map ~f:(fun x -> Formula.eq x (T_bool.mk_true ())))
      (classify approx_level csvm params pos_examples neg_examples) )

module Make (Config : sig
  val approx_level : int
  val csvm : float
end) =
struct
  let qualifiers_of _pvar sorts labeled_atoms _examples =
    let pos_examples =
      Set.Poly.filter_map labeled_atoms ~f:(fun (atom, label) ->
          if TruthTable.label_pos = label then
            match ExAtom.instantiate atom with
            | ExAtom.PApp (_, terms) -> Some terms
            | ExAtom.PPApp (_, (_, terms)) -> Some terms
            | _ -> None
          else None)
    in
    let neg_examples =
      Set.Poly.filter_map labeled_atoms ~f:(fun (atom, label) ->
          if TruthTable.label_neg = label then
            match ExAtom.instantiate atom with
            | ExAtom.PApp (_, terms) -> Some terms
            | ExAtom.PPApp (_, (_, terms)) -> Some terms
            | _ -> None
          else None)
    in
    let params, quals =
      svm_half_spaces_of Config.approx_level Config.csvm sorts pos_examples
        neg_examples
    in
    Set.Poly.map ~f:(fun qual -> (params, Normalizer.normalize qual)) quals

  let str_of_domain =
    "SVM with approx_level="
    ^ string_of_int Config.approx_level
    ^ " csvm="
    ^ string_of_float Config.csvm
end
