(* One fixed template per predicate unknown, with real-valued parameters, for
   the admissible predicates of Kura and Unno, "Automated Verification of
   Higher-Order Probabilistic Programs via a Dependent Refinement Type System"
   (ICFP 2024).  The shapes are those of PCSat's admissible template with real
   instead of integer parameters:

   - without conditioning, for each real component [v] of the value (the last
     argument): [0 <= v /\ p * v <= c + |e_1| + ... + |e_L|], where each [e_l]
     is affine in the real components of the other arguments;
   - with conditioning, for the value [(x, score)]:
     [0 <= x /\ p1 * x <= B /\ 0 <= score
      /\ min (c' + |e'_1| + ... + |e'_L|, 1 + p2) <= (1 + p2) * score
      /\ score <= 1], where [B] is [score * c] ([cond_scaled]) or
     [c + |e_1| + ... + |e_L|].

   Kind conditions: every [p], [p1], [p2], [c] and [c'] is non-negative.  They
   make the bound non-negative by construction, which is what makes every
   instance admissible (a bound that is an affine function required to be
   non-negative in every environment would be a constant); the conjunct
   [0 <= score] is implied by the others under them (the minimum is
   non-negative, and [1 + p2] is positive), and is stated so that the
   absolute values can be split by sign.

   Arguments of sort [unit] are ignored (there is one value), a tuple of reals
   is read component-wise, and any other non-real argument is declined, as is
   an unknown of any kind other than [Adm]. *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

exception Decline of string

(* a translation past the configured number of cases: declined too, but a
   template with fewer pieces may fit *)
exception Too_large of string

let decline fmt = Printf.ksprintf (fun msg -> raise (Decline msg)) fmt
let too_large fmt = Printf.ksprintf (fun msg -> raise (Too_large msg)) fmt

(* The real components of an argument [t] of sort [sort], read through tuple
   selectors; [unit] has none.  Any other sort is declined. *)
let rec components sort t =
  match sort with
  | T_real.SReal -> [ t ]
  | T_tuple.STuple sorts ->
      List.concat_mapi sorts ~f:(fun i s ->
          components s (T_tuple.mk_tuple_sel sorts t i))
  | s when Datatype.is_unit_sort s -> []
  | s -> decline "an argument of sort %s" (Term.str_of_sort s)

(* the value components of an admissible predicate: a real, or a flat tuple of
   reals (exactly two, [(x, score)], with conditioning) *)
let value_components ~with_cond sort t =
  match sort with
  | T_real.SReal when not with_cond -> [ t ]
  | T_tuple.STuple sorts
    when List.for_all sorts ~f:(Stdlib.( = ) T_real.SReal)
         && ((not with_cond) || List.length sorts = 2) ->
      List.mapi sorts ~f:(fun i _ -> T_tuple.mk_tuple_sel sorts t i)
  | s -> decline "an admissible value of sort %s" (Term.str_of_sort s)

let fresh_param () = Ident.mk_fresh_parameter ()
let var x = Term.mk_var x T_real.SReal
let sum = function [] -> T_real.rzero () | t :: ts -> List.fold ts ~init:t ~f:T_real.mk_radd

(* [c + |e_1| + ... + |e_L|] with [e_l = a_l . xs + b_l]: the parameters
   [c], [a_l], [b_l]; [c] is the one with a kind condition *)
type bound = { c : Ident.tvar; pieces : (Ident.tvar list * Ident.tvar) list }

let mk_bound ~pieces ~arity =
  {
    c = fresh_param ();
    pieces =
      List.init pieces ~f:(fun _ ->
          (List.init arity ~f:(fun _ -> fresh_param ()), fresh_param ()));
  }

let params_of_bound b =
  b.c :: List.concat_map b.pieces ~f:(fun (a, b) -> b :: a)

let affine xs (a, b) =
  sum (List.map2_exn a xs ~f:(fun a x -> T_real.mk_rmul (var a) x) @ [ var b ])

(* the sign vectors over [n] pieces: [2^n] of them *)
let rec signs n =
  if n <= 0 then [ [] ]
  else List.concat_map (signs (n - 1)) ~f:(fun s -> [ true :: s; false :: s ])

let signed_sum b xs sigma =
  sum
    (var b.c
    :: List.map2_exn b.pieces sigma ~f:(fun piece pos ->
        let e = affine xs piece in
        if pos then e else T_real.mk_rneg e))

let bound_term b xs =
  sum (var b.c :: List.map b.pieces ~f:(fun piece -> T_real.mk_rabs (affine xs piece)))

(* [lhs <= bound]: with [abs], as written; without, as the disjunction over
   sign vectors, which is equivalent since [|e| >= s] iff [e >= s \/ -e >= s]
   and a sum of absolute values is the maximum of its signed sums *)
let leq_bound ~abs lhs b xs =
  if abs then Formula.leq lhs (bound_term b xs)
  else
    Formula.or_of
    @@ List.map (signs (List.length b.pieces)) ~f:(fun sigma ->
        Formula.leq lhs (signed_sum b xs sigma))

(* [bound <= rhs], dually a conjunction over sign vectors *)
let bound_leq ~abs b xs rhs =
  if abs then Formula.leq (bound_term b xs) rhs
  else
    Formula.and_of
    @@ List.map (signs (List.length b.pieces)) ~f:(fun sigma ->
        Formula.leq (signed_sum b xs sigma) rhs)

type t = {
  params : Ident.tvar list;  (** every one real-valued *)
  kind_conds : Formula.t list;  (** over [params] only *)
  body : abs:bool -> Term.t list -> Formula.t;
      (** the predicate applied to arguments.  With [~abs:false] it is a
          positive Boolean combination of polynomial comparisons, free of
          [abs], [ite] and [min]; with [~abs:true] it is the same predicate
          written with [abs]. *)
}

let nonneg x = Formula.geq (var x) (T_real.rzero ())

let adm ~pieces ~cond_scaled ~with_cond (arg_sorts : Sort.t list) =
  let arg_sorts, value_sort =
    match List.rest_last arg_sorts with
    | args, last -> (args, last)
    | exception _ -> decline "an admissible predicate with no argument"
  in
  (* the arity of the bounds: count the components of placeholder arguments *)
  let arity =
    List.length
    @@ List.concat_map arg_sorts ~f:(fun s ->
        components s (Term.mk_var (Ident.Tvar "_") s))
  in
  let n_values =
    List.length
    @@ value_components ~with_cond value_sort
         (Term.mk_var (Ident.Tvar "_") value_sort)
  in
  let split ts =
    let args, value = List.rest_last ts in
    ( List.concat (List.map2_exn arg_sorts args ~f:components),
      value_components ~with_cond value_sort value )
  in
  if not with_cond then
    let comps =
      List.init n_values ~f:(fun _ -> (fresh_param (), mk_bound ~pieces ~arity))
    in
    {
      params = List.concat_map comps ~f:(fun (p, b) -> p :: params_of_bound b);
      kind_conds = List.concat_map comps ~f:(fun (p, b) -> [ nonneg p; nonneg b.c ]);
      body =
        (fun ~abs ts ->
          let xs, vs = split ts in
          Formula.and_of
          @@ List.map2_exn comps vs ~f:(fun (p, b) v ->
              Formula.mk_and
                (Formula.leq (T_real.rzero ()) v)
                (leq_bound ~abs (T_real.mk_rmul (var p) v) b xs)));
    }
  else
    let p1 = fresh_param () and p2 = fresh_param () in
    let bx = mk_bound ~pieces:(if cond_scaled then 0 else pieces) ~arity in
    let bs = mk_bound ~pieces ~arity in
    {
      params = [ p1; p2 ] @ params_of_bound bx @ params_of_bound bs;
      kind_conds = [ nonneg p1; nonneg p2; nonneg bx.c; nonneg bs.c ];
      body =
        (fun ~abs ts ->
          let xs, vs = split ts in
          match vs with
          | [ x; score ] ->
              let q = T_real.mk_radd (T_real.rone ()) (var p2) in
              let qscore = T_real.mk_rmul q score in
              Formula.and_of
                [
                  Formula.leq (T_real.rzero ()) x;
                  (if cond_scaled then
                     Formula.leq
                       (T_real.mk_rmul (var p1) x)
                       (T_real.mk_rmul score (var bx.c))
                   else leq_bound ~abs (T_real.mk_rmul (var p1) x) bx xs);
                  Formula.leq (T_real.rzero ()) score;
                  (* min (B', q) <= q * score *)
                  Formula.or_of
                    [ bound_leq ~abs bs xs qscore; Formula.leq q qscore ];
                  Formula.leq score (T_real.rone ());
                ]
          | _ -> decline "a conditioned admissible value that is not a pair");
    }

let of_kind ~pieces ~cond_scaled kind arg_sorts =
  match kind with
  (* the [[0, 1]] instance's template here lacks the [v <= 1] conjunct, which
     loses no admissibility: [0 <= v /\ d * v <= B] is admissible in [0, 1]
     with the usual order as it is in [0, infinity] *)
  | Kind.Adm ((Kind.Adm_expectation | Kind.Adm_probability) as a)
  | Kind.Adm (Kind.Adm_conditional as a) ->
      adm ~pieces ~cond_scaled ~with_cond:(Kind.adm_with_cond a) arg_sorts
  | Kind.Adm Kind.Adm_liberal ->
      decline "an admissible unknown over [0,1] with the opposite order"
  | k -> decline "an unknown of kind %s" (Kind.short_str_of k)
