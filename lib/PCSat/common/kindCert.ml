open Core
open Common.Ext
open Ast.LogicOld

(* An instantiated kind certificate: the ranking structure that makes a
   template's solution satisfy its kind, recorded so that a checker can
   re-verify it.  Per priority level
   (one level for WF and NWF, the truncated priority of the left tag for
   Parity), the pieces of the first argument half and of the second: a
   discriminator and a ranking tuple, both over the certificate's parameters
   [params_shared @ params_x @ params_y].  Negative components stand for
   "undefined".  Level 0 is the most significant. *)
type pieces = (Formula.t * Term.t list) list

type ranking = {
  params_shared : sort_env_list;
  params_x : sort_env_list;
  params_y : sort_env_list;
  levels : (pieces * pieces) list;
  accepting : bool;
}

(* A certificate is a finite union of rankings: one for WF, NWF and Parity;
   for DWF (disjunctive well-foundedness, a finite union of well-founded
   relations) as many as the template produced.  The union's
   relation is the disjunction of the members' relations. *)
type t = ranking list

let params_of c = c.params_shared @ c.params_x @ c.params_y

(* The comparisons are those of the template ([Templ.mk_decrease] through
   [T_irb]): the strict step is [a >= b + 1] — over the reals a bare [a > b]
   with [a >= 0] is *not* well-founded (1, 1/2, 1/4, ...), and a checker
   using it would accept relations the template never produces and that
   are not well-founded; for bit-vectors [gt_of] adds the overflow guard.
   Sorts are taken from the terms; anything [T_irb] does not know falls back to
   the integer comparison.  The fallbacks catch a *sort* failure only: an
   asynchronous exception must pass through, or a timeout during certificate
   construction would be turned into a silently mis-sorted certificate
   (the earlier pass that guarded such handlers did not reach these four
   sites). *)
let sort_of t =
  try Term.sort_of t
  with exn_ when not (Common.Timer.is_async exn_) -> T_int.SInt

let zero_of t =
  try T_irb.zero_of (sort_of t)
  with exn_ when not (Common.Timer.is_async exn_) -> T_int.zero ()

let geq a b =
  try Formula.mk_atom (T_irb.geq_of (sort_of a) a b)
  with exn_ when not (Common.Timer.is_async exn_) -> Formula.geq a b

let gt a b =
  try T_irb.gt_of (sort_of a) a b
  with exn_ when not (Common.Timer.is_async exn_) -> Formula.gt a b

let neg a = Formula.negate (geq a (zero_of a))

(* [al] dominates [bl] in one component: both undefined, or [al >= bl] *)
let geq_or_bottom al bl =
  Formula.or_of [ Formula.and_of [ neg al; neg bl ]; geq al bl ]

(* lexicographic decrease of the tuple [a] to [b], negatives as bottom:
   strictly at some component, with dominance before it; the
   non-strict version also admits dominance everywhere *)
let lexdec ~strict a b =
  let strictly =
    Formula.or_of
    @@ List.mapi a ~f:(fun k ak ->
        let bk = List.nth_exn b k in
        Formula.and_of
          ([ geq ak (zero_of ak); gt ak bk ]
          @ List.init k ~f:(fun l ->
              geq_or_bottom (List.nth_exn a l) (List.nth_exn b l))))
  in
  if strict then strictly
  else
    Formula.or_of
      [ strictly; Formula.and_of (List.map2_exn a b ~f:geq_or_bottom) ]

(* the decrease relation of one level, as the template defines it: some
   piece contains y, and some piece i contains x such that for every piece j
   containing y the tuple of i at x decreases to the tuple of j at y *)
let level_dec ~strict ((px, py) : pieces * pieces) =
  Formula.and_of
    [
      Formula.or_of (List.map py ~f:fst);
      Formula.or_of
      @@ List.map px ~f:(fun (disc_i, r_i) ->
          Formula.and_of
            (disc_i
            :: List.map py ~f:(fun (disc_j, r_j) ->
                Formula.mk_imply disc_j (lexdec ~strict r_i r_j))));
    ]

(* the relation the certificate induces, over [params_of c]: the truncated
   lexicographic progress of Kura & Unno (arXiv:2607.10650, Def. 7.8) — a
   strict decrease at some level with non-strict decreases at all more
   significant ones, or, at an accepting priority, non-strict decreases at
   every level; with one non-accepting level this is the WF/NWF decrease *)
let dec_of_ranking c =
  let at l = List.nth_exn c.levels l in
  let n = List.length c.levels in
  let nonstrict_below l =
    List.init l ~f:(fun m -> level_dec ~strict:false (at m))
  in
  let strictly =
    Formula.or_of
    @@ List.init n ~f:(fun l ->
        Formula.and_of (level_dec ~strict:true (at l) :: nonstrict_below l))
  in
  if c.accepting then
    Formula.or_of [ strictly; Formula.and_of (nonstrict_below n) ]
  else strictly

let dec_of (c : t) = Formula.or_of (List.map c ~f:dec_of_ranking)

let str_of_pieces =
  String.concat_map_list ~sep:"" ~f:(fun (disc, rs) ->
      sprintf "\n    (piece (when %s) (rank %s))" (Formula.str_of disc)
        (String.concat_map_list rs ~sep:", " ~f:Term.str_of))

let str_of_ranking c =
  sprintf "(ranking%s%s)"
    (if c.accepting then " accepting" else "")
    (String.concat_mapi_list c.levels ~sep:"" ~f:(fun l (px, py) ->
         sprintf "\n  (level %d (x%s)\n   (y%s))" l (str_of_pieces px)
           (str_of_pieces py)))

let str_of (c : t) =
  match c with
  | [ r ] -> str_of_ranking r
  | rs ->
      sprintf "(union-of-rankings%s)"
        (String.concat_map_list rs ~sep:"" ~f:(fun r ->
             "\n " ^ str_of_ranking r))
