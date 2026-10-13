(* Which predicate templates were grown from which, for a consumer that wants
   to reuse what it computed for the template a growth step started from.

   A template module that grows a template by keeping its built disjuncts
   registers the result [tmpl] together with the template it was grown from
   ([old]) and the template of the added disjuncts alone ([delta], over the
   same lambda parameters), and the holes of [delta].  The contract a
   registration states, and the only one a reader may rely on: for every
   argument tuple [e], [tmpl e] is equivalent to [old e \/ delta e], and the
   holes of [delta] are exactly [delta_holes], none of them a hole of [old].
   Nothing else is promised -- [tmpl] need not be built as a disjunction of
   the two terms.

   Keyed by the physical identity of [tmpl]: a template is an immutable term
   built once per growth step, and a reader holding another term, even an
   equal one, finds nothing, which is a lost reuse and never a wrong one.  The
   table keeps the few most recent registrations only, since a reader asks
   about the template it currently holds. *)

open Core

type entry = {
  tmpl : Ast.Logic.term;
  old : Ast.Logic.term;
  delta : Ast.Logic.term;
  delta_holes : Ast.Ident.tvar list;
}

let keep = 64
let entries : entry list Atomic.t = Atomic.make []

let register ~tmpl ~old ~delta ~delta_holes =
  let rec update () =
    let cur = Atomic.get entries in
    let next = { tmpl; old; delta; delta_holes } :: List.take cur (keep - 1) in
    if not (Atomic.compare_and_set entries cur next) then update ()
  in
  update ()

let find tmpl =
  List.find (Atomic.get entries) ~f:(fun e -> phys_equal e.tmpl tmpl)

(* Set once by a template module whose growth registers templates here; a
   reader does nothing (and keeps nothing) until then. *)
let active_flag = Atomic.make false
let activate () = Atomic.set active_flag true
let active () = Atomic.get active_flag

(* The templates a growing module has built, most recent first: a reader
   remembers terms under these only, so that the other templates it is given
   (a learning attempt's, say) neither fill its memory nor displace them. *)
let bases : Ast.Logic.term list Atomic.t = Atomic.make []

let note_base tmpl =
  let rec update () =
    let cur = Atomic.get bases in
    if not (Atomic.compare_and_set bases cur (tmpl :: List.take cur 3)) then
      update ()
  in
  update ()

let is_base tmpl =
  List.exists (Atomic.get bases) ~f:(fun t -> phys_equal t tmpl)
