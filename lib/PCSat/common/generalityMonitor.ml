open Core

(* How much generality each phase of the loop RECEIVES, how much it destroys,
   and -- the count that decides whether producing any of it was worth doing --
   how much it USES.

   Why the third count is the point.  A counterexample is a model, and a
   mechanism that makes it more general is easy to measure at the producer: the
   examples come out parametric, the arbitrary constants are gone, and the
   producer's own numbers say so.  None of that says a phase downstream can act
   on what arrived.  It often cannot: the labeling phase's query is
   propositional and keyed on the atom's structure INCLUDING its guard, so a
   guarded example is not a weaker fact to it but a different opaque atom; and a
   guard is only discharged when it is ground, so the generality a producer adds
   is exactly what stops the consumer treating the atom as forced.  Measured
   once without this instrument, a mechanism that removed every invented value
   from the validator's examples cost a tracked benchmark's refutation, and
   which phase stopped paying for the generality had to be guessed -- the first
   guess being a symptom that repaired cleanly and changed nothing.

   So the rule this exists to check is: a mechanism that raises ARRIVAL without
   raising USE has bought nothing, and that must be visible from the run that
   produces it rather than from a corpus verdict afterwards.

   Switched on with [COAR_GENERALITY=1] rather than through a config field,
   because the counts span four phases whose configurations are separate files
   and because every diagnostic dump in this tree is reached the same way.  The
   counters are process-global, so a run that starts several solver domains
   attributes their phases to one set of numbers; read them on single-domain
   runs, as the other per-phase measurements here are read. *)

type phase = Validation | Labeling | Resolution | Synthesis

let str_of_phase = function
  | Validation -> "validation"
  | Labeling -> "labeling"
  | Resolution -> "resolution"
  | Synthesis -> "synthesis"

(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let enabled =
  Lazy.from_val
    (match Sys.getenv "COAR_GENERALITY" with
    | Some ("1" | "true" | "yes") -> true
    | _ -> false)

let on () = Lazy.force enabled

(* (phase, kind, name) -> count, where [kind] is one of the three questions.
   An association list rather than a hashtable: there are a few dozen keys and
   the report wants them in insertion order, which is the order a reader meets
   the phases in. *)
let counts : ((string * string * string) * int ref) list ref = ref []

(* A ZERO IS REGISTERED, which is the opposite of what a counter usually wants
   and is the whole point here.  The question this instrument answers is whether
   a phase USES the generality it receives, and "the count is zero" and "the
   counter was never reached" are different answers to it -- the first says the
   mechanism is not paying, the second says the measurement is not running.  A
   report that silently omits the zeros cannot tell them apart, which is the
   shape of every probe in this tree that was read as evidence and was not. *)
let bump key n =
  match List.Assoc.find !counts ~equal:Stdlib.( = ) key with
  | Some r -> r := !r + n
  | None -> counts := !counts @ [ (key, ref n) ]

(* examples reaching a phase, split by what they carry.  [ground] is a plain
   application, [parametric] one with parameters, [guarded] one whose guard is
   not [true] -- the three are not exclusive and are not meant to be: a
   parametric atom usually also carries a guard, and the point of reporting both
   is that they are lost to different things. *)
(* [site] names WHERE in the phase, because a phase can have more than one
   consumer of the same examples and they need not receive the same thing: the
   labeling hands one search the instantiated atoms and lets another read the
   examples as they are, so one arrival number summed over both would say
   nothing about either. *)
let arrive ?(site = "") phase ~ground ~parametric ~guarded =
  if on () then (
    let p = str_of_phase phase in
    let n what = if String.is_empty site then what else site ^ "-" ^ what in
    bump (p, "arrive", n "ground") ground;
    bump (p, "arrive", n "parametric") parametric;
    bump (p, "arrive", n "guarded") guarded)

(* generality this phase destroys: grounded, filled with a dummy, or dropped
   because it was parametric.  [what] names the site so that the four places
   this happens stay distinguishable in the report. *)
let lose phase what n = if on () then bump (str_of_phase phase, "lose", what) n

(* outputs this phase produced that the ground form could not have produced.
   The name should say which mechanism, not which phase, because that is what a
   reader compares across settings. *)
let use phase what n = if on () then bump (str_of_phase phase, "use", what) n

(* Register a counter at zero so that it appears in the report before anything
   has happened to it.  Without this the zeros come back only for the counters a
   phase reached, and a key that is missing means either "this did not happen"
   or "this phase did not run" -- the distinction the zero above exists to
   preserve, one level up.  Called at a phase's entry with the counters it owns.
*)
let expect phase kind names =
  if on () then
    List.iter names ~f:(fun what ->
        let key = (str_of_phase phase, kind, what) in
        match List.Assoc.find !counts ~equal:Stdlib.( = ) key with
        | Some _ -> ()
        | None -> counts := !counts @ [ (key, ref 0) ])

(* The size of the version space at the end of a round: how many examples are
   decided positive, decided negative, and undecided.

   It is reported here rather than through a second switch because the numbers
   above are UNINTERPRETABLE without it.  Those ask how much generality a phase
   receives and uses; if nothing is ever decided, the loop has learned nothing
   whatever the generality figures say, and a reader comparing two settings on
   them would be comparing two ways of deciding nothing.  Measured on one
   benchmark family, three sizes, 340/378/368 labelings: not one decided example
   at any of them, the size that ANSWERS included -- its single positive being
   the vacuous "=> true".  So the loop was running and not learning, which the
   verdict cannot show and tracing can only show by changing the run: under a
   verbose chain that family answers at no size at all.

   A zero is reported, for the reason the counters above register theirs: "no
   example was decided" and "this was not measured" are different answers. *)
let vspace : (int * int * int * int) option ref = ref None

let version_space ~pos ~neg ~und ~vacuous =
  if on () then vspace := Some (pos, neg, und, vacuous)

let report ~round print =
  if on () && ((not (List.is_empty !counts)) || Option.is_some !vspace) then (
    print @@ lazy (sprintf "[generality] round %d" round);
    (match !vspace with
    | None -> ()
    | Some (pos, neg, und, vacuous) ->
        print
        @@ lazy
             (sprintf
                "[generality]   version space decided+ = %d decided- = %d \
                 undecided = %d vacuous+ = %d%s"
                pos neg und vacuous
                (if pos + neg = 0 then "   (nothing decided: not learning)"
                 else if vacuous = pos && neg = 0 then
                   "   (every decided example is the vacuous one: validation \
                    decided nothing)"
                 else "")));
    List.iter !counts ~f:(fun ((p, kind, what), n) ->
        print @@ lazy (sprintf "[generality]   %s %s %s = %d" p kind what !n)))

let reset () =
  if on () then (
    counts := [];
    vspace := None)
