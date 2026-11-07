(* Lemmas are claims to be proved, never assumptions.  [count n] is [n] for
   [n >= 0], so the assertion fails: the program is unsafe.  The first lemma
   claims [count] never exceeds 1, which is false ([count 2 = 2]); were it
   assumed, it would prove the assertion and the answer would be a wrong
   sat.  The relational proof search of MuCyc
   (config/solver/rcaml_mucyc_relational.json) tries to prove it, refutes it,
   reports it unused, and cannot decide the assertion, whose failure needs a
   derivation of height 1001: it answers unknown or runs out of time, never
   sat.  The second lemma applies [f], a variable rather than a function
   defined at the top level of the file, which has no graph to refer to, and
   is refused when the file is read. *)
let rec count n = if n <= 0 then 0 else 1 + count (n - 1)

let main () = assert (count 1000 <> 1000)

[@@@lemma "forall n r. count n = r => r <= 1"]
[@@@lemma "forall f n. f n >= 0"]
