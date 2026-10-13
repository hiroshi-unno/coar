(* Nested predicate polymorphism: each level uses the level below twice, and RCaml
   instantiates a predicate-polymorphic definition by copying its constraints, so the
   generated system doubles per level.  Measured with
   config/solver/rcaml_wopp_printer.json, 2026-09-06:

     depth 1:  28 clauses,  25 unknowns
     depth 2:  56 clauses,  49 unknowns
     depth 3: 112 clauses,  97 unknowns

   The modular QCHC encoding of the same program is linear in the depth --
   benchmarks/DQpCSP/handcrafted/pred_poly_modular_nested3_sat.smt2, four clauses.
   Verdict: sat. *)

let app0 f x = f x
let app1 f x = app0 f (app0 f x)
let app2 f x = app1 f (app1 f x)
let app3 f x = app2 f (app2 f x)

let main u =
  let a = app3 (fun z -> z + 1) u in
  assert (a >= u)

[@@@assert "typeof(main) <: {v: int | v >= 0} -> unit"]
