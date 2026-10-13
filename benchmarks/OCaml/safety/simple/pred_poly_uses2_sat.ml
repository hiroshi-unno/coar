(* RCaml's *own* predicate polymorphism, and what its instantiation costs
   compared with verifying the definition once for every predicate.

   `app` is generalized at its let-binding (Cgen.generalize), so it gets a
   predicate-polymorphic type, and every use instantiates it by *copying* the
   body's constraints with fresh predicate variables (Rtype.instantiate_val,
   case RForall).  This family measures the copy: dump the generated system with
   config/solver/rcaml_wopp_printer.json and count the clauses.

     definition `f x`      : 14 clauses at 1 use, 26 at 2, 50 at 4, 98 at 8  (+12 per use)
     definition `f (f (f x))` : 18, 34, 66 at 1, 2, 4 uses                   (+16 per use)

   The per-use increment grows with the *definition's* size, which is what makes
   it a copy rather than an application.  The QCHC counterpart keeps the
   definition part constant: benchmarks/DQpCSP/handcrafted/pred_poly_modular_uses8_sat.smt2
   is one definition clause plus one clause per use.  Verdict: sat. *)

let app f x = f x

let main u =
  let a0 = app (fun z -> z + 1) u in
  let a1 = app (fun z -> z + 2) u in
  assert (a0 > u && a1 > u)

[@@@assert "typeof(main) <: {v: int | v >= 0} -> unit"]
