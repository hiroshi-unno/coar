let optimize_formula hes =
  let funcs, entry = Problem.let_muclp hes in
  let funcs =
    List.map
      (fun func ->
         let fix, pvar, bounds, body = Problem.let_function func in
         let body = Ast.FormulaUtil.remove_unused_bounds body in
         Problem.mk_func fix pvar bounds body)
      funcs
  in
  let entry = Ast.FormulaUtil.remove_unused_bounds entry in
  Problem.make funcs entry

let optimize = optimize_formula
