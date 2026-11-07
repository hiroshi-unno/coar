[@@@mode "hfl_prop_as_expectation"]
let f = (1.0 [@annot "{ret:prop | ret <= 0.6}"])
[@@@infer "f"]
