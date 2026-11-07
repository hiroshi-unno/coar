let f () = (0 [@annot "{ret:int | post(ret)}"])
[@@@infer "f:min(post)"]
