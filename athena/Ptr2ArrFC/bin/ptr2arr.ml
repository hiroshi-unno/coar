(* The standalone [ptr2arr] command; its command line and exit statuses are
   the library Ptr2arr_cli's (../cli). The executable runs itself a second
   time as the Frama-C child, which this module boots when it sees the
   child's environment variable. *)

let () =
  if Ptr2arr_cli.is_child () then Ptr2arr_cli.boot_child ()
  else
    let args = List.tl (Array.to_list Sys.argv) in
    match Ptr2arr_cli.run ~exe:Sys.executable_name args with
    | Ptr2arr_cli.Exited status -> exit status
    | Ptr2arr_cli.Timed_out -> assert false (* no timeout was given *)
    | exception Ptr2arr_cli.Exit_with status -> exit status
