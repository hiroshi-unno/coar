(** Run a printer with default omission disabled on the calling thread only.
    Nested calls and exceptions restore the previous mode. *)
val with_full : (unit -> 'a) -> 'a

val is_full : unit -> bool
