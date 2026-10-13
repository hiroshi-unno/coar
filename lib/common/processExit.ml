(* Ending the process when solver domains may still be running.

   Contract: [exit code] runs every OCaml [at_exit] handler (in the order
   [Stdlib.exit] runs them, which includes flushing the OCaml standard
   channels), flushes the C stdio streams, and ends the process with status
   [code] WITHOUT running the C library's exit handlers: neither functions
   registered with [atexit] nor the static destructors of linked C++
   libraries.  It never returns.

   Why: a parallel backend returns its answer as soon as one of its domains
   has one, and the domains still solving are never joined -- one of them may
   be inside a Z3 call, which cannot be interrupted.  [Stdlib.exit] ends with
   the C [exit], which runs libz3's static destructors on the main thread
   while those domains are still using the objects being destroyed.  Under
   load this corrupted the heap after the verdict had been printed: glibc
   reported "malloc(): unsorted double linked list corrupted" or
   "malloc_consolidate(): unaligned fastbin chunk detected" from a worker,
   and the process either died with SIGSEGV/SIGABRT or deadlocked in the
   allocator until an outside timeout killed it, so a harness saw a crash or
   a timeout for a run that had answered.  [_exit] ends every thread at once
   and leaves the heap alone.

   What is skipped is only process-wide C cleanup the kernel performs anyway
   (memory, descriptors); no C library in this program writes a result from
   an [atexit] handler, and C stdio buffers are flushed here explicitly
   (C++ [std::cout] is synchronised with stdio by default, so it is covered). *)

external flush_c_stdio : unit -> unit = "coar_flush_c_stdio"

let exit code =
  Stdlib.do_at_exit ();
  flush_c_stdio ();
  Unix._exit code
