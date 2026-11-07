/* Definitions of the choice functions of a --memory-safety or
   --memory-cleanup output, for running the output: they replace the
   output's weak definitions, which make each choice nondeterministically.
   No call is a nondeterministic draw, so the trace of a run is the trace of
   the output without the checks' choices.

   The guess function of the guess form (--memtrack-check=guess): the n-th
   call (from 0) returns bit n of the mask P2A_GUESS_MASK (a decimal number;
   0 when unset), so a run with mask 0 guesses the empty set and never
   reports valid-memtrack, and the runs over every mask below 2^k try every
   set of k blocks. When P2A_GUESS_LOG names a file, each call appends one
   line to it (for the first 64 calls), so that a run with mask 0 tells how
   many choices the check makes.

   The probe function of --memtrack-nonterminating: the n-th call (from 1)
   returns 1 when n is P2A_PROBE_AT (0 when unset: never), so a run checks
   memtrack at most at the place of that call; P2A_PROBE_LOG counts the calls
   as P2A_GUESS_LOG does.

   The output may have renamed the functions (when the input uses the
   names); compile this file with -DP2A_GUESS_NAME=<name> and
   -DP2A_PROBE_NAME=<name>, the names in the record. A function whose name is
   not given is not defined. */
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>

/* Only the first calls are counted: the tools try at most the first few
   dozen choices, and a line per call would slow a long loop past the time
   limit. */
#define P2A_LOGGED_CALLS 64

static void p2a_choice_log(const char *var, long calls) {
  const char *log;
  if (calls > P2A_LOGGED_CALLS) return;
  log = getenv(var);
  if (log) {
    int fd = open(log, O_WRONLY | O_CREAT | O_APPEND, 0644);
    if (fd >= 0) {
      (void)!write(fd, "g\n", 2);
      close(fd);
    }
  }
}

#ifdef P2A_GUESS_NAME
int P2A_GUESS_NAME(void) {
  static int calls;
  static unsigned long long mask;
  static int ready;
  int bit;
  if (!ready) {
    const char *m = getenv("P2A_GUESS_MASK");
    mask = m ? strtoull(m, 0, 10) : 0;
    ready = 1;
  }
  bit = calls < 64 ? (int)((mask >> calls) & 1) : 0;
  calls++;
  p2a_choice_log("P2A_GUESS_LOG", calls);
  return bit;
}
#endif

#ifdef P2A_PROBE_NAME
int P2A_PROBE_NAME(void) {
  static long calls;
  static long at;
  static int ready;
  if (!ready) {
    const char *m = getenv("P2A_PROBE_AT");
    at = m ? strtol(m, 0, 10) : 0;
    ready = 1;
  }
  calls++;
  p2a_choice_log("P2A_PROBE_LOG", calls);
  return calls == at;
}
#endif
