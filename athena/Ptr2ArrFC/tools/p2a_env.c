/* Execution environment for differential runs of an input and its output.

   Every __VERIFIER_nondet_* call draws from one generator seeded by P2A_SEED,
   so two programs that make the same sequence of draws see the same values.
   Each draw, and each call to an error or assumption function, is appended to
   the trace file named by P2A_TRACE, one line per event, written unbuffered so
   that the trace of a run killed by a timeout is complete up to the kill.
   The comparison of two runs is a comparison of their traces, exit statuses
   and standard outputs.

   All definitions are weak: a program that defines one of these functions
   itself keeps its own definition. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <limits.h>
#include <stdint.h>
#ifdef __linux__
#include <sys/prctl.h>

/* No core dump. Where the system hands core dumps to a crash reporter
   through a pipe (kernel.core_pattern starting with '|', as apport does),
   RLIMIT_CORE does not stop the hand-over, and the reporter makes a run that
   aborts take a second or more, several under load: past the runner's time
   limit, so that an abort read as a timeout. A process that is not dumpable
   is not handed over. */
__attribute__((constructor)) static void p2a_no_core_dump(void) {
  prctl(PR_SET_DUMPABLE, 0, 0, 0, 0);
}
#endif

static unsigned long long p2a_state;
static int p2a_ready;
static int p2a_trace_fd = -2;

static void p2a_event(const char *fmt, long long v) {
  char buf[96];
  int n;
  if (p2a_trace_fd == -2) {
    const char *path = getenv("P2A_TRACE");
    p2a_trace_fd = path ? open(path, O_WRONLY | O_CREAT | O_APPEND, 0644) : -1;
  }
  if (p2a_trace_fd < 0) return;
  n = snprintf(buf, sizeof buf, fmt, v);
  if (n > 0) (void)!write(p2a_trace_fd, buf, (size_t)n);
}

static unsigned long long p2a_next(void) {
  if (!p2a_ready) {
    const char *s = getenv("P2A_SEED");
    p2a_state = s ? strtoull(s, 0, 10) : 1;
    p2a_state = p2a_state * 6364136223846793005ULL + 1442695040888963407ULL;
    p2a_ready = 1;
  }
  p2a_state = p2a_state * 6364136223846793005ULL + 1442695040888963407ULL;
  return p2a_state >> 33;
}

/* Small values, and now and then a boundary value, so that loops stop soon
   and indices stay in range while the edges of each type are still drawn. */
static long long p2a_signed(long long lo, long long hi) {
  unsigned long long r = p2a_next();
  if (r % 50 == 0) return (r / 50) % 2 ? hi : lo;
  return (long long)(r % 21) - 5;
}
static unsigned long long p2a_unsigned(unsigned long long hi) {
  unsigned long long r = p2a_next();
  if (r % 50 == 0) return (r / 50) % 2 ? hi : 0;
  return r % 16;
}

#define W __attribute__((weak))
#define NONDET_S(name, type, lo, hi)                        \
  W type name(void) {                                       \
    type v = (type)p2a_signed((long long)(lo), (long long)(hi)); \
    p2a_event(#name " %lld\n", (long long)v);               \
    return v;                                               \
  }
#define NONDET_U(name, type, hi)                            \
  W type name(void) {                                       \
    type v = (type)p2a_unsigned((unsigned long long)(hi));  \
    p2a_event(#name " %lld\n", (long long)v);               \
    return v;                                               \
  }

/* The bounds of each type come from the headers, so that a program compiled
   with -m32 (ILP32, where long and size_t are 32 bits wide) draws its edges. */
NONDET_S(__VERIFIER_nondet_int, int, INT_MIN, INT_MAX)
NONDET_S(__VERIFIER_nondet_long, long, LONG_MIN, LONG_MAX)
NONDET_S(__VERIFIER_nondet_longlong, long long, LLONG_MIN, LLONG_MAX)
NONDET_S(__VERIFIER_nondet_short, short, SHRT_MIN, SHRT_MAX)
NONDET_S(__VERIFIER_nondet_char, char, -128, 127)
NONDET_U(__VERIFIER_nondet_uint, unsigned int, UINT_MAX)
NONDET_U(__VERIFIER_nondet_unsigned, unsigned int, UINT_MAX)
NONDET_U(__VERIFIER_nondet_ulong, unsigned long, ULONG_MAX)
NONDET_U(__VERIFIER_nondet_ulonglong, unsigned long long, ULLONG_MAX)
NONDET_U(__VERIFIER_nondet_ushort, unsigned short, USHRT_MAX)
NONDET_U(__VERIFIER_nondet_uchar, unsigned char, UCHAR_MAX)
NONDET_U(__VERIFIER_nondet_size_t, size_t, SIZE_MAX)

W _Bool __VERIFIER_nondet_bool(void) {
  _Bool v = (_Bool)(p2a_next() % 2);
  p2a_event("__VERIFIER_nondet_bool %lld\n", (long long)v);
  return v;
}

/* Exit statuses 77 and 78 mark an error reached and an assumption violated.
   The split violation markers of a --memory-safety output end with the same
   statuses (77 valid-deref, 78 valid-free) but are defined by the output and
   leave no event in the trace, which is how the runner tells them apart. */
W void reach_error(void) {
  fflush(stdout);
  p2a_event("reach_error %lld\n", 0);
  _Exit(77);
}
W void __VERIFIER_error(void) { reach_error(); }
/* With --violation-markers=reach-error the output calls the input's own
   reach_error by this name; when the input only declares it, this stands in
   for it as reach_error above stands in for the input's. */
W void __p2a_input_reach_error(void) { reach_error(); }
W void __VERIFIER_assume(int c) {
  if (!c) {
    fflush(stdout);
    p2a_event("assume_false %lld\n", 0);
    _Exit(78);
  }
}

/* The body of a generated stand-in for an external function the program
   declares but does not define (see p2a_diff.py): the call is recorded in the
   trace with the value it returns, a small integer drawn like a nondet int.
   The stand-in returns long long whatever the declared return type; on x86-64
   an integer return of any width is read from the same register, so a caller
   expecting a narrower integer, or nothing, sees the low bits or ignores it. */
long long p2a_extern_value(const char *name) {
  long long v = p2a_signed(-2147483647 - 1, 2147483647);
  char fmt[96];
  snprintf(fmt, sizeof fmt, "extern %s %%lld\n", name);
  p2a_event(fmt, v);
  return v;
}
