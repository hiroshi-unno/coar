/* The seconds of CLOCK_MONOTONIC, for measuring durations.  Unlike
   gettimeofday's CLOCK_REALTIME, this clock is never stepped by a time
   synchronisation, and it is the clock a relative timer (`timeout`, alarm,
   nanosleep, a solver's own budget) counts in. */
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <time.h>

double coar_monotonic_seconds_unboxed(value unit)
{
  struct timespec ts;
  (void)unit;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

value coar_monotonic_seconds(value unit)
{
  return caml_copy_double(coar_monotonic_seconds_unboxed(unit));
}
