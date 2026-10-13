/* Ask the kernel to send SIGKILL to the calling process when its parent dies
   (Linux prctl(PR_SET_PDEATHSIG)).  Returns true when the request was taken;
   false where the call fails or the platform has no such request. */
#include <caml/mlvalues.h>
#ifdef __linux__
#include <signal.h>
#include <sys/prctl.h>
#endif

value coar_set_pdeathsig_kill(value unit)
{
  (void)unit;
#ifdef __linux__
  return Val_bool(prctl(PR_SET_PDEATHSIG, SIGKILL) == 0);
#else
  return Val_false;
#endif
}
