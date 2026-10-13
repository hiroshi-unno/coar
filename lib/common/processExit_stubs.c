/* Flush every C stdio stream (fflush(NULL)), so that output a C or C++
   library buffered through stdio is written before the process ends by
   _exit, which flushes nothing. */
#include <stdio.h>
#include <caml/mlvalues.h>

value coar_flush_c_stdio(value unit)
{
  (void)unit;
  fflush(NULL);
  return Val_unit;
}
