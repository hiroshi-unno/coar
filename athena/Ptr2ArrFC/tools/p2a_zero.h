/* Included into every program the differential runner compiles: the
   function behind the redefinition of __builtin_alloca that zero-fills each
   block (see p2a_diff.py). */
static inline void *p2a_zero_fill(void *p, unsigned long n) {
  unsigned char *q = p;
  for (unsigned long i = 0; i < n; i++) q[i] = 0;
  return p;
}
