/* Included into the E-ACSL-instrumented input by p2a_diff.py --uninit
   check: its malloc becomes p2a_zmalloc (tools/p2a_eacsl_zheap.c), which
   zero-fills the block. */
void *p2a_zmalloc(__SIZE_TYPE__ n);
#define malloc(n) p2a_zmalloc(n)
