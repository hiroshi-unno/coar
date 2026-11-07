/* p2a-expect: normal=0 */
/* a * 5000000u with a in [0, 999] is non-negative in the mathematical
   reading but can exceed UINT_MAX: --integers=auto must place the
   non-negative reduction __p2a_wrapnn_u32, not leave it out. */
extern unsigned __VERIFIER_nondet_uint(void);
int main(void) {
    unsigned a = __VERIFIER_nondet_uint() % 1000u;
    unsigned b = a * 5000000u;
    if (a == 999u) return b == 700032704u ? 0 : 1;
    return 0;
}
