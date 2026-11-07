/* p2a-expect: normal=0 */
/* An & between two variables cannot be written in the direct route's
   integer mode, so --integers=auto must choose the fixed-width reading and
   place no reduction. */
extern unsigned __VERIFIER_nondet_uint(void);
int main(void) {
    unsigned a = __VERIFIER_nondet_uint();
    unsigned b = __VERIFIER_nondet_uint();
    unsigned c = a & b;
    return c <= a ? 0 : 1;
}
