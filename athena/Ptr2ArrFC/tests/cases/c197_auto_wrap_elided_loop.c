/* p2a-expect: normal=0 */
/* --integers=auto must leave out the reduction of i + 1u: the loop bound n
   is at most 255, so i + 1u stays in range and the value analysis shows it.
   The nondet's own reduction is left out too, the consumer confining a
   nondet to its type. */
extern unsigned __VERIFIER_nondet_uint(void);
int main(void) {
    unsigned n = __VERIFIER_nondet_uint();
    if (n > 255u) n = 255u;
    unsigned i = 0u;
    while (i < n) i = i + 1u;
    return i == n ? 0 : 1;
}
