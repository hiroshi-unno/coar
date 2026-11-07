/* p2a-expect: normal=0 */
/* A shift whose count is a variable holding one value on every execution:
   --integers=auto replaces the count by that constant, so the shift is one
   the integer mode can write and the reading stays the integer one. */
extern unsigned __VERIFIER_nondet_uint(void);
int main(void) {
    unsigned x = __VERIFIER_nondet_uint() % 16u;
    int k = 3;
    unsigned y = x << k;
    return y == x * 8u ? 0 : 1;
}
