extern int __VERIFIER_nondet_int(void);
int main(void) {
    int x = 1, y = 2;
    int *p = __VERIFIER_nondet_int() ? &x : &y;
    *p = 7;
    return x + y;
}
