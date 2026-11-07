typedef unsigned int size_t;
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "c18.c", 3, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern void *malloc(size_t size);
int main() {
    int n = __VERIFIER_nondet_int();
    if (n <= 0 || n > 100) return 0;
    int *a = malloc(n * sizeof(int));
    int i;
    for (i = 0; i < n; i++) a[i] = i;
    if (a[0] != 0) reach_error();
    return 0;
}
