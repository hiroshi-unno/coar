/* p2a-expect: normal=0 normal+uninit-check=0 memory-safety+uninit-check=0 assume-safety+uninit-check=0 */
/* Every kind of scalar starts uninitialised: integers of each width and
   signedness, _Bool, an enumeration, floating point, a pointer, a
   bit-field, and arrays and structures of them; only written values are
   read. With --uninit=nondet each is drawn from the generator of its
   type. */
extern int __VERIFIER_nondet_int(void);
enum E { E0, E1 = 5 };
struct B { int a : 3; unsigned b : 5; char c; double d[2]; short *p; };
int main(void) {
    char c; signed char sc; unsigned char uc; short s; unsigned short us;
    int i; unsigned u; long l; unsigned long ul; long long ll;
    unsigned long long ull; _Bool bo; enum E e; float f; double d;
    int *p; struct B b[2]; int m[2][3];
    c = 1; sc = 1; uc = 1; s = 1; us = 1; i = 1; u = 1; l = 1; ul = 1;
    ll = 1; ull = 1; bo = 1; e = E1; f = 1; d = 1; p = 0;
    b[1].a = 1; b[1].c = 2; b[1].d[1] = 3;
    m[1][2] = 4;
    int r = c + sc + uc + s + us + i + (int)u + (int)l + (int)ul + (int)ll
            + (int)ull + bo + (int)e + (int)f + (int)d + (p == 0)
            + b[1].a + b[1].c + (int)b[1].d[1] + m[1][2];
    return r - 30;
}
