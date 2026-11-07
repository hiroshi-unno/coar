extern unsigned short __VERIFIER_nondet_ushort(void);
extern unsigned char __VERIFIER_nondet_uchar(void);
/*
Athena front end: nondet_narrow_declared_terminating.c and nondet_narrow_undeclared_terminating.c
differ only in the declarations of their nondeterministic functions, and must translate to the
same transition system.
*/
int main()
{
    unsigned short n = __VERIFIER_nondet_ushort();
    unsigned char c;
    c = __VERIFIER_nondet_uchar();
    while (n > c) {
        n--;
    }
    return 0;
}
