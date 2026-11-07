union U { int i; unsigned u; };
int main(void) { union U x; x.i = 2; return x.u != 2; }
