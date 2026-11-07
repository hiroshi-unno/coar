int f(void) { int y = 1; int *p = &y; return *p; }
int main(void) { char c = 'a'; char *p = &c; *p = 'b'; return c + f(); }
