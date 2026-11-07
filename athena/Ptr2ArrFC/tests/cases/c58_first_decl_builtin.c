extern void abort(void);
int main(void) { char *s = "x"; if (s[0] != 'x') abort(); return 0; }
