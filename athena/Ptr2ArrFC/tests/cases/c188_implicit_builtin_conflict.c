/* Expected: refused (exit status 2), kind implicit-declaration. memcpy
   called before it is declared, and then declared with another type than
   GCC's builtin: GCC reads the call with the builtin's type and the later
   declaration with the program's, so the program has no single reading. */
typedef __SIZE_TYPE__ size_t;
int f(char *d, char const *s) {
  return memcpy((void *)d, (void const *)s, 1) != 0;
}
extern int memcpy(void *, void const *, size_t);
int main(void) {
  char a[1] = {'a'}, b[1];
  return f(b, a) ? 0 : 1;
}
