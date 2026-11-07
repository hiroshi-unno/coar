/* p2a-expect: normal=17 memory-safety=17 memory-safety+reach-error=17 assume-safety=17 */
/* The difference of two pointers written through integers wide enough for an
   address: a string length in bytes over char pointers, and a distance in
   bytes over int pointers (3 ints, 12 bytes, in the input's layout and in the
   translated one alike). */
static unsigned long my_strlen(const char *str) {
  const char *s = str;
  while (*s != 0) s++;
  return (unsigned long)((long)s - (long)str);
}
int main(void) {
  char buf[8] = "abcde";
  int a[6];
  int *p = &a[1], *q = &a[4];
  long d = (long)q - (long)p;
  return (int)my_strlen(buf) + (int)d;
}
