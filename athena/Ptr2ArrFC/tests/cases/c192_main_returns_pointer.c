/* main returns a pointer converted to int, as the dietlibc termination
   tasks do (return (int) strcpy(out, in)): the exit status, which no
   property reads, becomes a nondeterministic int (the input's is the low
   bits of an address, so the differential run differs in the status). */
static char buf[4];
static char *fill(char *d) {
  d[0] = 'a';
  d[1] = 0;
  return d;
}
int main(void) {
  return (int) fill(buf);
}
