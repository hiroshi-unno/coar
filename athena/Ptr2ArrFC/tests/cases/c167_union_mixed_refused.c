/* Expected: refused (exit status 2). A union read through a member of another type than the one written
   reinterprets the bytes: left as a union, and refused. */
int main(void) {
  union { int a; char b; } u;
  u.a = 0x41;
  return u.b == 0x41 ? 0 : 1;
}
