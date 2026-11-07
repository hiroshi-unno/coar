// Conversions to the narrow types reduce modulo 2^w: (char)300 is 44,
// (short)32768 is -32768 and (unsigned char)-1 is 255 (C11 6.3.1.3; for the
// signed targets the GCC/Clang reduction).  expected: -p cltl valid
//@ ltl invariant a: [](AP((x == 0 || x == 44) && (y == 0 || y == -32768) && (z == 0 || z == 255)));
int x;
int y;
int z;
int main() {
  x = (char)300;
  y = (short)32768;
  z = (unsigned char)-1;
  while (1) {}
  return 0;
}
