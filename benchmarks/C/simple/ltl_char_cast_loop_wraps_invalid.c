// (char)(x + 1) reduces modulo 256 into -128..127: after 127 the counter is
// -128, so x >= 0 fails.  Read as the identity, the cast made x grow forever
// and the property was proved.  expected: -p cltl invalid
//@ ltl invariant a: [](AP(x >= 0));
int x;
int main() { while (1) { x = (char)(x + 1); } return 0; }
