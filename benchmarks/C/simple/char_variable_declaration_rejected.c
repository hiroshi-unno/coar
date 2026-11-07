// A char variable holds the assigned value modulo 256 (here 44), and the
// frontend reads every variable as an unbounded integer, so the declaration is
// refused rather than decided as if c were 300.
// expected: -p cltl a semantic error naming the char-typed declaration
//@ ltl invariant a: [](AP(c == 0 || c == 44));
char c;
int main() { c = 300; while (1) {} return 0; }
