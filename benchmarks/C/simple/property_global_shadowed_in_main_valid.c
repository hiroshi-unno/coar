// A global i and a local i of main: the property is written at file scope,
// where the global is the one visible, so it names the global, which nothing
// changes.  main's local i is set to 1, which would make it fail.
// expected: -p cltl valid
int i = 0;
//@ ltl invariant a: [](AP(i == 0));
int main() { int i = 0; while (1) { i = 1; } return 0; }
