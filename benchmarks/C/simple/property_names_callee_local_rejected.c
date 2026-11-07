// The property names k, a local of a function main calls: it exists only
// during each call, so the file is refused.
// expected: -p cltl refused ("neither a global variable nor a local declared in main's outermost block")
//@ ltl invariant a: [](AP(k == 0));
void f() { int k = 0; }
int main() { f(); while (1) {} return 0; }
