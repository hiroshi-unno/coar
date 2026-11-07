// abort() does not return, so x = 1 never runs.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 0));
extern void abort();
int x = 0;
int main() { abort(); x = 1; while (1) {} return 0; }
