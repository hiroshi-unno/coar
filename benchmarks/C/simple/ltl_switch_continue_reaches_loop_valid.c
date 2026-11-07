// A continue inside a switch belongs to the enclosing loop, and a break to the
// switch: z counts the odd i in 0..3.
// expected: -p cltl valid
//@ ltl invariant a: <>(AP(x == 1) && AP(z == 2));
int x = 0; int i = 0; int z = 0;
int main() { for (i = 0; i < 4; i++) { switch (i % 2) { case 0: continue; default: break; } z = z + 1; } x = 1; while (1) {} return 0; }
