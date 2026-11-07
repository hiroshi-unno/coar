// The property's negation is <>(x == 1 || (y == 1 && z == 1)).  ltl3ba gives
// || and && the same precedence, associating to the left, so a conjunction on
// the right of a disjunction must be parenthesised in the formula handed to it;
// read as <>((x == 1 || y == 1) && z == 1) the negation never holds here, since
// z stays 0.  x becomes 1, so the property fails.
// expected: -p cltl invalid
//@ ltl invariant a: [](AP(x != 1) && (AP(y != 1) || AP(z != 1)));
int x = 0;
int y = 0;
int z = 0;
int main() { x = 1; while (1) {} return 0; }
