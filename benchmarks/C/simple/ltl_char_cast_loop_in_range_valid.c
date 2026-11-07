// The twin of ltl_char_cast_loop_wraps_invalid.c: a value converted to char
// never exceeds 127, however often the loop increments it.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x <= 127));
int x;
int main() { while (1) { x = (char)(x + 1); } return 0; }
