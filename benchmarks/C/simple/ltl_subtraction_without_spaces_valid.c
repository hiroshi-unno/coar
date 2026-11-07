/* A subtraction written without spaces, `x-1`, is `x`, `-`, `1`: a lexer that
   reads an optionally signed literal makes it `x` followed by the literal `-1`,
   which is a syntax error, in the program and in the property alike.  y
   follows x one step behind, so y is never ahead of x; every statement is a
   step of the run, and between `x = x+1` and `y = x-1` x is two ahead. */
//@ ltl invariant PHI: [] AP(x-y<=2 && y-x<=0);

int x = 0;
int y = 0;

int main() {
    while (1) {
        x = x+1;
        y = x-1;
    }
    return 0;
}
