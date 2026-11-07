/* p2a-expect: normal=0 */
/* A recursive call graph: the value analysis reads a recursive function
   without a specification unsoundly (a global it raises up to 10 is shown
   in {0; 1}), so --integers=auto must not use it and keeps every
   reduction. */
unsigned g;
void f(unsigned d) {
    g = g + 1u;
    if (d > 0u) f(d - 1u);
}
int main(void) {
    f(9u);
    return g == 10u ? 0 : 1;
}
