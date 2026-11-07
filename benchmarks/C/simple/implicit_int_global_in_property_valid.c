// a and r are declared at file scope without a type (C89 implicit int), as the
// decision-predicates benchmarks of Cook and Koskinen do.  They are globals, so a
// property may name them; refusing such a property as naming no global is wrong.
// r is set right after every a, so every a is followed by an r.
// expected: -p cltl valid
//@ ltl invariant positive: [](AP(a != 0) ==> <> AP(r != 0));
a = 0;
r = 0;
int main() {
  while (1) {
    a = 1;
    a = 0;
    r = 1;
    r = 0;
  }
  return 0;
}
