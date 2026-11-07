/* p2a-expect: normal=0 memory-safety=0 assume-safety=0 */
/* A global table of function pointers, read at a nondeterministic index
   and written at run time, and a typedef of a function pointer type. */
extern int __VERIFIER_nondet_int(void);
typedef int (*op_t)(int, int);
int add(int a, int b) { return a + b; }
int sub(int a, int b) { return a - b; }
int mul(int a, int b) { return a * b; }
op_t ops[3] = { add, sub, 0 };
int main(void) {
  ops[2] = mul;
  int acc = 1;
  for (int i = 0; i < 5; i++) {
    int k = __VERIFIER_nondet_int();
    if (k < 0 || k > 2) k = 0;
    op_t f = ops[k];
    acc = f(acc, i) % 1000;
  }
  if (ops[0] != add || ops[2] == ops[1]) return 1;
  return 0;
}
