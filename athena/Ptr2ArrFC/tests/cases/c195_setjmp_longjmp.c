/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* setjmp and longjmp written as jumps: a longjmp from a callee two levels
   down, the value 0 passed as 1, a counting loop through setjmp, a jmp_buf
   on the heap, and a recursive function whose activations each set their
   own buffer. */
#include <setjmp.h>
#include <stdlib.h>
static jmp_buf env;
static int global;
static void deep(int v) { global = 42; longjmp(env, v); }
static void middle(int v) { deep(v); global = -1; }
static int depth(jmp_buf *b, int n) {
  jmp_buf here;
  if (n == 0) longjmp(*b, 7);
  int r = setjmp(here);
  if (r == 0) return depth(&here, n - 1) + 1;
  return r + 100;
}
int main(void) {
  int r = setjmp(env);
  if (r == 0) {
    middle(0);
    return 1;
  }
  if (r != 1 || global != 42) return 2;
  jmp_buf *h = malloc(sizeof(jmp_buf));
  if (!h) return 0;
  volatile int count = setjmp(*h);
  if (count < 3) longjmp(*h, count + 1);
  free(h);
  if (count != 3) return 3;
  jmp_buf top;
  int t = setjmp(top);
  if (t == 0) depth(&top, 2);
  if (t != 0 && t != 7) return 4;
  return 0;
}
