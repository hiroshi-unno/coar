#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

/* EXPECT: NO. The third byte of numbers[0] never changes, so the loop runs for ever whenever that
   byte is positive, and every access stays in the block. The block is accessed both as ints and as
   chars, which makes Ptr2Arr address it by bytes. */
int spin(int numbers[], int array_size)
{
    char* p;
    p = &(numbers[0]);
    p = p + 2;
    while (*p > 0) {
        (*p)--;
        (*p)++;
    }
    return 0;
}

int main() {
  int array_size = __VERIFIER_nondet_int();
  if (array_size < 4) {
     return 0;
  }
  int* numbers = (int*) alloca(array_size * sizeof(int));
  return spin(numbers, array_size);
}
