#include <stdlib.h>
#include <stdbool.h>

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x = __VERIFIER_nondet_int();

    while (x != 0)
    {
        if (x > 0)
            x = -x + 1;
        else
            x = -x - 1;
    }
    return 0;
}
