extern int __VERIFIER_nondet_int(void);

int main()
{
    int x = __VERIFIER_nondet_int();
    int y = 0;
    int z = 0;

    while (x > 0 || y > 0 || z > 0)
    {
        if (y > 0)
        {
            y--;
            z++;
        }
        else if (z > 0)
        {
            z--;
            x += 2;
        }
        else
        {
            y = __VERIFIER_nondet_int();
            x = -x - 1;
        }
    }

    return 0;
}