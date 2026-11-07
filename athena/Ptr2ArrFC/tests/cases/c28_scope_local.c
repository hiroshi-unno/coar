int *gp;
int main(void) {
    {
        int x = 1;
        gp = &x;
    }
    return *gp;
}
