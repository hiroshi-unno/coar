int g = 1;
int *gp = &g;
int main(void) {
    *gp = 4;
    return g;
}
