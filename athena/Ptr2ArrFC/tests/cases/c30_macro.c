#define DEREF(p) (*(p))
#define SET(p, v) (*(p) = (v))
int main(void) {
    int x = 0;
    int *p = &x;
    SET(p, 3);
    return DEREF(p);
}
