int g;
int *gp;
int arr[4];
int main(void) {
    gp = &g;
    *gp = 3;
    int *q = arr;
    q[1] = g;
    return arr[1];
}
