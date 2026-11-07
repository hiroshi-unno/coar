int sum(int a[], int n) { int s = 0; int i; for (i = 0; i < n; i++) s += a[i]; return s; }
int main(void) {
    int b[3];
    b[0] = 1; b[1] = 2; b[2] = 3;
    return sum(b, 3);
}
