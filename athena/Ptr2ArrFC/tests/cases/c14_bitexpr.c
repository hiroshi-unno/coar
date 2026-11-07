int main(void) {
    int a = 5, b = 3, c = 1;
    int x = (a & b) | (c << 2);
    int y = ((a ^ b) >> 1) & (b | c);
    return x + y;
}
