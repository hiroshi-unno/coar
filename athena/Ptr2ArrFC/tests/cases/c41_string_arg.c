int len(char *s) { int n = 0; while (s[n] != 0) n++; return n; }
int main(void) {
    return len("hello");
}
