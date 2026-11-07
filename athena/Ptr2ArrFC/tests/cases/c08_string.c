int len(char *s) { int n = 0; while (*s != '\0') { s++; n++; } return n; }
int main(void) {
    char *s = "abc";
    return len(s);
}
