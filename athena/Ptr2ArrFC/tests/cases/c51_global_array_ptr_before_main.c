int buf[8];
int *cur;
void push(int v) { *cur = v; cur++; }
int main(void) {
    cur = buf;
    push(1);
    push(2);
    return buf[1];
}
