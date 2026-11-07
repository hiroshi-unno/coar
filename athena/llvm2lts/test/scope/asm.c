int main(void) { int x = 1; __asm__ volatile("" : "+r"(x)); return x; }
