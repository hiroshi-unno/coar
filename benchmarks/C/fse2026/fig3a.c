#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

typedef struct Node
{
    int value;
    struct Node *next;
} Node;

Node *process(Node *n, char c)
{
    if (c == 'A')
        return n->next;
    return NULL;
}

int main()
{
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    int z = __VERIFIER_nondet_int();
    int arr[10];
    for (int i = 0; i < 10; i++)
    {
        arr[i] = __VERIFIER_nondet_int();
    }
    int *p1 = &x;
    int *p2 = &y;
    char *p3 = (char *)&y;
    int *p4 = arr;
    int *p5 = (arr[5] <= y) ? &x : &z;
    int **p6 = (*p5 % 2 == 0) ? &p1 : &p4;
    int **p7 = &p5;
    Node *head = (Node *)malloc(sizeof(Node));
    head->value = 0;
    head->next = head;
    while (**p6 < *p2)
    {
        **p6 += **p7;
        if (process(head, *p3) == NULL)
        {
            **p6 -= **p7;
        }
    }
    return 0;
}
