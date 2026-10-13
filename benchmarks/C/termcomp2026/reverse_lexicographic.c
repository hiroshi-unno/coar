#include <stdlib.h>
#include <stdbool.h>

extern int __VERIFIER_nondet_int(void);
extern bool __VERIFIER_nondet_bool(void);


int main() {
    int m = __VERIFIER_nondet_int();
    int x = m;
    int y = 0;
    int s = 0;
    int t = m;
    int pc = 0;
 
    while (x >= 0 && y >= 0 && s>=0 && t>=0) {
        if (pc == 0){
            if(__VERIFIER_nondet_bool()){
                while(y <= m && __VERIFIER_nondet_bool()){
                    y++;
                    t--;
                }
                x--;
                s++;
            }
            if(__VERIFIER_nondet_bool()){
                pc = 1;            
            }
            y--;
            t++;
        }
        else{
            if(__VERIFIER_nondet_bool()){
                while(t <= m && __VERIFIER_nondet_bool()){
                    t++;
                    y--;
                }
                s--;
                x++;
            }
            t--;
            y++;
        }
    }
    return 0;
}