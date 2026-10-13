extern int __VERIFIER_nondet_int(void);
extern bool __VERIFIER_nondet_bool(void);


int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    int z = __VERIFIER_nondet_int();
    int count = __VERIFIER_nondet_int();
 
    while(count > 0 && z > 0){
        if(x > 0){
            x--;
            y++;
            z++;
        }else if(y > 0){
            y--;
            z++;
        }else if(z > 0){
            z--;
            if(__VERIFIER_nondet_bool()){
                count--;
                x = __VERIFIER_nondet_int();
                y = __VERIFIER_nondet_int();
                z = __VERIFIER_nondet_int();
            }
        }
    }
    return 0;    
}