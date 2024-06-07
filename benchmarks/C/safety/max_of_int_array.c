#include <stdio.h>

int max_of_int_array(int a[], int len){
  int i, temp;
  /*begin -- set initial values*/
  i=0;
  temp = a[0];
  /*end -- set initial values*/

  /*begin -- run loop*/
  for (i=1;i<len;i++){
    if (temp<a[i]) temp=a[i];
  }
  /*end -- run loop*/

  return temp;
}

int f1(void){
  int x[5] = {14,1,23,3,9};
  int y = 5;
  int z = max_of_int_array(x,y);
  printf("%d\n", z);
}

int f2(void){
  int x[5] = {24,1,23,3,9};
  int y = 5;
  int z = max_of_int_array(x,y);
  printf("%d\n", z);
}

int main(void) {
  f1();f2();
}
