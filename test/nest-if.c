#include <stdbool.h>

void assert(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int n = __nondet_int();
  int i,k;

  k = 1;
  while (k<n){
    i = 1;
    while (i<n) {
      assert(1<=k);
      i++;
    }
    if(i<n) {
      i = 1;
      while (i<n) { i++; }
    }
    k++;
  }

 }
