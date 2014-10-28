#include <stdbool.h>

void assert(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int n = __nondet_int();
  int i,k,l;

  k = 1;
  while (k<n){
    assert(1<=k);
    i = 1;
    i = 1; while (i < n) i++;  
    i = 1; while (i < n) i++;
    i = 1; while (i < n) i++;
    i = 1; while (i < n) i++;
    i = 1; while (i < n) i++;
    i = 1; while (i < n) i++;
    i = 1; while (i < n) i++;
    k++;
  }

 }
