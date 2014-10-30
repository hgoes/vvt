#include "benchmarks.h"

int main() {
  NONDET_INT(l);
  NONDET_INT(n);
  int i,k;

  if (l<=0) return 0;
  k = 1;
  while (k<n){
    i = l;
    while (i<n){  
      assert(1<=i);
      i++;
    }
    if(__nondet_bool())
      l = l + 1;
    k++;
  }
 }
