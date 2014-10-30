#include "benchmarks.h"

int main() {
  int i,k;
  NONDET_INT(n);
  NONDET_INT(l);

  if (l<=0) return 0;

  k = 1;
  while (k<n){
    i = l;
    while (i<n) {
      assert(1<=i);
      i++;
    }
    k++;
  }

 }
