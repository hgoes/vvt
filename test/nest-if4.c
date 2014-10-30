#include "benchmarks.h"

int main() {
  NONDET_INT(l);
  NONDET_INT(n);
  int i,k;

  if (l<=0) return 0;

  k = 1;
  while (k<n){
    if(__nondet_bool()) {
      i = l;
      while (i<n) {
	assert(1<=i);
	i++;
      }
    }
    i = l;
    while (i<n) { i++; }
    k++;
  }

 }
