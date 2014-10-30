#include "benchmarks.h"

int main() {
  NONDET_INT(n);
  int i,j,k;

  i = 0;
  while (i<n) {
    j = i;
    while (j<n) {
      k = j;
      while (k<n) {
	if(__nondet_bool()){
	  assert(k>=j);
	  assert(j>=i);
	}
	k++;
      }
      j++;
    }
    i++;
  }
}
