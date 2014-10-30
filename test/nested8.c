#include "benchmarks.h"

int main() {
  NONDET_INT(n);
  NONDET_INT(m);
  int i,j,k;
  
  if(n>m) return 0;
  i = 0;
  while (i<n) {
    j = 0;
    while (j<n) {
      k = j;
      while (k<n+m) {
	assert(i+j<=n+k+m);
	k++;
      }
      j++;
    }
    i++;
  }
}
