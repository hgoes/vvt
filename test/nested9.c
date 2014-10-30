#include "benchmarks.h"

int main() {
  NONDET_INT(n);
  NONDET_INT(m);
  NONDET_INT(l);
  int i,j,k;
  
  if(3*n>m+l) return 0;
  i = 0;
  while (i<n) {
    j = 2 * i;
    while (j<3*i) {
      k = i;
      while (k< j) {
	assert( k-i <= 2*n );
	k++;
      }
      j++;
    }
    i++;
  }
}
