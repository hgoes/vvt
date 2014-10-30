#include "benchmarks.h"

int main() {
  int i,j;
  NONDET_INT(k);
  NONDET_INT(n);

  if( k != n) return 0;

  i = 0;
  while (i<n) {
    j = 2*i;
    while (j<n) {
      if(__nondet_bool()) {
        k = j;
	while (k<n) {
	  assert(k>=2*i);
	  k++;
	}
      }
      else {
	assert( k >= n );
	assert( k <= n );
      }
      j++;
    }
    i++;
  }
}
