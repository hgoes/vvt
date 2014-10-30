#include "benchmarks.h"

int main() {
  int i,j,k;
  NONDET_INT(n);

  i = 0;
  while (i<n) {
    j = i;
    while (j<n) {
      k = j;
      while (k<n) {
	assert(k>=i);
	k++;
      }
      j++;
    }
    i++;
  }
}
