#include "benchmarks.h"

int main() {
  NONDET_INT(n);
  int k;
  int i;
  int j;
  i = k = 0;
  while( i < n ) {
	i++;
	k++;
  }
  j = n;
  while( j > 0 ) {
	assert(k > 0);
	j--;
	k--;
  }
}
