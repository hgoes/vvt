#include "benchmarks.h"

int main() {
  NONDET_INT(n);
  int v;
  int i;
  int k;
  int j;
  i = k = 0;
  while( i < n ) {
	i++;
	v = __nondet_int();
	if( v > 0 )
	  k = k + v;
	else
	  k++;
  }
  j = 0;
  while( j < n ) {
	assert(k > 0);
	j++;
	k--;
  }
}
