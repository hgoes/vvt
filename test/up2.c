#include "benchmarks.h"

int main() {
  NONDET_INT(n);
  int i;
  int k;
  int j;
  i = k = 0;
  while( i < n ) {
    i++;
    k++;
  }
  j = 0;
  while( j < n ) {
    assert(k > 0);
    j = j + 2;
    k--;
  }
}
