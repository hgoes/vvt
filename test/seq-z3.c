#include "benchmarks.h"

int main() {
  NONDET_INT(n0);
  NONDET_INT(n1);
  int i;
  int k;
  i = k = 0;

  while( i < 20*n0 ) {
    i++;
    k++;
  }
  i = 0;
  while( i < 6*n1+128 ) {
    i++;
    k++;
  }
  i = 0;
  while( i < 6*n1+128 ) {
    i++;
    k--;
  }
  i = 0;
  while( i < 20*n0 ) {
    assert(k > 0);
    i++;
    k--;
  }
  return 0;
}
