#include "benchmarks.h"

int main() {
  NONDET_INT(n);
  NONDET_INT(m);
  int i;
  int k;
  i = k = 0;

  while( i < n ) {
    i++;
    k++;
  }
  i = 0;
  while( i < m ) {
    i++;
    k++;
  }
  i = 0;
  while( i < m ) {
    i++;
    k--;
  }
  i = 0;
  while( i < n ) {
    assert(k > 0);
    i++;
    k--;
  }
  return 0;
}
