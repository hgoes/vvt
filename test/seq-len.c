#include "benchmarks.h"

int main() {
  NONDET_INT(n0);
  NONDET_INT(n1);
  NONDET_INT(n2);
  int i;
  int k;
  i = k = 0;

  while( i < n0 ) {
    i++;
    k++;
  }
  i = 0;
  while( i < n1 ) {
    i++;
    k++;
  }

  i = 0;
  while( i < n2 ) {
    i++;
    k++;
  }

  i = 0;
  while( i < n2 ) {
    i++;
    k--;
  }

  i = 0;
  while( i < n1 ) {
    i++;
    k--;
  }
  i = 0;
  while( i < n0 ) {
    assert(k > 0);
    i++;
    k--;
  }
  return 0;
}
