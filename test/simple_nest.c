#include "benchmarks.h"

int main() {
  NONDET_INT(n);
  int m;
  int i;
  i = 1;
  m = 10;
  while( i < n ) {
    while( m > 0 ) {
      m--;
      i = 2*i;
    }
  }
  assert (i > 0 );
}
