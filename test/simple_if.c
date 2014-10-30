#include "benchmarks.h"

int main() {
  NONDET_INT(n);
  NONDET_INT(m);
  int i;
  i = 1;

  while( i < n ) {
    if( m > 0 ) {
      i = 2*i;
    } else {
      i = 3*i;
    }
    
  }
  assert (i > 0 );
}
