#include "benchmarks.h"

int main() {
  int x,m;
  NONDET_INT(n);

  x = 0;
  m = 0;
  while( x < n ) {
    if(__nondet_bool())
      m = x;
    x++;
  }
  if( n > 0 )
    {
      assert( 0<=m);
      assert(m<n);
    }
}
