#include "benchmarks.h"

int main() {
  int x;
  NONDET_INT(n);
  x = 0;
  
  if(n <= 0 ) return 0;
  while( x < n ){
    x++;
  }
  assert( x<=n );
}
