#include "benchmarks.h"

int main() {
  NONDET_INT(x);
  NONDET_INT(y);

  if (0 > x) return 0;  
  if (x > 2) return 0;
  if (0 > y) return 0;  
  if (y > 2) return 0;
  while(__nondet_bool()) {
	x=x+2;
	y=y+2;
  }
  if( y >= 0 ) 
    if( y <= 0 ) 
      if( 4 <= x ) 
	assert( x < 4 );
}
