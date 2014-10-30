#include "benchmarks.h"

int main() {
  int x;
  NONDET_INT(y);

  x = -50;
  while( x < 0 ) {
	x = x+y;
	y++;
  }
  assert(y>0);
}
