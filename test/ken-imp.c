#include "benchmarks.h"

int main() {
  NONDET_INT(i);
  NONDET_INT(j);
  int x;
  int y;
  x = i;
  y = j;
  while(x!=0) {
	x--;
	y--;
  }
  if (i==j) assert (y == 0);
}
