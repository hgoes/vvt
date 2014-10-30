#include "benchmarks.h"

int main ()
{
  int x;
  int y;
  NONDET_INT(z);

  x = y = 0;

  while (__nondet_bool()){
    x = x + 10;
    y = y + 1;
  }

  assert (x > z || y < z + 1);
}
