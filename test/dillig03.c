#include "benchmarks.h"

int main()
{
  int k;
  int w;
  int z;
  k = w = 1;
  while(__nondet_bool()) {
    z = __nondet_int();
    if(z>5) w++;
    k=k+w;
  }
  assert(k > 0);
}
