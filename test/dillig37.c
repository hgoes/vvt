#include "benchmarks.h"

/*
 * Taken from "Counterexample Driven Refinement for Abstract Interpretation" (TACAS'06) by Gulavani
 */

int main() {
  int x;
  int m;
  NONDET_INT(n);
  x = m = 0;
  while(x<=n-1) {
    if(__nondet_bool()) {
      m = x;
    }
    x= x+1;
  }
  if(x < n)
    return 0;
  assert(n<1 || m > -1);
  assert(n<1 || m < n);
}
