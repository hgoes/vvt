#include "benchmarks.h"

int main() {
  NONDET_INT(cpoff);
  NONDET_INT(n1);
  NONDET_INT(n2);
  int mc_i;
  NONDET_INT(maxdata);
  assume (maxdata > 0 ); 
  assume (n1 <= maxdata * 2); 
  assume (cpoff <= n1); 
  assume (n2 <= maxdata*2 - n1); 
  mc_i = 0;
  while (mc_i < n2) {
    assert (cpoff+mc_i < maxdata * 2);
    mc_i++;
  }
  return 0;
}
