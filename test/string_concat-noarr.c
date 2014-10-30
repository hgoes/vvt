#include "benchmarks.h"

int main() {
  int i, j;
  i = 0;
  while(__nondet_bool()){
    i++;
  }
  if(i >= 100) return 0;
  j = 0;
  while(__nondet_bool()){
    i++;
    j++;
  }
  if(j >= 100) return 0;
  assert( i < 200 );
  return 0;
}
