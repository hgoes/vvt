#include "benchmarks.h"

int main () {
  int i, j;
  NONDET_INT(from);
  int to;
  NONDET_INT(k);
  
  if (!(k >= 0)) return 0;
  if (!(k <= 100)) return 0;
  
  if (!(from >= 0)) return 0;
  if (!(from <= k)) return 0;
  
  i = from;
  j = 0;
  
  while (i < k) {
    i++;
    j++;
  }

  assert (j < 101);
}

