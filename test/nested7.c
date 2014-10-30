#include "benchmarks.h"

int main() {
  NONDET_INT(j);
  NONDET_INT(k);
  NONDET_INT(n);
  NONDET_INT(m);
  int i,l;

  if(j>n+k) return 0;

  i = 0;
  while (i<n) {
    i = 0;
    while(i<m){
      j=k;
      if(__nondet_bool()) {
        l = 0;
	while(l<n) { j++; l++; }
      }
      i++;
    }
    if (k > 5 ) {
      l = 0;
      while(l<m){
	l++;
      }
      l = 0;
      while(l<m){
        j = 0;
	while (j<n+k) { j++; }
	l++;
      }
    } else if ( k > n ) {
      l = 0;
      while(l<n) { j--; l++; }
    }
    i++;
  }
  assert(j<=n+k);
}
