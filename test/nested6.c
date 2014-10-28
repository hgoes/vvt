#include <stdbool.h>

void assert(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int i,j;
  int k = __nondet_int();
  int n = __nondet_int();

  if( k != n) return 0;

  i = 0;
  while (i<n) {
    j = 2*i;
    while (j<n) {
      if(__nondet_bool()) {
        k = j;
	while (k<n) {
	  assert(k>=2*i);
	  k++;
	}
      }
      else {
	assert( k >= n );
	assert( k <= n );
      }
      j++;
    }
    i++;
  }
}
