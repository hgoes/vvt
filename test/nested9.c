#include <stdbool.h>

void assert(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int n = __nondet_int();
  int m = __nondet_int();
  int l = __nondet_int();
  int i,j,k;
  
  if(3*n>m+l) return 0;
  i = 0;
  while (i<n) {
    j = 2 * i;
    while (j<3*i) {
      k = i;
      while (k< j) {
	assert( k-i <= 2*n );
	k++;
      }
      j++;
    }
    i++;
  }
}
