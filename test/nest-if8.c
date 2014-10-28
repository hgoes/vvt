#include <stdbool.h>

void assert(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int m = __nondet_int();
  int n = __nondet_int();
  int i,j,k;
  if(m+1 >= n ) return 0;
  i = 0;
  while (i<n) {
    j = i;
    while (j<m) {
      if (__nondet_bool()){
	assert( j >= 0 );
	j++;
	k = 0;
	while(k < j) {
	  assert( k < n );
	  k++;
	}
	
      }
      else { 
	assert( n+j+5>i );
	j= j + 2;
      }
    }

    i = i + 4;
  }
}
