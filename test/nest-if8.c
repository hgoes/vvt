#include <stdbool.h>

void assert(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int m = __undef_int();
  int n = __undef_int();
  int i,j,k;
  if(m+1 >= n ) return 0;
  i = 0;
  while (i<n) {
    j = i;
    while (j<m) {
      if (__undef_bool()){
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
