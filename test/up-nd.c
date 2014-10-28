#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int n = __nondet_int();
  int v;
  int i;
  int k;
  int j;
  i = k = 0;
  while( i < n ) {
	i++;
	v = __nondet_int();
	if( v > 0 )
	  k = k + v;
	else
	  k++;
  }
  j = 0;
  while( j < n ) {
	assert(k > 0);
	j++;
	k--;
  }
}
