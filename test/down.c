#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

int main() {
  int n = __undef_int();
  int k;
  int i;
  int j;
  i = k = 0;
  while( i < n ) {
	i++;
	k++;
  }
  j = n;
  while( j > 0 ) {
	assert(k > 0);
	j--;
	k--;
  }
}
