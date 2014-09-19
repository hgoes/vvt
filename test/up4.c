#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int n = __undef_int();
  int i;
  int k;
  int j;
  i = k = 0;
  while( i < n ) {
	i++;
	k = k + 2;
  }
  j = 0;
  while( j < n ) {
    assert(k > 0);
	j++;
	k--;
  }
}
