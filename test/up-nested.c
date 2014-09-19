#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int n = __undef_int();
  int j = __undef_int();
  int i,k;
  i = 0;
  k = 0;
  assume ( j<=n );
  while ( j <= n ) {
    assume( i >= 0);
    j++;
  }
  assert( i>= 0);
}
