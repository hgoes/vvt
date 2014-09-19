#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int n = __undef_int();
  int m;
  int i;
  i = 1;
  m = 10;
  while( i < n ) {
    while( m > 0 ) {
      m--;
      i = 2*i;
    }
  }
  assert (i > 0 );
}
