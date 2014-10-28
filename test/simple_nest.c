#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int n = __nondet_int();
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
