#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int n = __nondet_int();
  int m = __nondet_int();
  int i;
  int k;
  i = k = 0;

  while( i < n ) {
    i++;
    k++;
  }
  i = 0;
  while( i < m ) {
    i++;
    k++;
  }
  i = 0;
  while( i < m ) {
    i++;
    k--;
  }
  i = 0;
  while( i < n ) {
    assert(k > 0);
    i++;
    k--;
  }
  return 0;
}
