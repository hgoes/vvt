#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int n0 = __nondet_int();
  int n1 = __nondet_int();
  int i;
  int k;
  i = k = 0;

  while( i < 20*n0 ) {
    i++;
    k++;
  }
  i = 0;
  while( i < 6*n1+128 ) {
    i++;
    k++;
  }
  i = 0;
  while( i < 6*n1+128 ) {
    i++;
    k--;
  }
  i = 0;
  while( i < 20*n0 ) {
    assert(k > 0);
    i++;
    k--;
  }
  return 0;
}
