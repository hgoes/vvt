#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int n0 = __undef_int();
  int n1 = __undef_int();
  int i0, i1, j1, j0;
  int k;
  i0 = k = 0;

  while( i0 < n0 ) {
    i0++;
    k++;
  }
  i1 = 0;
  while( i1 < n1 ) {
    i1++;
    k++;
  }
  j1 = 0;
  while( j1 < n1 ) {
    j1++;
    k--;
  }
  j0 = 0;
  while( j0 < n0 ) {
    assert(k > 0);
    j0++;
    k--;
  }
  return 0;
}
