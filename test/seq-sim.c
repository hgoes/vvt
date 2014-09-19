#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int n = __undef_int();
  int m = __undef_int();
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
