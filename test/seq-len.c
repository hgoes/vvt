#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int n0 = __undef_bool();
  int n1 = __undef_bool();
  int n2 = __undef_bool();
  int i;
  int k;
  i = k = 0;

  while( i < n0 ) {
    i++;
    k++;
  }
  i = 0;
  while( i < n1 ) {
    i++;
    k++;
  }

  i = 0;
  while( i < n2 ) {
    i++;
    k++;
  }

  i = 0;
  while( i < n2 ) {
    i++;
    k--;
  }

  i = 0;
  while( i < n1 ) {
    i++;
    k--;
  }
  i = 0;
  while( i < n0 ) {
    assert(k > 0);
    i++;
    k--;
  }
  return 0;
}
