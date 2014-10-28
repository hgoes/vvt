#include <stdbool.h>

void assert(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int i,j,k;
  int n = __nondet_int();

  i = 0;
  while (i<n) {
    j = i;
    while (j<n) {
      k = j;
      while (k<n) {
	assert(k>=i);
	k++;
      }
      j++;
    }
    i++;
  }
}
