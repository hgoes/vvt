#include <stdbool.h>

void assert(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int i = __nondet_int();
  int k;
  int n = __nondet_int();
  int l;

  k = 1;
  while (k<n){
    i = 1;
    while (i<n) {
      i++;
    }
    k++;
  }
  assert(1<=k);
 }
