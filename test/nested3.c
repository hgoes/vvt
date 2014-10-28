#include <stdbool.h>

void assert(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int i,k;
  int n = __nondet_int();
  int l = __nondet_int();

  if (l<=0) return 0;

  k = 1;
  while (k<n){
    i = l;
    while (i<n) {
      assert(1<=i);
      k++;
    }
    k++;
  }

 }
