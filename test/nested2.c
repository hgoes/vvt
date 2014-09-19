#include <stdbool.h>

void assert(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int i,k;
  int n = __undef_int();
  int l = __undef_int();

  if(l<=0) return 0;

  k = 1;
  while (k<n){
    i = l;
    while (i<n) {
      assert(1<=k);
      i++;
    }
    k++;
  }

 }
