#include <stdbool.h>

void assert(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int l = __undef_int();
  int n = __undef_int();
  int i,k;

  if (l<=0) return 0;
  k = 1;
  while (k<n){
    i = l;
    while (i<n){  
      assert(1<=i);
      i++;
    }
    if(__undef_bool())
      l = l + 1;
    k++;
  }
 }
