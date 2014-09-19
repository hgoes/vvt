#include <stdbool.h>

void assert(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int n = __undef_int();
  int i,j,k;

  i = 0;
  while (i<n) {
    j = i;
    while (j<n) {
      k = j;
      while (k<n) {
	if(__undef_bool()){
	  assert(k>=j);
	  assert(j>=i);
	}
	k++;
      }
      j++;
    }
    i++;
  }
}
