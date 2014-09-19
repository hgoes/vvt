#include <stdbool.h>

void assert(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int j = __undef_int();
  int k = __undef_int();
  int n = __undef_int();
  int m = __undef_int();
  int i,l;

  if(j>n+k) return 0;

  i = 0;
  while (i<n) {
    i = 0;
    while(i<m){
      j=k;
      if(__undef_bool()) {
        l = 0;
	while(l<n) { j++; l++; }
      }
      i++;
    }
    if (k > 5 ) {
      l = 0;
      while(l<m){
	l++;
      }
      l = 0;
      while(l<m){
        j = 0;
	while (j<n+k) { j++; }
	l++;
      }
    } else if ( k > n ) {
      l = 0;
      while(l<n) { j--; l++; }
    }
    i++;
  }
  assert(j<=n+k);
}
