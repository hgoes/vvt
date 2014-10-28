#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main()
{
  int lda = __nondet_int();
  int n = __nondet_int();
  int k,kp1,l,nm1;
  int i, itemp;
  int dx, incx, ix;

  assume( n < lda);
  assume( 0 <= n );
  nm1 = n - 1;
  if (nm1 >=  0) {
    k = 0;
    while (k < nm1) {
      kp1 = k + 1;
      dx = k;
      incx = 1;
      if( n-k < 1 ) { itemp = -1; l = itemp + k; k++; continue; }
      if(n-k ==1 )  { itemp = 0; l = itemp + k; k++; continue; }
      if(incx != 1) {
	ix = 1;
	ix = ix + incx;
	i = 1;
	while (i < n-k) {
	  if(__nondet_bool()) {
	    itemp = i;
	  }
	  ix = ix + incx;
	  i++;
	}
      }
      else {
	itemp = 0;
	i = 1;
	while (i < n-k) {
	  if(__nondet_bool()) {
	    itemp = i;
	  }
	  i++;
	}
      }
      l = itemp +k;
      k++;
    }
  }
   assert(0 <= n);assert(n < lda);
}
