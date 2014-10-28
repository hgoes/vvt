#include <stdbool.h>

void assert(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

// Henning: Made variables local instead of global

int main()
{
  int i,n,t,k;
  int l,r,u,j;
  int x,y,z;

  n = __nondet_int();
  x=1;
  while (x<n) {
    z=1;
    while (z+x<=n) {
      y=z+x*2;
      if (y>n) y=n+1;
      l = z; r = z+x; u = y;
      i=l; j=r; k=l;
      while (i<r && j<u) { 
	if(__nondet_bool()) {
	  i++;
	} 
	else {
	  j++;
	}
	k++;
      }
      
      assert(k<=n);
      
      while (i<r) {
	i++; 
	k++;
      }
      while (j<u) { 
	j++; k++;
      }
      k = l;
      while (k<u) { 
        k++;
      }
      
      z=z+x*2;
    }
    x=x*2;
  }
}

