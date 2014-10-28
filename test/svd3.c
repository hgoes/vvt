#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main()
{
  int n = __nondet_int();
  int i,j,k;
  int l = __nondet_int();
  
  if (l<=1) return 0;

  i = n;
  while (i>=1) { // Accumulation of right-hand transwhilemations. 
    if (i < n) {
      if (__nondet_bool()) {
        j = l;
	while (j<=n) { // Double division to avoid possible underflow. 
	  assert(1<=j);
	  j++;
	}
	j = l;
	while (j<=n) {
	  k = l;
	  while (k<=n) { 
	    k++;
	  }
	  j++;
	}
      }
      j = l;
      while (j<=n) { 
        j++;
      }
    }
    
    l=i;
    i--;
  }
}
