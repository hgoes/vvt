#include "benchmarks.h"

int main ()
{
  NONDET_INT(base_sz);
  int i;
  int j;
  int len;
  len = base_sz;

  if(base_sz <= 0) return 0;

  assert( 0 <= base_sz-1 );

  if (len == 0)
    return 0; 
  
  i = 0;
  j = 0;
  while (1) {
    if ( len == 0 ){ 
      return 0;
    } else {
      assert(0<= j); assert(j < base_sz);
      assert(0<= i); assert(i < base_sz );
      if (__nondet_bool()) {
        i++;
        j++;
        return 0;
      }
    }
    i++;
    j++;
    len--;
  }

  return 0;
}

