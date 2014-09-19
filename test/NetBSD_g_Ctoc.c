#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main ()
{
  int base_sz = __undef_int();
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
      if (__undef_bool()) {
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

