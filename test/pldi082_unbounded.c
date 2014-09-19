#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main(){

  int x;
  int y;
  int n = __undef_int();
  x = y = 0;

  if(n < 0)
    return 1;

  while (1){
     if (x <= n)
        y++;
     else if(x >= n+1)
       y--;
     else return 1;

     if ( y < 0)
       break;
     x++;
  }

  if(n >= 0)
    if(y == -1)
      if (x >= 2 * n + 3)
        assert(0);
}

