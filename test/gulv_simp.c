#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main(){
  int x, y;
  x = 0; y = 0;
  while (__undef_bool()) {
    if (__undef_bool())
      {x = x+1; y = y+100;}
    else if (__undef_bool()){
      if (x >= 4)
	{x = x+1; y = y+1;}
    }
  }
  assert (x < 4 || y > 2);
}
