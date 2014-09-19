#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main(){
  int x;
  int y;
  int z;
  int w;
  x = y = z = w = 0;

  while (__undef_bool()){
    if (__undef_bool()) {
      x++; y = y+100;
    } else if  (__undef_bool()) {
      if( x >= 4)
	{ x=x+1; y=y+1;}
    } else if  ( y >10*w)
      if (z>=100*x )
      y = -y;
    w=w+1; 
    z=z+10;
  }
  if ( x >=4 )
    assert(y>2);
}
