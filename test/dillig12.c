#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

int main()
{
  int flag = __undef_int();
  int t;
  int s;
  int a;
  int b;
  int x,y;
  t = s = a = b = 0;
  while(__undef_bool()){
    a++;
    b++;
    s=s+a;
    t=t+b;
    if(flag){
      t=t+a;
    }
    t = t;
  } 
  x = 1;
  if(flag){
    x = t-2*s+2;
  }
  y = 0;
  while(y<=x){
    if(__undef_bool()) 
       y++;
    else 
       y=y+2;
    y = y;
  }
  assert(y < 5);
}

