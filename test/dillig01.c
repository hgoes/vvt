#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

/*
 * IC3 motivating example
 */ 

int main()
{
 int x; int y;
 int t1, t2;
 x = y = 1;
 while(__undef_bool()) {
   t1 = x;
   t2 = y;
   x = t1+ t2;
   y = t1 + t2;
 }
 assert(y >= 1);
}
