#include "benchmarks.h"

/*
 * IC3 motivating example
 */ 

int main()
{
 int x; int y;
 int t1, t2;
 x = y = 1;
 while(__nondet_bool()) {
   t1 = x;
   t2 = y;
   x = t1+ t2;
   y = t1 + t2;
 }
 assert(y >= 1);
}
