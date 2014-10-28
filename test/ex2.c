#include <stdbool.h>

void assert(bool);
int __nondet_int();
bool __nondet_bool();

/* Example where DAGGER is exponentially better thab SLAM, BLAST, SATABS */
int main () {
  int x;

  x=0;

  if (__nondet_bool()) x = x+1;
  else x = x+22; 

  if (__nondet_bool()) x = x+1;
  else x = x+20; 

  if (__nondet_bool()) x = x+1;
  else x = x+18; 

  if (__nondet_bool()) x = x+1;
  else x = x+16; 

  if (__nondet_bool()) x = x+1;
  else x = x+14; 

  if (__nondet_bool()) x = x+1;
  else x = x+12; 
  
  if (__nondet_bool()) x = x+1;
  else x = x+10; 

  if (__nondet_bool()) x = x+1;
  else x = x+8; 

  if (__nondet_bool()) x = x+1;
  else x = x+6; 

  if (__nondet_bool()) x = x+1;
  else x = x+4; 

  if (__nondet_bool()) x = x+1;
  else x = x+2; 

  assert (x <= 132);

  return 0;
}
