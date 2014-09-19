#include <stdbool.h>

void assert(bool);
int __undef_int();
bool __undef_bool();

/* Example where DAGGER is exponentially better thab SLAM, BLAST, SATABS */
int main () {
  int x;

  x=0;

  if (__undef_bool()) x = x+1;
  else x = x+22; 

  if (__undef_bool()) x = x+1;
  else x = x+20; 

  if (__undef_bool()) x = x+1;
  else x = x+18; 

  if (__undef_bool()) x = x+1;
  else x = x+16; 

  if (__undef_bool()) x = x+1;
  else x = x+14; 

  if (__undef_bool()) x = x+1;
  else x = x+12; 
  
  if (__undef_bool()) x = x+1;
  else x = x+10; 

  if (__undef_bool()) x = x+1;
  else x = x+8; 

  if (__undef_bool()) x = x+1;
  else x = x+6; 

  if (__undef_bool()) x = x+1;
  else x = x+4; 

  if (__undef_bool()) x = x+1;
  else x = x+2; 

  assert (x <= 132);

  return 0;
}
