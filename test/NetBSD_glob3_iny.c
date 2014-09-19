#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main ()
{
  int buf_off, pattern_off, bound_off;

  int maxpathlen = __undef_int();
  int error;
  int pathbuf_off;
  int pathend_off;
  int pathlim_off;
  int i;

  if(maxpathlen >0); else return 0;

  buf_off = 0;
  pattern_off = 0;

  bound_off = maxpathlen;

  pathbuf_off = 0;
  pathend_off = 0;
  pathlim_off = maxpathlen;

  error = 0;

  while (__undef_bool()) {
    assert(0 <= pattern_off ); assert( pattern_off <= maxpathlen);
    if (__undef_bool()) continue;
    i = 0;
    while (1) 
      if (i > maxpathlen) return 0;
      else {
	assert(0 <= i);	assert( i <= maxpathlen);
        i++;
        if (__undef_bool()) return 0;
      }

    assert(0 <= pathlim_off ); assert( pathlim_off <= maxpathlen);

    if (i > maxpathlen){
      if (__undef_bool()) {
	if (__undef_bool()) {
	  error = 5;
	  return 0;
	}
	else {
	  assert (0 <= i);assert (i <= maxpathlen + 1);
	  continue;
	}
      }
    }
    if (__undef_bool()) {
      assert (i <= maxpathlen + 1);
      continue;
    }
  }

 return 0;
}
