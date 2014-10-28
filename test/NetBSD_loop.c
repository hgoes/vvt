#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main ()
{
  int maxpathlen = __nondet_int();
  int pathbuf_off;
  int bound_off;
  int glob2_p_off;
  int glob2_pathbuf_off;
  int glob2_pathlim_off;

  if(maxpathlen > 0); else return 0;

  pathbuf_off = 0;
  bound_off = pathbuf_off + (maxpathlen + 1) - 1;

  glob2_pathbuf_off = pathbuf_off;
  glob2_pathlim_off = bound_off;

  glob2_p_off = glob2_pathbuf_off;
  while (glob2_p_off <= glob2_pathlim_off) {
    assert (0 <= glob2_p_off ); assert (glob2_p_off < maxpathlen + 1);
    glob2_p_off++;
  }
  return 0;
}
