#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main ()
{
  int maxpathlen = __nondet_int();

  int buf_off;
  int pattern_off;
  int bound_off;

  int glob3_pathbuf_off;
  int glob3_pathend_off;
  int glob3_pathlim_off;
  int glob3_pattern_off;
  int glob3_dc;

  if(maxpathlen > 0); else return 0;

  buf_off = 0;
  pattern_off = 0;

  bound_off = 0 + (maxpathlen + 1) - 1;

  glob3_pathbuf_off = buf_off;
  glob3_pathend_off = buf_off;
  glob3_pathlim_off = bound_off;
  glob3_pattern_off = pattern_off;

  glob3_dc = 0;
  while (1)
    if (glob3_pathend_off + glob3_dc >= glob3_pathlim_off) break;
    else {
      glob3_dc++;
      assert(0 <= glob3_dc);assert (glob3_dc < maxpathlen + 1);
      if (__nondet_bool()) return 0;
    }

 return 0;
}
