#include <stdbool.h>

void assert(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main()
{
  int p;
  int i;
  int leader_len = __undef_int();
  int bufsize = __undef_int();
  int bufsize_0;
  int ielen = __undef_int();

  if(leader_len >0); else return 0;
  if(bufsize >0); else return 0;
  if(ielen >0); else return 0;

  if (bufsize < leader_len)
    return 0;

  p = 0;
  bufsize_0 = bufsize;
  bufsize = bufsize - leader_len;
  p = p + leader_len;

  if (bufsize < 2*ielen)
    return 0;

  i = 0;
  while (i < ielen && bufsize > 2) {
    assert(0<=p);
    assert(p+1<bufsize_0);
    p = p+2;
    i++;
  }

}

