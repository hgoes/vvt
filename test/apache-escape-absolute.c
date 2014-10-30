#include "benchmarks.h"

int main ()
{
  NONDET_INT(scheme);
  NONDET_INT(urilen);
  NONDET_INT(tokenlen);
  int cp,c;

  if(urilen>0); else return 0;
  if(tokenlen>0); else return 0;
  if(scheme >= 0 );else return 0;
  if (scheme == 0
      || urilen-1 < scheme) {
    return 0;
  }

  cp = scheme;
  
  assert(cp-1 < urilen);
  assert(0 <= cp-1);

  if (__nondet_bool()) {
    assert(cp < urilen);
    assert(0 <= cp);
    while ( cp != urilen-1) {
      if(__nondet_bool()) break;
      assert(cp < urilen);
      assert(0 <= cp);
      ++cp;
    }
    assert(cp < urilen);
    assert( 0 <= cp );
    if (cp == urilen-1) return 0;
    assert(cp+1 < urilen);
    assert( 0 <= cp+1 );
    if (cp+1 == urilen-1) return 0;
    ++cp;

    scheme = cp;

    if (__nondet_bool()) {
      c = 0;
      assert(cp < urilen);
      assert(0<=cp);
      while ( cp != urilen-1
             && c < tokenlen - 1) {
	assert(cp < urilen);
	assert(0<=cp);
        if (__nondet_bool()) {
          ++c;
	  assert(c < tokenlen);
	  assert(0<=c);
	  assert(cp < urilen); //Interesting assert
	  assert(0<=cp);
        }
        ++cp;
      }
      return 0;
    }
  }
}
