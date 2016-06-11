#include "benchmarks.h"

int main()
{
  NONDET_INT(a);

  if (a <= 11) return 0;

  int i, Fnew, Fold, temp;

  Fnew = 1;  Fold = 0, temp = 0;
  for ( i = 2; i <= a; i++ )
    {
      temp = Fnew;
      Fnew = Fnew + Fold;
      Fold = temp;
    }

  assert(Fnew > a*a);

  return 0;
}
