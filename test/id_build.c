#include "benchmarks.h"

// from FreePastry source, file Id.java
  /**
   * Constructor, which takes the output of a toStringFull() and converts it back
   * into an Id.  Should not normally be used.
   *
   * @param hex The hexadeciaml representation from the toStringFull()
   */
/*
  public static Id build(char[] chars, int offset, int length) {
    int[] array = new int[nlen];
    
    for (int i=0; i<nlen; i++) 
      for (int j=0; j<8; j++) 
        array[nlen-1-i] = (array[nlen-1-i] << 4) | trans(chars[offset + 8*i + j]);
    
    return build(array);
  }  
*/

int main() {
  int offset, length;
  NONDET_INT(nlen);
  int i, j;

  i = 0;
  while (i<nlen) {
    j = 0;
    while (j<8) {
      assert(0 <= nlen-1-i);
      assert(nlen-1-i < nlen);
      j++;
    }
    i++;
  }
  return 0;
}  
