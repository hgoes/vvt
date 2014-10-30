#include "benchmarks.h"

int main ()
{
  int in;
  NONDET_INT(inlen);
  NONDET_INT(bufferlen);
  int buf;
  int buflim;

  if(bufferlen <= 1) return 0;
  if(inlen <= 0) return 0;
  if(bufferlen >= inlen) return 0;
  buf = 0;
  in = 0;
  buflim = bufferlen - 2;
  while (__nondet_bool())
  {
    if (buf == buflim)
      break;
    assert(0<=buf);
    assert(buf<bufferlen); 
    buf++;
    in++;
    assert(0<=in);//3
    assert(in<inlen);//4
  }

    assert(0<=buf);//5
    assert(buf<bufferlen);//5
  buf++;

  assert(0<=buf);//6
  assert(buf<bufferlen);

  buf++;

  return 0;
}
