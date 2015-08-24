#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int s;

void* thr1(void* arg)
{
  int l = __nondet_int();
  l = 4;
  s = l;
  assert(s == l);

  return 0;
}

int main()
{
  s = __nondet_int();

  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  pthread_yield();
  return 0;
}

