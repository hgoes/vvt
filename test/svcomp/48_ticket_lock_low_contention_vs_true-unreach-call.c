#include <pthread.h>
#include <assert.h>
#include <vvt.h>

volatile unsigned s = 0; //served
volatile unsigned t = 0; //next ticket


#define spin_lock(l,t,s)\
{\
  l = __sync_fetch_and_add(&t,1); \
  while (l != s) \
    ; /* spin */ \
}

#define spin_unlock(s)\
{\
  s++;\
}

unsigned c = 0;
void* thr1(void* arg)
{
  unsigned l;
  spin_lock(l,t,s);
  c = 1; assert(c == 1); c = 0;
  spin_unlock(s);

  return 0;
}

int main()
{
  pthread_t t1,t2;

  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  thr1(0);

  return 0;
}

