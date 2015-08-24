//Ticket lock with proportional backoff
//Algorithms for Scalable Synchronization on Shared-Memory Multiprocessors
//ACM TOCS
//February 1991

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

volatile unsigned s = 0; //served
volatile unsigned t = 0; //next ticket

#define pause(e)

#define spin_lock(l,t,s)\
{\
  __sync_fetch_and_add(&l,1); \
  while(1) { \
    pause(l - s); \
    /* consume this many units of time */ \
    /* on most machines, subtraction works correctly despite overflow */ \
    if(s == l) \
      break; \
  }\
}

#define spin_unlock(s)\
{\
  s++;\
}

unsigned c = 0;

void* thr1(void* arg) {
  while(1){
    unsigned l;
    spin_lock(l,t,s);
    c = 1; assert(c == 1); c = 0;
    spin_unlock(s);
  }

  return 0;
}

int main()
{
  pthread_t t1,t2;

  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  pthread_yield();
  thr1(0);

  return 0;
}

