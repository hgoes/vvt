#include <vvt.h>
#include <assert.h>
#include <pthread.h>

#define VARS(n) int* p##n;\
  int x##n = 0;\
  void* worker##n(void* arg) {\
    int limit = (int)arg;\
    for(int i = 0; i<limit; ++i) {\
      ++(*p##n);\
    }\
    return 0;\
  }

#if N>0
VARS(1)
#if N>1
VARS(2)
#if N>2
VARS(3)
#endif
#endif
#endif

void distribute(void) {
#if N==1
  p1 = &x1;
#elif N==2
  if(__nondet_bool()) {
    p1 = &x1;
    p2 = &x2;
  } else {
    p1 = &x2;
    p2 = &x1;
  }
#elif N==3
  switch(__nondet_int()) {
  case 0:
    p1 = &x1;
    p2 = &x2;
    p3 = &x3;
    break;
  case 1:
    p1 = &x1;
    p2 = &x3;
    p3 = &x2;
    break;
  case 2:
    p1 = &x2;
    p2 = &x1;
    p3 = &x3;
    break;
  case 3:
    p1 = &x2;
    p2 = &x3;
    p3 = &x1;
    break;
  case 4:
    p1 = &x3;
    p2 = &x1;
    p3 = &x2;
    break;
  case 5:
  default:
    p1 = &x3;
    p2 = &x2;
    p3 = &x1;
    break;
  }
#else
#error N not defined or out of range (must be 1 <= N < 3).
#endif
}

#define START(n,l)				\
  pthread_t t##n;				\
  pthread_create(&t##n,0,worker##n,l);
#define JOIN(n,l)				\
  pthread_join(t##n,0);				\
  assert(*p##n==l);

void run(int limit) {
  #if N>0
  START(1,limit);
  #if N>1
  START(2,limit);
  #if N>2
  START(3,limit);
  JOIN(3,limit);
  #endif
  JOIN(2,limit);
  #endif
  JOIN(1,limit);
  #endif
}

int main() {
  int limit = __nondet_int();
  assume(limit>0);
  distribute();
  run(limit);
  return 0;
}
