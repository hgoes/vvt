#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>

static int last = -1;
static int shared = 0;

static pthread_mutex_t a1,a2;
static pthread_mutex_t *p1,*p2;

template<int val,bool lock> void *thread (void *x) {
  if(lock) {
    pthread_mutex_lock(p1);
  } else {
    pthread_mutex_lock(p2);
  }
  for (int i = 0; i < PROBE_MAX; ++i) {
    last = val;
    shared = val;
  }
  if(lock) {
    pthread_mutex_unlock(p1);
  } else {
    pthread_mutex_unlock(p2);
  }
  return NULL;
}


#define SPAWN(Val,Lock,Rest) {\
    pthread_t t;\
    pthread_create(&t,NULL,thread<Val,Lock>,NULL);	\
    Rest;\
    pthread_join(t,NULL);\
  }

int main() {
  if(__nondet_bool()) {
    p1 = &a1;
    p2 = &a1;
  } else {
    p1 = &a2;
    p2 = &a2;
  }
  SEQUENCE;
  assert(last==shared);
  return 0;
}
