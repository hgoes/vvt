//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int calculateNext(int s2) {
  int calculateNext_return;
  do {
    calculateNext_return = __nondet_int();
  } while(calculateNext_return == s2 || calculateNext_return == 0);
  return calculateNext_return;
}

int seed;
pthread_mutex_t m;

void __VERIFIER_atomic_CAS(
  volatile int *v,
  int e,
  int u,
  int *r)
{
	if(*v == e)
	{
		*v = u, *r = 1;
	}
	else
	{
		*r = 0;
	}
}

int PseudoRandomUsingAtomic_nextInt(int n) {
  int read, nexts, casret, nextInt_return;
  
  while(1) {
    read = seed;
    pthread_yield();
    nexts = calculateNext(read);
    assert(nexts != read);
    casret = __sync_bool_compare_and_swap(&seed,read,nexts);
    pthread_yield();
    if(casret == 1){
      nextInt_return = nexts % n;
      //assume(nexts < n);
      //nextInt_return = nexts;
      break;
    }
  }
  return nextInt_return;
}

void PseudoRandomUsingAtomic_monitor() {
  while(1) {
    assert(seed != 0);
    pthread_yield();
  }
}

void PseudoRandomUsingAtomic_constructor(int init) {
  seed = init;
  pthread_yield();
}

void PseudoRandomUsingAtomic__threadmain() { 
  int myrand;
  
  myrand = PseudoRandomUsingAtomic_nextInt(10);
  assert(myrand <= 10);
}

#define STATE_UNINITIALIZED	0
#define STATE_INITIALIZED	1

int state = STATE_UNINITIALIZED;

void* thr1(void* arg) {
  pthread_mutex_lock(&m);
  pthread_yield();
  switch(state) {
  case STATE_UNINITIALIZED: 
    PseudoRandomUsingAtomic_constructor(1);
    state = STATE_INITIALIZED;
    pthread_yield();
    pthread_mutex_unlock(&m);
    PseudoRandomUsingAtomic_monitor(); //never returns
    break;
  case STATE_INITIALIZED: 
    pthread_mutex_unlock(&m);
    PseudoRandomUsingAtomic__threadmain();
    break;
  }
  return 0;
}

int main()
{
  pthread_t t1,t2,t3;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  pthread_create(&t3, 0, thr1, 0);
  pthread_yield();
  return 0;
}
