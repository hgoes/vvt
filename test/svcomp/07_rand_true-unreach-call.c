//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

pthread_mutex_t m;

int seed; 

int PseudoRandomUsingAtomic_nextInt(int n) {
  int read, nexts, nextInt_return;

  pthread_mutex_lock(&m);
  read = seed;
  do {
    nexts = __nondet_int();
  } while(nexts == read || nexts == 0);
  
  assert(nexts != read); 
  seed = nexts;
  pthread_mutex_unlock(&m);
  return nexts % n;
}

void PseudoRandomUsingAtomic_monitor(){
  while(1) {
    assert(seed != 0);
  }
}

void PseudoRandomUsingAtomic_constructor(int init){
  seed = init;
}

void PseudoRandomUsingAtomic__threadmain(){ 
  int myrand;

  myrand = PseudoRandomUsingAtomic_nextInt(10);
  assert(myrand <= 10);
}

#define STATE_UNINITIALIZED	0
#define STATE_INITIALIZED	1

int state = STATE_UNINITIALIZED;

void* thr1(void* arg)
{
  pthread_mutex_lock(&m);
  switch(state)	{
  case STATE_UNINITIALIZED: 
    PseudoRandomUsingAtomic_constructor(1);
    state = STATE_INITIALIZED;
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
  return 0;
}

