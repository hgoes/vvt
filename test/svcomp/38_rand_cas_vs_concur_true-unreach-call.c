//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int nC(int s2){ 
  int nC_return;
  do {
    nC_return = __nondet_int();
  } while(nC_return == s2 || nC_return == 0);
  return nC_return;
}

int seed = 1;

#define min(x,y) ((y>=x)?(x):(y))

#define NUM 10

int PseudoRandomUsingAtomic_nex() {
  int nex, nexts, casret, nex_return;
  while(1) {
    nex = seed;
    nexts = nC(nex);
    casret = __sync_bool_compare_and_swap(&seed,nex,nexts);
    if(casret == 1){
      nex_return = min(nexts,NUM);
      break;
    }
  }
  return nex_return;
}

void* thr1(void* arg){
  assert(PseudoRandomUsingAtomic_nex() <= NUM);

  return 0;
}

int main()
{
  pthread_t t1,t2;

  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

