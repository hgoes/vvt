//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;

#define min(x,y) ((y>=x)?(x):(y))

int calculateNext(int s2){ 
	int cnex;
	do cnex = __nondet_int();
	while(cnex == s2 || cnex == 0);
	return cnex;
}

int seed = 1; 

#define NUM 10

int PseudoRandomUsingAtomic_nextInt() {
	int read, nexts, nextInt_return;

	assert(seed != 0);
	pthread_mutex_lock(&m);
	read = seed;
	nexts = calculateNext(read);
	seed = nexts;
	pthread_mutex_unlock(&m);
	nextInt_return = min(nexts,NUM);
	return nextInt_return;
}

void* thr1(void* arg){
  PseudoRandomUsingAtomic_nextInt();

  return 0;
}

int main()
{
  pthread_t t1,t2;
  pthread_create(&t1,0,thr1,0);
  pthread_create(&t2,0,thr1,0);
  return 0;
}

