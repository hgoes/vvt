#include <pthread.h>
#include <assert.h>
#include <vvt.h>

#define WORKPERTHREAD 2
#define THREADSMAX 3
int max = 0x80000000;

int storage[WORKPERTHREAD*THREADSMAX];

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

void findMax(int offset) {
  int i;
  int e;
  int c; 
  int cret;
  
  for(i = offset; i < offset+WORKPERTHREAD; i++) {
    e = storage[i];
    pthread_yield();
    
    while(1) {
      c = max;
      pthread_yield();
      if(e > c){
	cret = __sync_bool_compare_and_swap(&max,c,e);
	pthread_yield();
	if(cret){
	  break;
	}
      } else{
	break;
      }
    }
    
    assert(e <= max);
  }
}

void* thr1(void* arg) {
  int offset;

  assume(offset % WORKPERTHREAD == 0 && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
  //assume(offset < WORKPERTHREAD && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);

  findMax(offset);

  return 0;
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  pthread_yield();
  return 0;
}

