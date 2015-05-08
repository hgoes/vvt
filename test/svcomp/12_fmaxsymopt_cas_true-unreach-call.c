#include <pthread.h>
#include <assert.h>
#include <vvt.h>

#define WORKPERTHREAD 2
#define THREADSMAX 3
int max = 0x80000000;

int storage[WORKPERTHREAD*THREADSMAX];

void findMax(int offset) {
  int i;
  int e;
  int my_max = 0x80000000;
  int c; 
  int cret;

  for(i = offset; i < offset+WORKPERTHREAD; i++) {
    e = storage[i];
    if(e > my_max) {
      my_max = e;
    }
    assert(e <= my_max);
  }

  while(1) {
    c = max;
    if(my_max > c){
      cret = __sync_bool_compare_and_swap(&max,c,my_max);
      if(cret){
	break;
      }
    } else{
      break;
    }
  }
  assert(my_max <= max);
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
  return 0;
}

