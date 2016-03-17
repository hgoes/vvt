//original file: EBStack.java
//amino-cbbs\trunk\amino\java\src\main\java\org\amino\ds\lockfree
//push only

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

#define MEMSIZE (2*320+1) //0 for "NULL"
int memory[MEMSIZE];
#define INDIR(cell,idx) memory[cell+idx]

int next_alloc_idx = 1;
pthread_mutex_t m;
int top;

int index_malloc(){
  int curr_alloc_idx = -1;

  pthread_mutex_lock(&m);
  if(next_alloc_idx+2-1 > MEMSIZE){
    pthread_mutex_unlock(&m);
    curr_alloc_idx = 0;
  }else{
    curr_alloc_idx = next_alloc_idx;
    next_alloc_idx += 2;
    pthread_mutex_unlock(&m);
  }
  
  return curr_alloc_idx;
}

void EBStack_init(){
	top = 0;
}

int isEmpty() {
  if(top == 0)
    return 1;
  else
    return 0;
}

int push(int d) {
  int oldTop = -1, newTop = -1, casret = -1;

  newTop = index_malloc();
  if(newTop == 0){
    return 0;
  }else{
    INDIR(newTop,0) = d;
    while (1) {
      oldTop = top;
      INDIR(newTop,1) = oldTop;
      if(__sync_bool_compare_and_swap(&top,oldTop,newTop)){
	return 1;
      }
      
    }
  }
}

void __VERIFIER_atomic_assert(int r)
{
  __atomic_begin();
  assert(!(!r || !isEmpty()));
  __atomic_end();
}

void push_loop(){
  int r = -1;
  int arg = __nondet_int();
  while(1){
    r = push(arg);
    __VERIFIER_atomic_assert(r);
  }
}

pthread_mutex_t m2;
int state = 0;
void* thr1(void* arg)
{
  pthread_mutex_lock(&m2);
  switch(state)
    {
    case 0: 
      EBStack_init();
      state = 1;
      //fall-through
    case 1: 
      pthread_mutex_unlock(&m2);
      
      push_loop();
      break;
    }
  
  return 0;
}

int main()
{
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

