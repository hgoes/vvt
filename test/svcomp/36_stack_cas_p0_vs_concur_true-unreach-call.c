//original file: EBStack.java
//amino-cbbs\trunk\amino\java\src\main\java\org\amino\ds\lockfree
//push only

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

#define MEMSIZE (2*32+1) //0 for "NULL"
int memory[MEMSIZE];
#define INDIR(cell,idx) memory[cell+idx]

int next_alloc_idx = 1;

int top = 0;

void __VERIFIER_atomic_index_malloc(int *curr_alloc_idx)
{
  if(next_alloc_idx+2-1 > MEMSIZE) *curr_alloc_idx = 0;
  else *curr_alloc_idx = next_alloc_idx, next_alloc_idx += 2;
}

#define isEmpty() (top == 0)

#define exit(r) assume(0);

void push(int d) {
  int oldTop, newTop;
  __VERIFIER_atomic_index_malloc(&newTop);
  if(newTop == 0)
    exit(-1);
  INDIR(newTop,0) = d;
  while (1) {
    oldTop = top;
    INDIR(newTop,1) = oldTop;
    if(__sync_bool_compare_and_swap(&top,oldTop,newTop))
      return;
  }
}

void* thr1(void* arg){
  while(1){push(10); assert(top != 0);}

  return 0;
}

int main()
{
  pthread_t t;

  pthread_create(&t, 0, thr1, 0);
  pthread_create(&t, 0, thr1, 0);
  pthread_create(&t, 0, thr1, 0);
}

