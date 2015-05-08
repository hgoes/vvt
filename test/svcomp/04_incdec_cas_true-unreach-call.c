//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A nonblocking counter using CAS

#include <pthread.h>
#include <vvt.h>
#include <assert.h>

unsigned value = 0;

/*helpers for the property*/
unsigned inc_flag = 0;
unsigned dec_flag = 0;

void __VERIFIER_atomic_assert1(unsigned inc__v)
{
  assert(dec_flag || value > inc__v);
}

unsigned inc() {
  unsigned inc__v, inc__vn, inc__casret;

  do {
    inc__v = value;
    if(inc__v == 0u-1) {
      return 0; /*increment failed, return min*/
    }
    
    inc__vn = inc__v + 1;

    inc__casret = __sync_bool_compare_and_swap(&value,inc__v,inc__vn);
    inc_flag = inc_flag||inc__casret;
  }
  while (inc__casret==0);
  
  __VERIFIER_atomic_assert1(inc__v);
  
  return inc__vn;
}

void __VERIFIER_atomic_assert2(unsigned dec__v)
{
  assert(inc_flag || value < dec__v);
}

unsigned dec() {
  unsigned dec__v, dec__vn, dec__casret;
  
  do {
    dec__v = value;
    
    if(dec__v == 0) {
      return 0u-1; /*decrement failed, return max*/
    }
    
    dec__vn = dec__v - 1;
    dec__casret = __sync_bool_compare_and_swap(&value,dec__v,dec__vn);
    dec_flag = dec_flag||dec__casret;
  }
  while (dec__casret==0);
  
  __VERIFIER_atomic_assert2(dec__v);
  return dec__vn;
}

void* thr1(void* arg){
  int r = __nondet_int();
  
  if(r){ inc(); }
  else{ dec(); }

  return 0;
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

