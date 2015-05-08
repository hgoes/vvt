//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A nonblocking counter using CAS

#include <pthread.h>
#include <assert.h>

unsigned value;

void* thr1(void* arg) {
  unsigned v,vn;
  bool casret;
  do {
    v = value;
    if(v == 0u-1) {
      return 0;
    }

    vn = v + 1;
    casret = __sync_bool_compare_and_swap(&value,v,vn);
  }
  while (!casret);
  assert(value > v);
  
  return 0;
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

