#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>

static const int EMPTY = 0;
static const int FULL = -1;

//static const int PROBE_MAX = 6;

//static int table[] = { 59, 1, 50, 20, 0, 0, 0, 0, 0, 0 };

static int table[] = TABLE_INIT;

static const int N = sizeof(table)/sizeof(int);

int find_or_insert (int val) {
  int h = val % N;
  
  int index = h;
  for (int i = 0; i < PROBE_MAX; ++i) {
#ifdef DEBUG
    printf ("checking for %d loc %d value found %d\n", val, index, table[index]);
#endif
    if (table[index] == EMPTY) {
      int success = __sync_bool_compare_and_swap(&table[index], EMPTY, val);
      if (success) {
	return 0;
      }
    }
    if (table[index] == val) {
      return 1;
    }
    
    index++;
    index = index < N ? index : 0; // mod N
  }
  return FULL;
}

template<int val,typename Check> void* process(void* arg) {
  int res = find_or_insert(val);
  assert(Check::check(res));
  return NULL;
}

struct IsFound {
  static bool check(int val) { return val==1; }
};

struct IsInserted {
  static bool check(int val) { return val==0; }
};

struct IsFull {
  static bool check(int val) { return val==FULL; }
};

template<typename L,typename R> struct IsOr {
  static bool check(int val) { return L::check(val) || R::check(val); }
};

template<typename T> struct argument_type;
template<typename T, typename U> struct argument_type<T(U)> { typedef U type; };

#define SPAWN(Val,Ret,Rest) {\
    pthread_t t;\
    pthread_create(&t,NULL,process<Val,argument_type<void(Ret)>::type>,NULL);\
    Rest;\
    pthread_join(t,NULL);\
  }

int main() {
  //SPAWN(30,IsInsert,SPAWN(40,IsInsert,0));
  SEQUENCE;
  return 0;
}
