extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

/*
to correctly model the cv_broadcast(COND) statement "b1_COND := 1;" must be manually changed to "b1_COND$ := 1;" in the abstract BP
*/

#define cv_wait(c,m){ \
  c = false; \
  pthread_mutex_unlock(&m); \
  assume(c); \
  pthread_mutex_lock(&m); }

#define cv_broadcast(c) c = true //overapproximates semantics (for threader)

#define mutex_enter(m) pthread_mutex_lock(&m);assert(pthread_mutex_locked(&m)); //acquire lock and ensure no other thread unlocked it
#define mutex_exit(m) pthread_mutex_unlock(&m)

pthread_mutex_t MTX = PTHREAD_MUTEX_INITIALIZER;
__thread bool COND = false;

#define boolean_t bool
#define ASSERT(e) assert(e)
#define MUTEX_HELD(e) (pthread_mutex_locked(&e))
#define B_TRUE true
#define B_FALSE false

bool LOADED = false;
bool LOADING = false;

void space_map_contains(){
	ASSERT(MUTEX_HELD(MTX));
  assert(1);
}

void space_map_walk(){
	ASSERT(MUTEX_HELD(MTX));
  assert(1);
}

void space_map_load_wait(){
	ASSERT(MUTEX_HELD(MTX));
	while (LOADING) {
		ASSERT(!LOADED);
		cv_wait(COND, MTX);
		ASSERT(COND); }
      	mutex_enter(MTX);
  assert(1);
}

void space_map_load(){
	ASSERT(MUTEX_HELD(MTX));
	ASSERT(!LOADED);
	ASSERT(!LOADING);
	LOADING = B_TRUE;
	mutex_exit(MTX);
	mutex_enter(MTX);
	for (;__nondet_int();) {
		mutex_exit(MTX);
		mutex_enter(MTX);
		if (__nondet_int())
			break; }
	if (__nondet_int())
		LOADED = B_TRUE;
	LOADING = B_FALSE;
	cv_broadcast(COND);
  assert(1);
}

void space_map_unload(){
	ASSERT(MUTEX_HELD(MTX));
	LOADED = B_FALSE;
	ASSERT(MUTEX_HELD(MTX));
  assert(1);
}

int space_map_alloc(){
	if (__nondet_int())
		ASSERT(MUTEX_HELD(MTX));
  assert(1);
	return __nondet_int();
}

void space_map_sync(){
	ASSERT(MUTEX_HELD(MTX));
	if (__nondet_int())
		return;
	while (__nondet_int()) {
		while (__nondet_int()) {
			if (__nondet_int()) {
				mutex_exit(MTX);
				mutex_enter(MTX); }}}
	if (__nondet_int()) {
		mutex_exit(MTX);
		mutex_enter(MTX); }
  assert(1);
}

void space_map_ref_generate_map(){
	ASSERT(MUTEX_HELD(MTX));
  assert(1);
}

void* thr1(void* arg){
	mutex_enter(MTX);
	switch(__nondet_int()){
		case 1: space_map_contains(); break;
		case 2: space_map_walk(); break;
		case 3: if(LOADING)
				space_map_load_wait();
			else if(!LOADED)
				space_map_load();
			else
				space_map_unload(); break;
			break;
		case 6: space_map_alloc(); break;
		case 7: space_map_sync(); break;
		case 8: space_map_ref_generate_map(); break; }
	ASSERT(MUTEX_HELD(MTX));
	mutex_exit(MTX);
  assert(1);

  return 0;
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  pthread_yield();
  return 0;
}

