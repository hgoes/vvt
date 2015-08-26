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

#define mtx_lock(m) pthread_mutex_lock(&m);assert(pthread_mutex_locked(&m)); //acquire lock and ensure no other thread unlocked it
#define mtx_unlock(m) pthread_mutex_unlock(&m)

pthread_mutex_t MTX = PTHREAD_MUTEX_INITIALIZER;
__thread bool COND = false; //local
bool buf = false;

/*inline static*/ int adb_kbd_receive_packet(){
	mtx_lock(MTX);
	mtx_unlock(MTX);
	cv_broadcast(COND);
	return 0; }
	
/*inline static*/ void akbd_repeat() {
	mtx_lock(MTX);
	mtx_unlock(MTX); }
	
/*inline static*/ void akbd_read_char(int wait) {
	mtx_lock(MTX);
	if (!buf && wait){
		cv_wait(COND,MTX);
		assert(COND);}
	if (!buf) {
		mtx_unlock(MTX);
		return; 	}
	mtx_unlock(MTX); }
	
/*inline static*/ void akbd_clear_state(){
	mtx_lock(MTX);
	buf = false;
	mtx_unlock(MTX); }

void* thr1(void* arg){
  while(1)
  {
    switch(__nondet_int())
    {
    case 0: adb_kbd_receive_packet(); break;
    case 1: akbd_repeat(); break;
    case 2: akbd_read_char(__nondet_int()); break;
    case 3: akbd_clear_state(); break;
    case 4: while(1){
        mtx_lock(MTX);
        buf = !buf;
        mtx_unlock(MTX);
      }
    }
  }

  return 0;
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

