#include <pthread.h>
#include <assert.h>
#include <vvt.h>

/*
to correctly model the cv_broadcast(COND) statement "b1_COND := 1;" must be manually changed to "b1_COND$ := 1;" in the abstract BP
*/

#define cv_wait(c,m){ \
  c = false; \
  pthread_mutex_unlock(&m);			\
  assume(c); \
  pthread_mutex_lock(&m); }

#define cv_broadcast(c) c = true //overapproximates semantics (for threader)

#define mutex_enter(m) pthread_mutex_lock(&m);assert(pthread_mutex_locked(&m)); //acquire lock and ensure no other thread unlocked it
#define mutex_exit(m) pthread_mutex_unlock(&m)

pthread_mutex_t MTX = PTHREAD_MUTEX_INITIALIZER;
__thread bool COND = false;

#define PSWITCH_EVENT_RELEASED 1
#define PENVSYS_EVENT_NORMAL 2
#define POWER_EVENT_RECVDICT 3

#define KASSERT(e) assert(e)
#define is_locked(m) pthread_mutex_locked(&m)

int sysmon_queue_power_event(){
	KASSERT(is_locked(MTX));
  assert(1);
	if (__nondet_int())
		return 0;
	return 1; }

int sysmon_get_power_event(){
	KASSERT(is_locked(MTX));
  assert(1);
	if (__nondet_int())	
		return 0;
	return 1; }

int sysmon_power_daemon_task(){
	if (__nondet_int()) return __nondet_int();
	mutex_enter(MTX);
	switch (__nondet_int()) {
	case PSWITCH_EVENT_RELEASED:
		KASSERT(is_locked(MTX));
		if (__nondet_int()) {
			mutex_exit(MTX);
			goto out;}
		break;
	case PENVSYS_EVENT_NORMAL:
		KASSERT(is_locked(MTX));
		if (__nondet_int()) {
			mutex_exit(MTX);
			goto out;}
		break;
	default:
		mutex_exit(MTX);
		goto out;}
	sysmon_queue_power_event();
	if (__nondet_int()) {
		mutex_exit(MTX);
		goto out;} 
	else {
		cv_broadcast(COND);
		mutex_exit(MTX);}
	out:
  assert(1);
	return __nondet_int(); }

void sysmonopen_power(){
	mutex_enter(MTX);
	if (__nondet_int())
		KASSERT(is_locked(MTX));
	mutex_exit(MTX);
  assert(1);
}

void sysmonclose_power(){
	mutex_enter(MTX);
	KASSERT(is_locked(MTX));
	mutex_exit(MTX);
  assert(1);
}

void sysmonread_power(){
	if (__nondet_int()){
		mutex_enter(MTX);
		for (;;) {
			if (sysmon_get_power_event()) {
				break;}
			if (__nondet_int()) {
				break;}
			cv_wait(COND,MTX);
      assert(COND); }
		mutex_exit(MTX); }
  assert(1);
}

void sysmonpoll_power(){
	if(__nondet_int()){
		mutex_enter(MTX);
		mutex_exit(MTX); }
  assert(1);
}

void filt_sysmon_power_rdetach(){
	mutex_enter(MTX);
	mutex_exit(MTX);
  assert(1);
}

void filt_sysmon_power_read(){
	mutex_enter(MTX);
	mutex_exit(MTX);
  assert(1);
}

void sysmonkqfilter_power(){
	mutex_enter(MTX);
	mutex_exit(MTX);
  assert(1);
}

void sysmonioctl_power(){
	switch (__nondet_int()) {
	case POWER_EVENT_RECVDICT:
		mutex_enter(MTX);
		if (__nondet_int()) {
			mutex_exit(MTX);
			break;}
		mutex_exit(MTX);
		mutex_enter(MTX);
		mutex_exit(MTX);
		break; }
  assert(1);
}

void* thr1(void* arg){
  while(1)
    switch(__nondet_int()){
    case 0: sysmon_power_daemon_task(); break;
    case 1: sysmonopen_power(); break;
    case 2: sysmonclose_power(); break;
    case 3: sysmonread_power(); break;
    case 4: sysmonpoll_power(); break;
    case 5: filt_sysmon_power_rdetach(); break;
    case 6: filt_sysmon_power_read(); break;
    case 7: sysmonkqfilter_power(); break;
    case 8: sysmonioctl_power(); break; }}

int main(){
  pthread_t t1,t2;

  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

