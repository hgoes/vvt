extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int usecount;
int locked;
int flag1 = 0;
int flag2 = 0;
int release_thr1 = 0;

void* thr2 (void* arg) //dummy_open
{
  while(!release_thr1);

  usecount = usecount + 1;

  if (locked)
    return 0;
  locked = 1;
  flag1 = 1;
  return 0;
}

void dummy_release ()
{
  usecount = usecount - 1;
  locked = 0;
  return;
}

void unregister_chrdev ()
{
  if (usecount != 0)
    {
    // this should fail
    assert (0);
    }
  else
    return;
}

void* thr1 (void* arg)
{
  int count;

  usecount = 0;
  locked = 0;
  
  release_thr1 = 1;
  while(1)
  {
    if(flag1)
      break;
  }

  do
    {
      if (__nondet_bool())
	{
	  count = 1;
	  dummy_release ();
	}
      else
	count = 0;
    }
  while	(count != 0);

  dummy_release ();

  unregister_chrdev ();

  return 0;
}

int main(){
  pthread_t t1,t2;

  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr2, 0);
}

