#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int();
bool __nondet_bool();

//This example is adapted from StIng 
int main()
{

  int invalid = __nondet_int();
  int unowned = __nondet_int();
  int nonexclusive = __nondet_int();
  int exclusive = __nondet_int();

	if (! (exclusive==0)) return 0;
	if (! (nonexclusive==0)) return 0;
	if (! (unowned==0)) return 0;
	if (! (invalid>= 1)) return 0;

	while (__nondet_bool())
	{
	  if (__nondet_bool())
		{
			if (! (invalid >= 1)) return 0;
			nonexclusive=nonexclusive+exclusive;
			exclusive=0;
			invalid=invalid-1;
			unowned=unowned+1;
		}
		else
		{
		  if (__nondet_bool())
			{
				if (! (nonexclusive + unowned >=1)) return 0;
				invalid=invalid + unowned + nonexclusive-1;
				exclusive=exclusive+1;
				unowned=0;
				nonexclusive=0;
			}
			else
			{
				if (! (invalid >= 1)) return 0;
				unowned=0;
				nonexclusive=0;
				exclusive=1;
				invalid=invalid+unowned+exclusive+nonexclusive-1;
			}
		}
	}

	assert (exclusive >= 0);
	assert (unowned >= 0);
	assert (invalid + unowned + exclusive + nonexclusive >= 1);
}

// LI computed is 
// exclusive >= 0 && unowned >= 0 &&  nonexclusive >= 0 && invalid + unowned + exclusive >= 1 &&
// 2*invalid + unowned + 2*exclusive >= 1

