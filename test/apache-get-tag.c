#include <stdbool.h>

void assert(bool);
int __nondet_int();
bool __nondet_bool();

int main()
{
  int tagbuf_len = __nondet_int();
  int t;

  if(tagbuf_len >= 1); else return 0;

  t = 0;

  --tagbuf_len;
  while (1) {
    if (t == tagbuf_len) {
      assert(0 <= t);
      assert(t <= tagbuf_len);
      return 0;
    }
    if (__nondet_bool()) {
      break;
    }
     assert(0 <= t);
     assert(t <= tagbuf_len);
    t++;
  }

   assert(0 <= t);
   assert(t <= tagbuf_len);
  t++;
  while (1) {
    if (t == tagbuf_len) { /* Suppose t == tagbuf_len - 1 */
      assert(0 <= t);
      assert(t <= tagbuf_len);
      return 0;
    }

    if (__nondet_bool()) {
      if (__nondet_bool()) {
	assert(0 <= t);
	assert(t <= tagbuf_len);
        t++;
        if (t == tagbuf_len) {
	  assert(0 <= t);
	  assert(t <= tagbuf_len);
          return 0;
        }
      }
    }
    else if (__nondet_bool()) {
      break;
    }

    assert(0 <= t);
    assert(t <= tagbuf_len);
    t++;
  }
  assert(0 <= t);
  assert(t <= tagbuf_len);
}
