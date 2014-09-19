#include <stdbool.h>

void assert(bool);
int __undef_int();
bool __undef_bool();

int main()
{
  int tagbuf_len = __undef_int();
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
    if (__undef_bool()) {
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

    if (__undef_bool()) {
      if (__undef_bool()) {
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
    else if (__undef_bool()) {
      break;
    }

    assert(0 <= t);
    assert(t <= tagbuf_len);
    t++;
  }
  assert(0 <= t);
  assert(t <= tagbuf_len);
}
