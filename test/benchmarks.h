#include <stdbool.h>

#if defined(HCTIGAR)
void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
long __nondet_long() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

#define NONDET_INT(name) int name = __nondet_int()
#define NONDET_BOOL(name) bool name = __nondet_bool()

#elif defined(CPACHECKER)
void assert(bool c) {
  if(!c) { ERROR:; }
}
int __nondet_int() {
  int x;
  return x;
}
bool __nondet_bool() {
  bool x;
  return x;
}
#elif defined(CTIGAR)
#define __nondet_int() *
#define __nondet_bool() *

#define NONDET_INT(name) int name
#define NONDET_BOOL(name) bool name

#endif
