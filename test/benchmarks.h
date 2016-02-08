#include <stdbool.h>

#if defined(VVT)
void assert(bool);
void assume(bool);
int __nondet_int();
long __nondet_long();
bool __nondet_bool();

#define NONDET_INT(name) int name = __nondet_int()
#define NONDET_BOOL(name) bool name = __nondet_bool()

#elif defined(CPACHECKER)
void assert(bool c) {
  if(c) {
    return;
  } else {
  ERROR:
    goto ERROR;
  }
}
void assume(bool c) {
  if(c) {
    return;
  } else {
  LOOP:
    goto LOOP;
  }
}
int __nondet_int() {
  int x;
  return x;
}
bool __nondet_bool() {
  bool x;
  return x;
}
#define NONDET_INT(name) int name
#define NONDET_BOOL(name) bool name

#elif defined(CTIGAR)
#define __nondet_int() *
#define __nondet_bool() *

#define NONDET_INT(name) int name
#define NONDET_BOOL(name) bool name

#endif
