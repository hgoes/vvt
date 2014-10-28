#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main()
{
  int m = __nondet_int();
  int n = __nondet_int();
  int flag,i,its,j,jj,k,l,nm;
  i=1;
  while (i<=n) {
    l=i+1;
    
    assert(1<=i);assert(i<=n);
    if (i <= m) {
      k=i; while (k<=m) {
	assert(1<=k);assert(k<=m);
	assert(1<=i);assert(i<=n);
	k++;
      }
      if (__nondet_int()) {
	k=i; while (k<=m) {
	  assert(1<=k);assert(k<=m);
	  assert(1<=i);assert(i<=n);
	  k++;
	}
	assert(1<=i);assert(i<=m);
	assert(1<=i);assert(i<=n);
	assert(1<=i);assert(i<=m);
	assert(1<=i);assert(i<=n);
	j=l; while (j<=n) {
	  k=i; while (k<=m) {
	    assert(1<=k);assert(k<=m);
	    assert(1<=i);assert(i<=n);
	    assert(1<=j);assert(j<=n);
	    k++;
	  }
	  k=i; while (k<=m) {
	    assert(1<=k);assert(k<=m);
	    assert(1<=i);assert(i<=n);
	    assert(1<=j);assert(j<=n);
	    k++;
	  }
	  j++;
	}
	k=i; while (k<=m) { 
	  assert(1<=k);assert(k<=m);
	  assert(1<=i);assert(i<=n);
	  k++;
	}
      }
      }
    if (i <= m && i != n) {
      k=l; while (k<=n) {
	assert(1<=i);assert(i<=m);
	assert(1<=k);assert(k<=n);
	k++;
      }
      if (__nondet_bool()) {
	k=l; while (k<=n) {
	 assert(1<=i);assert(i<=m);
	 assert(1<=k);assert(k<=n);
	 assert(1<=i);assert(i<=m);
	 assert(1<=k);assert(k<=n);
	 k++;
	}
	assert(1<=i);assert(i<=m);
	assert(1<=l);assert(l<=n);
	assert(1<=i);assert(i<=m);
	assert(1<=l);assert(l<=n);
	k=l; while (k<=n) {
	 assert(1<=i);assert(i<=m);
	 assert(1<=k);assert(k<=n);
	 k++;
	}
	j=l; while (j<=m) {
	  k=l; while (k<=n) { 
	    assert(1<=j);assert(j<=m);
	    assert(1<=i);assert(i<=m);
	    assert(1<=k);assert(k<=n);
	    k++;
	  }
	  k=l; while (k<=n) { 
	    assert(1<=j);assert(j<=m);
	    assert(1<=k);assert(k<=n);
	    k++;
	  }
	  j++;
	}
	k=l; while (k<=n) { 
	  assert(1<=i);assert(i<=m);
	  assert(1<=k);assert(k<=n);
	  k++;
	}
      }
    }
    i++;
  }

  i=n; while (i>=1) { // Accumulation of right-hand transformations. 
    l = i+1;
    if (i < n) {
      if (__nondet_bool()) {
	j=l; while (j<=n) { // Double division to avoid possible underflow. 
	  assert(1<=j);assert(j<=n);
	  assert(1<=i);assert(i<=n);
	  assert(1<=l);assert(l<=n);
	  j++;
	}
	j=l; while (j<=n) {
	  k=l; while (k<=n) { 
	    assert(1<=k);assert(k<=n);
	    assert(1<=j);assert(j<=n);
	    k++;
	  }
	  k=l; while (k<=n) { 
	    assert(1<=k);assert(k<=n);
	    assert(1<=j);assert(j<=n);
	    assert(1<=i);assert(i<=n);
	    k++;
	  }
	  j++;
	}
      }
      j=l; while (j<=n) { 
        assert(1<=j);assert(j<=n);
	assert(1<=i);assert(i<=n);
	j++;
      }
    }

    assert(1<=i);assert(i<=n);
    assert(1<=i);assert(i<=n);
    i--;
  }
}
