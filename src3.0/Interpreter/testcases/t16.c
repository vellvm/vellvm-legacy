#include "stdio.h"

struct ST {
  int X;
};

int* foo(struct ST* s) {
  putchar(s[1].X);	
  return &(s[1].X);
}

int main () {
  struct ST s[2];
  s[1].X='a';
  int r=*foo(&s);
  putchar(r);
  return 0;
}

