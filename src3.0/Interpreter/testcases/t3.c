#include "stdio.h"

struct RT {
  char A;
  int B[10][20];
  char C;
};
struct ST {
  int X;
  int Y;
  struct RT Z;
};

int *foo(struct ST *s) {
  return &s[1].Z.B[5][13];
}

int main () {
  struct ST s[2];
  s[1].Z.B[5][13]='a';
  int r = *foo(s);
  putchar(r);	
  return 0;
}

