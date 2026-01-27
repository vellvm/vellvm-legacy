#include "stdio.h"

struct RT {
  char A;
  double B[10][20];
  char C;
};
struct ST {
  int X;
  int Y;
  struct RT Z;
};

double *foo(struct ST *s) {
  return &s[1].Z.B[5][13];
}

int main () {
  struct ST s[2];
  double b = 97 - 100.0 + 3.0;
  s[1].Z.B[5][13]= b + 'a';
  int r = *foo(s);
  putchar(r);	
  return 0;
}

