#include "stdio.h"

struct RT {
  char A;
  int B[10][20];
  char C;
};
struct ST {
  int X;
  int Y;
  int B[10][20];
  struct RT Z;
};

int main () {
  struct ST s;
  s.Z.B[3][5]='a';
  int r = s.Z.B[3][5];
  putchar(r);	
  return 0;
}

