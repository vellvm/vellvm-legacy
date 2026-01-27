#include "stdio.h"

struct RT {
  char A;
  int B[10][20];
  char C;
  char D[11];
};
struct ST {
  int X;
  int Y;
  int B[10][20];
  struct RT Z;
};

int main () {
  struct ST s[2];
  s[0].Z.D[9]='a';
  int r = s[0].Z.D[9];
  putchar(r);	
  return 0;
}

