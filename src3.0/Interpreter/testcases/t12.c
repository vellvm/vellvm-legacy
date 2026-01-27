#include "stdio.h"

struct RT {
  char A;
  char B[10][20];
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
  s[0].Z.B[9][4]='a';
  int r = s[0].Z.B[9][4];
  putchar(r);	
  return 0;
}

