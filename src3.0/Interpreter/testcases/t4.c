#include "stdio.h"

struct ST {
  int X;
  int Y;
};

int main () {
  struct ST s;
  s.X='a';
  int r = s.X;
  putchar(r);	
  return 0;
}

