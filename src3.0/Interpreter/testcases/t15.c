#include "stdio.h"

void foo(int* s) {
  putchar(s[1]);	
  return;
}

int main () {
  int s[3];
  s[1]='a';
  foo(&s);
  return 0;
}

