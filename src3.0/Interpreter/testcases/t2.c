#include "stdio.h"

//failed because we dont support constant expressions

int i;
int j=0;

int main () {
  printf("testcast2=%d,%d,%d\n", 1, i, j);	
  return 0;
}

