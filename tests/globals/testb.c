#include <stdlib.h>
#include <stdio.h>

int value=0;

void test(int mm)
{
  int *ptr;
  int i=0;

  ptr = &value;
  
  while (i<mm) {
    value += ptr[i++];
    ptr = ptr+i;
  }
  printf("%d\n", value);
}
