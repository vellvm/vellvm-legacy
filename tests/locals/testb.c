#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int value=mm;
  int *ptr;
  int i=0;

  ptr = &value;
  
  while (i<mm) {
    value += ptr[i++];
    ptr = ptr+i;
  }
  printf("%d\n", value);
}
