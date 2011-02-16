#include <stdlib.h>
#include <stdio.h>

int* test(int mm)
{
  int *ptr;
  int i=0;
  int value;

  ptr = &value;
  
  while (i<mm) {
    value += ptr[i++];
    ptr = ptr+i;
  }
  printf("%d\n", value);

  return (int*)(malloc(sizeof(int)));
}
