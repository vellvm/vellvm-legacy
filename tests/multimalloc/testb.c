#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int *ptr;
  int i=0;
  int value = 0;

  ptr=(int **)malloc(sizeof(int*)*100);
  *(ptr+mm) = 42;
  
  while (i<mm) {
    value += *ptr;
    ptr=(int **)malloc(sizeof(int*)*mm);
    *(ptr+i) = 42;
    i++;
  }
  printf("%x\n", value);
}
