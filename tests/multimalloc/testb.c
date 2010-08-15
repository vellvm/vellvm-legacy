#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int *ptr;
  int i=0;
  int value = 0;

  ptr=(int **)malloc(sizeof(int*)*100);
  
  while (i<mm) {
    value += *ptr;
    free (ptr);
    ptr=(int **)malloc(sizeof(int*)*mm);
    i++;
  }
  printf("%x\n", value);
}
