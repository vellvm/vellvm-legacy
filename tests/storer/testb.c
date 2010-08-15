#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int *arr1, *ptr;
  int i=0;

  arr1=(int *)malloc(sizeof(int)*100);
  ptr = arr1;
  
  while (i<mm) {
    ptr[i++] = 0;
    ptr = arr1+i;
  }

  printf("%x\n", ptr);
}
