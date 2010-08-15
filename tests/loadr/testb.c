#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int *arr1, *ptr;
  int value=0;
  int i=0;

  arr1=(int *)malloc(sizeof(int)*100);
  ptr = arr1;
  
  while (i<mm) {
    value += ptr[i++];
    ptr = arr1+i;
  }
  printf("%d\n", value);
}
