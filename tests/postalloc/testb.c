#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int *arr;
  int value=0;
  int i=0;

  arr = 0;
  
  while (i<mm) {
    value += arr[i++];
    arr=(int *)malloc(sizeof(int)*100);
  }
  printf("%d\n", value);
}
