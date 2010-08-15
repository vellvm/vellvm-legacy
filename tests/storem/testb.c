#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int **arr1, *ptr;
  int i=0;

  arr1 = (int **)malloc(sizeof(int*)*100);
  ptr = (int *)malloc(sizeof(int)*100);
  *arr1 = ptr;
  
  while (i < mm) {
    *arr1 = ptr+i;
    i++;
  }
  printf("%x\n", *arr1);
}
