#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int **arr1, *ptr;
  int i=0;

  ptr = (int *)malloc(sizeof(int)*100);
  *arr1 = ptr;
  
  while (i < mm) {
    *arr1 = ptr+i;
    i++;
    printf("%d, %d, %d\n", i, mm, *arr1);
  }
  printf("%x\n", *arr1);
}
