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
    int **arr2;
    *arr1 = ptr+i;
    i++;
    arr2 = (int **)malloc(sizeof(int*)*100);
    *arr2 = ptr+i;
    printf("%x\n", *arr2);
    if (i%2) arr1 = arr2;
    if (*ptr < i) break;
  }
  printf("%x\n", *arr1);
}
