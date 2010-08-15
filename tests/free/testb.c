#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int **arr1, *ptr;
  int i=0;

  arr1=(int **)malloc(sizeof(int*)*100);
  ptr = *arr1;
  
  while (i<mm) {
    free (ptr);
    *ptr = 0;
    ptr = *(arr1+i);
    if (*ptr < i) break;
    i++;
  }

  free (arr1);
  printf("%x\n", ptr);
}
