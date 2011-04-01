#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int **arr1, *ptr1, *ptr2;
  int i=0;

  arr1=(int **)malloc(sizeof(int*)*100);
  
  while (i<mm) {
    int **arr2;
    arr2=(int **)malloc(sizeof(int*)*100);
    while (i<mm+1) {
      // Without the loop, LLVM considers values in arr2 as undefined
      // Although it is still undefined, the loop stops LLVM analysis.
      ptr2 = *(arr2+i+1);
      i++;
    }
    ptr1 = *(arr1+i);
    i++;
    if (i%2) arr1 = arr2;
    if (*ptr1 < i) break;
  }
  printf("%x\n", ptr1);
  printf("%x\n", ptr2);
}
