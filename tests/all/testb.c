#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int *arr1;
  int *arr2;
  int **mp;

  mp = (int**)malloc(sizeof(int*)*10);
  arr1=(int *)malloc(sizeof(int)*100);
  arr2=(int *)malloc(sizeof(int)*50);

  int *ptr1;
  int prev=0;

  int i=0;
  int value=0;
  ptr1=arr1;

  while (i<mm) {
    value += *ptr1;
    value += *mp[i];
    *ptr1 = value;
    (*mp[i]) = value;
    if (prev==0) {
      ptr1=arr2+i;
      prev=1;
    } else {
      ptr1=arr1+i;
      prev=0;
    }
    i++;
  }
  printf("%d\n", value);
}
