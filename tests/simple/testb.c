#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int* i=(int*)malloc(sizeof(int)*10);
  i[mm] = 42;
  printf("%d\n", *i);
}
