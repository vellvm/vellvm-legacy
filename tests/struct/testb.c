#include <stdlib.h>
#include <stdio.h>

typedef struct _A {
  int b[99];
  int a;
} A;

void test(int mm)
{
  A *ptr;
  A value1[42];
  int i=0;
  int sum=0;

  value1[0].a=42;
  ptr = value1;
  while (i<mm) {
    A value2[42];
    value2[0].a=42;
    i=i+1;
    sum+=ptr[i].b[i];
    sum+=ptr[i].a;
    ptr = value2;
  }
  printf("%d\n", sum);
}
