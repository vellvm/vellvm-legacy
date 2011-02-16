#include <stdlib.h>

extern void test(int mm, int *value);

int value;

int main(int argc, char** argv)
{
  int i = atoi(argv[1]);
  test(i, &value);
  return 0;
}

