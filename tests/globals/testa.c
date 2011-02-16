#include <stdlib.h>

extern void test(int mm);

int main(int argc, char** argv)
{
  int i = atoi(argv[1]);
  test(i);
  return 0;
}

