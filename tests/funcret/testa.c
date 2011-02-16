#include <stdlib.h>

extern int* test(int mm);

int main(int argc, char** argv)
{
  int i = atoi(argv[1]);
  int *ptr=NULL;

  ptr = test(i);
  
  return (ptr!=NULL);
}

