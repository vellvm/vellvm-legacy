// testing external global variables that don't have initializer.

#include <typeinfo>
#include <cstdio>

int main() {
  printf("%d", typeid(int) == typeid(float));
}
