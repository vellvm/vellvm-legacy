#!/bin/bash

DIRS="./testcases/ ../Interpreter/testcases/ ../Interpreter/testcases/llvm \
	../Interpreter/testcases/softbound/"
GVN=../_build/Transforms/main.d.byte

for dir in $DIRS; do
  for name in $dir/*.ll; do 
    echo -e $name": \c"  
    llvm-as -f $name -o input.bc
    llvm-ld -disable-opt input.bc -o test.exe
    echo -e "before \c"; time ./test.exe
    $GVN input.bc >& output.ll
    llvm-as -f output.ll
    llvm-ld -disable-opt output.bc -o test.exe
    echo -e "after \c"; time ./test.exe
  done;
done;
rm -f input.* output.* test.exe test.exe.bc



