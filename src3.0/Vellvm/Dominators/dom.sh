#!/bin/bash

DOM=../../_build/Vellvm/Dominators/main.native
OC_DIR=../../Transforms/testcases/olden-ccured/
OC_CASES="bh bisort em3d health mst perimeter power treeadd tsp"
S95_DIR=../../Transforms/testcases/spec95-ccured/
S95_CASES="129.compress 099.go 130.li 132.ijpeg"

Compiling ()
{
  echo -e $2": \c" ;

  echo -e "Fast Dom"; time $DOM $1
  echo -e "Slow Dom"; time $DOM -slow-dom $1
  echo -e "LLVM Dom"; time $DOM -llvm-dom $1
}

for name in $OC_CASES; do 
  Compiling $OC_DIR$name"/test.bc" $name
done;

for name in $S95_CASES; do 
  Compiling $S95_DIR$name"/src/test.bc" $name
done;

