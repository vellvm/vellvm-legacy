#!/bin/bash

OC_DIR=./olden-ccured/
# bh: llvm opt fails to optimize SoftBound's instrumentation.
# power: TV isn't terminating.
# perimeter tsp have 'switch' instructions that we do not support so far.
# em3d: removed 'free', since Softbound is not sound with 'free'.
OC_CASES="bisort bh em3d health mst treeadd power perimeter tsp"
S95_DIR=./spec95-ccured/
# In 099.go 130.li 132.ijpeg there are 'switch'
# compress and ijpeg: undefined reference to `softbound__01___isoc99_sscanf'
S95_CASES="099.go/src 129.compress/src 132.ijpeg/src"

for name in $OC_CASES; do 
  echo -e $name": \c" ; 
  cd $OC_DIR$name ; 
  make clean ;
  make ;
  cd ../../ ;
done;
for name in $S95_CASES; do 
  echo -e $name": \c" ; 
  cd $S95_DIR$name ;
  make clean ;
  make ;
  cd ../../../ ;
done



