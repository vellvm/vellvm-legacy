#!/bin/bash

TV=../../_build/Parser/main.d.byte
NN_DIR=./nano/
ML_DIR=./milli/
ML_CASES="addrof all bug1 bug2 cint2ptr fptr fptr2 fptr3 fptrret free funcargs 
  funcargs2 funcargsm funcargsret funcret funcret2 funcret3 globals int2ptr 
  loadm loadm2 loadr locals multimalloc postalloc ptr2int samechk select simple 
  storem storem2 storer struct undef"
MC_DIR=./microbench/
MC_CASES="array array2 array3 global_array linkedlist linkedlistloop
          reference_test struct_array"
OC_DIR=./olden-ccured/
# bh: llvm opt fails to optimize SoftBound's instrumentation.
# power: TV isn't terminating.
# perimeter tsp have 'switch' instructions that we do not support so far.
# em3d: removed 'free', since Softbound is not sound with 'free'.
OC_CASES="bisort bh em3d health mst treeadd power perimeter tsp"
S95_DIR=./spec95-ccured/
# In 099.go 130.li 132.ijpeg there are 'switch'
# compress and ijpeg: undefined reference to `softbound__01___isoc99_sscanf'
S95_CASES="099.go/src 129.compress/src 130.li/src 132.ijpeg/src"

rm -rf softbound.bc softbound-checks.bc softbound-wrappers.bc
for name in $ML_CASES; do 
  echo -e $name": \c" ; 
  cd $ML_DIR$name ;
  sh ../compile.sh ;
  cd ../../ ; 
done;
for name in $MC_CASES; do 
  echo -e $name": \c" ; 
  cd $MC_DIR$name ; 
  make clean ;
  make ;
  cd ../../ ;
done;
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



