#!/bin/bash

LYNX=./lynx
OC_DIR=./olden-ccured/
OC_CASES="bh bisort em3d health mst perimeter power treeadd tsp"
S95_DIR=./spec95-ccured/
S95_CASES="129.compress 099.go 132.ijpeg"

Compiling ()
{
  echo -e $2": \c" ;
  echo -e "OPT"; time opt -f $1 -o $2".bc"
  echo -e "LD"; time llvm-ld -native -lm $1 -o $2".exe"
}

Running ()
{
  echo -e "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n"
  echo -e $1" nat: \c"; eval "time ./"$1".exe "$2 " >& "$1".nat"
  echo -e "\n"
  echo -e $1" lynx: \c"; eval "timeout 60 "$LYNX" ./"$1".bc "$2" >& "$1".lynx"
  echo -e "\n"
  echo -e $1" Diff nat lynx"; eval "diff "$1".nat "$1".lynx | tee "$1".diff-nat-lynx"
}

#echo -e $1" lli: \c"; eval "timeout 100 lli -force-interpreter=true ./"$1".bc "$2" >& "$1".lli"
#echo -e "\n"
#echo -e $1" Diff nat lli"; eval "diff "$1".nat "$1".lli | tee "$1".diff-nat-lli"
#echo -e "\n"
#echo -e $1" Diff nat lynx"; eval "diff "$1".lynx "$1".lli | tee "$1".diff-nat-lynx"

for name in $OC_CASES; do 
  Compiling $OC_DIR$name"/test.bc" $name
done;
Running "bh" "< olden-ccured/bh/fast_input";
Running "bisort" "10 1";
Running "em3d" "";
Running "health" "3 30 3";
Running "mst" "32";
Running "perimeter" "4 4";
Running "power" "";
Running "treeadd" "10 10"; 
Running "tsp" "100 1";

for name in $S95_CASES; do 
  Compiling $S95_DIR$name"/src/test.bc" $name
done;
Running "099.go" "1 9"
#Running "130.li" "../../Transforms/testcases/spec95-ccured/130.li/src/ref.lsp";
Running "129.compress" "< ../../Transforms/testcases/spec95-ccured/129.compress/src/fast_input.data";
Running "132.ijpeg" "-image_file ../../Transforms/testcases/spec95-ccured/132.ijpeg/data/ref/input/vigo.ppm -GO"

rm -f bisort* em3d* health* mst* treeadd* 129.compress* test-softbound.bc \
  130.li* 099.go* tsp* bh* power* perimeter* 132.ijpeg* *.lli *.lynx *.nat *.diff-*

# bh
#   nbody=2^n: # of objects under simulation, less --> faster
#   tstop: the total sim time, less --> faster
# bisort
#   n: length of array, less --> faster, but must be > 1
#   flag: silent 0, verbose otherwise
# em3d
#   n: n_nodes, less --> faster
#   d: d_nodes, less --> faster
#   iter: # of iteration, less --> faster
# health
#   level: less --> faster
#   time: less --> faster
#   seed
# mst
#   size = 2^n: less --> faster
# perimeter
#   level: less --> faster
#   iteration: less --> faster
# power
#   The arguments are fixed in power.h
# treeadd
#   size: less --> faster
#   iteration: less --> faster
# tsp
#   size: less --> faster
#   flag: 1 print; 0 silent
