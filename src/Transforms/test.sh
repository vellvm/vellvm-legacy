#!/bin/bash

DIRS="../Interpreter/testcases/ ../Interpreter/testcases/llvm \
	../Interpreter/testcases/softbound/"
GVN=../_build/Transforms/main.d.byte
BC_DIR=./testcases/
OC_DIR=./testcases/olden-ccured/
# bh: llvm-gcc fails.
# perimeter tsp: GVN is slow.
OC_CASES="bisort em3d health mst power treeadd"
S95_DIR=./testcases/spec95-ccured/
# 129.compress has floats and functions named like "\01__soc95" and "@^0"
# In 099.go 130.li 132.ijpeg there are 'switch'
# ijpeg: undefined reference to `softbound__01___isoc99_sscanf'
# 132.ijpeg is slow for SBpass
#S95_CASES="129.compress 099.go 130.li 132.ijpeg"
S95_CASES=""
OPT_FLAG=

for name in ./testcases/*.ll; do 
  echo -e $name": \c"  
  llvm-as -f $name -o input.bc
  llvm-ld -disable-opt input.bc -o test.exe
  echo -e "before \c"; time ./test.exe
  $GVN input.bc
  $GVN input.bc >& output.ll
  llvm-as -f output.ll
  llvm-ld -disable-opt output.bc -o test.exe
  echo -e "after \c"; time ./test.exe
done;
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

for name in $OC_CASES; do 
  echo -e $name": \c" ; 
  $GVN $OC_DIR$name"/test.bc" >& $name"o.ll"
  llvm-as -f $name"o.ll" -o $name"o.bc"
  llvm-ld -disable-opt $name"o.bc" -o $name"a.exe"
  llvm-ld -disable-opt -gvn $OC_DIR$name"/test.bc" -o $name"b.exe"
  llvm-ld -disable-opt $OC_DIR$name"/test.bc" -o $name"c.exe"
done;
#echo -e "bh b: \c"; time ./bhb.exe;
#echo -e "bh a: \c"; time ./bha.exe;
#echo -e "bh c: \c"; time ./bhc.exe;
echo -e "bisort b: \c"; time ./bisortb.exe 5000000 0;
echo -e "bisort a: \c"; time ./bisorta.exe 5000000 0;
echo -e "bisort c: \c"; time ./bisortc.exe 5000000 0;
echo -e "em3d b: \c"; time ./em3db.exe 30000 300 50;
echo -e "em3d a: \c"; time ./em3da.exe 30000 300 50;
echo -e "em3d c: \c"; time ./em3dc.exe 30000 300 50;
echo -e "health b: \c"; time ./healthb.exe 8 250 1;
echo -e "health a: \c"; time ./healtha.exe 8 250 1;
echo -e "health c: \c"; time ./healthc.exe 8 250 1;
echo -e "mst b: \c"; time ./mstb.exe 4000;
echo -e "mst a: \c"; time ./msta.exe 4000;
echo -e "mst c: \c"; time ./mstc.exe 4000;
#echo -e "perimeter b: \c"; time ./perimeterb.exe 12 2000;
#echo -e "perimeter a: \c"; time ./perimetera.exe 12 2000;
#echo -e "perimeter c: \c"; time ./perimeterc.exe 12 2000;
echo -e "power b: \c"; time ./powerb.exe;
echo -e "power a: \c"; time ./powera.exe;
echo -e "power c: \c"; time ./powerc.exe;
echo -e "treeadd b: \c"; time ./treeaddb.exe 24 10; 
echo -e "treeadd a: \c"; time ./treeadda.exe 24 10; 
echo -e "treeadd c: \c"; time ./treeaddc.exe 24 10; 
#echo -e "tsp b: \c"; time ./tspb.exe 2000000 0;
#echo -e "tsp a: \c"; time ./tspa.exe 2000000 0;
#echo -e "tsp c: \c"; time ./tspc.exe 2000000 0;
for name in $S95_CASES; do 
  echo -e $name": \c" ; 
  $GVN $S95_DIR$name"/src/test.bc" >& $name"o.ll"
  llvm-as -f $name"o.ll" -o $name"o.bc"
  llvm-ld -disable-opt $name"o.bc" -o $name".exe"
done;
#echo -e "099.go: \c"; time ./099.go.exe 100 15;
#echo -e "130.li: \c"; time ./130.li.exe ./testcases/spec95-ccured/130.li/src/ref.lsp;
rm -f bisort* em3d* health* mst* treeadd* 129.compress* test-softbound.bc \
  130.li* 099.go* tsp* bh* power* perimeter*


