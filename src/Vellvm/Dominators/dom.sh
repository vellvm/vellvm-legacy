#!/bin/bash

DOM=~/SVN/sol/vol/src3.0/_build/Vellvm/Dominators/main.native
OC_DIR=../../Transforms/testcases/olden-ccured/
OC_CASES="bh bisort em3d health mst perimeter power treeadd tsp"
S95_DIR=../../Transforms/testcases/spec95-ccured/
S95_CASES="129.compress 099.go 130.li 132.ijpeg"
S00_DIR=../../../softbound_test/spec2k/
S00_CASES="164.gzip/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-gzip-prefix.bc
           175.vpr/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-vpr-prefix.bc
           177.mesa/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-mesa-prefix.bc
           179.art/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-art-prefix.bc
           188.ammp/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-ammp-prefix.bc
           183.equake-modified/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-equake-modified-prefix.bc
           256.bzip2/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-bzip2-prefix.bc
           197.parser/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-parser-prefix.bc
           300.twolf/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-twolf-prefix.bc"
# 186.crafty: "InlineAsmVal: Not_Supported"
S06_DIR=../../../softbound_test/spec2k6/
S06_CASES="401.bzip2/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-bzip2-prefix.bc
           429.mcf/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-mcf-prefix.bc
           456.hmmer/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-hmmer-prefix.bc
           462.libquantum/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-libquantum-prefix.bc
           470.lbm/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-lbm-prefix.bc
           433.milc/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-milc-prefix.bc
           458.sjeng/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-sjeng-prefix.bc
           464.h264ref/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-h264-prefix.bc"
# 403.gcc/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-gcc-prefix.bc: slow
WORST_DIR=./worstcases/
WORST_CASES="itworst_large.bc idfsquad_large.bc ibfsquad_large.bc sncaworst_large.bc"

DEBUG="$1"

Compiling ()
{
  echo -e $2": \c" ;

  if [[ $DEBUG != "debug" ]]; then
    echo -e "Push RPO"; time $DOM $1
    echo -e "Pull RPO"; time $DOM -type 1 $1
    echo -e "Slow"; time $DOM -type 2 $1
    echo -e "LLVM"; time $DOM -type 3 $1
  else
    echo -e "Push RPO"; time $DOM -d $1
  fi
}

for name in $OC_CASES; do 
  Compiling $OC_DIR$name"/test.bc" $name
done;

for name in $S95_CASES; do 
  Compiling $S95_DIR$name"/src/test.bc" $name
done;

if [[ $DEBUG != "debug" ]]; then
  for name in $S00_CASES; do 
    Compiling $S00_DIR$name $name
  done;

  for name in $S06_CASES; do 
    Compiling $S06_DIR$name $name
  done
fi

Worstcase() 
{
  echo -e $2": \c" ;
  opt -lowerswitch $1 -f -o lower.bc
  echo -e "Push RPO"; time $DOM lower.bc
  echo -e "Pull RPO"; time $DOM -type 1 lower.bc
  echo -e "LLVM"; time $DOM -type 3 lower.bc
}

if [[ $DEBUG != "debug" ]]; then
  for name in $WORST_CASES; do 
    Worstcase $WORST_DIR$name $name
  done
fi

