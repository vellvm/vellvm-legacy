#!/bin/bash

DIRS="../Interpreter/testcases/ ../Interpreter/testcases/llvm \
	../Interpreter/testcases/softbound/"
M2R=../_build/Transforms/main.native
BC_DIR=./testcases/
OC_DIR=./testcases/olden-ccured/
OC_CASES="bh bisort em3d health mst perimeter power treeadd tsp"
S95_DIR=./testcases/spec95-ccured/
S95_CASES="129.compress 099.go 130.li 132.ijpeg"
S00_DIR=../../softbound_test/spec2k/
S00_CASES="177.mesa/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-mesa.bc
           164.gzip/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-gzip.bc
           175.vpr/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-vpr.bc
           179.art/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-art.bc
           188.ammp/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-ammp.bc
           183.equake-modified/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-equake-modified.bc
           256.bzip2/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-bzip2.bc
           197.parser/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-parser.bc
           300.twolf/src/obj/zjzzjz/llvm-mem2reg-test/spec2k-twolf.bc
          "
S06_DIR=../../softbound_test/spec2k6/
S06_CASES="401.bzip2/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-bzip2.bc
           429.mcf/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-mcf.bc
           456.hmmer/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-hmmer.bc
           462.libquantum/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-libquantum.bc
           470.lbm/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-lbm.bc
           433.milc/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-milc.bc
           458.sjeng/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-sjeng.bc
           464.h264ref/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-h264.bc"
# 403.gcc/src/obj/zjzzjz/llvm-mem2reg-test/spec2k6-gcc.bc
LD_FLAG="-disable-opt"

#opt -mem2reg -debug-pass=Arguments -disable-output bho.bc
#Pass Arguments: -targetlibinfo -targetdata -domtree -mem2reg -preverify -verify

#-targetdata pass causes errors
PRE_OPT_FLAG="-disable-opt -targetlibinfo"
M2R_OPT_FLAG="-disable-opt -targetlibinfo -domtree -mem2reg"

DEBUG="$1"

Compiling ()
{
  opt="-opt"
  if [[ $DEBUG != "opt" ]]; then
    opt=""
  fi  

  echo -e $2": \c" ;

  echo -e "Pre"; time opt -f $PRE_OPT_FLAG $1 -o $2"o.bc"

  echo -e "Coq only insert phis"; time $M2R -mem2reg -maximal -no-stld-elim $opt $2"o.bc" >& $2"f.ll"
  llvm-as -f $2"f.ll" -o /dev/null

  echo -e "Coq max"; time $M2R -mem2reg -maximal $opt $2"o.bc" >& $2"e.ll"
  llvm-as -f $2"e.ll" -o /dev/null

  echo -e "Coq M2R"; time $M2R -mem2reg $opt $2"o.bc" >& $2"a.ll"
  llvm-as -f $2"a.ll" -o /dev/null

  echo -e "Coq M2R pruned"; time $M2R -mem2reg -prune $opt $2"o.bc" >& $2"c.ll"
  llvm-as -f $2"c.ll" -o /dev/null

  echo -e "LLVM M2R"; time opt -f $M2R_OPT_FLAG $1 -o $2"d.bc"
  llvm-dis -f $2"d.bc" -o $2"d.ll" 
}

for name in $S95_CASES; do 
  Compiling $S95_DIR$name"/src/test.bc" $name
done

Compiling0 ()
{
  opt="-opt"
  if [[ $DEBUG != "opt" ]]; then
    opt=""
  fi  

  echo -e $2": \c" ;

  echo -e "Coq only insert phis"; time $M2R -mem2reg -maximal -no-stld-elim $opt $1 >& $1"f.ll"
  llvm-as -f $1"f.ll" -o /dev/null

  echo -e "Coq max"; time $M2R -mem2reg -maximal $opt $1 >& $1"e.ll"
  llvm-as -f $1"e.ll" -o /dev/null

  echo -e "Coq M2R"; time $M2R -mem2reg $opt $1 >& $1"a.ll"
  llvm-as -f $1"a.ll" -o /dev/null

  echo -e "Coq M2R pruned"; time $M2R -mem2reg -prune $opt $1 >& $1"c.ll"
  llvm-as -f $1"c.ll" -o /dev/null
 
  echo -e "LLVM M2R"; time opt -f $M2R_OPT_FLAG $1 -o $1"d.bc"
  llvm-dis -f $1"d.bc" -o $1"d.ll" 
}

for name in $S00_CASES; do 
  Compiling0 $S00_DIR$name $name
done

for name in $S06_CASES; do 
  Compiling0 $S06_DIR$name $name
done

if [[ $DEBUG != "debug" ]]; then
rm -f bisort* em3d* health* mst* treeadd* 129.compress* test-softbound.bc \
  130.li* 099.go* tsp* bh* power* perimeter* 132.ijpeg* opt.bc input.* output.* \
  test.exe test.exe.bc aa.db
fi


