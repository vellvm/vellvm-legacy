#!/bin/bash

DIRS="../Interpreter/testcases/ ../Interpreter/testcases/llvm \
	../Interpreter/testcases/softbound/"
M2R=../_build/Transforms/main.native
BC_DIR=./testcases/
OC_DIR=./testcases/olden-ccured/
OC_CASES="bh bisort em3d health mst perimeter power treeadd tsp"
S95_DIR=./testcases/spec95-ccured/
S95_CASES="129.compress 099.go 130.li 132.ijpeg"

# We need to rerun
# llvm-as < /dev/null | opt -O1 -disable-output -debug-pass=Arguments, or
# opt -mem2reg -debug-pass=Arguments -disable-output test.bc

#PRE_OPT_FLAG="-disable-opt -raiseallocs -simplifycfg -domtree -domfrontier 
#  -mem2reg 
#  -globalopt -globaldce -ipconstprop -deadargelim -instcombine -simplifycfg 
#  -basiccg -prune-eh -functionattrs -inline -simplify-libcalls -instcombine 
#  -jump-threading -simplifycfg -domtree -domfrontier -scalarrepl -instcombine 
#  -break-crit-edges -condprop -tailcallelim -simplifycfg -lowerswitch 
#  -reassociate -domtree 
#  -loops -loopsimplify -domfrontier -lcssa -loop-rotate -licm -lcssa 
#  -loop-unswitch -instcombine -scalar-evolution -lcssa -iv-users -indvars 
#  -loop-deletion -lcssa -loop-unroll -instcombine -lowerswitch -memdep"

#SUF_OPT_FLAG="-disable-opt -memdep 
#  -memcpyopt -sccp -instcombine -break-crit-edges -condprop -domtree -memdep -dse 
#  -adce -simplifycfg -strip-dead-prototypes -print-used-types -deadtypeelim 
#  -constmerge -preverify -domtree -verify"

#PRE_LD_FLAG="-disable-opt -internalize -ipsccp -globalopt -constmerge 
#  -deadargelim -instcombine -basiccg -inline -prune-eh -globalopt -globaldce 
#  -basiccg -argpromotion -instcombine -jump-threading -domtree -domfrontier 
#  -scalarrepl -basiccg -functionattrs -globalsmodref-aa -domtree -loops 
#  -loopsimplify -domfrontier -licm -memdep"

#SUF_LD_FLAG="-disable-opt -memdep -memcpyopt -dse -instcombine -jump-threading 
#  -domtree -domfrontier -mem2reg -simplifycfg -globaldce -instcombine -simplifycfg 
#  -adce -globaldce -preverify -domtree -verify"

#OPT_FLAG="-disable-opt -raiseallocs -simplifycfg -domtree -domfrontier -mem2reg 
#  -globalopt -globaldce -ipconstprop -deadargelim -instcombine -simplifycfg 
#  -basiccg -prune-eh -functionattrs -inline -simplify-libcalls -instcombine 
#  -jump-threading -simplifycfg -domtree -domfrontier -scalarrepl -instcombine 
#  -break-crit-edges -condprop -tailcallelim -simplifycfg -reassociate -domtree 
#  -loops -loopsimplify -domfrontier -lcssa -loop-rotate -licm -lcssa 
#  -loop-unswitch -instcombine -scalar-evolution -lcssa -iv-users -indvars 
#  -loop-deletion -lcssa -loop-unroll -instcombine -memdep 
#  -gvn
#  -memdep 
#  -memcpyopt -sccp -instcombine -break-crit-edges -condprop -domtree -memdep -dse 
#  -adce -simplifycfg -strip-dead-prototypes -print-used-types -deadtypeelim 
#  -constmerge -preverify -domtree -verify"

#NOGVN_OPT_FLAG="-disable-opt -raiseallocs -simplifycfg -domtree -domfrontier 
#  -mem2reg 
#  -globalopt -globaldce -ipconstprop -deadargelim -instcombine -simplifycfg 
#  -basiccg -prune-eh -functionattrs -inline -simplify-libcalls -instcombine 
#  -jump-threading -simplifycfg -domtree -domfrontier -scalarrepl -instcombine 
#  -break-crit-edges -condprop -tailcallelim -simplifycfg -reassociate -domtree 
#  -loops -loopsimplify -domfrontier -lcssa -loop-rotate -licm -lcssa 
#  -loop-unswitch -instcombine -scalar-evolution -lcssa -iv-users -indvars 
#  -loop-deletion -lcssa -loop-unroll -instcombine -memdep 
#  -memdep 
#  -memcpyopt -sccp -instcombine -break-crit-edges -condprop -domtree -memdep -dse 
#  -adce -simplifycfg -strip-dead-prototypes -print-used-types -deadtypeelim 
#  -constmerge -preverify -domtree -verify"

#LD_FLAG="-disable-opt -internalize -ipsccp -globalopt -constmerge 
#  -deadargelim -instcombine -basiccg -inline -prune-eh -globalopt -globaldce 
#  -basiccg -argpromotion -instcombine -jump-threading -domtree -domfrontier 
#  -scalarrepl -basiccg -functionattrs -globalsmodref-aa -domtree -loops 
#  -loopsimplify -domfrontier -licm -memdep
#  -gvn
#  -memdep -memcpyopt -dse -instcombine -jump-threading 
#  -domtree -domfrontier -mem2reg -simplifycfg -globaldce -instcombine -simplifycfg 
#  -adce -globaldce -preverify -domtree -verify"
LD_FLAG="-disable-opt"

#opt -mem2reg -debug-pass=Arguments -disable-output bho.bc
#Pass Arguments: -targetlibinfo -targetdata -domtree -mem2reg -preverify -verify

#-targetdata pass causes errors
PRE_OPT_FLAG="-disable-opt -targetlibinfo"
M2R_OPT_FLAG="-disable-opt -targetlibinfo -domtree -mem2reg"

Compiling ()
{
  echo -e $2": \c" ;

  echo -e "Pre"; time opt -f $PRE_OPT_FLAG $1 -o $2"o.bc"

  echo -e "Coq M2R"; time $M2R -mem2reg $2"o.bc" >& $2"a.ll"
  llvm-as -f $2"a.ll" -o $2"a.bc"
  echo -e "  LLVM ld1"; time llvm-ld -native -lm $LD_FLAG $2"a.bc" -o $2"a.exe"

  echo -e "Coq M2R no phielim"; time $M2R -mem2reg-no-phi-elim $2"o.bc" >& $2"c.ll"
  llvm-as -f $2"c.ll" -o $2"c.bc"
  echo -e "  LLVM ld"; time llvm-ld -native -lm $LD_FLAG $2"c.bc" -o $2"c.exe"
 
  echo -e "LLVM ld"; time llvm-ld -native -lm $LD_FLAG $2"o.bc" -o $2"b.exe"

  echo -e "LLVM M2R"; time opt -f $M2R_OPT_FLAG $1 -o $2"d.bc"
  llvm-dis -f $2"d.bc" -o $2"d.ll" 
  echo -e "  LLVM ld"; time llvm-ld -native -lm $LD_FLAG $2"d.bc" -o $2"d.exe"
}

Running ()
{
  echo -e $1" nopt: \c"; eval "time ./"$1"b.exe "$2" >& /dev/null"
  echo -e $1" vm2r: \c"; eval "time ./"$1"a.exe "$2" >& /dev/null"
  echo -e $1" vm2r noelim: \c"; eval "time ./"$1"c.exe "$2" >& /dev/null"
  echo -e $1" m2r: \c"; eval "time ./"$1"d.exe "$2" >& /dev/null"
}

for name in ./testcases/*.ll; do 
  echo -e $name": \c"  
  llvm-as -f $name -o input.bc
  $M2R -mem2reg input.bc
  $M2R -mem2reg input.bc >& output.ll
  llvm-as -f output.ll
  llvm-ld output.bc -o test.exe
  time ./test.exe
done;

for name in $OC_CASES; do 
  Compiling $OC_DIR$name"/test.bc" $name
done;
Running "bh" "< ./testcases/olden-ccured/bh/slow_input";
Running "bisort" "5000000 0";
Running "em3d" "30000 300 50";
Running "health" "8 250 1";
Running "mst" "4000";
Running "perimeter" "12 2000";
Running "power" "";
Running "treeadd" "24 10"; 
Running "tsp" "2000000 0";

for name in $S95_CASES; do 
  Compiling $S95_DIR$name"/src/test.bc" $name
done;
Running "099.go" "100 15"
#Running "130.li" "./testcases/spec95-ccured/130.li/src/ref.lsp";
Running "129.compress" "< ./testcases/spec95-ccured/129.compress/src/slow_input.data";
Running "132.ijpeg" "-image_file testcases/spec95-ccured/132.ijpeg/data/ref/input/vigo.ppm -compression.quality 90 -compression.optimize_coding 0 -compression.smoothing_factor 90 -difference.image 1 -difference.x_stride 10 -difference.y_stride 10 -verbose 1 -GO.findoptcomp"

rm -f bisort* em3d* health* mst* treeadd* 129.compress* test-softbound.bc \
  130.li* 099.go* tsp* bh* power* perimeter* 132.ijpeg* opt.bc input.* output.* \
  test.exe test.exe.bc aa.db


