llvm-as $1.ll -f
opt -dot-cfg-only -lowerswitch $1.bc -f -o lower.bc
dotty cfg.foo.dot&
opt lower.bc >& /dev/null
../../../_build/Vellvm/Dominators/main.native -d lower.bc >& push.log
../../../_build/Vellvm/Dominators/main.native -d type = 1 lower.bc >& pull.log
diff push.log pull.log

