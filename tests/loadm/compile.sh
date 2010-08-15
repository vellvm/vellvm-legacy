# STEP1: Compile softbound instrumentation files to LLVM bitcode (.bc) files
#   Execute the following set of commands:

gcc -c --emit-llvm -O3 -D__SOFTBOUND_HASHTABLE ../../softbound-checks.c -o softbound-checks.bc
gcc -c --emit-llvm -O3 -D__SOFTBOUND_HASHTABLE ../../softbound.c -o softbound.bc
gcc -c --emit-llvm -O3 -D__SOFTBOUND_HASHTABLE ../../softbound-wrappers.c -o softbound-wrappers.bc
 
# Note: If you want to use the hash table then use -D__SOFTBOUND_HASHTABLE
# as the flag in the above command line. If you want to use shadow space,
# use -D__SOFTBOUND_SHADOWSPACE as the flag.
 
# STEP2: compile each individual source file
 
gcc -O3 -c -Wall --emit-llvm testa.c -o testa.bc
gcc -O3 -c -Wall --emit-llvm testb.c -o testb.bc
llvm-dis -f testa.bc
llvm-dis -f testb.bc

# STEP3: create a single module using llvm-ld by using all the source files

# disable all opts except mem2reg to simplify proofs
llvm-ld -disable-opt -mem2reg testa.bc testb.bc -o test
 
# STEP4: link the softbound checks file
 
llvm-link softbound-checks.bc test.bc > test-linked.bc
llvm-dis -f test-linked.bc
 
# STEP5: run the softbound instrumentation

# disable all opts except mem2reg to simplify proofs
opt -disable-opt -mem2reg -SoftBoundPass -load_opt=false -global_const_opt=false --debug-pass=Structure test-linked.bc > test-instrumented.bc
llvm-dis -f test-instrumented.bc

# STEP6: link the wrappers
 
llvm-link test-instrumented.bc softbound.bc softbound-wrappers.bc > test-softbound.bc
llvm-dis -f test-softbound.bc
 
# STEP7: generate native code
 
llvm-ld -native -lm -lcrypt test-softbound.bc -o test
 
# STEP8: run the program:
 
./test 50    # no overflow
./test 55    # generates an overflow, should be detected by SoftBound

# SoftBound Usage Flags to "opt"
# ------------------------------
 
# The default parameters are given below
# 
# -load_checks=true         Enables/disables checking bounds of loads
# 
# -store_checks=true        Enables/disables checking bounds of stores
# 
# -load_opt=true            Enables/disables a simple redundant check elimination optimization
# 
# -global_const_opt=true    Enables/disables removing checks on globals
# 
# -shrink_bounds=false      Enables/disables shrinking of bounds of pointers to struct fields

