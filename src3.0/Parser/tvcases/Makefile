TV=../../_build/Parser/main.d.byte
NN_DIR=./nano/
ML_DIR=./milli/
ML_CASES=addrof all bug1 bug2 cint2ptr fptr fptr2 fptr3 fptrret free funcargs \
  funcarg2 funcargsm funcargsret funcret funcret2 funcret3 int2ptr loadm \
  loadm2 loadr locals multimalloc postalloc ptr2int samechk select simple \
  storem storem2 storer struct undef
MC_DIR=./microbench/
MC_CASES=array array2 array3 global_array linkedlist linkedlistloop \
         reference_test struct_array
OC_DIR=./olden-ccured/
OC_CASES=bisort em3d health mst treeadd

all:
	rm -rf *.db
	sh ./test.sh &> _log
	diff _log log

test:
	number=0 ; \
	while [[ $$number -le 13 ]] ; do \
  	  echo -e $$number": \c" ; \
	  llvm-as -f $(NN_DIR)"Input"$$number".ll" -o Input.bc ; \
	  llvm-as -f $(NN_DIR)"Output"$$number".ll" -o Output.bc ; \
	  $(TV) "Input.bc" "Output.bc" ; \
	  ((number = number + 1)) ; \
	done; \
	for name in $(ML_CASES); do \
          echo -e $$name": \c" ; \
	  llvm-as -f $(ML_DIR)$$name"/test-linked.ll" -o Input.bc ; \
	  llvm-as -f $(ML_DIR)$$name"/test-instrumented.ll" -o Output.bc ; \
          cp $(ML_DIR)$$name"/renaming.db" .; \
	  $(TV) "Input.bc" "Output.bc" ; \
	done; \
	for name in $(MC_CASES); do \
          echo -e $$name": \c" ; \
	  llvm-as -f $(MC_DIR)$$name"/test-linked.ll" -o Input.bc ; \
	  llvm-as -f $(MC_DIR)$$name"/test-instrumented.ll" -o Output.bc ; \
          cp $(MC_DIR)$$name"/renaming.db" .; \
	  $(TV) "Input.bc" "Output.bc" ; \
	done; \
	for name in $(OC_CASES); do \
	  echo -e $$name": \c" ;  \
	  llvm-as -f $(OC_DIR)$$name"/test-linked.ll" -o Input.bc ; \
	  llvm-as -f $(OC_DIR)$$name"/test-instrumented.ll" -o Output.bc ; \
          cp $(OC_DIR)$$name"/renaming.db" .; \
	  $(TV) "Input.bc" "Output.bc" ; \
	done

clean:
	rm -rf *.bc *.db _log


