import os

do_clean = False
do_build = True
do_time_run = False
do_clang= True

benchmarks = [
     "../../../../src/Parser/tvcases/spec95-ccured/099.go/src",
     "../../../../src/Parser/tvcases/spec95-ccured/129.compress/src",
     "../../../../src/Parser/tvcases/spec95-ccured/132.ijpeg/src",
     "../../../../softbound_test/spec2k/164.gzip/src",
     "../../../../softbound_test/spec2k/175.vpr/src",
     "../../../../softbound_test/spec2k/177.mesa/src",      
     "../../../../softbound_test/spec2k/179.art/src",
     "../../../../softbound_test/spec2k/188.ammp/src",
     "../../../../softbound_test/spec2k/183.equake-modified/src",
##   "../../../../softbound_test/spec2k/186.crafty/src",
     "../../../../softbound_test/spec2k/256.bzip2/src",
     "../../../../softbound_test/spec2k/197.parser/src",
     "../../../../softbound_test/spec2k/300.twolf/src",

     "../../../../softbound_test/spec2k6/401.bzip2/src",   
     "../../../../softbound_test/spec2k6/403.gcc/src",
     "../../../../softbound_test/spec2k6/429.mcf/src",
     "../../../../softbound_test/spec2k6/456.hmmer/src",
     "../../../../softbound_test/spec2k6/462.libquantum/src",
     "../../../../softbound_test/spec2k6/470.lbm/src",
     "../../../../softbound_test/spec2k6/433.milc/src",
     "../../../../softbound_test/spec2k6/458.sjeng/src",
     "../../../../softbound_test/spec2k6/464.h264ref/src",
     ]


cwd = os.getcwd() # current working directory
print "cwd is ", cwd 
configs = []

entry = { "NAME" : "dom-push-tree",

         "prefix" : " -disable-opt ", # "prefix" : " -simplifycfg
         "suffix": " -disable-opt ", 
         "do_gvn": " -disable-opt ",
         "pass_args" : " -gvn ", 
         "OUR_PASS_ARGS" : " ",
         "BUILD_LINE" : "handle_our_pass",
        } 
configs.append(entry);

entry = { "NAME" : "dom-llvm-tree",

         "prefix" : " -disable-opt ", # "prefix" : " -simplifycfg
         "suffix": " -disable-opt ", 
         "do_gvn": " -disable-opt ",
         "pass_args" : " -gvn ", 
         "OUR_PASS_ARGS" : " -type 3 ",
         "BUILD_LINE" : "handle_our_pass",
        } 
configs.append(entry);

entry = { "NAME" : "dom-pull",

         "prefix" : " -disable-opt ", # "prefix" : " -simplifycfg
         "suffix": " -disable-opt ", 
         "do_gvn": " -disable-opt ",
         "pass_args" : " -gvn ", 
         "OUR_PASS_ARGS" : " -type 1 ",
         "BUILD_LINE" : "handle_our_pass",
        } 
configs.append(entry);

entry = { "NAME" : "dom-push",

         "prefix" : " -disable-opt ", # "prefix" : " -simplifycfg
         "suffix": " -disable-opt ", 
         "do_gvn": " -disable-opt ",
         "pass_args" : " -gvn ", 
         "OUR_PASS_ARGS" : " -type 0 -notree ",
         "BUILD_LINE" : "handle_our_pass",
        } 
configs.append(entry);

entry = { "NAME" : "dom-slow",

         "prefix" : " -disable-opt ", # "prefix" : " -simplifycfg
         "suffix": " -disable-opt ", 
         "do_gvn": " -disable-opt ",
         "pass_args" : " -gvn ", 
         "OUR_PASS_ARGS" : " -type 2 -notree ",
         "BUILD_LINE" : "handle_our_pass",
        } 
configs.append(entry);

entry = { "NAME" : "dom-slow-tree",

         "prefix" : " -disable-opt ", # "prefix" : " -simplifycfg
         "suffix": " -disable-opt ", 
         "do_gvn": " -disable-opt ",
         "pass_args" : " -gvn ", 
         "OUR_PASS_ARGS" : " -type 2 ",
         "BUILD_LINE" : "handle_our_pass",
        } 
configs.append(entry);

entry = { "NAME" : "dom-push-ptree",

         "prefix" : " -disable-opt ", # "prefix" : " -simplifycfg
         "suffix": " -disable-opt ", 
         "do_gvn": " -disable-opt ",
         "pass_args" : " -gvn ", 
         "OUR_PASS_ARGS" : " -type 0 -only-pdtree ",
         "BUILD_LINE" : "handle_our_pass",
        } 
configs.append(entry);
