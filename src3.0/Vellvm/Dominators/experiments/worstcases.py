#!/usr/bin/python

import sys, string, os, re, popen2, difflib, platform, shutil
import util
from configs import *

ref_cwd = os.getcwd();
arch = platform.machine()
full_hostname = platform.node()
print full_hostname
hostname=full_hostname
print hostname

ocaml_extraction_binary = "/home/jianzhou/SVN/sol/vol/src3.0/_build/Vellvm/Dominators/main.native "
#ocaml_extraction_binary = "/mnt/eclipse/acg/users/jianzhou/svn/sol/vol/src3.0/_build/Vellvm/Dominators/main.native "

custom_mem2reg_pass = "/mnt/eclipse/acg/users/santoshn/skylynx/sol/vol/optimizations_test/OptimizationPass/Debug/bin/Opts "


do_use_aliasdb = False
do_m32_compilation = False
m32_flags = "" 
Xlinker_flags = ""

if do_m32_compilation:
  
  m32_flags = " -m32 "
  if m32_flags != "":
    Xlinker_flags= " -Xlinker=-m32"



clang_compile = 1
gcc_compile = 2
cpp_compile = 3

cwd = os.getcwd()

#=========================================
def copy_input_and_test(bench_config, f):

    print ref_cwd
    path_backup = os.getcwd();
    os.chdir("../../../");
    
    if "COPY_INPUT" in bench_config:
        copy_input = "cp " + bench_config["COPY_INPUT"] + " ./"
#        util.run_command(copy_input, "",  verbose=True, throw_exception=False);
        
    built_binary_name = "./" + f + "-" + config["NAME"] + (" %(COMMANDLINE)s" % bench_config)
    util.run_command(built_binary_name, verbose = True)
    
    os.chdir(path_backup);

    print os.getcwd()


def generate_bitcode_gcc_clang(file_path_name, file_name, cflags, compiler_type):

    build_string = ""
    if compiler_type == gcc_compile:
        build_string = "gcc -c --emit-llvm -I../../../ -I../../../libutil " + cflags + " " + file_path_name + " -o " + file_name + ".bc"
        util.run_command(build_string, verbose = False)

    elif compiler_type == cpp_compile:
        build_string = "g++ -c --emit-llvm -I../../../ -I../../../libutil " + cflags + " " + file_path_name + " -o " + file_name + ".bc"        
        util.run_command(build_string, verbose = False)
    elif compiler_type == clang_compile:
        build_string = "clang -c -std=gnu89 -I../../../ -I../../../libutil -emit-llvm " + cflags + " " + file_path_name + " -o " + file_name + ".bc"
        util.run_command(build_string, verbose = False)
        # build_string_as = "llvm-as " + file_name + ".ll"
        # util.run_command(build_string_as, verbose = False)
    else:
        print "Compiler type not recognized"
        sys.exit(1);

def handle_our_pass(benchmark, config):
    target = benchmark + "-prefix.bc"
    if not os.path.isfile(target):
      build_string_opt_prefix  = " opt  " + config["prefix"] + " -lowerswitch " +  benchmark + ".bc -f -o " + target
      util.run_command(build_string_opt_prefix, verbose= True)
      
    build_string_opt_pass = ""
    build_string_opt_pass = ocaml_extraction_binary + config["OUR_PASS_ARGS"] + target

    ##### time run #####
    # open the output file
    path = os.path.join(ref_cwd, "data")
    print path
    util.mkdir(path)
    path = os.path.join(path, "runtime-%s_%s_%s.txt" % (benchmark, config["NAME"], hostname))
    f = open(path, "w")

    times = []

    for i in range(3):
      output = util.run_command("time -p " + build_string_opt_pass, verbose=True);
      time = util.parse_time(output)
      print "run %d: " % i, target, time
      times.append(time)
      f.write("%s\n" % time)
                     
      s = str(sum(times)/len(times))
      print benchmark, "average: ", target, s

    f.close()

os.environ["PATH"] = "/mnt/eclipse/acg/users/santoshn/skylynx/llvm-3.0-obj/Debug+Asserts/bin:" + os.environ["PATH"]
#os.environ["PATH"] = ref_cwd + "/../../llvm/llvm-2.8-obj/Debug/bin:" + os.environ["PATH"]
print os.environ["PATH"]

benchmarks = [
#              "ibfsquad_large", 
              "idfsquad_large",
#             "itworst_large",
#             "sncaworst_large"
             ]

for benchmark in benchmarks:
    
    util.log_heading(benchmark, character="=")

    print "cwd:", cwd, "benchmark:", benchmark

    bench_path = os.path.join(cwd, "../worstcases");
    print "bench_path is ", bench_path
    
    os.chdir(bench_path)

    for config in configs:
        try:

            ##### build #####
            if do_build: # and (arch in config["BUILD_ARCH"]):
               handle_our_pass(benchmark, config)

            ##### cleanup #####

        except util.ExperimentError, e:
            print "Error: %s" % e
            print "-----------"
            print "%s" % e.output
            print "-----------"


