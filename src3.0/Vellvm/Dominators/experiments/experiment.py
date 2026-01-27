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
time_run_num = 6

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

def do_separate_compilation(bench_config, config):
  path = os.path.join(ref_cwd, "data")
  print path
  util.mkdir(path)
  path = os.path.join(path, "runtime-%s_%s_%s.txt" % (bench_config["NAME"], config["NAME"], hostname))
  f = open(path, "w")
  
  times = []
  for i in range(time_run_num):
    cfiles = string.split(bench_config["CFILES"]);
    cflags = ("%(CFLAGS)s") % bench_config
    time = 0.0
    for cf in cfiles:
      target = cf + "-switch.bc"
      if not os.path.isfile(target):
        ind_file = os.path.join("..","..", "..", cf)
        base_file = os.path.basename(ind_file)
        generate_bitcode_gcc_clang(ind_file ,cf, " -c " + cflags + m32_flags , clang_compile)
        build_string_opt = " opt  -lowerswitch " +  cf+ ".bc -f -o " + target
        util.run_command(build_string_opt, verbose= True)
    
      build_string_opt_pass = ocaml_extraction_binary + config["OUR_PASS_ARGS"] + target
      output = util.run_command("time -p " + build_string_opt_pass, verbose=True)
      time += util.parse_time(output)
    f.write("%s\n" % time)
    times.append(time)
    s = str(sum(times)/len(times))
    print bench_config["NAME"], "average: ", build_binary_name, s
   
  f.close()

def handle_our_pass(bench_config, config):
    if bench_config["NAME"] == "spec2k6-gcc":
      do_separate_compilation(bench_config, config)
      return

    target = bench_config["NAME"] + "-prefix.bc"
    if not os.path.isfile(target):
      cfiles = string.split(bench_config["CFILES"]);
      cflags = ("%(CFLAGS)s") % bench_config

      for f in cfiles:
        
        temp = os.path.join("..", "..", "..",  f)        
        generate_bitcode_gcc_clang(temp, f, cflags + m32_flags , clang_compile)

                
      cfiles = [f+".bc" for f in cfiles ]
      cfiles = string.join(cfiles);
      build_string2 = "llvm-ld -disable-opt -lowerswitch " + cfiles + " -o " + bench_config["NAME"]
      util.run_command(build_string2, verbose = False)
      
      build_string_opt_prefix  = " opt  " + config["prefix"] + " -lowerswitch " +  bench_config["NAME"] + ".bc -f -o " + bench_config["NAME"] + "-prefix.bc "
      util.run_command(build_string_opt_prefix, verbose= True)
      
    #    build_string_opt_pass = ocaml_extraction_binary + bench_config["NAME"]+"-prefix.bc  -o " + bench_config["NAME"] + "-opt-our-pass.bc "
      
    build_string_opt_pass = ""
    build_string_opt_pass = ocaml_extraction_binary + config["OUR_PASS_ARGS"] + bench_config["NAME"] + "-prefix.bc"

    ##### time run #####
    # open the output file
    path = os.path.join(ref_cwd, "data")
    print path
    util.mkdir(path)
    path = os.path.join(path, "runtime-%s_%s_%s.txt" % (bench_config["NAME"], config["NAME"], hostname))
    f = open(path, "w")

    times = []

    for i in range(time_run_num):
      output = util.run_command("time -p " + build_string_opt_pass, verbose=True);
      time = util.parse_time(output)
      print "run %d: " % i, build_binary_name, time
      times.append(time)
      f.write("%s\n" % time)
                     
      s = str(sum(times)/len(times))
      print bench_config["NAME"], "average: ", build_binary_name, s

    f.close()

os.environ["PATH"] = "/mnt/eclipse/acg/users/santoshn/skylynx/llvm-3.0-obj/Debug+Asserts/bin:" + os.environ["PATH"]
#os.environ["PATH"] = ref_cwd + "/../../llvm/llvm-2.8-obj/Debug/bin:" + os.environ["PATH"]
print os.environ["PATH"]


for benchmark in benchmarks:
    
    util.log_heading(benchmark, character="=")

    print "cwd:", cwd, "benchmark:", benchmark

    bench_path = os.path.join(cwd, benchmark);
    print "bench_path is ", bench_path
    
    os.chdir(bench_path)
    assert os.path.isfile("config.py")
    bench_config = eval(open("config.py").read())

    for config in configs:
        try:

            util.log_heading(config["NAME"], character="-")
            os.chdir(os.path.join(cwd, benchmark))

            if do_clean:
                if os.path.exists("obj"):
                    print "Removing directory 'obj'"
                    shutil.rmtree("obj")

            util.mkdir("obj")
            os.chdir("obj")
            util.mkdir(hostname)
            os.chdir(hostname)
            util.mkdir("dom")
            os.chdir("dom")
            bench_config["CWD"] = os.getcwd()
            print os.getcwd()

            build_binary_name = bench_config["NAME"] + "-" + config["NAME"]

            # set gcc as 3.x if mscc, and store PATH
            path_backup = os.environ["PATH"]
            if "LD_LIBRARY_PATH" in os.environ:
                ld_path_backup = os.environ["LD_LIBRARY_PATH"]

            ##### build #####
            if do_build: # and (arch in config["BUILD_ARCH"]):

                if "BUILD_LINE" in config:

                  if config["BUILD_LINE"] == "handle_custom_llvm":
                    handle_custom_llvm(bench_config, config)
                  elif config["BUILD_LINE"] == "handle_our_pass":
                    handle_our_pass(bench_config, config)
                  elif config["BUILD_LINE"] == "handle_custom_mem2reg":
                    handle_custom_mem2reg(bench_config, config)
                  elif config["BUILD_LINE"] == "handle_llvm_gcc":
                    handle_llvm_gcc(bench_config, config, 1)
                  elif config["BUILD_LINE"] == "handle_gcc":
                    handle_llvm_gcc(bench_config, config, 2);
                  elif config["BUILD_LINE"] == "handle_wpa":
                    handle_wpa(bench_config, config)
                else:
                    handle_llvm(bench_config, config)
            
            # restore PATH
            os.environ["PATH"] = path_backup
            if "LD_LIBRARY_PATH" in os.environ:
                os.environ["LD_LIBRARY_PATH"] = ld_path_backup

            ##### cleanup #####

        except util.ExperimentError, e:
            print "Error: %s" % e
            print "-----------"
            print "%s" % e.output
            print "-----------"


