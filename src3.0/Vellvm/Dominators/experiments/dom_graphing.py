#! /usr/bin/python

import sys, string, os, re, popen2, difflib, platform, shutil
import util,mfgraph
import pickle

from configs import *

time_run_num = 6

ref_cwd = os.getcwd();

opt_graph_configs = [
    "push-tree",
#    "push-ptree",
    "push",
#    "pull",
    "slow-tree",
    "slow",
    "llvm-tree",
]

pldi_main_performance_graph_configs=[
     "push-tree",
#     "push-ptree",
     "push",
#     "pull",
     "slow-tree",
     "slow",
     "llvm-tree",
]

graph_config_names= {
    "push-tree":"dom-push-tree",
#    "push-ptree":"dom-push-ptree",
    "push":"dom-push",
#    "pull":"dom-pull",
    "slow-tree":"dom-slow-tree",
    "slow":"dom-slow",
    "llvm-tree":"dom-llvm-tree",
}

bench_names={
    "../../../../src/Parser/tvcases/spec95-ccured/099.go/src": "go",
    "../../../../src/Parser/tvcases/spec95-ccured/129.compress/src" : "compress",
    "../../../../src/Parser/tvcases/spec95-ccured/132.ijpeg/src" : "ijpeg",
    
    "../../../../softbound_test/spec2k/164.gzip/src": "gzip",
    "../../../../softbound_test/spec2k/175.vpr/src" : "vpr",
    "../../../../softbound_test/spec2k/177.mesa/src" : "mesa",      
    "../../../../softbound_test/spec2k/179.art/src": "art",
    "../../../../softbound_test/spec2k/188.ammp/src" : "ammp",
    "../../../../softbound_test/spec2k/183.equake-modified/src" : "equake",
    "../../../../softbound_test/spec2k/186.crafty/src" : "crafty",
    "../../../../softbound_test/spec2k/256.bzip2/src" : "256.bzip2",
    "../../../../softbound_test/spec2k/197.parser/src" : "parser",
    "../../../../softbound_test/spec2k/300.twolf/src" : "twolf",
    "../../../../softbound_test/spec2k6/401.bzip2/src"  : "401.bzip2",   
    "../../../../softbound_test/spec2k6/403.gcc/src" : "gcc",
    "../../../../softbound_test/spec2k6/429.mcf/src" : "mcf",
    "../../../../softbound_test/spec2k6/456.hmmer/src" : "hmmer",
    "../../../../softbound_test/spec2k6/462.libquantum/src" : "libquantum",
    "../../../../softbound_test/spec2k6/470.lbm/src" : "lbm",
    "../../../../softbound_test/spec2k6/433.milc/src": "milc",
    "../../../../softbound_test/spec2k6/458.sjeng/src": "sjeng",
    "../../../../softbound_test/spec2k6/464.h264ref/src" : "h264ref",
}

data_dir= ref_cwd + "/data/"

tag_path = ref_cwd + "/"

benchmark_data={}

def pldi_main_performance_graph():
    stacks=[]
    bars=[]
    labels=[]

    base = "llvm-tree"

    average = {}

    for gconfig in pldi_main_performance_graph_configs:
        average[gconfig]=1.0
    
    for benchmark in benchmarks:
        bars=[]
        base_exec_time = benchmark_data[benchmark][base]
        
        for gconfig in pldi_main_performance_graph_configs:
            
            if gconfig == base:
                continue;
            
            config_exec_time = benchmark_data[benchmark][gconfig]
            
            speedup = config_exec_time/base_exec_time;
            average[gconfig] = average[gconfig] * speedup;

            print "benchmark:", benchmark, "config_exec_time:", config_exec_time, "base_exec_time:", base_exec_time, "speedup:", speedup
            
            
            percentage_speedup = (speedup - 1) * 100;

            numbers = []
            numbers.append(percentage_speedup);
            numbers = mfgraph.stack_bars(numbers)                
            bars.append([""] + numbers)

        
        stacks.append([bench_names[benchmark]] + bars)
        
    bars=[]
    for gconfig in pldi_main_performance_graph_configs:
        if gconfig == base:
            continue;

        numbers = []
        avg_config = pow(average[gconfig], 1.0/len(benchmarks));
        
        percentage_speedup = (avg_config -1 ) * 100;
        numbers.append(percentage_speedup);
        numbers = mfgraph.stack_bars(numbers)                
        bars.append([""] + numbers)
        print bars

    stacks.append(["Geo. mean"] + bars);

    for gconfig in pldi_main_performance_graph_configs:
        if(gconfig == base):
            continue;
        if(gconfig == "push-tree"):
            labels.append("CHK-tree");
        elif(gconfig == "push"):
            labels.append("CHK");
	elif(gconfig == "slow-tree"):
            labels.append("AC-tree");
        elif(gconfig == "slow"):
            labels.append("AC");
        elif(gconfig == "o3"):
            labels.append("llvm-O3");
        
        elif(gconfig == "llvm-mem2reg"):
            labels.append("LLVM's  mem2reg");
        
        elif(gconfig == "ourpass-mem2reg-prune"):
            labels.append("Pruned Mem2reg");
        
        elif (gconfig == "ourpass-mem2reg-extractp"):
            labels.append("Extracted vmem2reg");
        else:
            labels.append(gconfig)

    print stacks
       
    return [mfgraph.stacked_bar_graph(stacks,
                                      bar_segment_labels = labels,
                                      # bar_segment_labels = ["Conservative pointer identification", "ISA-assisted pointer identification"],
                                      patterns = ["solid", "solid"],
                                      legend_fontsize = "9",
                                       legend_x = "5",
                                       legend_y = "80",
#                                       legend_type = "on",
# #
                                      legend_type_x = [0, 15],
#                                      legend_type_y = [0, 0],
#                                      xsize = 5.9,
#                                      ysize = 1.1,
#                                      clip = 1,
                                      stack_name_rotate = 20.0,
                                      stack_name_font_size = "9",
#                                      colors = [ "0.375 0.375 0.375", "0.875 0.875 0.875", "0 0 0", "0.625 0.625 0.625"],
                                      colors = [ "0 0 0", "0.9 0.9 0.9"],
                                      #                                     colors = [ "0.9 0.9 0.9", "0.3 0.3 0.3", "0.6 0.6 0.6", "0 0 0"],
                                      ylabel = "Overhead over LLVM",
                                      title = "",
                             #                                     title = "Runtime Overhead",
                                      title_fontsize = "9",
                                      label_fontsize = "9",
                                      ymax = 250,
                                      ymin = 0,
                                      clip = 1,
                                      yhash_marks=["0", "50", "100", "150", "200", "250"],
                                      yhash_names=["0%", "50%", "100%", "150%", "200%", "250%"],
                                      grid_gray= "0.5",
				      ysize = 2.0,
                                      )]


for benchmark in benchmarks:
    config_file_path = tag_path + benchmark + "/" + "config.py"
    bench_config = eval(open(config_file_path).read())

    benchmark_data[benchmark] = {}
    
    for graph_config in opt_graph_configs:

        file_name = data_dir + "/" + "runtime-"+bench_config["NAME"] + "_"+ graph_config_names[graph_config] + "_zjzzjz.txt"
        print file_name
        data_file = open(file_name, 'r')

        average = 0.0
        for i in range(time_run_num):
            val = data_file.readline();
            print "value read is :", val;
            average = average + float(val);
        
        average = average/time_run_num;
        benchmark_data[benchmark][graph_config] = average;
        
        
print benchmark_data

#mfgraph.run_jgraph("newpage\n".join(main_execution_time_graph()), "llvm-wpa-graph");


mfgraph.run_jgraph("newpage\n".join(pldi_main_performance_graph()), "perf_common");

#mfgraph.run_jgraph("newpage\n".join(pldi_motivation_graph()), "motivation_graph");

