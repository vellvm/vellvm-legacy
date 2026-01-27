#!/usr/bin/python

import sys, string, os, re, popen2, difflib, platform, shutil
import util,mfgraph
import pickle

from configs import *

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
    "push-ptree":"dom-push-ptree",
    "push":"dom-push",
    "pull":"dom-pull",
    "slow-tree":"dom-slow-tree",
    "slow":"dom-slow",
    "llvm-tree":"dom-llvm-tree",
}

data_dir= ref_cwd + "/data/"

tag_path = ref_cwd + "/"

benchmark_data={}

benchmarks = [
              "ibfsquad_large", 
#              "idfsquad_large",
              "itworst_large",
             "sncaworst_large"
             ]

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
            
            
            percentage_speedup = (speedup - 1);

            numbers = []
            numbers.append(percentage_speedup);
            numbers = mfgraph.stack_bars(numbers)                
            bars.append([""] + numbers)

        
        stacks.append([benchmark] + bars)
        
    bars=[]
    for gconfig in pldi_main_performance_graph_configs:
        if gconfig == base:
            continue;

        numbers = []
        avg_config = pow(average[gconfig], 1.0/len(benchmarks));
        
        percentage_speedup = (avg_config -1 );
        numbers.append(percentage_speedup);
        numbers = mfgraph.stack_bars(numbers)                
        bars.append([""] + numbers)
        print bars

    stacks.append(["Geo. mean"] + bars);

    for gconfig in pldi_main_performance_graph_configs:
        if(gconfig == base):
            continue;
        if(gconfig == "push-tree"):
            labels.append("IListTr");
        elif(gconfig == "push"):
            labels.append("IList");
        elif(gconfig == "slow-tree"):
            labels.append("ISetTr");
        elif(gconfig == "slow"):
            labels.append("ISet");
        
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
#                                       legend_x = "5",
#                                       legend_y = "84",
#                                       legend_type = "on",
# #
                                      legend_type_x = [0, 15],
#                                      legend_type_y = [0, 0],
#                                      xsize = 5.9,
#                                      ysize = 1.1,
#                                      clip = 1,
                                      stack_name_rotate = 15.0,
                                      stack_name_font_size = "9",
#                                      colors = [ "0.375 0.375 0.375", "0.875 0.875 0.875", "0 0 0", "0.625 0.625 0.625"],
                                      colors = [ "0 0 0", "0.9 0.9 0.9"],
                                      #                                     colors = [ "0.9 0.9 0.9", "0.3 0.3 0.3", "0.6 0.6 0.6", "0 0 0"],
                                      ylabel = "Overhead over LLVM",
                                      title = "",
                             #                                     title = "Runtime Overhead",
                                      title_fontsize = "9",
                                      label_fontsize = "9",
#                                      ymax = 200,
                                      ymin = 0,
#                                      yhash_marks=["0", "50", "100", "150", "200"],
#                                      yhash_names=["0%", "50%", "100%", "150%", "200%"],
                                      grid_gray= "0.5",
				      ysize = 2.0,
                                      )]

for benchmark in benchmarks:
    benchmark_data[benchmark] = {}
    
    for graph_config in opt_graph_configs:

        file_name = data_dir + "/" + "runtime-"+benchmark + "_"+ graph_config_names[graph_config] + "_zjzzjz.txt"
        print file_name
        data_file = open(file_name, 'r')

        average = 0.0
        total = 3
        for i in range(3):
            val = data_file.readline();
            print "value read is :", val;
            average = average + float(val);
        
        average = average/1;
        benchmark_data[benchmark][graph_config] = average;
        
        
print benchmark_data

#mfgraph.run_jgraph("newpage\n".join(main_execution_time_graph()), "llvm-wpa-graph");


mfgraph.run_jgraph("newpage\n".join(pldi_main_performance_graph()), "perf_worst");

#mfgraph.run_jgraph("newpage\n".join(pldi_motivation_graph()), "motivation_graph");


