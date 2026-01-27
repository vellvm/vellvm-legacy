from __future__ import nested_scopes
import sys, string, os, glob, re, math
from types import *

graph_counter = 1

# returns a list of lines in the file that matches the pattern
def grep(filename, pattern):
    result = [];
    file = open(filename,'r')
    for line in file.readlines():
        if re.match(pattern, line):
            result.append(string.strip(line))
            return result

# returns a list of lines in the file that DO NOT match the pattern
def inverse_grep(filename, pattern):
    result = [];
    file = open(filename,'r')
    for line in file.readlines():
        if not re.match(pattern, line):
            result.append(string.strip(line))
    return result

# returns the median of the list
def median(list):
    sorted = list
    sorted.sort()
    length = len(list)
        
    if length == 0:
        return 0
    elif length == 1:
        return list[0]
    elif length % 2 == 0:
        # even  
        return (list[length/2]+list[(length/2)-1])/2.0
    else:
        # odd
        return list[length/2]

# returns the Nth percentile element of the list
def nth_percentile(list, n):
    sorted = list
    sorted.sort()
    length = len(list)
        
    if length == 0:
        return 0
    elif length == 1:
        return list[0]
    else:
        return list[length*n/100]

# returns the maximum element of the list
def maximum(list):
    sorted = list
    sorted.sort()
    length = len(list)
        
    if length == 0:
        return 0
    elif length == 1:
        return list[0]
    else:
        return list[length-1]

# returns the minimum of the list
def minimum(list):
    sorted = list
    sorted.sort()
    length = len(list)

    if length == 0:
        return 0
    else:
        return list[0]

# returns the average of the list
def average(list):
    if (type(list) is TupleType) or (type(list) is ListType):
        sum = reduce(lambda x, y: x+y, list, 0);
        length = len(list)
        if length == 0:   
            return 0
        else:
            return 1.0*sum/length
    else:
        return list
    
# returns the average of the list without the two extremes
def averageWithoutExtremes(list):
    av = average(list)
    length = len(list)
    max = maximum(list)
    min = minimum(list)
    if length < 3:
        return av
    else:
        return ((av*length-min-max)/(length-2))

# returns the standard deviation
def stddev(list):
    if len(list) == 1:
        print "Warning: standard deviation of a one element list"
        return 0
    
    if len(list) == 0:
        print "Warning: standard deviation of a zero element list"

    sum = 0.0;
    sumsq = 0.0;
    for num in list:
        sum = sum + num
        sumsq = sumsq + pow(num, 2)

    size = float(len(list))
    average = sum / size
    variance = (sumsq - pow(sum, 2)/size)/(size-1.0)

    if variance < 0.0:
        print "Warning: negative variance"
        variance = 0.0
        
    stddev = math.sqrt(variance)
    return stddev

#normalizes an associative array
def normalize(assoc_array, normal_key):
    if not assoc_array.has_key(normal_key):
        raise RuntimeError, "Normalization key missing"

    base = assoc_array[normal_key]
    if (type(base) is TupleType) or (type(base) is ListType):
        base = base[0]

    if base == 0:
        raise RuntimeError, "Normalizing with zero base"
    for key in assoc_array.keys():
        item = assoc_array[key]

        # act differently if we are a list or not
        if (type(item) is TupleType) or (type(item) is ListType):
            for index in range(len(item)):
                item[index] = item[index]/base
        else:
            item = item/base

        assoc_array[key] = item

def normalize_list(lines, config):
    normal_map = {}
    for line in lines:
        if line[0] == config:
            line = line[1:]  # skip label
            for pair in line:
                normal_map[pair[0]] = pair[1]

    counter = 0
    for line in lines:
        new_line = [line[0]]
        line = line[1:]  # strip off label
        for pair in line:
            x_value = pair[0]
            new_pair = [x_value]
            if normal_map.has_key(x_value):
                for index in range(1, len(pair)):
                    new_pair.append(normal_map[x_value]/pair[index])
                new_line.append(new_pair)
        lines[counter] = new_line
        counter += 1



# find the minimum value and inverted normalize to it
def make_relative(lines):
    lst = []
    for line in lines:
        line = line[1:]  # skip label
        for pair in line:
            lst.append(pair[1]) # the y-value

    minimum = min(lst)

    for line in lines:
        line = line[1:]  # strip off label
        for pair in line:
            for index in range(1, len(pair)):
                pair[index] = minimum/pair[index]

# generates multiple jgraphs on the same page.
def multi_graph(data_list,       # list of data, one element per graph
                param_list = [], # list of parameters to the gen_graph function unique to each graph
                cols = 2,        # number of columns
                row_space = 3,
                col_space = 2.5,
                **other_params   # default parameters used by all the graphs generated by this function
                ):
    num = 0
    jgraph_input = []
    for (data, params) in map(None, data_list, param_list):
        new_params = other_params
        if params:
            new_params.update(params)
        jgraph_input.append(gen_graph(data,
                                      x_translate = (num % cols) * col_space,
                                      y_translate = (num / cols) * -row_space,
                                      **new_params
                                      ))
        num += 1
    return "\n".join(jgraph_input)

def stacked_bar_graph(stacks,
                      **params):
    return gen_graph(stacks,
                     graph_type = "bar",
                     **params)

def line_graph(stacks,
               **params):
    return gen_graph(stacks,
                     graph_type = "line",
                     **params)

def gen_graph(data,
              graph_type = "line", # should be either "bar" or "line"
              # bar chart specific items
              bar_space = 1.1,
              bar_segment_labels = [],
              bar_name_font_size = "12",
              bar_name_rotate = 0.0,
              stack_name_rotate=0.0,
              stack_space = 1.0,
              stack_name_font_size = "12",
              stack_name_location = 5.0,
              patterns = ["solid", "stripe -45", "solid", "stripe 45"],
              yhash = "",
              ymhash = "",
              yhash_format = "",
              # line graph specific items
              linetype = ["solid", "dotted", "longdash", "dotdash", "dashed"],
              marktype = ["none"],
              mrotate = 0.0,
              marksize = None,
              line_thickness = 1.0,
              xhash_marks = [],
              yhash_marks = [],
              yhash_names = [],
              fills = ["0 0 0", "1 1 1", "0.5 0.5 0.5"],
              # title
              title = "",
              title_fontsize = "24",
              title_font = "Times-Roman",
              title_y = 115,
              # labels
              xlabel = "",
              ylabel = "",
              label_fontsize = "14",
              label_font = "Times-Roman",
              ylabel_location = [],
              xlabel_location = [],
              # legends
              legend = "on",
              legend_fontsize = "14",
              legend_font = "Times-Roman",
              legend_x = "",
              legend_y = "",
              legend_default = "",
              legend_hack = "",
              legend_type ="",
              legend_type_x=[0, 0, 5, 5],
              legend_type_y=[0, 5, 0, 5] ,
              # presentation
              xsize = 7.0,
              ysize = 7.0,
              x_translate = 0.0,
              y_translate = 0.0,
              xmax = "",
              ymax = "",
              xmin = "",
              ymin = 0,
              xlog = "",
              ylog = "",
              clip = 0,
              colors = ["1 0 0", "0 0 1", "0 .5 0", "1 0 1", "0 1 0", "0 0 1", "0 1 1", "1 1 0", ".5 0 0"],
              # set colors for each benchmark
              scolors = [],
              grid_gray = "",
              ):

    # Figure out which graph number we are
    global graph_counter
    data_graph = graph_counter  # used to plot data
    position_graph = graph_counter + 1  # use to position titles, etc
    graph_counter += 2 
    counter = 1.0

    output = ""
    output += "graph %d x_translate %f y_translate %f\n" % (data_graph, x_translate, y_translate)
    if clip:
        output += "clip\n"
    output += "graph %d clip x_translate %f y_translate %f\n" % (position_graph, x_translate, y_translate)
    if (title != ""):
        output += "graph %d title y %d font %s fontsize %s : %s\n" % (position_graph, title_y, title_font, title_fontsize, title)

    # place legends (using the position graph)
    output += "graph %d\n" % position_graph

    if legend_type != "":
        legend = "on"
        output += "legend custom "
    else:
        if legend != "on":
            legend = "off"
        output += "legend %s defaults %s font %s fontsize %s" % (legend, legend_default, legend_font, legend_fontsize)
        if (legend_x != ""):
            output += " x %s" % legend_x
        if (legend_y != ""):
            output += " y %s" % legend_y
    output += "\n"

    if legend_type != "":
        if len(bar_segment_labels) > 1:
            for bar_num in range(len(bar_segment_labels)):
                output += "curve " + str(bar_num) + " marktype xbar marksize 1 5 pattern %s cfill %s clip\n" % (patterns[bar_num%len(patterns)], colors[bar_num%len(colors)])
                output += "label x %d y %d fontsize 9 hjl vjt : %s\n" %(int(legend_x) + legend_type_x[bar_num], int(legend_y) + legend_type_y[bar_num], bar_segment_labels[bar_num]) 
                
    else:
        if len(bar_segment_labels) > 1:     # bar legend - only if there is more than one type of bar
            for bar_num in range(len(bar_segment_labels)):
                output += "newcurve pts 0 0 marktype xbar marksize 1 5 pattern %s cfill %s label : %s\n" % \
                          (patterns[bar_num%len(patterns)], colors[bar_num%len(colors)], bar_segment_labels[bar_num])
                
    if graph_type == "bar":
        stack_num = 0
        for stack in data:
            stack_name = stack[0]
            bars = stack[1:]
            x_begin = counter
            x_end = counter
            bar_num = 0  # should this be this way
            for bar in bars:
                bar_name = bar[0]
                components = bar[1:]
                for component in components:
                    # if it is a list, take the first element
                    if (type(component) is TupleType) or (type(component) is ListType):
                        value = component[0]
                    else:
                        value = component

                    if scolors == []:
                      output += "graph %d newcurve marksize 1 1 marktype xbar pattern %s cfill %s pts %f %f\n" % \
                                (data_graph, patterns[bar_num%len(patterns)], colors[bar_num%len(colors)], counter, value)
                    else:
                      output += "graph %d newcurve marksize 1 1 marktype xbar pattern %s cfill %s pts %f %f\n" % \
                                (data_graph, patterns[bar_num%len(patterns)], scolors[stack_num%len(scolors)], counter, value)

                    # error bars
                    if (type(component) is TupleType) or (type(component) is ListType):
                        output += "graph %d newcurve marksize 0.5 1 marktype none y_epts %f %f %f %f\n" % \
                                  (data_graph, counter, value, component[1], component[2])

                    bar_num += 1

                # bar name 
                if bar_name_rotate == 0:
                    output += "graph %d newstring fontsize %s x %f y -2.5 hjc vjt : %s\n" % (position_graph, bar_name_font_size, counter, bar_name)
                else:
                    output += "graph %d newstring fontsize %s x %f y -2.5 hjr vjc rotate %f : %s\n" % (position_graph, bar_name_font_size, counter, bar_name_rotate, bar_name)

                x_end = counter
                counter += bar_space
            counter = counter + stack_space
            average = (x_end+x_begin) / 2.0
	    if stack_name_rotate == 0:
	            output += "graph %d newstring fontsize %s hjc vjt x %f y %f : %s\n" % (position_graph, stack_name_font_size, average, -stack_name_location, stack_name)
	    else:
	            output += "graph %d newstring fontsize %s hjr vjt x %f y %f rotate %f : %s\n" % (position_graph, stack_name_font_size, average, -stack_name_location, stack_name_rotate, stack_name)

            stack_num += 1
            

    if graph_type == "line":
        counter = 100
        # add error bars first
        line_num = 0
        for line in data:
            if len(line) < 1:
                continue
            line_title = line[0]
            line = line[1:]

            error_bars = ""
            for point in line:
                if len(point) == 4:
                    error_bars += "%f %f %f %f\n" % (point[0], point[1], point[2], point[3])

            if error_bars != "":
                output += "graph %d newline\n" % (data_graph)
                output += "y_epts %s\n" % error_bars
                output += "color %s\n" % colors[line_num%len(colors)]
                output += "linetype none\n"
            line_num += 1

        # add lines and marks
        line_num = 0
        for line in data:
            if len(line) < 1:
                continue
            # line style
            style = "color %s\n" % colors[line_num%len(colors)]
            style += "cfill %s\n" % fills[line_num%len(fills)]
            style += "marktype %s\n" % (marktype[line_num%len(marktype)])
            if marksize:
                style += "marksize %f\n" % (marksize[line_num%len(marksize)])
            if mrotate:
                style += "mrotate %f\n" % (mrotate[line_num%len(mrotate)])
            style += "linetype %s\n" % linetype[line_num%len(linetype)]
            style += "linethickness %f\n" % line_thickness

            line_title = line[0]
            line = line[1:]
            output += "graph %d newline\n" % (data_graph)
            output += "pts\n"
            for point in line:
                output += "%f %f\n" % (point[0], point[1])
            output += style
            # we plot a point to get it to show up in the label (position graph)
            output += "graph %d newline pts -10 -10 %s\n" % (position_graph, style)
            if line_title != "":
                output += "label : %s\n" % (line_title)
            line_num += 1

    # x- and y-axis: sizes and ranges
    output += "graph %d\n" % (position_graph)
    output += "xaxis size %f min 0 nodraw max %f\n" % (xsize, counter)
    output += "yaxis size %f min 0 nodraw max 100\n" % (ysize)

    output += "graph %d\n" % (data_graph)
    output += "xaxis size %f\n" % (xsize)
    output += "yaxis size %f\n" % (ysize)
    if graph_type == "bar":
        xmin = 0
        output += "xaxis no_auto_hash_labels no_draw_hash_marks max %f\n" % (counter)
        output += "yaxis grid_lines\n"
        if grid_gray != "":
            output += "yaxis grid_gray " + grid_gray + "\n"

    if (ymax != ""):
        output += "yaxis max %f\n" % ymax
    if (xmax != ""):
        output += "xaxis max %f\n" % xmax
    if (ymin != ""):
        output += "yaxis min %f\n" % ymin
    if (xmin != ""):
        output += "xaxis min %f\n" % xmin
    if (xlog != ""):
        output += "xaxis log log_base %d\n" % (xlog) # xlog is the base
    if (ylog != ""):
        output += "yaxis log log_base %d\n" % (ylog) # ylog is the base

    # hashes (always on the data graph)
    output += "graph %d\n" % (data_graph)
    if len(xhash_marks) > 1:
        output += "xaxis no_auto_hash_marks\n"
        for mark in xhash_marks:
            output += "xaxis hash_at %s hash_label at %s : %s\n" % (mark, mark, mark)
    if len(yhash_marks) > 1:
        output += "yaxis no_auto_hash_marks\n"
        index = 0
        for mark in yhash_marks:
            output += "yaxis hash_at %s hash_label at %s : %s\n" % (mark, mark, yhash_names[index])
            index += 1
    if yhash != "":
        output += "yaxis hash %f\n" % (yhash)
    if ymhash != "":
        output += "yaxis mhash %f\n" % (ymhash)
    if yhash_format != "":
        output += "yaxis hash_format %s\n" % (yhash_format)

    output += "xaxis hash_labels font %s fontsize %s\n" % (label_font, label_fontsize); 
    output += "yaxis hash_labels font %s fontsize %s\n" % (label_font, label_fontsize);

    # axis labels (position graph)
    output += "graph %d\n" % (position_graph) 

    if xlabel_location != []:
        output += "graph %d\n" % (position_graph) # put us in the data independent scale
        label_pos = "y -%f " % (xlabel_location) # no newline
    else:
        output += "graph %d\n" % (data_graph)
        label_pos = ""
    output += "xaxis draw_axis_label label %s font %s fontsize %s : %s\n" % (label_pos, label_font, label_fontsize, xlabel)

    if ylabel_location != []:
        output += "graph %d\n" % (position_graph) # put us in the data independent scale
        label_pos += " x -%f " % (ylabel_location) # no newline
    else:
        output += "graph %d\n" % (data_graph)
        label_pos = ""
    output += "yaxis draw_axis_label label %s font %s fontsize %s : %s\n" % (label_pos, label_font, label_fontsize, ylabel)

    output += "graph %d\n" % (data_graph)
    return output

# converts a list of values to the 'stacked' equivalent
def stack_bars(list):
    data = list
    sum = 0.0
    lst = range(len(data))
    lst.reverse()
    for num in lst:
        data[num] += sum
        sum = data[num]
    return data

def stacked_curved_bar_graph(data,
              graph_type = "bar", # should be either "bar" or "line"
              # bar chart specific items
              bar_space = 1.1,
              bar_segment_labels = [],
              bar_name_font_size = "12",
              bar_name_rotate = 0.0,
              stack_name_rotate=0.0,
              stack_space = 1.0,
              stack_name_font_size = "12",
              stack_name_location = 5.0,
              patterns = ["solid", "stripe -45", "solid", "stripe 45"],
              yhash = "",
              ymhash = "",
              yhash_format = "",
              # line graph specific items
              line_thickness = 1.0,
              xhash_marks = [],
              yhash_marks = [],
              yhash_names = [],
              fills = ["0 0 0", "1 1 1", "0.5 0.5 0.5"],
              # title
              title = "",
              title_fontsize = "24",
              title_font = "Times-Roman",
              title_y = 115,
              # labels
              xlabel = "",
              ylabel = "",
              label_fontsize = "14",
              label_font = "Times-Roman",
              ylabel_location = [],
              xlabel_location = [],
              # legends
              legend = "on",
              legend_fontsize = "14",
              legend_font = "Times-Roman",
              legend_x = "",
              legend_y = "",
              legend_default = "",
              legend_hack = "",

              legend_type ="",
              legend_type_x=[0, 0, 5, 5],
              legend_type_y=[0, 5, 0, 5] ,
                             
              # presentation
              xsize = 7.0,
              ysize = 7.0,
              x_translate = 0.0,
              y_translate = 0.0,
              xmax = "",
              ymax = "",
              xmin = "",
              ymin = 0,
              xlog = "",
              ylog = "",
              clip = 0,
              colors = ["1 0 0", "0 0 1", "0 .5 0", "1 0 1", "0 1 0", "0 0 1", "0 1 1", "1 1 0", ".5 0 0"],
              # set colors for each benchmark
              scolors = [],
              curve_name = "",
               
              ):

    # Figure out which graph number we are
    global graph_counter
    data_graph = graph_counter  # used to plot data
    position_graph = graph_counter + 1  # use to position titles, etc
    graph_counter += 2 
    counter = 1.0

    output = ""
    output += "graph %d x_translate %f y_translate %f\n" % (data_graph, x_translate, y_translate)
    if clip:
        output += "clip\n"
    output += "graph %d clip x_translate %f y_translate %f\n" % (position_graph, x_translate, y_translate)
    if (title != ""):
        output += "graph %d title y %d font %s fontsize %s : %s\n" % (position_graph, title_y, title_font, title_fontsize, title)

    # place legends (using the position graph)
    output += "graph %d\n" % position_graph

    if legend_type != "":
        legend = "on"
        output += "legend custom "
    else:
        if legend != "on":
            legend = "off"
        output += "legend %s defaults %s font %s fontsize %s" % (legend, legend_default, legend_font, legend_fontsize)
        if (legend_x != ""):
            output += " x %s" % legend_x
        if (legend_y != ""):
            output += " y %s" % legend_y
    output += "\n"

    if legend_type != "":
        if len(bar_segment_labels) > 1:
#            output += "newcurve pts 0 0 0 3 marktype none linetype solid linethickness %f label : %s\n" % \
#                      (line_thickness, curve_name)

            for bar_num in range(len(bar_segment_labels)):
                output += "curve " + str(bar_num) + " marktype xbar marksize 1 5 pattern %s cfill %s clip\n" % (patterns[bar_num%len(patterns)], colors[bar_num%len(colors)])
                output += "label x %d y %d fontsize 9 hjl vjt : %s\n" %(int(legend_x) + legend_type_x[bar_num], int(legend_y) + legend_type_y[bar_num], bar_segment_labels[bar_num]) 
                
    else:
        if len(bar_segment_labels) > 1:     # bar legend - only if there is more than one type of bar
            for bar_num in range(len(bar_segment_labels)):
                output += "newcurve pts 0 0 0 3 marktype none linetype solid linethickness %f label : %s\n" % \
                          (line_thickness, curve_name)

                output += "newcurve pts 0 0 marktype xbar marksize 1 5 pattern %s cfill %s label : %s\n" % \
                          (patterns[bar_num%len(patterns)], colors[bar_num%len(colors)], bar_segment_labels[bar_num])


    if graph_type == "bar":
        stack_num = 0
        for stack in data:
            curve_value = stack[0]
            stack_name = stack[1]
            bars = stack[2:]
            x_begin = counter
            x_end = counter
            bar_num = 0  # should this be this way
            for bar in bars:
                bar_name = bar[0]
                components = bar[1:]
                for component in components:
                    # if it is a list, take the first element
                    if (type(component) is TupleType) or (type(component) is ListType):
                        value = component[0]
                    else:
                        value = component

                    if scolors == []:
                      output += "graph %d newcurve marksize 1 1 marktype xbar pattern %s cfill %s pts %f %f\n" % \
                                (data_graph, patterns[bar_num%len(patterns)], colors[bar_num%len(colors)], counter, value)
                    else:
                      output += "graph %d newcurve marksize 1 1 marktype xbar pattern %s cfill %s pts %f %f\n" % \
                                (data_graph, patterns[bar_num%len(patterns)], scolors[stack_num%len(scolors)], counter, value)

                    # error bars
                    if (type(component) is TupleType) or (type(component) is ListType):
                        output += "graph %d newcurve marksize 0.5 1 marktype none y_epts %f %f %f %f\n" % \
                                  (data_graph, counter, value, component[1], component[2])

                    bar_num += 1

                # bar name 
                if bar_name_rotate == 0:
                    output += "graph %d newstring fontsize %s x %f y -2.5 hjc vjt : %s\n" % (position_graph, bar_name_font_size, counter, bar_name)
                else:
                    output += "graph %d newstring fontsize %s x %f y -2.5 hjr vjc rotate %f : %s\n" % (position_graph, bar_name_font_size, counter, bar_name_rotate, bar_name)

                x_end = counter
                counter += bar_space
            counter = counter + stack_space
            average = (x_end+x_begin) / 2.0
            output += "graph %d newcurve marksize 1 1 marktype none linetype solid linethickness %f pts %f %f %f %f\n" % \
                                (data_graph, line_thickness, x_begin-0.7, curve_value, x_end+0.7, curve_value)
	    if stack_name_rotate == 0:
	            output += "graph %d newstring fontsize %s hjc vjt x %f y %f : %s\n" % (position_graph, stack_name_font_size, average, -stack_name_location, stack_name)
	    else:
	            output += "graph %d newstring fontsize %s hjr vjt x %f y %f rotate %f : %s\n" % (position_graph, stack_name_font_size, average, -stack_name_location, stack_name_rotate, stack_name)

            stack_num += 1
            
    # x- and y-axis: sizes and ranges
    output += "graph %d\n" % (position_graph)
    output += "xaxis size %f min 0 nodraw max %f\n" % (xsize, counter)
    output += "yaxis size %f min 0 nodraw max 100\n" % (ysize)

    output += "graph %d\n" % (data_graph)
    output += "xaxis size %f\n" % (xsize)
    output += "yaxis size %f\n" % (ysize)
    if graph_type == "bar":
        xmin = 0
        output += "xaxis no_auto_hash_labels no_draw_hash_marks max %f\n" % (counter)
        output += "yaxis grid_lines\n"
        if grid_gray != "":
            output += "yaxis grid_gray " + grid_gray + "\n"

    

    if (ymax != ""):
        output += "yaxis max %f\n" % ymax
    if (xmax != ""):
        output += "xaxis max %f\n" % xmax
    if (ymin != ""):
        output += "yaxis min %f\n" % ymin
    if (xmin != ""):
        output += "xaxis min %f\n" % xmin
    if (xlog != ""):
        output += "xaxis log log_base %d\n" % (xlog) # xlog is the base
    if (ylog != ""):
        output += "yaxis log log_base %d\n" % (ylog) # ylog is the base

    # hashes (always on the data graph)
    output += "graph %d\n" % (data_graph)
    if len(xhash_marks) > 1:
        output += "xaxis no_auto_hash_marks\n"
        for mark in xhash_marks:
            output += "xaxis hash_at %s hash_label at %s : %s\n" % (mark, mark, mark)
    if len(yhash_marks) > 1:
        output += "yaxis no_auto_hash_marks\n"
        index = 0
        for mark in yhash_marks:
            output += "yaxis hash_at %s hash_label at %s : %s\n" % (mark, mark, yhash_names[index])
            index += 1
    if yhash != "":
        output += "yaxis hash %f\n" % (yhash)
    if ymhash != "":
        output += "yaxis mhash %f\n" % (ymhash)
    if yhash_format != "":
        output += "yaxis hash_format %s\n" % (yhash_format)

    output += "xaxis hash_labels font %s fontsize %s\n" % (label_font, label_fontsize); 
    output += "yaxis hash_labels font %s fontsize %s\n" % (label_font, label_fontsize);

    # axis labels (position graph)
    output += "graph %d\n" % (position_graph) 

    if xlabel_location != []:
        output += "graph %d\n" % (position_graph) # put us in the data independent scale
        label_pos = "y -%f " % (xlabel_location) # no newline
    else:
        output += "graph %d\n" % (data_graph)
        label_pos = ""
    output += "xaxis draw_axis_label label %s font %s fontsize %s : %s\n" % (label_pos, label_font, label_fontsize, xlabel)

    if ylabel_location != []:
        output += "graph %d\n" % (position_graph) # put us in the data independent scale
        label_pos += " x -%f " % (ylabel_location) # no newline
    else:
        output += "graph %d\n" % (data_graph)
        label_pos = ""
    output += "yaxis draw_axis_label label %s font %s fontsize %s : %s\n" % (label_pos, label_font, label_fontsize, ylabel)

    output += "graph %d\n" % (data_graph)
    return output

    
# generate .eps, .ps, and .pdf
def run_jgraph(input_str, base_filename):

  
    jgr_file = open("%s.jgr" % base_filename, "w")
    jgr_file.write(input_str)
    jgr_file.close()

    # generate .eps (ghostview-able)
    (in_file, out_file) = os.popen2("~/Tools/jgraph/jgraph")
    in_file.write(input_str)
    in_file.close()

    eps_file = open("%s.eps" % base_filename, "w")
    eps_file.writelines(out_file.readlines())
    eps_file.close()

    # generate .pdf
    os.system("epstopdf %s.eps" % base_filename)
        
    # generate .ps (lpr-able)
    (in_file, out_file) = os.popen2("~/Tools/jgraph/jgraph -P")
    in_file.write(input_str)
    in_file.close()

    ps_file = open("%s.ps" % base_filename, "w")
    ps_file.writelines(out_file.readlines())
    ps_file.close()

    # generate .pdf
#    os.system("ps2pdf %s.ps" % base_filename)

    # generate .gif
#    (in_file, out_file) = os.popen2("/p/multifacet/scripts/jgrtogif 1")
#    in_file.write(input_str)
#    in_file.close()

#    eps_file = open("%s.gif" % base_filename, "w")
#    eps_file.writelines(out_file.readlines())
#    eps_file.close()

    # generate .epsi
#    os.system("ps2epsi %s.ps" % base_filename)

# generates a .eps file from a .jgr file
def run_jgraph_from_file(input_filename, base_filename):

    input_str = ""
    jgr_file = open("%s.jgr" % input_filename, "r")
    for line in jgr_file.readlines():
        input_str += line
    jgr_file.close()

    # generate .eps (ghostview-able)
    (in_file, out_file) = os.popen2("~/Tools/jgraph/jgraph")
    in_file.write(input_str)
    in_file.close()

    eps_file = open("%s.eps" % base_filename, "w")
    eps_file.writelines(out_file.readlines())
    eps_file.close()
        

##############################
# Note: The linreg() function for linear regression was taken from a
# web page "Simple Recipes in Python" by William Park
# http://www.python.org/topics/scicomp/recipes_in_python.html

"""
Returns coefficients to the regression line 'y=ax+b' from x[] and
y[].  Basically, it solves 
    Sxx a + Sx b = Sxy
     Sx a +  N b = Sy
where Sxy = \sum_i x_i y_i, Sx = \sum_i x_i, and Sy = \sum_i y_i.  The
solution is
    a = (Sxy N - Sy Sx)/det
    b = (Sxx Sy - Sx Sxy)/det
where det = Sxx N - Sx^2.  In addition,
    Var|a| = s^2 |Sxx Sx|^-1 = s^2 | N  -Sx| / det
       |b|       |Sx  N |          |-Sx Sxx|
    s^2 = {\sum_i (y_i - \hat{y_i})^2 \over N-2}
        = {\sum_i (y_i - ax_i - b)^2 \over N-2}
        = residual / (N-2)
    R^2 = 1 - {\sum_i (y_i - \hat{y_i})^2 \over \sum_i (y_i - \mean{y})^2}
        = 1 - residual/meanerror

It also prints to <stdout> few other data,
    N, a, b, R^2, s^2,
which are useful in assessing the confidence of estimation.
"""
def linreg(X, Y):
    from math import sqrt
    if len(X) != len(Y):  raise ValueError, 'unequal length'

    N = len(X)
    Sx = Sy = Sxx = Syy = Sxy = 0.0
    for x, y in map(None, X, Y):
        Sx = Sx + x
        Sy = Sy + y
        Sxx = Sxx + x*x
        Syy = Syy + y*y
        Sxy = Sxy + x*y
    det = Sxx * N - Sx * Sx
    a, b = (Sxy * N - Sy * Sx)/det, (Sxx * Sy - Sx * Sxy)/det

    meanerror = residual = 0.0
    for x, y in map(None, X, Y):
        meanerror = meanerror + (y - Sy/N)**2
        residual = residual + (y - a * x - b)**2
#    RR = 1 - residual/meanerror
    ss = residual / (N-2)
    Var_a, Var_b = ss * N / det, ss * Sxx / det
    
#    print "y=ax+b"
#    print "N= %d" % N
#    print "a= %g \\pm t_{%d;\\alpha/2} %g" % (a, N-2, sqrt(Var_a))
#    print "b= %g \\pm t_{%d;\\alpha/2} %g" % (b, N-2, sqrt(Var_b))
#    print "R^2= %g" % RR
#    print "s^2= %g" % ss
    
    return a, b

##############################
# Code to calculate exponential regressions using a transformation and
# a linear regression

def exp_regress(X, Y):
    # map into logarithmic space
    Y_prime = map(math.log, Y)

    # perform a linear regression in log space
    a, b = linreg(X, Y_prime)

    # Calculate the rate of growth. # The continuously compounding
    # rate equation for r:
    #       F = P*e^(Tr)   --->   r = ln(F/P) / T
    # where F is the final value, P is the starting value, T is time,
    # and r is the rate

    # Note: a, the slope of the fit, is the rate of growth of the
    # exponential curve.  This is only true because we're using the
    # natural logarithm as the base of our transformation

    rate = a
    
    # calculate the smooth line in log space
    Y_fit_prime = map(lambda x:(a*x)+b, X)

    # translate the log space back into original coordinates
    Y_fit = map(lambda x:math.pow(math.e, x), Y_fit_prime)
    
    return Y_fit, rate

#### Function for calculating confidence intervals
def t_distribution(v):
    if v > len(t_distribution_95_percent_lookup_table):
        return 1.96 # this is the value in the limit
    else:
        return t_distribution_95_percent_lookup_table[v-1]

def confidence_interval_95_percent(lst):
    n = len(lst)
    sd = stddev(lst) # standard deviation
    se = sd / math.sqrt(n) # standard error
    confidence_interval_95p = se * t_distribution(n-1)
    return confidence_interval_95p

# Note: for n < 5, the confidence interval is actually larger than the
# standard deviation.  At about n=6 is where the two are about the
# same, and around n=18 is where the 95% confidence interval is about
# half the standard deviation.  At n=60 the 95% confidence interval is
# about 1/4th the standard deviation.  The above data can be found by
# using the following code:

#for n in range(2, 100):
#    sd = 1
#    se = sd / math.sqrt(n) # standard error
#    confidence_interval_95p = se * t_distribution(n-1)
#    print n, confidence_interval_95p


# T-distribution table used in calculating 95% confidence intervals.
# The alpha for the table is 0.025 which corresponds to a 95%
# confidence interval.  (Note: a C-language stats package was used to
# generate this table, but it can also be calculated using Microsoft
# Excel's TINV() function.)

t_distribution_95_percent_lookup_table = (
    12.7062,
    4.30265,
    3.18245,
    2.77645,
    2.57058,
    2.44691,
    2.36462,
    2.306,
    2.26216,
    2.22814,
    2.20099,
    2.17881,
    2.16037,
    2.14479,
    2.13145,
    2.11991,
    2.10982,
    2.10092,
    2.09302,
    2.08596,
    2.07961,
    2.07387,
    2.06866,
    2.0639,
    2.05954,
    2.05553,
    2.05183,
    2.04841,
    2.04523,
    2.04227,
    2.03951,
    2.03693,
    2.03452,
    2.03224,
    2.03011,
    2.02809,
    2.02619,
    2.02439,
    2.02269,
    2.02108,
    2.01954,
    2.01808,
    2.01669,
    2.01537,
    2.0141,
    2.0129,
    2.01174,
    2.01063,
    2.00958,
    2.00856,
    2.00758,
    2.00665,
    2.00575,
    2.00488,
    2.00404,
    2.00324,
    2.00247,
    2.00172,
    2.001,
    2.0003,
    1.99962,
    1.99897,
    1.99834,
    1.99773,
    1.99714,
    1.99656,
    1.99601,
    1.99547,
    1.99495,
    1.99444,
    1.99394,
    1.99346,
    1.993,
    1.99254,
    1.9921,
    1.99167,
    1.99125,
    1.99085,
    1.99045,
    1.99006,
    1.98969,
    1.98932,
    1.98896,
    1.98861,
    1.98827,
    1.98793,
    1.98761,
    1.98729,
    1.98698,
    1.98667,
    1.98638,
    1.98609,
    1.9858,
    1.98552,
    1.98525,
    1.98498,
    1.98472,
    1.98447,
    1.98422,
    )
