import sys
import argparse
import os
import subprocess
import mk_table
import statistics

def analyze_interface_static(stats):
    numBranch = max ([int(s["numBranch"]) for s in stats])
    numVars = max ([int(s["numVars"]) for s in stats])
    return (numBranch, numVars)

def filename_to_dt_lib(filename: str):
    path = filename.split('/')
    method_str = path[-1]
    datatype_name = method_str.split('_')[0]
    lib_name = method_str.split('_')[1]
    return (datatype_name, lib_name)

def num_total_avg (l):
    return (len(l),
            "{:.2f}".format(sum(l)),
            "{:.2f}".format(statistics.mean(l)))

def analyze_interface_dynamic(stat):
    numQuery = int(stat["numQuery"])
    tTypeCheck = float(stat["tTypeCheck"])
    sizeA = int(statistics.mean([int(s["sizeA"]) for s in stat["totalInclusionStat"]]))
    numInclusion = len(stat["totalInclusionStat"])
    tTrans = sum([float(s["tTrans"]) for s in stat["totalInclusionStat"]])
    tInclusion = sum([float(s["tInclusion"]) for s in stat["totalInclusionStat"]])
    # xx = [s for s in stat["totalInclusionStat"]]
    # xx.sort(key=lambda x: x["tInclusion"])
    # print(xx)
    tOther = (tTypeCheck - tInclusion - tTrans)
    # print("tTrans:{}(s) tInclusion:{}(s) tTypeCheck:{}(s) tOthers:{}(s)".format(
    #     tTrans, tInclusion, tTypeCheck, tOther
    # ))
    return {
        "interfaceDynamic": stat["interfaceDynamic"],
        "numQuery": str(numQuery),
        "numInclusion": str(numInclusion),
        "sizeA": str(sizeA),
        "tTrans": "{:.2f}".format(tTrans),
        "tInclusion": "{:.2f}".format(tInclusion),
        "tTypeCheck": "{:.2f}".format(tTypeCheck),
        "tOther": "{:.2f}".format(tOther)
    }

def analyze_dynamic(stats):
    res = [ analyze_interface_dynamic(s) for s in stats]
    res.sort(key=lambda x: float(x["tTypeCheck"]), reverse=True)
    return res[0]

def get_prog_stat_by_name(stats, name):
    # print(stats)
    # print(name)
    for s in stats:
        if s["interface"] + ".ml" == name:
            return (s)
    print("never happen")
    exit(1)

def get_total_time(names, stat):
    # print(names)
    time = 0.0
    for s in names:
        name = s["interface"] + ".ml"
        # print(name)
        # print(stat)
        matches_a = [x for x in stat if x["interfaceDynamic"] == name]
        if len(matches_a) == 1:
            time = time + float(matches_a[0]["tTypeCheck"])
        # else:
            # print(name, matches_a)
            # exit(0)
            # return "??"
    return "{:.2f}".format(time)

def analyze_for_display(col):
    br = col.get("numBranch", " ")
    par = col.get("numParam", " ")
    app = col.get("numApp", " ")
    # br = '{:2d}'.format(int(col.get("numBranch", "0")))
    # par = '{:2d}'.format(int(col.get("numParam", "0")))
    # app = '{:2d}'.format(int(col.get("numApp", "0")))
    col["numBrParApp"] = "({}, {}, {})".format(br, par, app)
    gh = col.get("numGhost", " ")
    sizeI = col.get("sizeRI", " ")
    col["GhsizeRI"] = "({}, {})".format(gh, sizeI)
    gh = col.get("numGhost", " ")
    sizeI = col.get("sizeRI", " ")
    if "numInclusion" in col.keys():
        numInclusion = int(col["numInclusion"])
        tInclusion = float(col["tInclusion"])
        col["tInclusionAvg"] = "{:.2f}".format((tInclusion / numInclusion))
        # print(tInclusion, numInclusion, col["tInclusionAvg"])
    return

def analyze_stat(paths, j):
    cols = []
    static_j = j["static"]
    dynamic_j = j["dynamic"]
    for filename in paths:
        dt, lib = filename_to_dt_lib(filename)
        matches = [x for x in static_j if x["dt"] == dt and x["lib"] == lib]
        static_stat = matches[0]
        # print(static_stat)
        # numBranch, numVars = analyze_interface_static(static_stat["interfaceStatStatic"])
        # print(static_stat)
        col = static_stat.copy()
        col["dt"] = dt
        col["lib"] = lib
        col["numMethod"] = str(len(static_stat["interfaceStatStatic"]))
        # col["numBranch"] = numBranch
        # col["numVars"] = numVars
        matches = [x for x in dynamic_j if x["dtDynamic"] == dt and x["libDynamic"] == lib]
        if len(matches) == 1:
            stat_d = matches[0]["interfaceStatDynamic"]
            # print( stat_d)
            # print(dt, lib)
            col["tTotal"] = get_total_time(static_stat["interfaceStatStatic"],  stat_d)
            res_a = analyze_dynamic( stat_d)
            # print(res_a)
            col.update(res_a)
            # col["numQuery"] = res["numQuery"]
            # col["numInclusion"] = res["numInclusion"]
            # col["sizeA"] = res["sizeA"]
            # col["tTrans"] = res["tTrans"]
            # col["tInclusion"] = res["tInclusion"]
            # print(dt, lib)
            # print(static_stat)
            res_s = get_prog_stat_by_name(static_stat["interfaceStatStatic"], res_a["interfaceDynamic"])
            col.update(res_s)
            # col["numBranch"] = numBranch
            # col["numVars"] = numVars
            analyze_for_display(col)
        elif len(matches) > 1:
            print("bad dynamic")
            exit(1)
        cols.append(col)
    return cols

# def analyze_one (stat):
#     num_smt, time_smt, time_smt_avg = num_total_avg(stat["smt_query_time_record"])
#     num_reg, time_reg, time_reg_avg = num_total_avg(stat["inclusion_query_time_record"])
#     stat["num_smt"] = num_smt
#     stat["time_smt"] = time_smt
#     stat["time_smt_avg"] = time_smt_avg
#     stat["num_reg"] = num_reg
#     stat["time_reg"] = time_reg
#     stat["time_reg_avg"] = time_reg_avg
#     return stat

# def flatten(l):
#     return [item for sublist in l for item in sublist]

# def merge_stat(stats):
#     res = {}
#     res["typecheck_time"] = "{:.2f}".format(sum ([float(s["typecheck_time"]) for s in stats]))
#     res["smt_query_time_record"] = flatten ([s["smt_query_time_record"] for s in stats])
#     res["inclusion_query_time_record"] = flatten ([s["inclusion_query_time_record"] for s in stats])

#     res["pty_time_record"] = flatten ([s["pty_time_record"] for s in stats])
#     res["am_time_record"] = flatten ([s["am_time_record"] for s in stats])

#     res["num_candicate_minterm_record"] = flatten ([s["num_candicate_minterm_record"] for s in stats])
#     res["filter_time_record"] = flatten ([s["filter_time_record"] for s in stats])

#     res["inclusion_alphabet_record"] = flatten ([s["inclusion_alphabet_record"] for s in stats])
#     res["inclusion_automaton_size_record"] = flatten ([s["inclusion_automaton_size_record"] for s in stats])

#     res["code_size"] = sum ([int(s["code_size"]) for s in stats])
#     res["code_branchs"] = sum ([int(s["code_branchs"]) for s in stats])
#     res["code_effects"] = max ([int(s["code_effects"]) for s in stats])
#     res["rty_lits"] = sum ([int(s["rty_lits"]) for s in stats])
#     res["rty_events"] = sum ([int(s["rty_events"]) for s in stats])
#     res["max_inclusion_alphabet"] = max ([int(s["max_inclusion_alphabet"]) for s in stats])
#     res["max_inclusion_automaton_size"] = max ([int(s["max_inclusion_automaton_size"]) for s in stats])
#     return res

# def analyze (stat):
#     if_well_typed = all (bool(s["if_well_typed"]) for s in stat)
#     if not if_well_typed:
#         print("the type check fails")
#         exit(1)
#     stat = merge_stat([s["stat"] for s in stat])
#     # if len(stat) != 1:
#     #     print("each benchmark should has one function implementation")
#     #     exit(1)
#     # stat = stat[0]["stat"]
#     num_smt, time_smt, time_smt_avg = num_total_avg(stat["smt_query_time_record"])
#     num_reg, time_reg, time_reg_avg = num_total_avg(stat["inclusion_query_time_record"])

#     num_pty, time_pty, time_pty_avg = num_total_avg(stat["pty_time_record"])
#     num_am, time_am, time_am_avg = num_total_avg(stat["am_time_record"])

#     max_num_candicate_minterm = max ([int(i) for i in stat["num_candicate_minterm_record"] ])
#     avg_num_candicate_minterm = int(statistics.mean([int(i) for i in stat["num_candicate_minterm_record"] ]))
#     avg_inclusion_automaton_size = int(statistics.mean([int(i) for i in stat["inclusion_automaton_size_record"] ]))
#     num_filter, time_filter, time_filter_avg = num_total_avg(stat["filter_time_record"])

#     stat["num_smt"] = num_smt
#     stat["time_smt"] = time_smt
#     stat["time_smt_avg"] = time_smt_avg
#     stat["num_reg"] = num_reg
#     stat["time_reg"] = time_reg
#     stat["time_reg_avg"] = time_reg_avg

#     stat["num_pty"] = num_pty
#     stat["time_pty"] = time_pty
#     stat["time_pty_avg"] = time_pty_avg
#     stat["num_am"] = num_am
#     stat["time_am"] = time_am
#     stat["time_am_avg"] = time_am_avg

#     stat["num_filter"] = num_filter
#     stat["time_filter"] = time_filter
#     stat["time_filter_avg"] = time_filter_avg

#     stat["time_am_without_filter"] = "{:.2f}".format(float(stat["time_am"]) - float(stat["time_filter"]))

#     stat["max_num_candicate_minterm"] = max_num_candicate_minterm
#     stat["avg_num_candicate_minterm"] = avg_num_candicate_minterm
#     stat["avg_inclusion_automaton_size"] = avg_inclusion_automaton_size

#     return stat
