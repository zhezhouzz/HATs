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
        col = static_stat.copy()
        col["dt"] = dt
        col["lib"] = lib
        col["numMethod"] = str(len(static_stat["interfaceStatStatic"]))
        matches = [x for x in dynamic_j if x["dtDynamic"] == dt and x["libDynamic"] == lib]
        if len(matches) == 1:
            stat_d = matches[0]["interfaceStatDynamic"]
            # print( stat_d)
            # print(dt, lib)
            col["tTotal"] = get_total_time(static_stat["interfaceStatStatic"],  stat_d)
            res_a = analyze_dynamic( stat_d)
            col.update(res_a)
            res_s = get_prog_stat_by_name(static_stat["interfaceStatStatic"], res_a["interfaceDynamic"])
            col.update(res_s)
            analyze_for_display(col)
        elif len(matches) > 1:
            print("bad dynamic")
            exit(1)
        cols.append(col)
    return cols

def find_one(l, f):
    matches = [x for x in l if f(x)]
    if len(matches) == 1:
        return matches[0].copy()
    elif len(matches) > 1:
        print("bad list find")
        exit(1)
    else:
        print("no result")
        exit(1)

def analyze_details_stat(paths, j):
    cols = []
    static_j = j["static"]
    dynamic_j = j["dynamic"]
    # print(static_j)
    # exit(1)
    for filename in paths:
        dt, lib = filename_to_dt_lib(filename)
        static_stat = find_one(static_j, lambda x: x["dt"] == dt and x["lib"] == lib)
        stat_d = find_one(dynamic_j, lambda x: x["dtDynamic"] == dt and x["libDynamic"] == lib)["interfaceStatDynamic"]
        # print(len( static_stat["interfaceStatStatic"]))
        for interface_stat in static_stat["interfaceStatStatic"]:
            col = interface_stat.copy()
            col["dt"] = dt
            col["lib"] = lib
            col.update(static_stat)
            print(stat_d)
            print(dt, lib)
            print(col["interface"])
            stat_d_one = find_one(stat_d, lambda x: x["interfaceDynamic"] == "{}.ml".format(col["interface"]))
            col.update(stat_d_one)
            analyze_for_display(col)
            print(col)
            cols.append(col)
    print(len(cols))
    return cols

