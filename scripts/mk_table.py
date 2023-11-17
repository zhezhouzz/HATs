import sys
import argparse
import os
import json
# from tabulate import tabulate

# headers = ["", "Recursive", "#LocalVar" , "#OP" , "#Q_{SMT}" , "#Q_{automata}" , "(max. Char, Size)" ,
#            "smt total (avg. time)(s)", "automata total (avg. time)(s)"]

# latex_headers = ["Datatype", "Library",
#                  "\\#Method", "\\#Ghost", "size$_{I}$",
#                  "\\#Br", "\\#Var" ,
#                  "\\#SAT" , "\\#Incl", "avg. size$_{A}$" ,
#                  "t$_{\\text{trans}}$ (s) ", "t$_{A}$ (s)"]

def textsf(content: str):
    return "\\textsf{" + content + "}"

def textbf(content: str):
    return "\\textbf{" + content + "}"

def multirow(num: int, content: str):
    return "\\multirow{" + str(num) + "}{*}{" + content + "}"

latex_headers_map = {
    "dt": "Datatype",
    "lib": "Library",
    "interface": "Method",
    "numMethod": "\\#Method",
    "numGhost": "\\#Ghost",
    "sizeRI": "s$_{I}$",
    "GhsizeRI": "(\\#Gh, s$_{I})$",
    "numBranch": "\\#Branch",
    "numVars": "\\#Var",
    "numApp": "\\#App",
    "numParam": "\\#Par",
    "numBrParApp": "(\#Br, \#Pa, \#Ap)",
    "numQuery": "\\#SAT",
    "numInclusion": "\\#Inc",
    "sizeA": "avg. s$_{A}$" ,
    "tTrans": "t$_{\\text{SAT}}$ (s)",
    "tInclusion": "t$_{\\text{Inc}}$ (s)",
    "tInclusionAvg": "avg. t$_{\\text{Inc}}$ (s)",
    "tOther": "t$_{\\text{other}}$ (s)",
    "tTotal": "t$_{\\text{total}}$ (s)"
}

format_header = "\n\n\\begin{tabular}{cc|ccc|c||cc|ccc|cc}\n\\toprule"

header = ["dt", "lib", "numMethod",
          "numGhost", "sizeRI",
          # "GhsizeRI",
          "tTotal",
          "numBranch", "numApp",
          # "numBrParApp",
          "numQuery", "numInclusion", "sizeA",
          "tTrans", "tInclusion"]

details_format_header = "\n\n\\begin{tabular}{cc|cc|c||cc|ccc|cc}\n\\toprule"

details_header = ["dt", "lib",
                  "numGhost", "sizeRI",
                  "interface",
                  "numBranch", "numApp",
                  "numQuery", "numInclusion", "sizeA",
                  "tTrans", "tInclusion"]


def print_header(header):
    print(" & ".join([latex_headers_map[name] for name in header]) + "\\\\")

# def show_source(source, name):
#     tab = {"Okisaki": "*", "Miltner": "★", "ours": ""}
#     return "{} {}".format(name, tab[source])

def analysis_col_dts(cols):
    cur_dt = None
    res = [0] * len(cols)
    for i in range(len(cols) - 1, -1, -1):
        # print(cur_dt)
        col = cols[i]
        if cur_dt is None or cur_dt != col["dt"]:
            cur_dt = col["dt"]
            res[i] = 1
        else:
            res[i] = 1 + res[i + 1]
            res[i + 1] = 0
    return res

def print_col(header, print_dt_num: int, col):
    dt_str = ""
    if print_dt_num > 0:
        print("\\midrule")
        dt_str = multirow(print_dt_num, textsf(col["dt"]))
    lib_str = textsf(col["lib"])
    header_res = header[2:]
    strs = [ str(col.get(name, " ")) for name in header_res]
    rest = " & ".join(strs)
    res = "{} & {} & {} \\\\".format(dt_str, lib_str, rest)
    print(res)
    return

import re
def safe_print(s):
    return re.sub(r"_", "\_", s)

def print_details_col(header, print_dt_num: int, col):
    dt_str = ""
    if print_dt_num > 0:
        print("\\midrule")
        dt_str = multirow(print_dt_num, textsf(col["dt"]))
    col["interface"] = textsf(safe_print(col["interface"]))
    lib_str = textsf(col["lib"])
    header_res = header[2:]
    strs = [ str(col.get(name, " ")) for name in header_res]
    rest = " & ".join(strs)
    res = "{} & {} & {} \\\\".format(dt_str, lib_str, rest)
    print(res)
    return

def print_cols(format_header, header ,cols):
    print(format_header)
    print_header(header)
    nums = analysis_col_dts(cols)
    for i in range(len(cols)):
        print_col(header, nums[i], cols[i])
    print("\\bottomrule\n\\end{tabular}\n\n")
    return

def mk_table1(cols):
    print(format_header)
    print_header(header)
    nums = analysis_col_dts(cols)
    for i in range(len(cols)):
        print_col(header, nums[i], cols[i])
    print("\\bottomrule\n\\end{tabular}\n\n")
    return

def mk_table2(cols):
    print(details_format_header)
    print_header(details_header)
    nums = analysis_col_dts(cols)
    for i in range(len(cols)):
        print_details_col(details_header, nums[i], cols[i])
    print("\\bottomrule\n\\end{tabular}\n\n")
    return
