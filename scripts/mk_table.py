import sys
import argparse
import os
import json
from tabulate import tabulate

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

# format_header = "\n\n\\begin{tabular}{ccc|cc|c||ccc|ccc|cc}\n\\toprule"
format_header = "\n\n\\begin{tabular}{cc|ccc|c||cc|ccc|cc}\n\\toprule"

header = ["dt", "lib", "numMethod",
          "numGhost", "sizeRI",
          # "GhsizeRI",
          "tTotal",
          "numBranch", "numApp",
          # "numBrParApp",
          "numQuery", "numInclusion", "sizeA",
          "tTrans", "tInclusion"]

# latex_headers = ["Datatype", "Library",
#                  "\\#Method", "\\#Ghost", "size$_{I}$",
#                  "\\#Br", "\\#Var" ,
#                  "\\#SAT" , "\\#Incl", "avg. size$_{A}$" ,
#                  "t$_{\\text{trans}}$ (s) ", "t$_{A}$ (s)"]

def print_header():
    print(" & ".join([latex_headers_map[name] for name in header]) + "\\\\")

# def mk_col (dt: str, lib: str, numMethod: int,
#             numGhost: int, sizeRI: int,
#             numBranch: int, numVars: int,
#             numQuery: int, numInclusion: int, sizeA: int,
#             tTrans: float, tInclusion: float):
#     return {"dt": dt, "lib": lib,
#             "numMethod": numMethod, "numGhost": numGhost, "sizeRI": sizeRI,
#             "numBranch": numBranch, "numVars": numVars,
#             "numQuery": numQuery, "numInclusion": numInclusion, "sizeA": sizeA,
#             "tTrans":tTrans, "tInclusion":tInclusion }

# def show_source(source, name):
#     tab = {"Okisaki": "*", "Miltner": "★", "ours": ""}
#     return "{} {}".format(name, tab[source])

def print_col(print_dt_num: int, col):
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

def print_cols(cols):
    print(format_header)
    print_header()
    nums = analysis_col_dts(cols)
    for i in range(len(cols)):
        print_col(nums[i], cols[i])
    print("\\bottomrule\n\\end{tabular}\n\n")
    return
