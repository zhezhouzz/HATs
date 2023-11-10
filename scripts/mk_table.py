import sys
import argparse
import os
import json
from tabulate import tabulate

# headers = ["", "Recursive", "#LocalVar" , "#OP" , "#Q_{SMT}" , "#Q_{automata}" , "(max. Char, Size)" ,
#            "smt total (avg. time)(s)", "automata total (avg. time)(s)"]

latex_headers = ["Datatype", "Library",
                 "\\#Ghost", "size$_{I}$",
                 "\\#Branch", "\\#Var" ,
                 "\\#SAT" , "\\#Inclusion", "avg. size$_{A}$" ,
                 "time$_{\\text{trans}}$ (s) ", "time$_{A}$ (s)"]

def print_header(head):
    print(" & ".join(head) + "\\\\")

def mk_col (dt: str, lib: str, numBranch: int, numVars: int,
            numGhost: int, sizeRI: int, numQuery: int, numInclusion: int, sizeA: int,
            tTrans: float, tInclusion: float):
    return {"dt": dt, "lib": lib,
            "numGhost": numGhost, "sizeRI": sizeRI,
            "numBranch": numBranch, "numVars": numVars,
            "numQuery": numQuery, "numInclusion": numInclusion, "sizeA": sizeA,
            "tTrans":tTrans, "tInclusion":tInclusion }

# def show_source(source, name):
#     tab = {"Okisaki": "*", "Miltner": "★", "ours": ""}
#     return "{} {}".format(name, tab[source])

def textsf(content: str):
    return "\\textsf{" + content + "}"

def multirow(num: int, content: str):
    return "\\multirow{" + str(num) + "}{*}{" + content + "}"

def print_col(print_dt_num: int, col):
    dt_str = ""
    if print_dt_num > 0:
        print("\\midrule")
        dt_str = multirow(print_dt_num, textsf(col["dt"]))
    lib_str = textsf(col["lib"])
    res = "{} & {} & {} & {} & {} & {} & {} & {} & {} & {:.2f} & {:.2f} \\\\".format(
        dt_str, lib_str, col["numBranch"], col["numVars"], col["numGhost"],
        col["sizeRI"], col["numQuery"], col["numInclusion"], col["sizeA"],
        col["tTrans"], col["tInclusion"])
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
    print_header(latex_headers)
    nums = analysis_col_dts(cols)
    for i in range(len(cols)):
        print_col(nums[i], cols[i])
    return
