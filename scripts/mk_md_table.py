import sys
import argparse
import os
import json
from tabulate import tabulate

def textsf(content: str):
    return "_" + content + "_"

def textbf(content: str):
    return "**" + content + "**"

def textsub(content: str):
    return "<sub>" + content + "</sub>"

def multirow(num: int, content: str):
    return "\\multirow{" + str(num) + "}{*}{" + content + "}"

latex_headers_map = {
    "dt": "ADT",
    "lib": "Library",
    "interface": "Method",
    "numMethod": "#Method",
    "numGhost": "#Ghost",
    "sizeRI": "s{}".format(textsub("I")),
    "GhsizeRI": "(#Gh, s{}".format(textsub("I")),
    "numBranch": "#Branch",
    "numVars": "#Var",
    "numApp": "#App",
    "numParam": "#Par",
    "numQuery": "#SAT",
    "numInclusion": "#FA{}".format(textsub("⊆")),
    "sizeA": "avg. s{}".format(textsub("FA")),
    "tTrans": "t{} (s)".format(textsub("SAT")),
    "tInclusion": "t{} (s)".format(textsub("FA⊆")),
    "tInclusionAvg": "avg. t{} (s)".format(textsub("FA⊆")),
    "tOther": "t{} (s)".format(textsub("other")),
    "tTotal": "t{} (s)".format(textsub("total"))
}

header = ["dt", "lib", "numMethod",
          "numGhost", "sizeRI",
          # "GhsizeRI",
          "tTotal",
          "numBranch", "numApp",
          # "numBrParApp",
          "numQuery", "numInclusion", "sizeA",
          "tTrans", "tInclusion"]

details_header = ["dt", "lib",
                  "numGhost", "sizeRI",
                  "interface",
                  "numBranch", "numApp",
                  "numQuery", "numInclusion", "sizeA",
                  "tTrans", "tInclusion"]


def print_header(header,lines):
    hh = [latex_headers_map[name] for name in header]
    # print(tabulate(lines, hh, tablefmt='orgtbl', numalign="left"))
    print(tabulate(lines, hh, tablefmt='github', numalign="left"))

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

def get_col(header, print_dt_num: int, col):
    dt_str = textsf(col["dt"])
    lib_str = textsf(col["lib"])
    header_res = header[2:]
    strs = [ str(col.get(name, " ")) for name in header_res]
    res = [dt_str, lib_str]
    return res + strs

import re
def safe_print(s):
    return re.sub(r"_", "\_", s)

def get_details_col(header, print_dt_num: int, col):
    dt_str = textsf(col["dt"])
    col["interface"] = textsf(safe_print(col["interface"]))
    lib_str = textsf(col["lib"])
    header_res = header[2:]
    strs = [ str(col.get(name, " ")) for name in header_res]
    return [dt_str, lib_str] + strs

def mk_table1(cols):
    nums = analysis_col_dts(cols)
    lines = []
    for i in range(len(cols)):
        lines.append(get_col(header, nums[i], cols[i]))
    print_header(header, lines)
    return

def mk_table2(cols):
    nums = analysis_col_dts(cols)
    lines = []
    for i in range(len(cols)):
        lines.append(get_details_col(details_header, nums[i], cols[i]))
    print_header(details_header, lines)
    return
