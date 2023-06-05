import sys
import argparse
import os
import json
from tabulate import tabulate

headers = ["", "Recursive", "#LocalVar" , "#OP" , "#Q_{SMT}" , "#Q_{automata}" , "(max. Char, Size)" ,
           "smt total (avg. time)(s)", "automata total (avg. time)(s)"]

latex_headers = ["", "(\\#LocalVar, \\#Lit)" , "\\#OP" , "\\#Q$_{SMT}$" , "\\#Q$_{A}$" , "max. size$_{A}$" ,
           "t$_{SMT}$ total (avg.)(s)", "t$_{A}$ total (avg.)(s)"]

def show_source(source, name):
    tab = {"Protocols": "⬦", "Algebraic Effects": "*",  "Datatypes": "◯", "leonidas": "★", "stlc": ""}
    return "{} {}".format(name, tab[source])

def show_is_rec(is_rec, branches):
    if is_rec:
        return [branches, "✓"]
    else:
        return [branches, ""]

def show_is_rec_latex(is_rec):
    if is_rec:
        return "$\\checkmark$"
    else:
        return ""

def show_data(data):
    print("\n")
    lines = []
    for (source, is_rec, res) in data:
        res = [show_source(source, res[0])] + show_is_rec(is_rec, res[1]) + res[2:]
        lines.append(res)
    print(tabulate(lines, headers, tablefmt='orgtbl', numalign="left"))

def latex_name(name):
    name = name.replace("_", "\_")
    name = "\\textsf{" + name + "}"
    # print(name)
    return name

def show_latex_tab(data):
    print("\n")
    header_str = " & ".join(latex_headers)
    print("""
\\toprule
 {}\\\\
\\midrule""".format(header_str))
    for name, stat in data.items():
        line = "{} & $({}, {})$ & ${}$ & ${}$ & ${}$ & ${}$ & $({},{})$ & $({},{})$ \\\\".format(
            latex_name(name),
            # show_is_rec_latex(stat["is_rec"]),
            stat["code_size"],stat["code_lits"],
            stat["code_effects"], stat["num_smt"], stat["num_reg"],
            # stat["max_inclusion_alphabet"],
            stat["max_inclusion_automaton_size"],
            stat["time_smt"], stat["time_smt_avg"],
            stat["time_reg"], stat["time_reg_avg"]
        )
        print(line)
    print("\\bottomrule")
