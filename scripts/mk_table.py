import sys
import argparse
import os
import json
from tabulate import tabulate

headers = ["", "Recursive", "#LocalVar" , "#OP" , "#Q_{SMT}" , "#Q_{automata}" , "(max. Char, Size)" ,
           "smt total (avg. time)(s)", "automata total (avg. time)(s)"]

latex_headers = ["", "\\#Branch", "\\#LVar" , "\\#Event", "\\#Lit", "\\#Query" , "avg. \\#Mt", "avg. size$_{A}$" ,
                 "time$_{\\text{trans}}$ (s) ", "time$_{A}$ (s)"]

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
        line = "{} & ${}$ & ${}$ & ${}$ & ${}$ & ${}$ & ${}$ & ${}$ & ${}$ & ${}$ \\\\".format(
            latex_name(name),
            # show_is_rec_latex(stat["is_rec"]),
            stat["code_branchs"],
            stat["code_size"],
            stat["rty_events"],
            stat["rty_lits"],
            # stat["code_effects"],
            # stat["num_pty"],
            stat["num_am"],
            stat["avg_num_candicate_minterm"],
            # stat["max_num_candicate_minterm"],
            # stat["max_inclusion_alphabet"],
            stat["avg_inclusion_automaton_size"],
            # stat["max_inclusion_automaton_size"],
            stat["time_filter"],
            stat["time_am_without_filter"]
        )
        print(line)
    print("\\bottomrule")
