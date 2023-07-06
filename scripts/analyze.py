import sys
import argparse
import os
import subprocess

import statistics

def num_total_avg (l):
    return (len(l),
            "{:.2f}".format(sum(l)),
            "{:.2f}".format(statistics.mean(l)))

def analyze_one (stat):
    num_smt, time_smt, time_smt_avg = num_total_avg(stat["smt_query_time_record"])
    num_reg, time_reg, time_reg_avg = num_total_avg(stat["inclusion_query_time_record"])
    stat["num_smt"] = num_smt
    stat["time_smt"] = time_smt
    stat["time_smt_avg"] = time_smt_avg
    stat["num_reg"] = num_reg
    stat["time_reg"] = time_reg
    stat["time_reg_avg"] = time_reg_avg
    return stat

def flatten(l):
    return [item for sublist in l for item in sublist]

def merge_stat(stats):
    res = {}
    res["typecheck_time"] = "{:.2f}".format(sum ([float(s["typecheck_time"]) for s in stats]))
    res["smt_query_time_record"] = flatten ([s["smt_query_time_record"] for s in stats])
    res["inclusion_query_time_record"] = flatten ([s["inclusion_query_time_record"] for s in stats])

    res["pty_time_record"] = flatten ([s["pty_time_record"] for s in stats])
    res["am_time_record"] = flatten ([s["am_time_record"] for s in stats])

    res["num_candicate_minterm_record"] = flatten ([s["num_candicate_minterm_record"] for s in stats])
    res["filter_time_record"] = flatten ([s["filter_time_record"] for s in stats])

    res["inclusion_alphabet_record"] = flatten ([s["inclusion_alphabet_record"] for s in stats])
    res["inclusion_automaton_size_record"] = flatten ([s["inclusion_automaton_size_record"] for s in stats])

    res["code_size"] = sum ([int(s["code_size"]) for s in stats])
    res["code_branchs"] = sum ([int(s["code_branchs"]) for s in stats])
    res["code_effects"] = max ([int(s["code_effects"]) for s in stats])
    res["rty_lits"] = sum ([int(s["rty_lits"]) for s in stats])
    res["rty_events"] = sum ([int(s["rty_events"]) for s in stats])
    res["max_inclusion_alphabet"] = max ([int(s["max_inclusion_alphabet"]) for s in stats])
    res["max_inclusion_automaton_size"] = max ([int(s["max_inclusion_automaton_size"]) for s in stats])
    return res

def analyze (stat):
    if_well_typed = all (bool(s["if_well_typed"]) for s in stat)
    if not if_well_typed:
        print("the type check fails")
        exit(1)
    stat = merge_stat([s["stat"] for s in stat])
    # if len(stat) != 1:
    #     print("each benchmark should has one function implementation")
    #     exit(1)
    # stat = stat[0]["stat"]
    num_smt, time_smt, time_smt_avg = num_total_avg(stat["smt_query_time_record"])
    num_reg, time_reg, time_reg_avg = num_total_avg(stat["inclusion_query_time_record"])

    num_pty, time_pty, time_pty_avg = num_total_avg(stat["pty_time_record"])
    num_am, time_am, time_am_avg = num_total_avg(stat["am_time_record"])

    max_num_candicate_minterm = max ([int(i) for i in stat["num_candicate_minterm_record"] ])
    avg_num_candicate_minterm = int(statistics.mean([int(i) for i in stat["num_candicate_minterm_record"] ]))
    avg_inclusion_automaton_size = int(statistics.mean([int(i) for i in stat["inclusion_automaton_size_record"] ]))
    num_filter, time_filter, time_filter_avg = num_total_avg(stat["filter_time_record"])

    stat["num_smt"] = num_smt
    stat["time_smt"] = time_smt
    stat["time_smt_avg"] = time_smt_avg
    stat["num_reg"] = num_reg
    stat["time_reg"] = time_reg
    stat["time_reg_avg"] = time_reg_avg

    stat["num_pty"] = num_pty
    stat["time_pty"] = time_pty
    stat["time_pty_avg"] = time_pty_avg
    stat["num_am"] = num_am
    stat["time_am"] = time_am
    stat["time_am_avg"] = time_am_avg

    stat["num_filter"] = num_filter
    stat["time_filter"] = time_filter
    stat["time_filter_avg"] = time_filter_avg

    stat["time_am_without_filter"] = "{:.2f}".format(float(stat["time_am"]) - float(stat["time_filter"]))

    stat["max_num_candicate_minterm"] = max_num_candicate_minterm
    stat["avg_num_candicate_minterm"] = avg_num_candicate_minterm
    stat["avg_inclusion_automaton_size"] = avg_inclusion_automaton_size

    return stat
