import sys
import argparse
import os
import subprocess

import statistics

def num_total_avg (l):
    return (len(l),
            "{:.2f}".format(sum(l)),
            "{:.2f}".format(statistics.mean(l)))

def analyze (stat):
    if len(stat) != 1:
        print("each benchmark should has one function implementation")
        exit(1)
    stat = stat[0]["stat"]
    num_smt, time_smt, time_smt_avg = num_total_avg(stat["smt_query_time_record"])
    num_reg, time_reg, time_reg_avg = num_total_avg(stat["inclusion_query_time_record"])
    stat["num_smt"] = num_smt
    stat["time_smt"] = time_smt
    stat["time_smt_avg"] = time_smt_avg
    stat["num_reg"] = num_reg
    stat["time_reg"] = time_reg
    stat["time_reg_avg"] = time_reg_avg
    return stat
