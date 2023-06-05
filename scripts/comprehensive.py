import sys
import argparse
import os
import subprocess
import colored
import benchs
import run
import analyze
import mk_table
import json

meta_config_file = "meta-config.json"
stat_file = ".stat.json"

def run_all_benchs(verbose):
    tab = benchs.load_benchmarks()
    res = {}
    for name, (source, path) in tab.items():
        run.typecheck(path, verbose)
        with open (stat_file) as f:
            j = json.load(f)
            stat = analyze.analyze(j)
            stat["source"] = source
            res[name] = analyze.analyze(j)
            # break
    mk_table.show_latex_tab(res)
    return

if __name__ == '__main__':
    try:
        if sys.argv[2] == "verbose":
            verbose = True
    except:
        verbose = False
    if "table1" == sys.argv[1]:
        run_all_benchs(verbose)

