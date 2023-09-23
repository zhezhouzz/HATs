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

def load_stat (source):
    with open (stat_file) as f:
        j = json.load(f)
        stat = analyze.analyze(j)
        stat["source"] = source
        return analyze.analyze(j)
    exit(1)

def run_all_benchs(verbose):
    tab = benchs.load_benchmarks()
    res = {}
    for name, (source, path) in tab.items():
        run.typecheck(path, verbose)
        res[name] = load_stat (source)
    mk_table.show_latex_tab(res)
    return

def run_one_benchs(verbose, bench_name):
    tab = benchs.load_benchmarks()
    res = {}
    for name, (source, path) in tab.items():
        if bench_name == name:
            run.typecheck(path, verbose)
            res[name] = load_stat (source)
            mk_table.show_latex_tab(res)
            return
    exit(1)

def make_table(verbose, bench_name):
    tab = benchs.load_benchmarks()
    res = {}
    for name, (source, path) in tab.items():
        if bench_name == name:
            res[name] = load_stat(source)
            mk_table.show_latex_tab(res)
            return
    exit(1)

if __name__ == '__main__':
    verbose = False
    try:
        if sys.argv[1] == "verbose":
            verbose = True
    except:
        verbose = False
    if "table1" == sys.argv[2]:
        run_all_benchs(verbose)
    elif "make_table" == sys.argv[2]:
        make_table(verbose, sys.argv[3])
    elif "run_one" == sys.argv[2]:
        run_one_benchs(verbose, sys.argv[3])

