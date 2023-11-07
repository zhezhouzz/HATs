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
from pathlib import Path
import pathlib
import run_datatype

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

def load_benchmarks(path):
    # print(path)
    files = [str(f) for f in pathlib.Path().glob("{}/*_*".format(path)) if Path.is_dir(f)]
    # files = [str(f) for f in pathlib.Path().glob("{}/*.sh".format(path))]
    files.sort()
    # print(files)
    return files

def show_benchmarks(verbose, paths):
    for path in paths:
        run_datatype.print_datatype(run_datatype.load_datatype(path), verbose)

def show_one(verbose, path):
    run_datatype.print_datatype(run_datatype.load_datatype(path), verbose)

def ntypecheck_benchmarks(verbose, paths):
    for path in paths:
        run_datatype.ntypecheck_datatype(run_datatype.load_datatype(path), verbose)

def ntypecheck_one(verbose, path):
    run_datatype.ntypecheck_datatype(run_datatype.load_datatype(path), verbose)

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
    if "benchmarks" == sys.argv[2]:
        load_benchmarks(sys.argv[3])
    elif "ntyping" == sys.argv[2]:
        ntypecheck_benchmarks(verbose, load_benchmarks(sys.argv[3]))
    elif "ntyping-one" == sys.argv[2]:
        ntypecheck_one(verbose, sys.argv[3])
    elif "show" == sys.argv[2]:
        show_benchmarks(verbose, load_benchmarks(sys.argv[3]))
    elif "show-one" == sys.argv[2]:
        show_one(verbose, sys.argv[3])
    elif "make_table" == sys.argv[2]:
        make_table(verbose, sys.argv[3])
    elif "run_one" == sys.argv[2]:
        run_one_benchs(verbose, sys.argv[3])

