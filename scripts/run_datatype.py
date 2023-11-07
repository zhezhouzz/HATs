import sys
import argparse
import os
import json
import marple_interface
import colored
import pathlib

def load(tab):
    top_dir = tab['benchmark_dir']
    res = {}
    for info in tab['benchmarks_info']:
        source = info["benchmark_source"]
        for entry in info['benchmarks']:
            path = "{}/{}".format(top_dir,entry.lower())
            res[entry] = (source, path)
    return res

def load_datatype(path):
    ri_file = "{}/ri.ml".format(path)
    lib_nty_file = "{}/lib_nty.ml".format(path)
    lib_rty_file = "{}/lib_rty.ml".format(path)
    automata_preds_file = "{}/automata_preds.ml".format(path)
    known_files = [ri_file, lib_nty_file, lib_rty_file, automata_preds_file]
    # print(path)
    files = [str(f) for f in pathlib.Path().glob("{}/*.ml".format(path))]
    files = [f for f in files if not f in known_files]
    files.sort()
    config = { "ri_file": ri_file,
               "lib_nty_file": lib_nty_file,
               "lib_rty_file": lib_rty_file,
               "automata_preds_file": automata_preds_file,
               "methods": files }
    return config

def print_datatype(config, verbose):
    print (colored.bold_text("Basic Types of Underline Effectful Library:"))
    marple_interface.print_raw(config["lib_nty_file"], verbose)
    print (colored.bold_text("Automata Predicates:"))
    marple_interface.print_raw(config["automata_preds_file"], verbose)
    print (colored.bold_text("Refinement Types of Underline Effectful Library:"))
    marple_interface.print_raw(config["lib_rty_file"], verbose)
    print (colored.bold_text("Rrepresentaion Invariant:"))
    marple_interface.print_raw(config["ri_file"], verbose)
    print (colored.bold_text("Datatype Interefaces:"))
    for path in config["methods"]:
        marple_interface.print_raw(path, verbose)

def ntypecheck_datatype(config, verbose):
    for path in config["methods"]:
        marple_interface.ri_ntype_check(path, verbose)

if __name__ == '__main__':
    try:
        if sys.argv[2] == "verbose":
            verbose = True
    except:
        verbose = False
    # print_datatype(load_datatype(sys.argv[1]), verbose)
    marple_interface.build_marple(verbose)
    ntypecheck_datatype(load_datatype(sys.argv[1]), verbose)
