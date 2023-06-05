import sys
import argparse
import os
import json

meta_config_file = "meta-config.json"

def load (tab):
    top_dir = tab['benchmark_dir']
    res = {}
    for info in tab['benchmarks_info']:
        source = info["benchmark_source"]
        for entry in info['benchmarks']:
            path = "{}/{}".format(top_dir,entry.lower())
            res[entry] = (source, path)
    return res

def load_benchmarks ():
    with open (meta_config_file) as f:
        j = json.load(f)
        resfile = j['resfile']
        benchmark_table_file = j['benchmark_table_file']
        with open (benchmark_table_file) as f:
            benchmark_table = json.load(f)
    return load(benchmark_table)
