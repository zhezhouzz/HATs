import sys
import argparse
import os
import json

meta_config_file = "meta-config.json"

names = [
    "SizedList",
    "SortedList",
    "UniqueList",
    "SizedTree",
    "CompleteTree",
    "RedBlackTree",
    "SizedBST",
    "BatchedQueue",
    "BankersQueue",
    "Stream",
    "SizedHeap",
    "LeftistHeap",
    "SizedSet",
    "UnbalanceSet"
]

stlc_names = [
    "nonderter_dec",
    "gen_const",
    "type_eq'",
    "type_eq",
    "gen_type'",
    "gen_type",
    "var_with_type'",
    "var_with_type",
    "or_var_in_typectx",
    "combine_terms",
    "gen_term_no_app'",
    "gen_term_no_app",
    "gen_term_size'",
    "gen_term_size"
]

test_names = ["parsecons"]

# stlc_names = [
#     "type_eq'",
#     "gen_type'",
#     "var_with_type'",
#     "gen_term_no_app'",
#     "gen_term_size'"
# ]

def get_info_from_name(tab, name):
    source = None
    path = None
    is_rec = True
    for info in tab['benchmarks_info']:
        for entry in info['benchmarks']:
            if entry["name"] == name:
                source = info["benchmark_source"]
                path = "{}/{}/{}".format(tab['benchmark_dir'], source, entry["path"])
                is_rec = entry["is_rec"]
                break
    return source, path, is_rec

def init ():
    resfile = None
    benchmark_table = None
    with open (meta_config_file) as f:
        j = json.load(f)
        resfile = j['resfile']
        benchmark_table_file = j['benchmark_table_file']
        with open (benchmark_table_file) as f:
            benchmark_table = json.load(f)
    return benchmark_table, resfile
