import sys
import argparse
import os
import json
import iter_benchs
import run

if __name__ == '__main__':
    if_verbose = None
    try:
        if sys.argv[1] == "verbose":
            if_verbose = True
    except:
        if_verbose = False
    benchmark_table, resfile = iter_benchs.init ()
    # print(benchmark_table)
    for name in iter_benchs.test_names:
        source, path, is_rec = iter_benchs.get_info_from_name (benchmark_table, name)
        if os.path.exists(resfile):
            os.remove(resfile)
        run.test_parsing(path, if_verbose)
